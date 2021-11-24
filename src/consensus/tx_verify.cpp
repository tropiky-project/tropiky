// Copyright (c) 2017-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <consensus/tx_verify.h>

#include <consensus/consensus.h>
#include <primitives/transaction.h>
#include <script/interpreter.h>
#include <consensus/validation.h>

// TODO remove the following dependencies
#include <chain.h>
#include <coins.h>
#include <util/moneystr.h>

#include <cassert>
#include "leveldb/db.h"
#include <leveldb/c.h>
#include <sstream>
#include <string>
#include <iostream>
#ifdef ENABLE_WALLET
#include <../wallet/rpcwallet.h>
#endif
#include <../wallet/coincontrol.h>
#include <../wallet/feebumper.h>
#include <../wallet/rpcwallet.h>
#include <../wallet/wallet.h>
#include <../wallet/walletdb.h>
#include <../wallet/walletutil.h>
#include <future>
#include <stdint.h>
#include <core_io.h>
#include <key_io.h>

#include <consensus/consensus.h>
#include <consensus/validation.h>
#include <key_io.h>
#include <script/script.h>
#include <script/standard.h>
#include <serialize.h>
#include <streams.h>
#include <univalue.h>
#include <util/system.h>
#include <util/moneystr.h>
#include <util/strencodings.h>

using namespace std;

vector <string> explode_raw_tx_verify(const string &delimiter, const string &explodeme);

vector <string> explode_raw_tx_verify(const string &delimiter, const string &str) {
    vector <string> arr;

    int strleng = str.length();
    int delleng = delimiter.length();
    if (delleng == 0)
        return arr;//no change

    int i = 0;
    int k = 0;
    while (i < strleng) {
        int j = 0;
        while (i + j < strleng && j < delleng && str[i + j] == delimiter[j])
            j++;
        if (j == delleng)//found delimiter
        {
            arr.push_back(str.substr(k, i - k));
            i += delleng;
            k = i;
        } else {
            i++;
        }
    }
    arr.push_back(str.substr(k, i - k));
    return arr;
}


std::vector<std::string> HexAddrPow = {
        "58374348377031714153313152544a345877566667514c36454d7456386874597866",
        "54764e33595670474270334e5877683379775864784564657733315134363752574a",
        "547062734c66755539575a386e37544e4e5a366a7337477141367532526f6456337a",
        "54757731395353695566596d596650566b4e416d4e56326e48615a674638776b5757",
        "54677539384d4b37626150506859644e644e33633141525a3773574362624c693448",
        "5461356679797850674b62566566695337686f32334242776135354a787869453569",
};

int hex_value_tx_verify(char hex_digit) {
    switch (hex_digit) {
        case '0':
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
        case '8':
        case '9':
            return hex_digit - '0';

        case 'A':
        case 'B':
        case 'C':
        case 'D':
        case 'E':
        case 'F':
            return hex_digit - 'A' + 10;

        case 'a':
        case 'b':
        case 'c':
        case 'd':
        case 'e':
        case 'f':
            return hex_digit - 'a' + 10;
    }
    throw std::invalid_argument("invalid hex digit");
}

string stringToHex_tx_verify(string str) {
    static const char hex_digits[] = "0123456789abcdef";
    std::string output;
    output.reserve(str.length() * 2);
    for (unsigned char c : str) {
        output.push_back(hex_digits[c >> 4]);
        output.push_back(hex_digits[c & 15]);
    }
    return output;
}

string hexToString_tx_verify(string str) {
    const auto len = str.length();
    if (len & 1) throw std::invalid_argument("odd length");
    std::string output_string;
    output_string.reserve(len / 2);
    for (auto it = str.begin(); it != str.end();) {
        int hi = hex_value_tx_verify(*it++);
        int lo = hex_value_tx_verify(*it++);
        output_string.push_back(hi << 4 | lo);
    }
    return output_string;
}

bool IsFinalTx(const CTransaction &tx, int nBlockHeight, int64_t nBlockTime)
{
    if (tx.nLockTime == 0)
        return true;
    if ((int64_t)tx.nLockTime < ((int64_t)tx.nLockTime < LOCKTIME_THRESHOLD ? (int64_t)nBlockHeight : nBlockTime))
        return true;
    for (const auto& txin : tx.vin) {
        if (!(txin.nSequence == CTxIn::SEQUENCE_FINAL))
            return false;
    }
    return true;
}

std::pair<int, int64_t> CalculateSequenceLocks(const CTransaction &tx, int flags, std::vector<int>* prevHeights, const CBlockIndex& block)
{
    assert(prevHeights->size() == tx.vin.size());

    // Will be set to the equivalent height- and time-based nLockTime
    // values that would be necessary to satisfy all relative lock-
    // time constraints given our view of block chain history.
    // The semantics of nLockTime are the last invalid height/time, so
    // use -1 to have the effect of any height or time being valid.
    int nMinHeight = -1;
    int64_t nMinTime = -1;

    // tx.nVersion is signed integer so requires cast to unsigned otherwise
    // we would be doing a signed comparison and half the range of nVersion
    // wouldn't support BIP 68.
    bool fEnforceBIP68 = static_cast<uint32_t>(tx.nVersion) >= 2
                      && flags & LOCKTIME_VERIFY_SEQUENCE;

    // Do not enforce sequence numbers as a relative lock time
    // unless we have been instructed to
    if (!fEnforceBIP68) {
        return std::make_pair(nMinHeight, nMinTime);
    }

    for (size_t txinIndex = 0; txinIndex < tx.vin.size(); txinIndex++) {
        const CTxIn& txin = tx.vin[txinIndex];

        // Sequence numbers with the most significant bit set are not
        // treated as relative lock-times, nor are they given any
        // consensus-enforced meaning at this point.
        if (txin.nSequence & CTxIn::SEQUENCE_LOCKTIME_DISABLE_FLAG) {
            // The height of this input is not relevant for sequence locks
            (*prevHeights)[txinIndex] = 0;
            continue;
        }

        int nCoinHeight = (*prevHeights)[txinIndex];

        if (txin.nSequence & CTxIn::SEQUENCE_LOCKTIME_TYPE_FLAG) {
            int64_t nCoinTime = block.GetAncestor(std::max(nCoinHeight-1, 0))->GetMedianTimePast();
            // NOTE: Subtract 1 to maintain nLockTime semantics
            // BIP 68 relative lock times have the semantics of calculating
            // the first block or time at which the transaction would be
            // valid. When calculating the effective block time or height
            // for the entire transaction, we switch to using the
            // semantics of nLockTime which is the last invalid block
            // time or height.  Thus we subtract 1 from the calculated
            // time or height.

            // Time-based relative lock-times are measured from the
            // smallest allowed timestamp of the block containing the
            // txout being spent, which is the median time past of the
            // block prior.
            nMinTime = std::max(nMinTime, nCoinTime + (int64_t)((txin.nSequence & CTxIn::SEQUENCE_LOCKTIME_MASK) << CTxIn::SEQUENCE_LOCKTIME_GRANULARITY) - 1);
        } else {
            nMinHeight = std::max(nMinHeight, nCoinHeight + (int)(txin.nSequence & CTxIn::SEQUENCE_LOCKTIME_MASK) - 1);
        }
    }

    return std::make_pair(nMinHeight, nMinTime);
}

bool EvaluateSequenceLocks(const CBlockIndex& block, std::pair<int, int64_t> lockPair)
{
    assert(block.pprev);
    int64_t nBlockTime = block.pprev->GetMedianTimePast();
    if (lockPair.first >= block.nHeight || lockPair.second >= nBlockTime)
        return false;

    return true;
}

bool SequenceLocks(const CTransaction &tx, int flags, std::vector<int>* prevHeights, const CBlockIndex& block)
{
    return EvaluateSequenceLocks(block, CalculateSequenceLocks(tx, flags, prevHeights, block));
}

unsigned int GetLegacySigOpCount(const CTransaction& tx)
{
    unsigned int nSigOps = 0;
    for (const auto& txin : tx.vin)
    {
        nSigOps += txin.scriptSig.GetSigOpCount(false);
    }
    for (const auto& txout : tx.vout)
    {
        nSigOps += txout.scriptPubKey.GetSigOpCount(false);
    }
    return nSigOps;
}

unsigned int GetP2SHSigOpCount(const CTransaction& tx, const CCoinsViewCache& inputs)
{
    if (tx.IsCoinBase())
        return 0;

    unsigned int nSigOps = 0;
    for (unsigned int i = 0; i < tx.vin.size(); i++)
    {
        const Coin& coin = inputs.AccessCoin(tx.vin[i].prevout);
        assert(!coin.IsSpent());
        const CTxOut &prevout = coin.out;
        if (prevout.scriptPubKey.IsPayToScriptHash())
            nSigOps += prevout.scriptPubKey.GetSigOpCount(tx.vin[i].scriptSig);
    }
    return nSigOps;
}

int64_t GetTransactionSigOpCost(const CTransaction& tx, const CCoinsViewCache& inputs, int flags)
{
    int64_t nSigOps = GetLegacySigOpCount(tx) * WITNESS_SCALE_FACTOR;

    if (tx.IsCoinBase())
        return nSigOps;

    if (flags & SCRIPT_VERIFY_P2SH) {
        nSigOps += GetP2SHSigOpCount(tx, inputs) * WITNESS_SCALE_FACTOR;
    }

    for (unsigned int i = 0; i < tx.vin.size(); i++)
    {
        const Coin& coin = inputs.AccessCoin(tx.vin[i].prevout);
        assert(!coin.IsSpent());
        const CTxOut &prevout = coin.out;
        nSigOps += CountWitnessSigOps(tx.vin[i].scriptSig, prevout.scriptPubKey, &tx.vin[i].scriptWitness, flags);
    }
    return nSigOps;
}

bool CheckTransaction(const CTransaction& tx, CValidationState &state, bool fCheckDuplicateInputs)
{
    // Basic checks that don't depend on any context
    if (tx.vin.empty())
        return state.DoS(10, false, REJECT_INVALID, "bad-txns-vin-empty");
    if (tx.vout.empty())
        return state.DoS(10, false, REJECT_INVALID, "bad-txns-vout-empty");
    // Size limits (this doesn't take the witness into account, as that hasn't been checked for malleability)
    if (::GetSerializeSize(tx, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS) * WITNESS_SCALE_FACTOR > MAX_BLOCK_WEIGHT)
        return state.DoS(100, false, REJECT_INVALID, "bad-txns-oversize");

    // Check for negative or overflow output values
    CAmount nValueOut = 0;
    for (const auto& txout : tx.vout)
    {
        if (txout.nValue < 0)
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-vout-negative");
        if (txout.nValue > MAX_MONEY)
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-vout-toolarge");
        nValueOut += txout.nValue;
        if (!MoneyRange(nValueOut))
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-txouttotal-toolarge");
    }

    // Check for duplicate inputs - note that this check is slow so we skip it in CheckBlock
    if (fCheckDuplicateInputs) {
        std::set<COutPoint> vInOutPoints;
        for (const auto& txin : tx.vin)
        {
            if (!vInOutPoints.insert(txin.prevout).second)
                return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-duplicate");
        }
    }

    if (tx.IsCoinBase())
    {
        if (/*tx.vin[0].scriptSig.size() < 2 ||*/ tx.vin[0].scriptSig.size() > 150)
            return state.DoS(100, false, REJECT_INVALID, "bad-cb-length");
    }
    else
    {
        for (const auto& txin : tx.vin)
            if (txin.prevout.IsNull())
                return state.DoS(10, false, REJECT_INVALID, "bad-txns-prevout-null");
    }

    return true;
}

bool CheckTransactionToGetData(const CTransaction &tx, CValidationState &state, int nHeight , double mlcDistribution ,const CBlock& block,
                               bool fCheckDuplicateInputs) {

    // Basic checks that don't depend on any context
    if (tx.vin.empty())
        return state.DoS(10, false, REJECT_INVALID, "bad-txns-vin-empty");
    if (tx.vout.empty())
        return state.DoS(10, false, REJECT_INVALID, "bad-txns-vout-empty");
    // Size limits (this doesn't take the witness into account, as that hasn't been checked for malleability)
    if (::GetSerializeSize(tx, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS) *
        WITNESS_SCALE_FACTOR > MAX_BLOCK_WEIGHT)
        return state.DoS(100, false, REJECT_INVALID, "bad-txns-oversize");
    // Check for negative or overflow output values
    CAmount nValueOut = 0;
    for (const auto &txout : tx.vout) {
        if (txout.nValue < 0)
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-vout-negative");
        if (txout.nValue > MAX_MONEY)
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-vout-toolarge");
        nValueOut += txout.nValue;
        if (!MoneyRange(nValueOut))
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-txouttotal-toolarge");
    }
    // Check for duplicate inputs - note that this check is slow so we skip it in CheckBlock
    if (fCheckDuplicateInputs) {
        std::set <COutPoint> vInOutPoints;
        for (const auto &txin : tx.vin) {
            if (!vInOutPoints.insert(txin.prevout).second)
                return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-duplicate");
        }
    }

    string hexconverted = "";
    std::string std_data_dir = GetDataDir().string();
    leveldb::Status status;
    leveldb::DB *db;
    leveldb::Options options;
    options.create_if_missing = true;
    bool canMine = true;

    if (tx.IsCoinBase()) {
        if (/*tx.vin[0].scriptSig.size() < 2 || */tx.vin[0].scriptSig.size() > 150) {
            return state.DoS(100, false, REJECT_INVALID, "bad-cb-length");
        }
        if (nHeight >=  Params().GetConsensus().nLastPOWBlock) {

            int result = mlcDistribution; //GetBlockSubsidy(nHeight, Params().GetConsensus()) * 90 / 100;
            const CScript &scriptPubKey = tx.vout[0].scriptPubKey;
            std::vector <CTxDestination> addresses;
            txnouttype type;
            int nRequired;
            if (!ExtractDestinations(scriptPubKey, type, addresses, nRequired)) {
                std::cout<<"address not found in tx_verify.cpp\n";
                //address not found
            }else{
                std::cout<<"address found in tx_verify.cpp\n";
            }
            for (const CTxDestination &addr : addresses) {
                std::string addressPow = EncodeDestination(addr);
                for (int i = 0; i < HexAddrPow.size(); ++i) {
                    if (addressPow == hexToString_tx_verify(HexAddrPow[i])) {
                        std::cout<<"addressMAtches= \n";
                        if (tx.vout[0].nValue < result) {
                            std::cout<<"addressMAtches value less= \n";
                            canMine = false;
                        }else{
                            std::cout<<"addressMAtches value good= \n";
                            canMine = true;
                            break;
                        }
                    } else {
                        std::cout<<"addressMAtches not matches= \n";
                        canMine = false;
                    }
                }
            }
            if (tx.IsCoinBase()) {
                if (!canMine) {
                    return state.DoS(100, false, REJECT_INVALID, "You can't mine pow now");
                }
            }
        }
    }
    else if (tx.IsCoinStake()) {
        if (/*tx.vin[0].scriptSig.size() < 2 || */tx.vin[0].scriptSig.size() > 150) {
            return state.DoS(100, false, REJECT_INVALID, "bad-cb-length");
        }
    }
    else {
        for (const auto &txin : tx.vin)
            if (txin.prevout.IsNull())
                return state.DoS(10, false, REJECT_INVALID, "bad-txns-prevout-null");
    }

    return true;
}

bool Consensus::CheckTxInputs(const CTransaction& tx, CValidationState& state, const CCoinsViewCache& inputs, int nSpendHeight, CAmount& txfee)
{
    // are the actual inputs available?
    if (!inputs.HaveInputs(tx)) {
        return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-missingorspent", false,
                         strprintf("%s: inputs missing/spent", __func__));
    }

    CAmount nValueIn = 0;
    for (unsigned int i = 0; i < tx.vin.size(); ++i) {
        const COutPoint &prevout = tx.vin[i].prevout;
        const Coin& coin = inputs.AccessCoin(prevout);
        assert(!coin.IsSpent());

        // If prev is coinbase, check that it's matured
        if (coin.IsCoinBase() && nSpendHeight - coin.nHeight < COINBASE_MATURITY) {
            return state.Invalid(false,
                                 REJECT_INVALID, "bad-txns-premature-spend-of-coinbase",
                                 strprintf("tried to spend coinbase at depth %d", nSpendHeight - coin.nHeight));
        }

        // Check for negative or overflow input values
        nValueIn += coin.out.nValue;
        if (!MoneyRange(coin.out.nValue) || !MoneyRange(nValueIn)) {
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputvalues-outofrange");
        }
    }

    const CAmount value_out = tx.GetValueOut();
    if (!tx.IsCoinStake()) {
        if (nValueIn < value_out) {
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-in-belowout", false,
                             strprintf("value in (%s) < value out (%s)", FormatMoney(nValueIn),
                                       FormatMoney(value_out)));
        }
    }

    // Tally transaction fees
    const CAmount txfee_aux = nValueIn - value_out;
    if (!tx.IsCoinStake()) {
        if (!MoneyRange(txfee_aux)) {
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-fee-outofrange");
        }
    }

    txfee = txfee_aux;
    return true;
}
