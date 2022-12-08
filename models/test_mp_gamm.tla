---- MODULE test_mp_gamm ----

\* Osmosis GAMM model using multiple pools and multiple denoms
\* Autho: Rano

EXTENDS Apalache, Integers, Sequences, FiniteSets, Variants, HighPrecisionDec

(*
    @typeAlias: denom = Str;
    @typeAlias: lpId = Int;

    @typeAlias: pool = {
        id: $lpId,
        swap_fee: Int,
        exit_fee: Int,
        share: Int,
        amounts: $denom -> Int,
        weights: $denom -> Int
    };

    @typeAlias: action =
        CreatePool({sender: Str, amounts: $denom -> Int, weights: $denom -> Int}) |
        JoinPool({sender: Str, id: $lpId, share: Int}) |
        ExitPool({sender: Str, id: $lpId, share: Int}) |
        SwapInAmount({sender: Str, id: $lpId, denom_in: $denom, denom_out: $denom, amount_in: Int}) |
        SwapOutAmount({sender: Str, id: $lpId, denom_in: $denom, denom_out: $denom, amount_out: Int}) |
        Genesis(Str -> $denom -> Int);

    @typeAlias: outcome =
        CreatePool({id: $lpId}) |
        UpdatePool({deltas: $denom -> Int}) |
        Genesis(Int);

    @typeAlias: state = {
        pools: Seq($pool),
        bank: Str -> $denom -> Int,
        lp_bank: Str -> $lpId-> Int,
        action: $action,
        outcome: $outcome
    };

    @typeAlias: trace = Seq($state);
*)
typedefs == TRUE


VARIABLES
    \* @type: Seq($pool);
    pools,
    \* @type: Str -> $denom -> Int;
    bank,
    \* @type: Str -> $lpId-> Int;
    lp_bank,

    \* @type: $action;
    action,

    \* @type: $outcome;
    outcome


USERS == {"A", "B", "C"}
DENOMS == {"uosmo", "uatom", "ujuno"}
ONE == 10^18


\* @type: (a -> b, a, b) => b;
GetOr(map, key, value) ==
    IF key \in DOMAIN map THEN map[key] ELSE value


\* @type: (a -> Int, a -> Int) => a -> Int;
MergeMap(map1, map2) ==
    [
        key \in DOMAIN map1 \union DOMAIN map2 |->
        GetOr(map1, key, 0) + GetOr(map2, key, 0)
    ]


\* @type: ($pool, Int) => $pool;
UpdatePoolShare(pool, user_share) ==
    LET
    user_share_dec == ToDec(user_share)
    pool_share_dec == ToDec(pool.share)
    \* pool_share should never be zero
    ratio_dec == Div(user_share_dec, pool_share_dec)
    update_amount == [d \in DOMAIN pool.amounts |-> Ceil(Mult(ToDec(pool.amounts[d]), ratio_dec))]
    IN
    [
        pool
        EXCEPT
        !.share = @ + user_share,
        !.amounts = MergeMap(@, update_amount)
    ]


\* if share > 0, join pool
\* if share < 0, exit pool
\* @type: (Str, Int, Int) => Bool;
UpdatePoolHandler(sender, pool_id, share) ==
    LET
    old_pool == pools[pool_id]
    new_pool == UpdatePoolShare(old_pool, share)
    old_balance == bank[sender]
    new_balance == MergeMap(old_balance, [d \in DOMAIN old_pool.amounts |-> old_pool.amounts[d] - new_pool.amounts[d]])
    old_lp_balance == lp_bank[sender]
    new_lp_balance == MergeMap(old_lp_balance, SetAsFun({<<old_pool.id, new_pool.share - old_pool.share>>}))
    IN
    \* pre-condition: can not exit pool with negative share
    \* potential problem when share is zero.
    \* what happens, when pool share is empty and the amounts are empty.
    \* how is ratio is calculated? how to keep track of ratio when share is zero?
    /\ new_pool.share > 0
    \* pre-condition: can not exit pool with more than available lp shares
    /\ \A d \in DOMAIN new_lp_balance: new_lp_balance[d] >= 0
    \* pre-condition: can not join pool with more than available amounts
    /\ \A d \in DOMAIN new_balance: new_balance[d] >= 0
    /\ pools' = [pools EXCEPT ![pool_id] = new_pool]
    /\ bank' = [bank EXCEPT ![sender] = new_balance]
    /\ lp_bank' = [lp_bank EXCEPT ![sender] = new_lp_balance]


\* @type: ($lpId, $denom -> Int, $denom -> Int) => $pool;
NewPool(id, amounts, weights) ==
    [
        id |-> id,
        swap_fee |-> 0,
        exit_fee |-> 0,
        share |-> 100 * ONE,
        amounts |-> amounts,
        weights |-> weights
    ]


\* @type: (Str, $denom -> Int, $denom -> Int) => Bool;
CreatePoolHandler(sender, amounts, weights) ==
    LET
    next_pool_id == Len(pools) + 1
    new_pool == NewPool(next_pool_id, amounts, weights)
    old_balance == bank[sender]
    new_balance == MergeMap(old_balance, [d \in DOMAIN amounts |-> -amounts[d]])
    old_lp_balance == lp_bank[sender]
    new_lp_balance == MergeMap(old_lp_balance, SetAsFun({<<new_pool.id, new_pool.share>>}))
    IN
    \* pre-condition: can not create pool with more than available amounts
    /\ \A d \in DOMAIN new_balance: new_balance[d] >= 0
    /\ pools' = Append(pools, new_pool)
    /\ bank' = [bank EXCEPT ![sender] = new_balance]
    /\ lp_bank' = [lp_bank EXCEPT ![sender] = new_lp_balance]


\* @type: Str => Bool;
CreatePoolNext(sender) ==
    \E lpIds \in SUBSET DOMAIN bank[sender]:
    \E amounts \in [lpIds -> Nat]:
    \E weights \in [lpIds -> Nat]:
        /\ Cardinality(lpIds) > 1
        /\ \A d \in lpIds: amounts[d] > 0 /\ weights[d] > 0
        /\ CreatePoolHandler(sender, amounts, weights)
        /\ action' = Variant("CreatePool", [sender |-> sender, amounts |-> amounts, weights |-> weights])
        /\ outcome' = Variant("CreatePool", [id |-> pools'[Len(pools')].id])


\* @type: Str => Bool;
UpdatePoolNext(sender) ==
    \E pool_id \in DOMAIN pools:
    \E share \in Nat:
        /\ share > 0
        /\ \/ /\ UpdatePoolHandler(sender, pool_id, share)
              /\ action' = Variant("JoinPool", [sender |-> sender, id |-> pool_id, share |-> share])
           \/ /\ UpdatePoolHandler(sender, pool_id, -share)
              /\ action' = Variant("ExitPool", [sender |-> sender, id |-> pool_id, share |-> share])
        /\ outcome' = Variant("UpdatePool", [
                deltas |-> [d \in DOMAIN pools[pool_id].amounts |-> pools'[pool_id].amounts[d] - pools[pool_id].amounts[d]]
            ])

\* amount_in can be negative
\* @type: ($pool, $denom, $denom, Int) => Int;
CalcAmountOut(pool, denom_in, denom_out, amount_in) ==
    LET
    current_balance_in == ToDec(pool.amounts[denom_in])
    current_balance_out == ToDec(pool.amounts[denom_out])
    next_balance_in == ToDec(pool.amounts[denom_in] + amount_in)
    \* https://docs.osmosis.zone/osmosis-core/modules/gamm/#swap
    \* balance_in^weight_in * balance_out^weight_out = constant
    \* balance_in^weight_in * balance_out^weight_out = (balance_in + amount_in)^weight_in * (balance_out - amount_out)^weight_out
    \* (balance_out - amount_out) = balance_out * (balance_in / (balance_in + amount_in))^(weight_in / weight_out)
    \* weight_ratio == pool.weights[denom_in] \div pool.weights[denom_out]
    \*
    \* TODO: Z3 doesn't support constraining exponents
    \* next_balance_out == Mult(current_balance_out, PowInt(Div(current_balance_in, next_balance_in), weight_ratio))
    \*
    \* when weight_ratio is 1
    next_balance_out == Mult(current_balance_out, Div(current_balance_in, next_balance_in))
    IN
    pool.amounts[denom_out] - Floor(next_balance_out)


\* if amount is positive, we are calculating amount_out
\* if amount is negative, we are calculating amount_in
\* @type: (Str, $lpId, $denom, $denom, Int) => Bool;
SwapAmountHandler(sender, pool_id, denom_in, denom_out, amount_in) ==
    LET
    old_pool == pools[pool_id]
    amount_out == CalcAmountOut(old_pool, denom_in, denom_out, amount_in)
    new_pool == [old_pool EXCEPT !.amounts = MergeMap(@, SetAsFun({<<denom_in, amount_in>>, <<denom_out, -amount_out>>}))]
    old_balance == bank[sender]
    new_balance == MergeMap(old_balance, SetAsFun({<<denom_in, -amount_in>>, <<denom_out, amount_out>>}))
    IN
    \* pre-condition: because Z3 doesn't support constraining exponents
    \* assumes, the weight ratio is 1
    /\ old_pool.weights[denom_in] = old_pool.weights[denom_out]
    \* pre-condition: can not swap with more than available amounts
    /\ \A d \in DOMAIN new_balance: new_balance[d] >= 0
    \* pre-condition: can not swap with pool with smaller amounts
    \* pre-condition: pool balance will always be positive
    /\ \A d \in DOMAIN new_pool.amounts: new_pool.amounts[d] > 0
    /\ pools' = [pools EXCEPT ![pool_id] = new_pool]
    /\ bank' = [bank EXCEPT ![sender] = new_balance]
    /\ UNCHANGED lp_bank


\* @type: Str => Bool;
SwapAmountNext(sender) ==
    \E pool_id \in DOMAIN pools:
    \E amount \in Nat:
    \E denom_in \in DOMAIN pools[pool_id].amounts:
    \E denom_out \in DOMAIN pools[pool_id].amounts:
        /\ denom_in /= denom_out
        /\ amount > 0
        /\ \/ /\ SwapAmountHandler(sender, pool_id, denom_in, denom_out, amount)
              /\ action' = Variant("SwapInAmount", [
                    sender |-> sender, id |-> pool_id, denom_in |-> denom_in, denom_out |-> denom_out, amount_in |-> amount
                ])
           \/ /\ SwapAmountHandler(sender, pool_id, denom_out, denom_in, -amount)
              /\ action' = Variant("SwapOutAmount", [
                    sender |-> sender, id |-> pool_id, denom_in |-> denom_in, denom_out |-> denom_out, amount_out |-> amount
                ])
        /\ outcome' = Variant("UpdatePool", [
                deltas |-> [d \in DOMAIN pools[pool_id].amounts |-> pools'[pool_id].amounts[d] - pools[pool_id].amounts[d]]
            ])


Init ==
    \E init_balance \in Nat:
        /\ init_balance > 0
        \* cosmos-sdk balance upper limit
        /\ init_balance < 2^(256-60)
        /\ pools = <<>>
        /\ bank \in [USERS -> [DENOMS -> {init_balance}]]
        /\ lp_bank = [u \in USERS |-> SetAsFun({})]
        /\ action = Variant("Genesis", bank)
        /\ outcome = Variant("Genesis", 0)


Next ==
    \E sender \in USERS:
        \/ CreatePoolNext(sender)
        \/ UpdatePoolNext(sender)
        \/ SwapAmountNext(sender)


\* invariant
ConstantDenomSupply ==
    \A denom \in DENOMS:
        LET
        OldPoolAdd(sum, pool_id) == sum + GetOr(pools[pool_id].amounts, denom, 0)
        OldBankAdd(sum, user) == sum + GetOr(bank[user], denom, 0)
        NewPoolAdd(sum, pool_id) == sum + GetOr(pools'[pool_id].amounts, denom, 0)
        NewBankAdd(sum, user) == sum + GetOr(bank'[user], denom, 0)
        old_pool_amount == ApaFoldSet(OldPoolAdd, 0, DOMAIN pools)
        old_bank_amount == ApaFoldSet(OldBankAdd, 0, DOMAIN bank)
        new_pool_amount == ApaFoldSet(NewPoolAdd, 0, DOMAIN pools')
        new_bank_amount == ApaFoldSet(NewBankAdd, 0, DOMAIN bank')
        IN
        old_pool_amount + old_bank_amount = new_pool_amount + new_bank_amount


\* invariant
ConsistentLPTokenSupply ==
    \A pool_id \in DOMAIN pools:
        LET
        LPBankAdd(sum, user) == sum + GetOr(lp_bank[user], pool_id, 0)
        lp_bank_amount == ApaFoldSet(LPBankAdd, 0, DOMAIN lp_bank)
        IN
        pools[pool_id].share = lp_bank_amount


\* invariant
PositiveLPAmounts ==
    \A pool_id \in DOMAIN pools:
        /\ \A user \in DOMAIN lp_bank: GetOr(lp_bank[user], pool_id, 0) >= 0
        /\ pools[pool_id].share >= 0


\* invariant
PositiveDenomAmounts ==
    \A denom \in DENOMS:
        /\ \A pool_id \in DOMAIN pools: GetOr(pools[pool_id].amounts, denom, 0) >= 0
        /\ \A user \in DOMAIN bank: GetOr(bank[user], denom, 0) >= 0


\* invariant
\* @type: ($trace) => Bool;
SameJoinExitShareNetPositiveDeltas(trace) ==
    \A i, j \in DOMAIN trace:
        LET
        si == trace[i]
        sj == trace[j]
        action_i == VariantGetUnsafe("JoinPool", si.action)
        action_j == VariantGetUnsafe("ExitPool", sj.action)
        outcome_i == VariantGetUnsafe("UpdatePool", si.outcome)
        outcome_j == VariantGetUnsafe("UpdatePool", sj.outcome)
        IN
        (
            /\ i /= j
            /\ VariantTag(si.action) = "JoinPool"
            /\ VariantTag(sj.action) = "ExitPool"
            /\ action_i.id = action_j.id
            /\ action_i.share = action_j.share
        ) => \A k \in DOMAIN outcome_i.deltas: outcome_i.deltas[k] + outcome_j.deltas[k] >= 0


CexZeroPoolShare ==
    \A i \in DOMAIN pools:
        pools[i].share > 0


\* @type: ($trace) => Bool;
CexZeroAssetIn(trace) ==
    \A i \in DOMAIN trace:
        LET
        si == trace[i]
        outcome_i == VariantGetUnsafe("UpdatePool", si.outcome)
        IN
        VariantTag(si.action) = "JoinPool"
        => \A k \in DOMAIN outcome_i.deltas: outcome_i.deltas[k] /= 0


\* @type: ($trace) => Bool;
CexZeroAssetOut(trace) ==
    \A i \in DOMAIN trace:
        LET
        si == trace[i]
        outcome_i == VariantGetUnsafe("UpdatePool", si.outcome)
        IN
        VariantTag(si.action) = "ExitPool"
        => \A k \in DOMAIN outcome_i.deltas: outcome_i.deltas[k] /= 0


\* @type: ($trace) => Bool;
CexCreateJoinExit(trace) ==
    {"Genesis", "CreatePool", "JoinPool", "ExitPool"} /= {VariantTag(trace[i].action): i \in DOMAIN trace}

View ==
    VariantTag(action)

====
