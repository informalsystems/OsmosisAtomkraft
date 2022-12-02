---- MODULE multi_pool_gamm ----

\* Osmosis GAMM model using multiple pools and multiple denoms
\* Autho: Rano

EXTENDS Apalache, Integers, Sequences, FiniteSets, Variants, SequencesExt

(*
    @typeAlias: denom = Str;
    @typeAlias: lpDenom = Int;

    @typeAlias: pool = {
        swap_fee: Int,
        exit_fee: Int,
        denom: $lpDenom,
        share: Int,
        amounts: $denom -> Int,
        weights: $denom -> Int
    };

    @typeAlias: action =
        CreatePool({sender: Str, amounts: $denom -> Int, weights: $denom -> Int}) |
        JoinPool({sender: Str, id: Int, share: Int}) |
        ExitPool({sender: Str, id: Int, share: Int}) |
        Genesis(Str -> $denom -> Int);

    @typeAlias: outcome =
        CreatePool({denom: $lpDenom}) |
        JoinPool({real_share: Int}) |
        ExitPool({real_share: Int}) |
        Genesis(Int);
*)
typedefs == TRUE


VARIABLES
    \* @type: Seq($pool);
    pools,
    \* @type: Str -> $denom -> Int;
    bank,
    \* @type: Str -> $lpDenom -> Int;
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


\* @type: Int => Int;
Abs(x) == IF x < 0 THEN -x ELSE x

\* Example:
\* RoundDiv(10, 2) = 5
\* RoundDiv(10, 3) = 3
\* RoundDiv(10, 4) = 3
\* @type: (Int, Int) => Int;
RoundDiv(x, y) ==
    LET
    q == x \div y
    r == x % y
    IN
    q + IF (2*r) < y THEN 0 ELSE 1

\* @type: (Int, Int) => Int;
SignDiv(sign_x, sign_y) ==
    LET
    q == RoundDiv(Abs(sign_x), Abs(sign_y))
    pos_x == sign_x > 0
    pos_y == sign_y > 0
    IN
    IF pos_x = pos_y THEN q ELSE -q


\* @type: ($pool, Int) => $pool;
UpdatePoolShare(pool, share) ==
    IF pool.share > Abs(share) THEN
        LET
        ratio == SignDiv(pool.share, share)
        update_amount == [d \in DOMAIN pool.amounts |-> SignDiv(pool.amounts[d], ratio)]
        \* `share` with precision consistency
        share_delta == SignDiv(pool.share, ratio)
        IN
        [
            pool
            EXCEPT
            !.share = @ + share_delta,
            !.amounts = MergeMap(@, update_amount)
        ]
    ELSE
        LET
        ratio == SignDiv(share, pool.share)
        update_amount == [d \in DOMAIN pool.amounts |-> pool.amounts[d] * ratio]
        share_delta == pool.share * ratio
        IN
        [
            pool
            EXCEPT
            !.share = @ + share_delta,
            !.amounts = MergeMap(@, update_amount)
        ]


\* if share > 0, join pool
\* if share < 0, exit pool
\* @type: (Str, Int, Int) => Bool;
UpdatePoolHandler(sender, pool_id, share) ==
    LET
    old_pool == pools[pool_id]
    new_pool == UpdatePoolShare(old_pool, share)
    lp_tokens == SetAsFun({<<old_pool.denom, new_pool.share - old_pool.share>>})
    old_balance == bank[sender]
    new_balance == MergeMap(old_balance, [d \in DOMAIN old_pool.amounts |-> old_pool.amounts[d] - new_pool.amounts[d]])
    old_lp_balance == lp_bank[sender]
    new_lp_balance == MergeMap(old_lp_balance, lp_tokens)
    IN
    \* pre-condition: can not exit pool with negative share
    /\ new_pool.share >= 0
    \* pre-condition: can not exit pool with more than available lp shares
    /\ \A d \in DOMAIN new_lp_balance: new_lp_balance[d] >= 0
    \* pre-condition: can not join pool with more than available amounts
    /\ \A d \in DOMAIN new_balance: new_balance[d] >= 0
    \* ignore-zero: action should change the pool token supply
    /\ new_pool.share /= old_pool.share
    \* ignore-low-precision: action should change the pool asset amounts
    /\ \A d \in DOMAIN new_pool.amounts: new_pool.amounts[d] /= old_pool.amounts[d]
    /\ pools' = [pools EXCEPT ![pool_id] = new_pool]
    /\ bank' = [bank EXCEPT ![sender] = new_balance]
    /\ lp_bank' = [lp_bank EXCEPT ![sender] = new_lp_balance]


\* @type: (Int, $denom -> Int, $denom -> Int) => $pool;
NewPool(id, amounts, weights) ==
    [
        swap_fee |-> 0,
        exit_fee |-> 0,
        denom |-> id,
        share |-> 100 * ONE,
        amounts |-> amounts,
        weights |-> weights
    ]


\* @type: (Str, $denom -> Int, $denom -> Int) => Bool;
CreatePoolHandler(sender, amounts, weights) ==
    LET
    next_pool_id == Len(pools) + 1
    new_pool == NewPool(next_pool_id, amounts, weights)
    lp_tokens == SetAsFun({<<new_pool.denom, new_pool.share>>})
    old_balance == bank[sender]
    new_balance == MergeMap(old_balance, [d \in DOMAIN amounts |-> -amounts[d]])
    old_lp_balance == lp_bank[sender]
    new_lp_balance == MergeMap(old_lp_balance, lp_tokens)
    IN
    \* pre-condition: can not create pool with more than available amounts
    /\ \A d \in DOMAIN new_balance: new_balance[d] >= 0
    /\ pools' = Append(pools, new_pool)
    /\ bank' = [bank EXCEPT ![sender] = new_balance]
    /\ lp_bank' = [lp_bank EXCEPT ![sender] = new_lp_balance]


\* @type: Str => Bool;
CreatePoolNext(sender) ==
    \E lp_denoms \in SUBSET DOMAIN bank[sender]:
    \E amounts \in [lp_denoms -> Nat]:
    \E weights \in [lp_denoms -> Nat]:
        /\ Cardinality(lp_denoms) > 1
        /\ \A d \in lp_denoms: amounts[d] > 0 /\ weights[d] > 0
        /\ CreatePoolHandler(sender, amounts, weights)
        /\ action' = Variant("CreatePool", [sender |-> sender, amounts |-> amounts, weights |-> weights])
        /\ outcome' = Variant("CreatePool", [denom |-> Last(pools').denom])


\* @type: Str => Bool;
UpdatePoolNext(sender) ==
    \E pool_id \in DOMAIN pools:
    \E share \in Nat:
        /\ share > 0
        /\ \/ /\ UpdatePoolHandler(sender, pool_id, share)
              /\ action' = Variant("JoinPool", [sender |-> sender, id |-> pool_id, share |-> share])
              /\ outcome' = Variant("JoinPool", [real_share |-> Abs(pools'[pool_id].share - pools[pool_id].share)])
           \/ /\ UpdatePoolHandler(sender, pool_id, -share)
              /\ action' = Variant("ExitPool", [sender |-> sender, id |-> pool_id, share |-> share])
              /\ outcome' = Variant("ExitPool", [real_share |-> Abs(pools'[pool_id].share - pools[pool_id].share)])


Init ==
    \E init_balance \in Nat:
        /\ init_balance > 0
        /\ pools = <<>>
        /\ bank \in [USERS -> [DENOMS -> {init_balance}]]
        /\ lp_bank = [u \in USERS |-> SetAsFun({})]
        /\ action = Variant("Genesis", bank)
        /\ outcome = Variant("Genesis", 0)


Next ==
    \E sender \in USERS:
        \/ CreatePoolNext(sender)
        \/ UpdatePoolNext(sender)


\* `apalache check` success for length 3
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


\* `apalache check` success for length 3
\* invariant
ConsistentLPTokenSupply ==
    \A pool_id \in DOMAIN pools:
        LET
        LPBankAdd(sum, user) == sum + GetOr(lp_bank[user], pool_id, 0)
        lp_bank_amount == ApaFoldSet(LPBankAdd, 0, DOMAIN lp_bank)
        IN
        pools[pool_id].share = lp_bank_amount


\* `apalache check` success for length 3
\* invariant
PositiveLPAmounts ==
    \A pool_id \in DOMAIN pools:
        /\ \A user \in DOMAIN lp_bank: GetOr(lp_bank[user], pool_id, 0) >= 0
        /\ pools[pool_id].share >= 0


\* `apalache check` success for length 3
\* invariant
PositiveDenomAmounts ==
    \A denom \in DENOMS:
        /\ \A pool_id \in DOMAIN pools: GetOr(pools[pool_id].amounts, denom, 0) >= 0
        /\ \A user \in DOMAIN bank: GetOr(bank[user], denom, 0) >= 0

====