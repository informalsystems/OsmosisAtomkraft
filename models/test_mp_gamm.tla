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
GetOr(_map, _key, _value) ==
    IF _key \in DOMAIN _map THEN _map[_key] ELSE _value


\* @type: (a -> Int, a -> Int) => a -> Int;
MergeMap(_map1, _map2) ==
    [
        _key \in DOMAIN _map1 \union DOMAIN _map2 |->
        GetOr(_map1, _key, 0) + GetOr(_map2, _key, 0)
    ]


\* @type: ($pool, Int) => $pool;
UpdatePoolShare(_pool, _user_share) ==
    LET
    _user_share_dec == ToDec(_user_share)
    _pool_share_dec == ToDec(_pool.share)
    \* pool_share should never be zero
    _ratio_dec == Div(_user_share_dec, _pool_share_dec)
    _update_amount == [_d \in DOMAIN _pool.amounts |-> Ceil(Mult(ToDec(_pool.amounts[_d]), _ratio_dec))]
    IN
    [
        _pool
        EXCEPT
        !.share = @ + _user_share,
        !.amounts = MergeMap(@, _update_amount)
    ]


\* if share > 0, join pool
\* if share < 0, exit pool
\* @type: (Str, Int, Int) => Bool;
UpdatePoolHandler(_sender, _pool_id, _share) ==
    LET
    _old_pool == pools[_pool_id]
    _new_pool == UpdatePoolShare(_old_pool, _share)
    _old_balance == bank[_sender]
    _new_balance == MergeMap(_old_balance, [_d \in DOMAIN _old_pool.amounts |-> _old_pool.amounts[_d] - _new_pool.amounts[_d]])
    _old_lp_balance == lp_bank[_sender]
    _new_lp_balance == MergeMap(_old_lp_balance, SetAsFun({<<_old_pool.id, _new_pool.share - _old_pool.share>>}))
    IN
    \* pre-condition: can not exit pool with negative share
    \* potential problem when share is zero.
    \* what happens, when pool share is empty and the amounts are empty.
    \* how is ratio is calculated? how to keep track of ratio when share is zero?
    /\ _new_pool.share > 0
    \* pre-condition: can not exit pool with more than available lp shares
    /\ \A _d \in DOMAIN _new_lp_balance: _new_lp_balance[_d] >= 0
    \* pre-condition: can not join pool with more than available amounts
    /\ \A _d \in DOMAIN _new_balance: _new_balance[_d] >= 0
    /\ pools' = [pools EXCEPT ![_pool_id] = _new_pool]
    /\ bank' = [bank EXCEPT ![_sender] = _new_balance]
    /\ lp_bank' = [lp_bank EXCEPT ![_sender] = _new_lp_balance]


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
CreatePoolHandler(_sender, _amounts, _weights) ==
    LET
    _next_pool_id == Len(pools) + 1
    _new_pool == NewPool(_next_pool_id, _amounts, _weights)
    _old_balance == bank[_sender]
    _new_balance == MergeMap(_old_balance, [_d \in DOMAIN _amounts |-> -_amounts[_d]])
    _old_lp_balance == lp_bank[_sender]
    _new_lp_balance == MergeMap(_old_lp_balance, SetAsFun({<<_new_pool.id, _new_pool.share>>}))
    IN
    \* pre-condition: can not create pool with more than available amounts
    /\ \A _d \in DOMAIN _new_balance: _new_balance[_d] >= 0
    /\ pools' = Append(pools, _new_pool)
    /\ bank' = [bank EXCEPT ![_sender] = _new_balance]
    /\ lp_bank' = [lp_bank EXCEPT ![_sender] = _new_lp_balance]


\* @type: Str => Bool;
CreatePoolNext(_sender) ==
    \E _lpIds \in SUBSET DOMAIN bank[_sender]:
    \E _amounts \in [_lpIds -> Nat]:
    \E _weights \in [_lpIds -> Nat]:
        /\ Cardinality(_lpIds) > 1
        /\ \A _d \in _lpIds: _amounts[_d] > 0 /\ _weights[_d] > 0
        /\ CreatePoolHandler(_sender, _amounts, _weights)
        /\ action' = Variant("CreatePool", [sender |-> _sender, amounts |-> _amounts, weights |-> _weights])
        /\ outcome' = Variant("CreatePool", [id |-> pools'[Len(pools')].id])


\* @type: Str => Bool;
UpdatePoolNext(_sender) ==
    \E _pool_id \in DOMAIN pools:
    \E _share \in Nat:
        /\ _share > 0
        /\ \/ /\ UpdatePoolHandler(_sender, _pool_id, _share)
              /\ action' = Variant("JoinPool", [sender |-> _sender, id |-> _pool_id, share |-> _share])
           \/ /\ UpdatePoolHandler(_sender, _pool_id, -_share)
              /\ action' = Variant("ExitPool", [sender |-> _sender, id |-> _pool_id, share |-> _share])
        /\ outcome' = Variant("UpdatePool", [
                deltas |-> [_d \in DOMAIN pools[_pool_id].amounts |-> pools'[_pool_id].amounts[_d] - pools[_pool_id].amounts[_d]]
            ])

\* amount_in can be negative
\* @type: ($pool, $denom, $denom, Int) => Int;
CalcAmountOut(_pool, _denom_in, _denom_out, _amount_in) ==
    LET
    _current_balance_in == ToDec(_pool.amounts[_denom_in])
    _current_balance_out == ToDec(_pool.amounts[_denom_out])
    _next_balance_in == ToDec(_pool.amounts[_denom_in] + _amount_in)
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
    _next_balance_out == Mult(_current_balance_out, Div(_current_balance_in, _next_balance_in))
    IN
    \* next_balance_out should never be less than actual value
    \* otherwise, users can exploit it to take out money
    _pool.amounts[_denom_out] - Ceil(_next_balance_out)


\* if amount is positive, we are calculating amount_out
\* if amount is negative, we are calculating amount_in
\* @type: (Str, $lpId, $denom, $denom, Int) => Bool;
SwapAmountHandler(_sender, _pool_id, _denom_in, _denom_out, _amount_in) ==
    LET
    _old_pool == pools[_pool_id]
    _amount_out == CalcAmountOut(_old_pool, _denom_in, _denom_out, _amount_in)
    _new_pool == [_old_pool EXCEPT !.amounts = MergeMap(@, SetAsFun({<<_denom_in, _amount_in>>, <<_denom_out, -_amount_out>>}))]
    _old_balance == bank[_sender]
    _new_balance == MergeMap(_old_balance, SetAsFun({<<_denom_in, -_amount_in>>, <<_denom_out, _amount_out>>}))
    IN
    \* pre-condition: because Z3 doesn't support constraining exponents
    \* assumes, the weight ratio is 1
    /\ _old_pool.weights[_denom_in] = _old_pool.weights[_denom_out]
    \* pre-condition: can not swap with more than available amounts
    /\ \A _d \in DOMAIN _new_balance: _new_balance[_d] >= 0
    \* pre-condition: can not swap with pool with smaller amounts
    \* pre-condition: pool balance will always be positive
    /\ \A _d \in DOMAIN _new_pool.amounts: _new_pool.amounts[_d] > 0
    /\ pools' = [pools EXCEPT ![_pool_id] = _new_pool]
    /\ bank' = [bank EXCEPT ![_sender] = _new_balance]
    /\ UNCHANGED lp_bank


\* @type: Str => Bool;
SwapAmountNext(_sender) ==
    \E _pool_id \in DOMAIN pools:
    \E _amount \in Nat:
    \E _denom_in \in DOMAIN pools[_pool_id].amounts:
    \E _denom_out \in DOMAIN pools[_pool_id].amounts:
        /\ _denom_in /= _denom_out
        /\ _amount > 0
        /\ \/ /\ SwapAmountHandler(_sender, _pool_id, _denom_in, _denom_out, _amount)
              /\ action' = Variant("SwapInAmount", [
                    sender |-> _sender, id |-> _pool_id, denom_in |-> _denom_in, denom_out |-> _denom_out, amount_in |-> _amount
                ])
           \/ /\ SwapAmountHandler(_sender, _pool_id, _denom_out, _denom_in, -_amount)
              /\ action' = Variant("SwapOutAmount", [
                    sender |-> _sender, id |-> _pool_id, denom_in |-> _denom_in, denom_out |-> _denom_out, amount_out |-> _amount
                ])
        /\ outcome' = Variant("UpdatePool", [
                deltas |-> [_d \in DOMAIN pools[_pool_id].amounts |-> pools'[_pool_id].amounts[_d] - pools[_pool_id].amounts[_d]]
            ])


Init ==
    \E init_balance \in Nat:
        /\ init_balance > 0
        \* cosmos-sdk balance upper limit
        /\ init_balance < 2^(256-60)
        /\ pools = <<>>
        /\ bank \in [USERS -> [DENOMS -> {init_balance}]]
        /\ lp_bank = [_u \in USERS |-> SetAsFun({})]
        /\ action = Variant("Genesis", bank)
        /\ outcome = Variant("Genesis", 0)


Next ==
    \E _sender \in USERS:
        \/ CreatePoolNext(_sender)
        \/ UpdatePoolNext(_sender)
        \/ SwapAmountNext(_sender)


\* invariant
ConstantDenomSupply ==
    \A _denom \in DENOMS:
        LET
        _OldPoolAdd(_sum, _pool_id) == _sum + GetOr(pools[_pool_id].amounts, _denom, 0)
        _OldBankAdd(_sum, _user) == _sum + GetOr(bank[_user], _denom, 0)
        _NewPoolAdd(_sum, _pool_id) == _sum + GetOr(pools'[_pool_id].amounts, _denom, 0)
        _NewBankAdd(_sum, _user) == _sum + GetOr(bank'[_user], _denom, 0)
        _old_pool_amount == ApaFoldSet(_OldPoolAdd, 0, DOMAIN pools)
        _old_bank_amount == ApaFoldSet(_OldBankAdd, 0, DOMAIN bank)
        _new_pool_amount == ApaFoldSet(_NewPoolAdd, 0, DOMAIN pools')
        _new_bank_amount == ApaFoldSet(_NewBankAdd, 0, DOMAIN bank')
        IN
        _old_pool_amount + _old_bank_amount = _new_pool_amount + _new_bank_amount


\* invariant
ConsistentLPTokenSupply ==
    \A _pool_id \in DOMAIN pools:
        LET
        _LPBankAdd(_sum, _user) == _sum + GetOr(lp_bank[_user], _pool_id, 0)
        _lp_bank_amount == ApaFoldSet(_LPBankAdd, 0, DOMAIN lp_bank)
        IN
        pools[_pool_id].share = _lp_bank_amount


\* invariant
PositiveLPAmounts ==
    \A _pool_id \in DOMAIN pools:
        /\ \A _user \in DOMAIN lp_bank: GetOr(lp_bank[_user], _pool_id, 0) >= 0
        /\ pools[_pool_id].share >= 0


\* invariant
PositiveDenomAmounts ==
    \A _denom \in DENOMS:
        /\ \A _pool_id \in DOMAIN pools: GetOr(pools[_pool_id].amounts, _denom, 0) >= 0
        /\ \A _user \in DOMAIN bank: GetOr(bank[_user], _denom, 0) >= 0


\* invariant
\* @type: ($trace) => Bool;
SameJoinExitShareNetPositiveDeltas(_trace) ==
    \A _i, _j \in DOMAIN _trace:
        LET
        _si == _trace[_i]
        _sj == _trace[_j]
        _action_i == VariantGetUnsafe("JoinPool", _si.action)
        _action_j == VariantGetUnsafe("ExitPool", _sj.action)
        _outcome_i == VariantGetUnsafe("UpdatePool", _si.outcome)
        _outcome_j == VariantGetUnsafe("UpdatePool", _sj.outcome)
        IN
        (
            /\ _i /= _j
            /\ VariantTag(_si.action) = "JoinPool"
            /\ VariantTag(_sj.action) = "ExitPool"
            /\ _action_i.id = _action_j.id
            /\ _action_i.share = _action_j.share
        ) => \A _k \in DOMAIN _outcome_i.deltas: _outcome_i.deltas[_k] + _outcome_j.deltas[_k] >= 0


CexZeroPoolShare ==
    \A _i \in DOMAIN pools:
        pools[_i].share > 0


\* @type: ($trace) => Bool;
CexZeroAssetIn(_trace) ==
    \A _i \in DOMAIN _trace:
        LET
        _si == _trace[_i]
        _outcome_i == VariantGetUnsafe("UpdatePool", _si.outcome)
        IN
        VariantTag(_si.action) = "JoinPool"
        => \A _k \in DOMAIN _outcome_i.deltas: _outcome_i.deltas[_k] /= 0


\* @type: ($trace) => Bool;
CexZeroAssetOut(_trace) ==
    \A _i \in DOMAIN _trace:
        LET
        _si == _trace[_i]
        _outcome_i == VariantGetUnsafe("UpdatePool", _si.outcome)
        IN
        VariantTag(_si.action) = "ExitPool"
        => \A _k \in DOMAIN _outcome_i.deltas: _outcome_i.deltas[_k] /= 0


\* @type: ($trace) => Bool;
CexCreateJoinExit(_trace) ==
    {"Genesis", "CreatePool", "JoinPool", "ExitPool"} /= {VariantTag(_trace[_i].action): _i \in DOMAIN _trace}

View ==
    VariantTag(action)

====
