-------------------------- MODULE gamm ----------------------------
EXTENDS
    Integers,
    FiniteSets,
    Sequences,
    gamm_typedefs,
    status_codes,
    TLC

VARIABLE
    \* @type: Str -> [amount: Int, weight: Int];
    pool_assets,
    \* @type: [share_denom: Str, amount: Int];
    total_shares,
    \* @type: Int;
    total_weight,
    \* @type: Set(Str);
    users,

    \* @type: ACTION;
    action_taken,
    \* @type: Str;
    outcome_status


\* @type: (Str, Str -> [amount: Int, weight: Int]) => Bool;
CreatePool(sender, initial_assets) == 
    /\  pool_assets' = [x \in DOMAIN initial_assets |-> [amount |-> initial_assets[x].amount, weight |-> (initial_assets[x].weight * GuaranteedWeightPrecision)]]
    /\  total_shares' = [share_denom |-> InitPoolShareDenom, amount |-> InitPoolShareAmount]
    \*TODO* /\  total_weight' = ApaFoldSet(LAMBDA x, y: x + pool_assets[y][1] * pool_assets[y][2], 0, DOMAIN pool_assets) \* sum of all pool_assets' "weight"
    /\  users' = {sender}
    /\  outcome_status' = CREATE_SUCCESS
    /\  action_taken' = [
            poolId          |-> 1,              \* TODO * - Add counter or numPools variable
            sender          |-> sender,
            action_type     |-> "create pool"
        ]
    /\  UNCHANGED <<total_weight>>

\* @type: (Str, Int) => Bool;
JoinPool(sender, shareOutAmount) ==
    \*LET poolLiquidity == <<>> IN          \* TODO *  Seq([denom, amount]) <= pool_assets: denom -> [amount, weight]
    LET neededLpLiquidity == GetMaximalNoSwapLPAmount(shareOutAmount, total_shares, <<>>) IN
    LET sharesAndTokensJoined == CalcJoinPoolNoSwapShares(neededLpLiquidity) IN
    /\  pool_assets' = [d \in DOMAIN pool_assets |-> [amount |-> pool_assets[d].amount + sharesAndTokensJoined.tokensJoined[d], weight |-> pool_assets[d].weight]]
    /\  total_shares' = [total_shares EXCEPT !.amount = (@ + sharesAndTokensJoined.numShares)]
    /\  users' = users \union {sender}
    /\  outcome_status' = JOIN_SUCCESS
    /\  action_taken' = [
            poolId          |-> 1,              \* TODO * - Add counter or numPools variable
            sender          |-> sender,
            action_type     |-> "join pool"
        ]
    /\  UNCHANGED <<total_weight>>

\* @type: (Str, Int) => Bool;
ExitPool(sender, exitingShares) ==
    (*
        exitingCoins, err = p.CalcExitPoolCoinsFromShares(ctx, exitingShares, exitFee)
        balances := p.GetTotalPoolLiquidity(ctx).Sub(exitingCoins)  \*sdk.Coins
    *)
    \*LET balances == Sub(total_liquidity, exitingCoins) IN   \* <= Str -> Int        \* denom -> amount
    \*/\  total_shares' = [total_shares EXCEPT !.amount = (@ - exitingShares)]
    \*/\  pool_assets' = [d \in DOMAIN pool_assets |-> [pool_assets[d].amount - balances[d], pool_assets[d].weight]]

    /\  UNCHANGED <<total_weight>>
    /\  users' = users \ {sender}
    /\  outcome_status' = EXIT_SUCCESS
    /\  UNCHANGED <<total_shares,pool_assets,action_taken>>

====