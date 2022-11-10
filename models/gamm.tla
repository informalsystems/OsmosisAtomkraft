-------------------------- MODULE gamm ----------------------------
EXTENDS
    Integers,
    FiniteSets,
    Sequences,
    gamm_typedefs

VARIABLE
    \* denom -> [amount, weight]
    \* @type: Str -> [Int, Int];
    pool_assets,
    \* @type: Coin;
    total_shares,
    \* @type: Int;
    total_weight,
    \* @type: Set(Str);
    users,


\* initial_assets: Str -> [Int, Int]   \* denom -> [amount, weight]
CreatePool(sender, initial_assets) == 
    /\  pool_assets' = [x \in DOMAIN initial_assets |-> [initial_assets[x].amount, initial_assets[x].weight * GuaranteedWeightPrecision]]
    /\  total_shares' = InitPoolSharesSupply
    /\  total_weight' = ApaFoldSet(LAMBDA x, y: x + pool_assets[y][1] * pool_assets[y][2], 0, DOMAIN pool_assets) \* sum of all pool_assets' "weight"
    /\  users' = {sender}


JoinPool(sender, shareOutAmount) ==
    (*
        poolLiquidity: set([denom, amount]) <= pool_assets: denom -> [amount, weight]
        neededLpLiquidity, err := getMaximalNoSwapLPAmount(ctx, pool, shareOutAmount)
        numShares, tokensJoined, err := p.CalcJoinPoolNoSwapShares(ctx, neededLpLiquidity, swapFee)
    *)
    /\  LET neededLpLiquidity == GetMaximalNoSwapLPAmount(shareOutAmount, total_shares, poolLiquidity)
    /\  LET numShares       \* <= Int
    /\  LET tokensJoined    \* <= Str -> Int        \* denom -> amount
    /\  total_shares' = [total_shares EXCEPT !.amount = (@ + numShares)]
    /\  pool_assets' = [d \in DOMAIN pool_assets |-> [pool_assets[d].amount + tokensJoined[d], pool_assets[d].weight]]

    /\  UNCHANGED <<total_weight>>
    /\  users' = users \union {sender}

ExitPool(sender, exitingShares) ==
    (*
        exitingCoins, err = p.CalcExitPoolCoinsFromShares(ctx, exitingShares, exitFee)
        balances := p.GetTotalPoolLiquidity(ctx).Sub(exitingCoins)  \*sdk.Coins
    *)
    /\  LET balances    \* <= Str -> Int        \* denom -> amount
    /\  total_shares' = [total_shares EXCEPT !.amount = (@ - exitingShares)]
    /\  pool_assets' = [d \in DOMAIN pool_assets |-> [pool_assets[d].amount - balances[d], pool_assets[d].weight]]

    /\  UNCHANGED <<total_weight>>
    /\  users = users \ {sender}
    

Init ==
    /\ pool_assets = [d \in {} |-> 0]     \*{} [token |-> EmptyCoin, weight |-> 0]
    /\ total_shares = EmptyCoin
    /\ total_weight = 0
    /\ users = {}

Next == 
    \* TODO



====