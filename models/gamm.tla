-------------------------- MODULE gamm ----------------------------
EXTENDS
    Integers,
    FiniteSets,
    Sequences,
    gamm_typedefs,
    status_codes,
    Apalache

VARIABLE
    \* @type: Str -> [amount: Int, weight: Int];
    pool_assets,
    \* @type: COIN;
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
    /\  total_shares' = [denom |-> InitPoolShareDenom, amount |-> InitPoolShareAmount]
    /\  total_weight' = 
            LET Add(sum, d) == sum + pool_assets'[d].weight IN
            FoldSet(Add, 0, DOMAIN pool_assets')
    /\  users' = {sender}
    /\  outcome_status' = CREATE_SUCCESS
    /\  action_taken' = [
            poolId          |-> 1,              \* TODO * - Add counter or numPools variable
            sender          |-> sender,
            action_type     |-> "create pool",
            shares          |-> total_shares'.amount
        ]

\* @type: (Str, Int) => Bool;
JoinPool(sender, shareOutAmount) ==
    \* poolLiquidity: Seq(COIN) FROM pool_assets: denom -> [amount, weight]
    LET poolLiquidity ==
        LET AppendSeq(seq, d) == Append(seq, [denom |-> d, amount |-> pool_assets[d].amount]) IN
            FoldSet(AppendSeq, <<>>, DOMAIN pool_assets) IN
    LET neededLpLiquidity == GetMaximalNoSwapLPAmount(shareOutAmount, total_shares.amount, poolLiquidity) IN
    LET sharesAndTokensJoined == CalcJoinPoolNoSwapShares(neededLpLiquidity, total_shares.amount, poolLiquidity) IN
    /\  pool_assets' = [d \in DOMAIN pool_assets |-> [amount |-> pool_assets[d].amount + sharesAndTokensJoined.tokensJoined[d], weight |-> pool_assets[d].weight]]
    /\  total_shares' = [total_shares EXCEPT !.amount = (@ + sharesAndTokensJoined.numShares)]
    /\  users' = users \union {sender}
    /\  action_taken' = [
            poolId          |-> 1,              \* TODO * - Add counter or numPools variable
            sender          |-> sender,
            action_type     |-> "join pool",
            shares          |-> shareOutAmount
        ]
    /\  outcome_status' = JOIN_SUCCESS
    /\  UNCHANGED <<total_weight>>

\* @type: (Str, Int) => Bool;
ExitPool(sender, exitingShares) ==
    LET poolLiquidity ==
        LET AppendSeq(seq, d) == Append(seq, [denom |-> d, amount |-> pool_assets[d].amount]) IN
            FoldSet(AppendSeq, <<>>, DOMAIN pool_assets) IN
    LET exitingCoins == CalcExitPoolCoinsFromShares(exitingShares, total_shares.amount, poolLiquidity) IN

    /\  pool_assets' = [d \in DOMAIN pool_assets |-> [amount |-> (pool_assets[d].amount - exitingCoins[d]), weight |-> pool_assets[d].weight]]
    /\  total_shares' = [total_shares EXCEPT !.amount = (@ - exitingShares)]
    /\  users' = users \ {sender}
    /\  action_taken' = [
            poolId          |-> 1,              \* TODO * - Add counter or numPools variable
            sender          |-> sender,
            action_type     |-> "exit pool",
            shares          |-> exitingShares
        ]
    /\  outcome_status' = EXIT_SUCCESS
    /\  UNCHANGED <<total_weight>>

====