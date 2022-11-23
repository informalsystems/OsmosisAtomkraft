---- MODULE gamm_typedefs ----

EXTENDS 
    Integers,
    Dec

\* action_type: "create pool", "join pool", "exit pool"
(*
    @typeAlias: coin = {
        denom:          Str,
        amount:         Int
    };

    @typeAlias: action = {
        poolId:         Int,
        sender:         Str,
        action_type:    Str,
        shares:         Int
    };

    @typeAlias: state = {
        pool_assets:    Str -> {amount: Int, weight: Int},
        total_shares:   $coin,
        total_weight:   Int,
        users:          Set(Str),
        action_taken:   $action,
        outcome_status: Str
    };
*)

\* @type: $action;
EmptyAction == [
    poolId |-> 0,
    sender |-> "",        
    action_type |-> "",
    shares |-> 0
]

\* @type: Set(Str);
Identifiers == {"A", "B", "C"}
\* @type: Set(Str);
Denoms == {"OSMO", "ATOM"}
\* @type: Int;
GuaranteedWeightPrecision == 1073741824
\* @type: Str;
InitPoolShareDenom == "gamm/pool/1"
\* @type: Int;
InitPoolShareAmount == 100 * ONE

\* @type: (Str -> Int) => Str;
Min(f) == CHOOSE x \in DOMAIN f: \A y \in DOMAIN f: f[x] <= f[y]
\* @type: (Str -> Int) => Str;
Max(f) == CHOOSE x \in DOMAIN f: \A y \in DOMAIN f: f[x] >= f[y]

\* @type: (Int, Int, Str -> {amount: Int, weight: Int}) => Str -> Int;
GetMaximalNoSwapLPAmount(shareOutAmount, totalShares, poolLiquidity) ==
    [d \in DOMAIN poolLiquidity |->
        TruncateInt(Mul(ToDec(poolLiquidity[d].amount), QuoInt(ToDec(shareOutAmount), totalShares)))]

\* @type: (Str -> Int, Int, Str -> {amount: Int, weight: Int}) => {numShares: Int, tokensJoined: Str -> Int};
CalcJoinPoolNoSwapShares(tokensIn, totalShares, poolLiquidity) ==
    \*LET sharesRatio == [d \in DOMAIN poolLiquidity |->
    \*                        QuoInt(ToDec(tokensIn[d]), poolLiquidity[d].amount)] IN
    \*LET minDenom == Min(sharesRatio) IN
    \*LET maxDenom == Max(sharesRatio) IN
    \*LET numShares == TruncateInt(Mul(sharesRatio[minDenom], totalShares)) IN
    \*LET usedAmount == Mul(sharesRatio[minDenom], poolLiquidity[maxDenom].amount) IN
    \*LET remCoin == IF sharesRatio[minDenom] = sharesRatio[maxDenom] THEN 0 ELSE poolLiquidity[maxDenom].amount - TruncateInt(Ceil(usedAmount)) IN
    \*[numShares |-> numShares, 
    \* tokensJoined |-> [d \in {maxDenom} |-> remCoin]]
    [numShares |-> 0, 
     tokensJoined |-> [d \in {""} |-> 0]]

\* exitFee == 0  =>  refundedShares == exitingShares.ToDec()
\* @type: (Int, Int, Str -> {amount: Int, weight: Int}) => Str -> Int;
CalcExitPoolCoinsFromShares(exitingShares, totalShares, poolLiquidity) ==
    [d \in DOMAIN poolLiquidity |->
        TruncateInt(Mul(QuoInt(ToDec(exitingShares), totalShares), poolLiquidity[d].amount))]

====