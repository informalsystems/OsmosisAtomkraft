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

\* @type: (Str -> $dec) => Str;
Min(f) == CHOOSE x \in DOMAIN f: \A y \in DOMAIN f: f[x].value <= f[y].value
\* @type: (Str -> $dec) => Str;
Max(f) == CHOOSE x \in DOMAIN f: \A y \in DOMAIN f: f[x].value >= f[y].value

\* @type: (Int, Int, Str -> {amount: Int, weight: Int}) => { error: Bool, amounts: Str -> Int };
GetMaximalNoSwapLPAmount(shareOutAmount, totalShares, poolLiquidity) ==
    LET results ==
      [d \in DOMAIN poolLiquidity |->
        Mul(ToDec(poolLiquidity[d].amount), 
                        QuoInt(ToDec(shareOutAmount), totalShares))]
    IN
    LET isError == \E d \in DOMAIN results: results[d].error IN
    [ error |-> isError,
      amounts |-> [d \in DOMAIN poolLiquidity |-> TruncateInt(results[d])]
    ]  

\* @type: (Str -> Int, Int, Str -> {amount: Int, weight: Int}) => { error: Bool, numShares: Int, tokensJoined: Str -> Int};
CalcJoinPoolNoSwapShares(tokensIn, totalShares, poolLiquidity) ==
    LET sharesRatio == [d \in DOMAIN poolLiquidity |->
                            QuoInt(ToDec(tokensIn[d]), poolLiquidity[d].amount)] IN
    LET minDenom == Min(sharesRatio) IN
    LET maxDenom == Max(sharesRatio) IN
    LET numSharesDec == MulInt(sharesRatio[minDenom], totalShares) IN
    LET numShares == TruncateInt(numSharesDec) IN
    LET usedAmount == MulInt(sharesRatio[minDenom], poolLiquidity[maxDenom].amount) IN
    LET ceilUsedAmountDec == Ceil(usedAmount) IN
    LET remCoin == IF sharesRatio[minDenom] = sharesRatio[maxDenom] THEN 0 ELSE poolLiquidity[maxDenom].amount - TruncateInt(ceilUsedAmountDec) IN
    [error |-> numSharesDec.error \/ ceilUsedAmountDec.error,
     numShares |-> numShares, 
     tokensJoined |-> [d \in {maxDenom} |-> remCoin]]

\* exitFee == 0  =>  refundedShares == exitingShares.ToDec()
\* @type: (Int, Int, Str -> {amount: Int, weight: Int}) => { error: Bool, amounts: Str -> Int };
CalcExitPoolCoinsFromShares(exitingShares, totalShares, poolLiquidity) ==
    LET decs == [d \in DOMAIN poolLiquidity |->
        MulInt(QuoInt(ToDec(exitingShares), totalShares), 
                           poolLiquidity[d].amount)]
    IN
    LET isError == \E d \in DOMAIN decs: decs[d].error IN
    [ error |-> isError,
      amounts |-> [d \in DOMAIN poolLiquidity |-> TruncateInt(decs[d])]]

====
