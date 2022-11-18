---- MODULE gamm_typedefs ----

EXTENDS 
    Integers,
    Dec

CONSTANT
    \* @type: Set(Str);
    Identifiers,
    \* @type: Set(Str);
    Denoms,
    \* @type: Int;
    GuaranteedWeightPrecision,
    \* @type: Str;
    InitPoolShareDenom,
    \* @type: Int;
    InitPoolShareAmount


\*@typeAlias: POOL = [
\*     id:             Int,
\*     pool_assets:    Str -> [amount: Int, weight: Int],
\*     total_shares:   COIN,
\*     total_weight:   Int,
\*     users:          Set(Str)
\*];
\* action_type: "create pool", "join pool", "exit pool"
(*
    @typeAlias: COIN = [
        denom:          Str,
        amount:         Int
    ];

    @typeAlias: ACTION = [
        poolId:         Int,
        sender:         Str,
        action_type:    Str,
        shares:         Int
    ];

    @typeAlias: STATE = [
        pool_assets:    Str -> [amount: Int, weight: Int],
        total_shares:   COIN,
        total_weight:   Int,
        users:          Set(Str),
        action_taken:   ACTION,
        outcome_status: Str
    ];
*)

\* @type: POOL;
EmptyPool == [
    id |-> 0,
    pool_assets |-> [d \in {} |-> [amount |-> 0, weight |-> 0]],
    total_shares |-> [denom |-> "", amount |-> 0],
    total_weight |-> 0,
    users |-> {}
]

\* @type: ACTION;
EmptyAction == [
    poolId |-> 0,
    sender |-> "",        
    action_type |-> "",
    shares |-> 0
]

\* @type: Set(Int);
Initial_Amounts == 1..100
\* @type: Set(Int);
Weights == 1..10
\* @type: Set(Int);
Amounts == 1..100

InitialAssets == [
    Denoms -> [amount: Initial_Amounts, weight: Weights]
]

\* @type: (Int) => Int;
TruncateInt(x) == x        \* TODO *

\* @type: (Int, Int, Seq(COIN)) => Str -> Int;
GetMaximalNoSwapLPAmount(shareOutAmount, totalShares, poolLiquidity) ==
    LET shareRatio == QuoInt(ToDec(shareOutAmount), totalShares) IN
    IF shareRatio[1]
    THEN
        [x \in {""} |-> 0] \* TODO: handle QuoInt panic
    ELSE
        LET coin1 == poolLiquidity[1] IN
        LET coin2 == poolLiquidity[2] IN
        LET neededAmt1 == Mul(ToDec(coin1.amount), shareRatio[2]) IN
        LET neededAmt2 == Mul(ToDec(coin2.amount), shareRatio[2]) IN
        IF neededAmt1[1] \/ neededAmt2[1]
        THEN
            [x \in {""} |-> 0] \* TODO: handle Mul panic
        ELSE
            LET retFunc == [x \in {coin1.denom, coin2.denom} |-> 0] IN
            [retFunc EXCEPT ![coin1.denom] = TruncateInt(neededAmt1[2]),
                            ![coin2.denom] = TruncateInt(neededAmt2[2])]

\* @type: (Str -> Int, Int, Seq(COIN)) => [numShares: Int, tokensJoined: Str -> Int];
CalcJoinPoolNoSwapShares(tokensIn, totalShares, poolLiquidity) ==
    LET coin1 == poolLiquidity[1] IN
    LET coin2 == poolLiquidity[2] IN
    LET shareRatio1 == QuoInt(ToDec(tokensIn[coin1.denom]), coin1.amount) IN
    LET shareRatio2 == QuoInt(ToDec(tokensIn[coin2.denom]), coin2.amount) IN
    IF shareRatio1[1] \/ shareRatio2[1]
    THEN
        [numShares |-> 0, tokensJoined |-> [x \in {""} |-> 0]] \* TODO: handle QuoInt panic
    ELSE
        LET minShareRation == IF shareRatio1[2] < shareRatio2[2] THEN shareRatio1[2] ELSE shareRatio2[2] IN
        LET maxCoin == IF shareRatio1[2] < shareRatio2[2] THEN coin2 ELSE coin1 IN
        LET numShares == Mul(minShareRation, totalShares) IN
        LET usedAmount == Mul(minShareRation, maxCoin.amount) IN
        IF numShares[1] \/ usedAmount[1]
        THEN
            [numShares |-> 0, tokensJoined |-> [x \in {""} |-> 0]] \* TODO: handle Mul panic
        ELSE
            LET remCoin == IF shareRatio1[2] = shareRatio2[2] THEN 0 ELSE maxCoin.amount - TruncateInt(Ceil(usedAmount[2])) IN
            [numShares    |-> TruncateInt(numShares[2]), 
             tokensJoined |-> [d \in {maxCoin.denom} |-> remCoin]]

\* exitFee == 0  =>  refundedShares == exitingShares.ToDec()
\* @type: (Int, Int, Seq(COIN)) => Str -> Int;
CalcExitPoolCoinsFromShares(exitingShares, totalShares, poolLiquidity) ==
    LET shareOutRatio == QuoInt(ToDec(exitingShares), totalShares) IN
    IF shareOutRatio[1]
    THEN
        [x \in {""} |-> 0] \* TODO: handle QuoInt panic
    ELSE
        LET coin1 == poolLiquidity[1] IN
        LET coin2 == poolLiquidity[2] IN
        LET neededAmt1 == Mul(shareOutRatio[2], coin1.amount) IN
        LET neededAmt2 == Mul(shareOutRatio[2], coin2.amount) IN
        IF neededAmt1[1] \/ neededAmt2[1]
        THEN
            [x \in {""} |-> 0] \* TODO: handle Mul panic
        ELSE
            LET retFunc == [x \in {coin1.denom, coin2.denom} |-> 0] IN
            [retFunc EXCEPT ![coin1.denom] = TruncateInt(neededAmt1[2]),
                            ![coin2.denom] = TruncateInt(neededAmt2[2])]

====