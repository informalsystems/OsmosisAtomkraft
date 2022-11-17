---- MODULE gamm_typedefs ----

EXTENDS 
    Integers

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
    InitPoolShareAmount,
    \* @type: Int;
    PRECISION


\*@typeAlias: POOL = [
\*     id:             Int,
\*     pool_assets:    Str -> [amount: Int, weight: Int],
\*     total_shares:   [share_denom: Str, amount: Int],
\*     total_weight:   Int,
\*     users:          Set(Str)
\*];
\* action_type: "create pool", "join pool", "exit pool"
(*
    @typeAlias: ACTION = [
        poolId:         Int,
        sender:         Str,
        action_type:    Str
    ];

    @typeAlias: STATE = [
        pool_assets:    Str -> [amount: Int, weight: Int],
        total_shares:   [share_denom: Str, amount: Int],
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
    total_shares |-> [share_denom |-> "", amount |-> 0],
    total_weight |-> 0,
    users |-> {}
]

\* @type: ACTION;
EmptyAction == [
    poolId |-> 0,
    sender |-> "",        
    action_type |-> ""
]

\* @type: Set(Int);
Initial_Amounts == 0..100
\* @type: Set(Int);
Weights == 0..10
\* @type: Set(Int);
Amounts == 0..200

InitialAssets == [
    Denoms -> [amount: Initial_Amounts, weight: Weights]
]

\* @type: (Int) => Int;
Ceil(x) == PRECISION * (CHOOSE y \in Int: y * PRECISION >= x /\ (y - 1) * PRECISION < x)
\* @type: (Int, Int) => Int;
Que(x, y) == 0          \* TODO *
\* @type: (Int) => Int;
RoundInt(x) == 0        \* TODO *

\* @type: (Int, [share_denom: Str, amount: Int], Seq([denom: Str, amount: Int])) => Set([denom: Str, amount: Int]);
GetMaximalNoSwapLPAmount(shareOutAmount, total_shares, poolLiquidity) == 
{
    [denom |-> poolLiquidity[1].denom, amount |-> RoundInt(Ceil(poolLiquidity[1].amount * Que(shareOutAmount, total_shares.amount)))],
    [denom |-> poolLiquidity[2].denom, amount |-> RoundInt(Ceil(poolLiquidity[2].amount * Que(shareOutAmount, total_shares.amount)))]
}

\* @type: (Set([denom: Str, amount: Int])) => [numShares: Int, tokensJoined: Str -> Int];
CalcJoinPoolNoSwapShares(neededLpLiquidity) ==
    [numShares |-> 0, tokensJoined |-> [denom \in {"TODO"} |-> 0]]      \* TODO *


====