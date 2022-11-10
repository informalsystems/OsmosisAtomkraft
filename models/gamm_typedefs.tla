---- MODULE gamm_typedefs ----

EXTENDS 
    Integers

CONSTANT
    GuaranteedWeightPrecision = 1073741824
    InitPoolSharesSupply = OneShare.MulRaw(100)

EmptyCoin == [
    denom |-> "",
    amount |-> 0
]

GetMaximalNoSwapLPAmount(shareOutAmount, total_shares, poolLiquidity) == 
    {
        [poolLiquidity[1].denom, Ceil(poolLiquidity[1].amount * Que(shareOutAmount, total_shares))],
        [poolLiquidity[2].denom, Ceil(poolLiquidity[2].amount * Que(shareOutAmount, total_shares))]
    }

Que(x, y) == \* TODO
Ceil(x) == PRECISION * (CHOOSE y \in Int: y * PRECISION >= x /\ (y - 1) * PRECISION < x)



Coin == [ 
    msgType: {"coin"},

    \* optional
    denom: STRING,

    \* optional
    amount: STRING
]

====