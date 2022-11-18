------------------------------ MODULE Dec --------------------------------------
(*
 * High-level specification of a subset of operations over Cosmos SDK decimals.
 *
 * Igor Konnov, Informal Systems, November 2022
 *
 * Source:
 * https://github.com/cosmos/cosmos-sdk/blob/v0.45.1/types/decimal.go
 *)
EXTENDS Integers

\* The number of decimal places after '.'
PRECISION == 18

\* The maximum number of bits to represent a decimal,
\* up to 256 bits for the whole part and up to 59/60 bits for the digits after '.'.
\* Required for chopping.
\*
\* In cosmos-sdk v0.46.4, it is 315.
\* In cosmos-sdk v0.45.1, it is 316.
MAX_DEC_BIT_LEN == 316

\* This is 1.00...00 with PRECISION digits afer '.' represented as an integer
ONE == 10^PRECISION

\* This is 0.500....00 with PRECISION digits after '.' represented as an integer
HALF == 5 * 10^(PRECISION - 1)

(**
 * Return the absolute value of a math integer.
 *)
Abs(x) ==
    IF x >= 0 THEN x ELSE -x

\* Go Int wraps big.Int with a 257 bit range bound
\* Checks overflow, underflow and division by zero
\* Exists in range from -(2^256 - 1) to 2^256 - 1.

(**
 * Does an integer represent a Cosmos decimal?
 *)
IsDec(bigint) ==
    Abs(bigint) <= (2^256 - 1) * ONE + 10^(PRECISION + 1) - 1

(**
 * Converts Int number to sdk.Dec number.
 * Creates new decimal number from big integer assuming WHOLE numbers.
 *)
ToDec(bigint) == bigint * ONE

(**
 * Divides the sdk.Dec number with sdk.Int number and returns sdk.Dec number
 * but only the truncated part (unlike the QuoRem, which returns the whole
 * number, and the remainder) - it implements food division.
 *
 * In our specification, QuoInt returns a pair:
 *  - the panic flag, which is set to true iff an error occurs;
 *  - the integer result, if the panic flag is false.
 *
 * @type: (Int, Int) => <<Bool, Int>>;
 *)
QuoInt(x, y) ==
    IF y = 0
    THEN \* division by zero
        <<TRUE, 0>>
    ELSE LET AbsResult == Abs(x) \div Abs(y) IN
        \* we are using absolute values, as integer division behaves differently
        \* on negatives numbers in different languages:
        \* https://github.com/informalsystems/apalache/issues/331
        IF (x < 0 /\ y > 0) \/ (x > 0 /\ y < 0)
        THEN <<FALSE, -(Abs(x) \div Abs(y))>>
        ELSE <<FALSE, Abs(x) \div Abs(y)>>

(**
 * Remove a PRECISION amount of rightmost digits and perform bankers rounding
 * on the remainder (gaussian rounding) on the digits which have been removed.
 *)
ChopPrecisionAndRound(x) ==
    LET absX == Abs(x) IN
    \* the whole part, that is, before '.'
    LET quo == absX \div ONE IN
    \* the part after '.'
    LET rem == absX % ONE IN
    LET absResult ==
        \* when at half precisely, use bankers rounding:
        \* round up to the even number
        IF rem < HALF \/ (rem = HALF /\ quo % 2 = 0)
        THEN quo
        ELSE quo + 1
    IN
    IF x > 0
    THEN absResult
    ELSE -absResult

(**
 * Decimal multiplication.
 *
 * In our specification, Mul returns a pair:
 *  - the panic flag, which is set to true iff an overflow occurs;
 *  - the integer result, if the panic flag is false.
 *
 * @type: (Int, Int) => <<Bool, Int>>;
 *)
Mul(x, y) ==
    \* the perfect math product of two integers, which we have to round
    LET perfectProd == x * y IN
    LET chopped == ChopPrecisionAndRound(perfectProd) IN
    \* equivalent to absResult.BitLen() > maxDecBitLen of Golang
    LET shouldPanic == Abs(chopped) >= 2^MAX_DEC_BIT_LEN IN
    <<shouldPanic, chopped>>

(**
 * Ceil returns the smallest interger value (as a decimal) that is greater than
 * or equal to the given decimal.
 *)
Ceil(x) ==
    IF x % PRECISION = 0 \/ x < 0
    THEN x
    ELSE ((x \div PRECISION) + 1) * PRECISION

(**
 * RoundInt round the decimal using bankers rounding
 *)
RoundInt(x) ==
    ChopPrecisionAndRound(x)

================================================================================