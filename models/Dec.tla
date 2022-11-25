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

\* In our specification, a decimal is a record that contains two fields:
\*
\*  - error is the error flag which is true
\*    iff the decimal number is considered invalid (e.g., overflow),
\*  - value is the math integer representing the decimal intPart.fractionalPart as
\*    intPart * 10^PRECISION + fractionalPart
\*
\* @typeAlias: dec = { error: Bool, value: Int };
\*
\* The number of decimal places after '.', that is, in the FRACTIONAL part.
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
 *
 * @type: Int => Int;
 *)
Abs(x) ==
    IF x >= 0 THEN x ELSE -x

\* Go Int wraps big.Int with a 257 bit range bound
\* Checks overflow, underflow and division by zero
\* Exists in range from -(2^256 - 1) to 2^256 - 1.

(**
 * Can an integer represent a Cosmos decimal?
 *
 * @type: Int => Bool;
 *)
IsDec(bigint) ==
    Abs(bigint) <= (2^256 - 1) * ONE + 10^(PRECISION + 1) - 1

(**
 * Converts Int number to sdk.Dec number.
 * Creates new decimal number from big integer assuming WHOLE numbers.
 *
 * @type: Int => $dec;
 *)
ToDec(bigint) == [ error |-> ~IsDec(bigint * ONE), value |-> bigint * ONE ]

(**
 * Divides the sdk.Dec number with sdk.Int number and returns sdk.Dec number
 * but only the truncated part (unlike the QuoRem, which returns the whole
 * number, and the remainder) - it implements food division.
 *
 * @type: ($dec, Int) => $dec;
 *)
QuoInt(x, y) ==
    IF x.error
    THEN [ error |-> TRUE, value |-> -1 ] \* propagate the error
    ELSE IF y = 0
        THEN \* division by zero
            [ error |-> TRUE, value |-> -1 ]
        ELSE LET absResult == Abs(x.value) \div Abs(y) IN
            \* we are using absolute values, as integer division behaves differently
            \* on negatives numbers in different languages:
            \* https://github.com/informalsystems/apalache/issues/331
            LET isNeg ==
              (x.value < 0 /\ y > 0) \/ (x.value > 0 /\ y < 0)
            IN
            [ error |-> FALSE, value |-> IF isNeg THEN -absResult ELSE absResult]

(**
 * Remove a PRECISION amount of rightmost digits and perform bankers rounding
 * on the remainder (gaussian rounding) on the digits which have been removed.
 *
 * @type: $dec => $dec;
 *)
ChopPrecisionAndRound(x) ==
    IF x.error
    THEN x  \* propagate the error
    ELSE
        LET absX == Abs(x.value) IN
        \* the integer part, that is, before '.'
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
        [ error |-> FALSE,
          value |-> IF x.value >= 0 THEN absResult ELSE -absResult ]

(**
 * Decimal multiplication.
 *
 * In our specification, Mul returns a pair:
 *  - the panic flag, which is set to true iff an overflow occurs;
 *  - the integer result, if the panic flag is false.
 *
 * @type: ($dec, Int) => $dec;
 *)
MulInt(x, y) ==
    IF x.error
    THEN [ error |-> TRUE, value |-> -1 ] \* propagate the error
    ELSE
        \* the perfect math product of two integers, which we have to round
        LET perfectProd == x.value * y IN
        LET chopped ==
          ChopPrecisionAndRound([ error |-> FALSE, value |-> perfectProd])
        IN
        \* equivalent to absResult.BitLen() > maxDecBitLen of Golang
        LET shouldPanic == Abs(chopped.value) >= 2^MAX_DEC_BIT_LEN IN
        [ error |-> shouldPanic, value |-> chopped.value ]

(**
 * Decimal multiplication.
 *
 * In our specification, Mul returns a pair:
 *  - the panic flag, which is set to true iff an overflow occurs;
 *  - the integer result, if the panic flag is false.
 *
 * @type: ($dec, $dec) => $dec;
 *)
Mul(x, y) ==
    IF x.error \/ y.error
    THEN [ error |-> TRUE, value |-> -1 ] \* propagate the error
    ELSE
        \* the perfect math product of two integers, which we have to round
        LET perfectProd == x.value * y.value IN
        LET chopped ==
          ChopPrecisionAndRound([ error |-> FALSE, value |-> perfectProd])
        IN
        \* equivalent to absResult.BitLen() > maxDecBitLen of Golang
        LET shouldPanic == Abs(chopped.value) >= 2^MAX_DEC_BIT_LEN IN
        [ error |-> shouldPanic, value |-> chopped.value ]

(**
 * Ceil returns the smallest interger value (as a decimal) that is greater than
 * or equal to the given decimal.
 *
 * @type: $dec => $dec;
 *)
Ceil(x) ==
    IF x.error
    THEN x  \* propagate the panic
    ELSE
        LET value ==
            IF x.value % PRECISION = 0 \/ x.value < 0
            THEN x.value
            ELSE ((x.value \div PRECISION) + 1) * PRECISION
        IN
        [ error |-> FALSE, value |-> value ]

(**
 * RoundInt round the decimal using bankers rounding
 *
 * @type: $dec => $dec;
 *)
RoundInt(x) ==
    ChopPrecisionAndRound(x)

(**
 * TruncateInt truncates the decimal to its whole part
 *
 * @type: $dec => Int;
 *)
TruncateInt(x) == x.value \div PRECISION

================================================================================
