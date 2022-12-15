---- MODULE HighPrecisionDec ----
EXTENDS Integers

\* (+-) (p / q) = <<sign, p, q>>
\* @typeAlias: decimal = <<Bool, Int, Int>>;

\* @type: Int => Int;
Abs(x) ==
    \* Returns the absolute value of x
    IF x < 0 THEN -x ELSE x

\* @type: Int => $decimal;
ToDec(x) ==
    \* Converts an integer to a decimal representation
    <<x < 0, Abs(x), 1>>

\* @type: () => $decimal;
DecOne ==
    \* Returns a decimal representation of the number 1
    ToDec(1)

\* @type: ($decimal) => $decimal;
Neg(a) ==
    \* Negates the sign of a decimal
    <<~a[1], a[3], a[2]>>

\* @type: ($decimal, $decimal) => $decimal;
Add(a, b) ==
    \* Computes the sum of two decimals
    LET
    \* Converts decimal `a` to fraction
    p_a == IF a[1] THEN -a[2] ELSE a[2]
    q_a == a[3]
    \* Converts decimal `b` to fraction
    p_b == IF b[1] THEN -b[2] ELSE b[2]
    q_b == b[3]
    \* Adds the fractions
    _p_c == p_a * q_b + q_a * p_b
    q_c == p_b * q_b
    \* Converts the result back to a decimal
    p_c == Abs(_p_c)
    s_c == _p_c < 0
    IN
    <<s_c, p_c, q_c>>


\* @type: ($decimal, $decimal) => $decimal;
Sub(a, b) ==
    \* Computes the difference of two decimals
    \* by negating the second input and then adding the two
    Add(a, Neg(b))

\* @type: ($decimal) => $decimal;
Inv(a) ==
    \* Inverts a decimal by flipping the numerator and denominator
    <<a[1], a[3], a[2]>>

\* @type: ($decimal, $decimal) => $decimal;
Mult(a, b) ==
    \* Computes the product of two decimals
    <<a[1] /= b[1], a[2] * b[2], a[3] * b[3]>>

\* @type: ($decimal, $decimal) => $decimal;
Div(a, b) ==
    \* Computes the quotient of two decimals
    \* by inverting the second input and then multiplying the two
    Mult(a, Inv(b))

\* @type: ($decimal) => Int;
Ceil(x) ==
    \* Computes the smallest integer that is greater than or equal to the decimal
    LET
    \* Computes the integer part of the decimal
    s == (IF x[1] THEN -1 ELSE 1)
    q == x[2] \div x[3]
    r == x[2] % x[3]
    IN
    \* Adjusts the result based on the sign and remainder of the division
    s * q + (IF (~x[1] /\ r > 0) THEN 1 ELSE 0)

\* @type: ($decimal) => Int;
Floor(x) ==
    \* Computes the largest integer that is less than or equal to the decimal
    \* Floor(a) == -Ceil(<<~a[1], a[2], a[3]>>)
    LET
    \* Computes the integer part of the decimal
    s == (IF x[1] THEN -1 ELSE 1)
    q == x[2] \div x[3]
    r == x[2] % x[3]
    IN
    \* Adjusts the result based on the sign and remainder of the division
    s * q + (IF (x[1] /\ r > 0) THEN -1 ELSE 0)


\* @type: ($decimal, Int) => $decimal;
PowInt(x, p) ==
    \* Computes the p-th power of a decimal
    \* by raising its numerator and denominator to the p-th power
    \* If p is negative, the decimal is inverted before computing the power
    \* If p is even, the sign of the result is set to false
    LET
    \* Computes whether p is even
    is_p_even == Abs(p) % 2 = 0
    \* Computes the sign of the result
    s == IF is_p_even THEN FALSE ELSE x[1]
    IN
    \* Raises the numerator and denominator to the p-th power
    \* If p is negative, the decimal is inverted first
    IF p < 0 THEN
        <<s, x[3]^(-p), x[2]^(-p)>>
    ELSE
        <<s, x[2]^p, x[3]^p>>

\* @type: Int => Int;
SqrtFloor(x) ==
    \* Computes the floor of the square root of x by choosing the largest integer y
    \* such that y*y is less than or equal to x
    CHOOSE y \in Nat:
        /\ y*y <= x
        /\ x < (y+1)*(y+1)

\* @type: Int => Int;
SqrtCeil(x) ==
    \* Computes the ceiling of the square root of x by choosing the smallest integer y
    \* such that y*y is greater than or equal to x
    CHOOSE y \in Nat:
        /\ (y-1)*(y-1) < x
        /\ x <= y*y

====
