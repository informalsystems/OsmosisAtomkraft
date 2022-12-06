---- MODULE HighPrecisionDec ----
EXTENDS Integers

\* @typeAlias: decimal = <<Bool, Int, Int>>;

\* (+-) (p / q) = <<sign, p, q>>
\* @type: Int => $decimal;
ToDec(x) == <<x < 0, IF x < 0 THEN -x ELSE x, 1>>

\* @type: ($decimal) => $decimal;
Inv(a) == <<a[1], a[3], a[2]>>

\* @type: ($decimal, $decimal) => $decimal;
Mult(a, b) == <<a[1] /= b[1], a[2] * b[2], a[3] * b[3]>>

\* @type: ($decimal, $decimal) => $decimal;
Div(a, b) == Mult(a, Inv(b))

\* @type: ($decimal) => Int;
Ceil(x) ==
    LET
    s == (IF x[1] THEN -1 ELSE 1)
    q == x[2] \div x[3]
    r == x[2] % x[3]
    IN
    s * q + (IF (~x[1] /\ r > 0) THEN 1 ELSE 0)



====
