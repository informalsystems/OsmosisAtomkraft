---- MODULE HighPrecisionDec ----
EXTENDS Integers

\* @typeAlias: decimal = <<Bool, Int, Int>>;

\* @type: Int => Int;
Abs(x) == IF x < 0 THEN -x ELSE x

\* (+-) (p / q) = <<sign, p, q>>
\* @type: Int => $decimal;
ToDec(x) == <<x < 0, Abs(x), 1>>

\* @type: () => $decimal;
DecOne == ToDec(1)

\* @type: ($decimal) => $decimal;
Neg(a) == <<~a[1], a[3], a[2]>>

\* @type: ($decimal, $decimal) => $decimal;
Add(a, b) ==
    LET
    p_a == IF a[1] THEN -a[2] ELSE a[2]
    q_a == a[3]
    p_b == IF b[1] THEN -b[2] ELSE b[2]
    q_b == b[3]
    _p_c == p_a * q_b + q_a * p_b
    q_c == p_b * q_b
    p_c == Abs(_p_c)
    s_c == _p_c < 0
    IN
    <<s_c, p_c, q_c>>


\* @type: ($decimal, $decimal) => $decimal;
Sub(a, b) == Add(a, Neg(b))

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

\* Floor(a) == -Ceil(<<~a[1], a[2], a[3]>>)
\* @type: ($decimal) => Int;
Floor(x) ==
    LET
    s == (IF x[1] THEN -1 ELSE 1)
    q == x[2] \div x[3]
    r == x[2] % x[3]
    IN
    s * q + (IF (x[1] /\ r > 0) THEN -1 ELSE 0)


\* @type: ($decimal, Int) => $decimal;
PowInt(x, p) ==
    LET
    is_p_even == Abs(p) % 2 = 0
    s == IF is_p_even THEN FALSE ELSE x[1]
    IN
    IF p < 0 THEN
        <<s, x[3]^(-p), x[2]^(-p)>>
    ELSE
        <<s, x[2]^p, x[3]^p>>


====
