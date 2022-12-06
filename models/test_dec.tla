---- MODULE test_dec ----

EXTENDS Integers

Igor == INSTANCE Dec
Rano == INSTANCE HighPrecisionDec

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y,
    \* @type: Int;
    z,
    \* @type: $dec;
    c,
    \* @type: Int;
    d

Op(_x, _y, _z, _c, _d) ==
    /\ _x \in Nat
    /\ _y \in Nat
    /\ _z \in Nat
    \* math.ceil((x / y) * z)
    /\ _c = Igor!Ceil(Igor!Mul(Igor!QuoInt(Igor!ToDec(_x), _y), Igor!ToDec(_z)))
    /\ _d = Rano!Ceil(Rano!Mult(Rano!Div(Rano!ToDec(_x), Rano!ToDec(_y)), Rano!ToDec(_z)))


Init == Op(x, y, z, c, d)
Next == Op(x', y', z', c', d')

Cex == ~c.error => Igor!Abs(Igor!TruncateInt(c) - d) < 4

====
