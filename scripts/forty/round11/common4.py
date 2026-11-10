"""round 11: with M7 at q, q^3:  L(q^2) = m3 m21/(m2 m14) - q^2 m1 m7/(m6 m42), and with Cramer
   chi^2(q) L(q^2) = bc + q ad.  4-term eta identity:  X3 - q^2 X4 = (X1 + q X2)  (all over a common factor).
Common multiplier search (generalized eta, moduli | 1680)."""
exec(open('common3.py').read().split("X1=etaq")[0])
def m(k): return add(eta(k),neg(eta(2*k)))
def p(k): return add(eta(2*k),eta(2*k),neg(eta(k)),neg(eta(4*k)))
def prod(*vs): return add(*vs)
def inv_(v): return neg(v)
p1sq=add(p(1),p(1))
bc=add(m(6),m(7),neg(m(2)),neg(m(1)))
ad=add(m(1),m(2),neg(m(3)),neg(m(14)))
t3=add(m(3),m(21),neg(m(2)),neg(m(14)),p1sq)
t4=add(m(1),m(7),neg(m(6)),neg(m(42)),p1sq)
terms=[t3,t4,bc,ad]
exec("LIM=int(sys.argv[1]) if len(sys.argv)>1 else 840\n"+open('common3.py').read().split("LIM=int(sys.argv[1]) if len(sys.argv)>1 else 840")[1].replace("terms=[add(fp(4,20),fp(56,112)), add(fp(8,16),fp(28,140)), X1, X2]",""))
