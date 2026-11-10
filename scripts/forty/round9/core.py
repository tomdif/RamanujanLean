import sympy as sp
s1,s2,P,R,Z,t,q=sp.symbols('s1 s2 P R Z t q')
A=s1*s2*t-P*t-4*q**4
B=Z-q**2*P-t
C=R**2-s1*s2*Z
D=(2*s1*s2*P-q*(s1**2-s2**2)-2*R)*t-4*q**4*P
F=s1*s2*(P**2-q**2)-q*P*(s1**2-s2**2)-t
G38=P*D-t*F-(P**2+q**2)*A
print(sp.expand(G38-(P**3*t+q**2*P*t+t**2+4*q**6-2*P*R*t)))
T0=(P**2-R)**2-4*q**4
print(sp.expand(t*T0-(t*C+Z*A+(P*t+4*q**4)*B-P*G38)))
print(sp.expand(t*T0-(t*C+Z*A+(P*t+4*q**4)*B+P*G38)))
# after branch R = P^2-2q^2 : (3.41) cleared: (P^3-5q^2P) t - t^2 - 4q^6 = G38 with R substituted
Rb=sp.Symbol('Rb')
print(sp.expand(G38.subs(R,P**2-2*q**2) - ((P**3-5*q**2*P)*t - t**2 - 4*q**6)*(-1)))
