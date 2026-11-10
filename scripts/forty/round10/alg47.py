"""round 10: algebra of Entry 3.35 (Yesilyurt (5.18)-(5.24)) with u = chi(q)chi(Q), v = chi(-q)chi(-Q), w = uv."""
from sympy import *
u,v,q,P,X1=symbols('u v q P X1')
m=u*v
K=(u**2+v**2)*m**2+4*q**12+2*q**2*(u+v)*m**2+4*q**8*m
M=(u**4+v**4)*m**4+16*q**24
f1=2*q**6+u**2*v+u*v**2
f2=2*q**6-2*q**2*u*v+u**2*v+u*v**2
L,T=symbols('L T')
E524=(4*T**3-T**2*L**2+2*q**2*T**2*L+8*q**4*T**2+4*q**6*T*L+4*q**8*T-4*q**12).subs({L:u+v,T:u*v})
print('K^2-2M = f1 f2 E524 ?', expand(K**2-2*M-f1*f2*E524)==0)
AB=(q**2+u)*(1+2*q**4/m)
D=AB-v-2*q**2-2*q**4/v
R=q**2*(4*v+9*q**2+8*q**4/v)
num=together(D**2-R)
n,d=fraction(num); print('denominator',factor(d)); print('num/E524 =',factor(cancel(n/E524)))

# certificate for entry_3_35 from (5.24): goal + iw^2 E524 in ideal (iw*u*v-1, iv*v-1)
iw,iv=symbols('iw iv')
ABs=(q**2+u)*(1+2*q**4*iw)
goal=(ABs-v-2*q**2-2*q**4*iv)**2-q**2*(4*v+9*q**2+8*q**4*iv)
r1=iw*u*v-1; r2=iv*v-1
Q,rem=reduced(expand(goal+iw**2*E524),[r1,r2],iw,iv,u,v,q)
print('entry remainder',rem); print('entry quotients',Q)
# K1, K2 certificates (atoms)
a,b,c,d,p,pp,X1,S4T1,ps,Ps,V,NV,S4V=symbols('a b c d p pp X1 S4T1 ps Ps V NV S4V')
P_=p*pp; uu=a*c; vv=b*d; mm=uu*vv
Kq=K.subs({u:uu,v:vv}); Mq=M.subs({u:uu,v:vv})
h518=X1-(S4T1+2*q**12*ps*Ps+q**2*(V+NV)+2*q**8*S4V)
hS4=2*S4T1-(a**2*p*c**2*pp+b**2*p*d**2*pp)
hps=ps*(a*b)**2-p; hPs=Ps*(c*d)**2-pp
hV=V-b*p*d*pp; hNV=NV-a*p*c*pp; hS4V=S4V*(a*b)*(c*d)-p*pp
cert=2*mm**2*h518+mm**2*hS4+4*q**12*((c*d)**2*Ps*hps+p*hPs)+2*q**2*mm**2*(hV+hNV)+4*q**8*mm*hS4V
print('K1 check', expand(2*mm**2*X1-P_*Kq-cert))
g2=expand((goal+iw**2*E524).subs(iv,iw*u))
Q2,rem2=reduced(g2,[r1],iw,u,v,q)
print('entry (iv=iw u) remainder',rem2); print('quotient',Q2)
f2_,F2,f4,F4,ps2,Ps2=symbols('f2_ F2 f4 F4 ps2 Ps2')  # phi(q^2)=fb24, Phi2=fb94_188, psi4=fb0 4, Psi4=fb0 188, psi(q^2)=fb28, Psi=fb94_376
ph=a**2*p; phb=b**2*p; Ph=c**2*pp; Phb=d**2*pp
A=f2_*F2+q**24*f4*F4
h7=X1-A
hph=ph**2-(f2_**2+q*f4**2); hphb=phb**2-(f2_**2-q*f4**2)
hPh=Ph**2-(F2**2+q**47*F4**2); hPhb=Phb**2-(F2**2-q**47*F4**2)
h7b=f2_*f4-2*ps2**2; hP7b=F2*F4-2*Ps2**2
step1=2*X1**2-(ph**2*Ph**2+phb**2*Phb**2+16*q**24*ps2**2*Ps2**2)
cert1=2*(X1+A)*h7-(ph**2*hPh+(F2**2+q**47*F4**2)*hph)-(phb**2*hPhb+(F2**2-q**47*F4**2)*hphb)+4*q**24*(h7b*F2*F4+2*ps2**2*hP7b)
print('step1', expand(step1-cert1))
hps2=ps2*(a*b)**2-p; hPs2=Ps2*(c*d)**2-pp
xx=(a*b)**2*ps2; yy=(c*d)**2*Ps2
step2=2*mm**4*X1**2-P_**2*Mq
cert2=mm**4*step1+16*q**24*(xx*yy+p*pp)*(hps2*yy+p*hPs2)
print('step2', expand(step2-cert2))
T2_,T3_,NT2,NT3,S2T1,S2T2,S2T3,S4T2,S4T3,S4T1_,V_,NV_,S4V_,ps_,Ps_=symbols('T2 T3 NT2 NT3 S2T1 S2T2 S2T3 S4T2 S4T3 S4T1 V NV S4V ps Ps')
R2e=T2_+NT2-2*(S2T3+S2T1-S4T2); R3e=T3_+NT3-2*(S2T2+S2T3-S4T3)
ee=T2_-T3_-2*q**2*V_; nee=NT2-NT3-2*q**2*NV_; s4e=S4T2-S4T3-2*q**8*S4V_; twe=S2T2-(S4T1_+2*q**12*ps_*Ps_)
g518=S2T1-(S4T1_+2*q**12*ps_*Ps_+q**2*(V_+NV_)+2*q**8*S4V_)
print('518', expand(2*g518-(-R2e+R3e+ee+nee+2*s4e+2*twe)))
# P6: fb12*fb02 = 2 fb14^2 ; atoms F02,F14,a,P12,P44 ; P24=a P12, P22 = a P12 P44, fb12 = a^2 P22
F02,F14,P12,P44=symbols('F02 F14 P12 P44')
P24=a*P12; P22=a*P12*P44; fb12=a**2*P22
h0=F02*P24-2*P44; h1=F14*P12-P22
goal6=(fb12*F02-2*F14**2)*P24*P12**2
Q6,rem6=reduced(expand(goal6),[h0,h1],F02,F14,a,P12,P44)
print('P6',rem6,Q6)
