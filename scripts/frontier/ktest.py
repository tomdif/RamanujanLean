import sys
sys.argv=['x','17','6','5','none']
exec(open('katz.py').read().split("mode=sys.argv[4]")[0])
res=katz_coeffs(EN,5); print('E^5:',[v(a,DMAX) for a in res])
M=miller(3*k1,L); b=M[-1]
F=b[:]
for _ in range(2): F=mul(F,E,L)
res=katz_coeffs(F,5); print('b_3*E^2:',[v(a,DMAX) for a in res])
