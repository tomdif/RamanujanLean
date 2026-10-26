import os, sys
sys.path.insert(0,'/private/tmp/claude-501/-Users-thomasdifiore/874f7000-fa1e-4981-92e1-5e09a663f92a/scratchpad/eg2')
os.environ['MOD']='80'
_g=dict(globals())
exec(open('/private/tmp/claude-501/-Users-thomasdifiore/874f7000-fa1e-4981-92e1-5e09a663f92a/scratchpad/eg2/small.py').read(),_g)
F=_g['F']; th_=_g['th']; mul_=_g['mul']; inv_=_g['inv']; poch_=_g['poch']; exact_=_g['exact']; key_=_g['key']
def J_(N):
    v={}; poch_(v,N,N,1,1); return (F(1),0,{r:n for r,n in v.items() if n})
G_=mul_(th_(5,2,1),inv_(J_(1))); H4_=mul_(th_(20,4,1),inv_(J_(4))); psi2_=mul_(J_(4),J_(4),inv_(J_(2)))
A_=mul_(psi2_,H4_); A_=(A_[0],A_[1]+1,A_[2])
terms_=[(4,A_),(1,mul_(th_(2,1,1),G_)),(-3,mul_(th_(10,5,1),G_)),(2,mul_(J_(10),J_(10),th_(10,4,1),inv_(th_(10,2,1)),inv_(th_(10,2,1))))]
specs_=[(2,('M',(10,1,1,3,-1)),0,1),(1,('M',(10,1,1,5,-1)),0,2),(1,('M',(10,1,-1,5,1)),0,2),(1,('M',(5,2,1,2,1)),1,0),(-2,('M',(5,1,-1,2,1)),2,0)]
SC=[]
from collections import Counter
for c,sp,ti,p in specs_:
    rel=exact_(sp); Ti=terms_[ti][1]
    cp,(sp_,kp,vp)=rel[p]
    cf=F(1)/(cp*F(sp_)); sh=Ti[1]-kp
    d={r:Ti[2].get(r,0)-vp.get(r,0) for r in set(Ti[2])|set(vp)}
    num=' * '.join(f'Aw {r}'+(f' ^ {n}' if n>1 else '') for r,n in sorted(d.items()) if n>0) or '1'
    den=' * '.join(f'Aw {r}'+(f' ^ {-n}' if n<-1 else '') for r,n in sorted(d.items()) if n<0) or '1'
    assert cf.denominator==1 and sh>=0
    SC.append((c,int(cf),sh,num,den))
