import mpmath as mp, math, sys
exec(open('hb2.py').read().split("rows=[]")[0].replace("DPS=int(sys.argv[1]) if len(sys.argv)>1 else 50","DPS=60"))
import random
random.seed(1)
worst={0.5:0,1.0:0}
out=[]
for K in [2,3,4,7,9,12,16,21,24,30]:
    hs=[h for h in range(K) if math.gcd(h,K)==1]
    for h in random.sample(hs,min(3,len(hs))):
        for rw in [0.5,3.0,30.0,100.0]:
            for iv in [0,2,10,50,-100]:
                w=mp.mpc(rw*K, iv*K); z=1/w
                q=qp(h,K,z)
                f,nt=fq(q)
                d = f - (eps(K)*bvia(h,K,z) if K%2==0 else 0)
                for D in worst: worst[D]=max(worst[D], float(abs(d)*abs(z)**D))
                out.append((K,h,rw,iv,float(abs(z)),float(abs(d)),float(abs(f))))
                print(K,h,rw,iv,"|z|=%.2e |f-eb|=%.3e |f|=%.3e"%(abs(z),abs(d),abs(f)),flush=True)
print("sup |f-eps b| |z|^D :",worst)
