import sys
exec(open(__import__('os').path.join(__import__('os').path.dirname(__file__),'mq_pair_classify.py')).read().split("def is_proj_lift")[0])
p=int(sys.argv[1]); v=tuple(int(x) for x in sys.argv[2].split(',')); r=int(sys.argv[3]); n=int(sys.argv[4])
pts=points(p,v,p*(n+1))
for t in range(n+1):
    K=p*t+r
    if pts.get(K):
        P=pts[K]
        print("N=%d K=%d coeff=%d"%(t,K,sum(s for _,s in P)), [(m,s) for m,s in P])
