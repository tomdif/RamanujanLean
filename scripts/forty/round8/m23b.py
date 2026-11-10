from glue import *
A=(4,1,6,0,0,1,1); B=(2,1,12,0,0,1,0); C=(3,1,8,1,8,1,0)
# target: A - B - t^2 C = 0
for ha,hb,hc in itertools.product([None,'x','y','xy'],repeat=3):
    items=[]
    for (F,h,co,sh) in [(A,ha,1,0),(B,hb,-1,0),(C,hc,-1,2)]:
        for (k,sg,G) in pieces(F,h):
            s=form(*G,k0=k); n=norm(s)
            if n is None: items.append((sh,0,0,(),G)); continue
            items.append((sh, co*sg*int(n[1]), n[0], n[2], G))
    # group by series shape: total shift and coefficient
    from collections import defaultdict
    grp=defaultdict(int)
    for (k,c,k0,shape,G) in items: grp[(k+k0,shape)]+=c
    if all(v==0 for v in grp.values()):
        print("FOUND",ha,hb,hc)
        for it in items: print("   ",it[0],it[1],it[4])
