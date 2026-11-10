# float least squares version
exec(open('m47b.py').read().split("M=sp.Matrix")[0])
import numpy as np
A=np.array([[float(c[i]) for c in cols] for i in range(N)])
bb=np.array([float(target[i]) for i in range(N)])
x,res,rk,sv=np.linalg.lstsq(A,bb,rcond=None)
print("rank",rk,"of",A.shape,"residual",np.linalg.norm(A@x-bb))
