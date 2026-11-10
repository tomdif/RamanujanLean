import itertools
def Q(A,B,C,v): return A*v[0]**2+2*B*v[0]*v[1]+C*v[1]**2
def Bil(A,B,C,v,w): return A*v[0]*w[0]+B*(v[0]*w[1]+v[1]*w[0])+C*v[1]*w[1]
D=126
forms=[]
for A in range(1,40):
  for B in range(0,A//2+1):
    if (D+B*B)%A==0:
      C=(D+B*B)//A
      if C>=A: forms.append((A,B,C))
print(forms)
R=40
vecs=[(x,y) for x in range(-R,R+1) for y in range(-R,R+1) if (x,y)!=(0,0)]
for (A,B,C) in forms:
  res={}
  for target in [(15,210),(35,90),(30,105)]:
    found=[]
    for v in vecs:
      if Q(A,B,C,v)!=target[0]: continue
      for w in vecs:
        if Q(A,B,C,w)!=target[1]: continue
        if Bil(A,B,C,v,w)!=0: continue
        if v[0]*w[1]-v[1]*w[0]==5: found.append((v,w))
    res[target]=found[:3]
  print((A,B,C),{k:len(v) for k,v in res.items()}, res)
