from srch2 import *
LIM=400
SB=dadd(dmul(thd(110,44),dadd(thd(90,39),dsh(3,1,thd(90,69))),LIM), dsh(5,1,dmul(thd(110,22),dadd(thd(90,57),dsh(9,1,thd(90,87))),LIM)))
SBt=norm(tq(SB))[0]
print(search(8,-2,50,SBt,range(0,16),range(0,100)))
