restart
loadPackage "Schubert2"
 base(0, Bundle=>(A, n=7, a))
 F = flagBundle ({r=3,4},A)
 
 CH = intersectionRing F;
 T=schubertCycle({1,0,0},F)
 T^7
T^7* schubertCycle({2,1,0},F)*schubertCycle({1,1,0},F)

base(0, Bundle => (A, n=6, a))
F = flagBundle ({r=3,3}, A)

CH = intersectionRing F;
T = schubertCycle({1,1,0}, F)
T^2
-----
restart
loadPackage "LRcheckergame";

playCheckers({2,1},{1,1},3,6)

