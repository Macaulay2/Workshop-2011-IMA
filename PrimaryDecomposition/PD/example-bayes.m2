loadPackage "Markov"
G = makeGraph {{}, {1}, {1}, {1} , {2,3,4}}
S = globalMarkovStmts G
R = markovRing(2,2,2,2,2)
I = markovIdeal(R,S)
phi = marginMap(1,R)
J = phi I
gens gb J;
codim J
end
restart
load "PD/example-bayes.m2"
debug needsPackage "PD"

time L1 = splitIdeal(J, Strategy=>splice{10:Birational});
time L1 = splitIdeal(J, Strategy=>splice{IndependentSet});
time L2 = splitIdeal(L1, Strategy=>splice{IndependentSet});



-- old:
gbTrace=3
C = time birationalSplit J;

C = o4;
C_0
#oo
C_0_2
C_0_1/(x -> x#2)

time minprimes J;
time factorizationSplit J;

time J1 = J : p_(1,1,1,1,1);
J2 = J : J1;
betti J2

time C = factorizationSplit(J2);
#C
C_0
class oo
time C/simplifyIdeal;
time C/simplifyIdeal2;
