newPackage(
	"BoijSoederbergExtension",
    	Version => ".1", 
    	Date => "August 5, 2012",
    	Authors => {
	     {Name => "David Eisenbud", Email => "de@msri.org", HomePage => "http://www.msri.org/~de/"},	     
	     {Name => "Frank Schreyer", Email => "schreyer@math.uni-sb.de", HomePage => "http://www.math.uni-sb.de/ag/schreyer/"},
	     },
    	Headline => "BoijSoederbergExtension",
	PackageExports => {"BoijSoederberg", "BGG"},
    	DebuggingMode => true
    	)

export {
     "decomposeCohomologyTable",
     "extendCohomologyTable",
     "isVectorBundleTally",
     "eulerCharacteristic",
     "eulerPolynomial",
     "interpolate",
     "range",
     "beilinsonData",
     "zeroesOfMonadTensorSupernatural",
     "supernatural",
     "decomposeC",
     "trimCohomologyTable"
     }
{*The version of projectiveProduct in
BGG.m2
in the repository fails when A is a field.
This bug is fixed in this version. 
Eventually this should replace the one in BGG in the repository.

projectiveProduct = method()
*}

projectiveProduct(Ring, List) := (A,D) -> (
     --Takes a list of dimensions D = d_1..d_r
     --and makes the  product 
     --P_A^{d_1}x..xP_A^{d_r} 
     --of projective spaces over the base A, as a tower ring.
     --Returns the tower ring
     --together with a system of multilinear parameters
     --(degree = {1,..,1})
     --for the whole product.
     --The length of the sop is 
     --numgens A + sum D, 1 more than 
     --the projective dimension of the whole product.
     --The sop is formed from the symmetric functions
     --using the functions "partitions" above. (It could
     --also be done putting an appropriate matrix
     --in the next routine.)
     S := A;
     x := local x;
     SList := apply (#D, i->S = S[x_(i,0)..x_(i,D_i)]);
     if numgens A > 0 then SList = prepend(A,SList);
     SS := last SList;
     if numgens A >0 then dimList := prepend(numgens A-1, D)
         else dimList = D;
        --now make the parameters
     params := matrix{
	  for k from 0 to sum dimList list(
     P := partitions(k,dimList);
     sum(P, p -> product(#dimList, i->sub(SList_i_(p_i), SS))
	  )
                                           ) 
                     };
     (SS,params)
     )

QQ * CohomologyTally := (d,C) -> applyValues(C, v -> d*v)

trimCohomologyTable=method()
trimCohomologyTable(CohomologyTally, ZZ, ZZ) := (C,lo,hi) ->(
newKeys := select(keys C, k -> lo <= first k + last k and first k + last k <= hi);
new CohomologyTally from apply(newKeys, k-> k => C_k)
)


CohomologyTally ++ CohomologyTally := (C,D) -> (
     loC:=0;
     hiC:=0;
     loD:=0;
     hiD:=0;
     (loC, hiC) = range C;
     (loD, hiD) = range D;
     bundleCase :=  isVectorBundleTally C and isVectorBundleTally D;
     lo := if bundleCase then min(loC, loD) else max(loC, loD);
     hi := if bundleCase then max(hiC, hiD) else min(hiC, hiD);
     C1 := {};
     D1 := {};
     K := if bundleCase then unique join (keys (C1=extendCohomologyTable(C,lo,hi)), keys (D1 = extendCohomologyTable(D,lo,hi)))
     	  else unique join (keys (C1= trimCohomologyTable(C,lo,hi)), keys (D1=trimCohomologyTable(D,lo,hi)));
     new CohomologyTally from apply(K, k-> k=>C1_k+D1_k)
     )
{*	  
topZeroSequence = method()
topZeroSequence CohomologyTally := C ->(
     K := keys C;
     K = select(K, k-> C_k !=0);
     n := max(K/first);
     Ki :={};
     zl := 0;
     apply(reverse toList(1..n), i-> (
	       Ki = select(K, k -> first k == i);
	       if Ki == {} then {zl = zl+1,0} else {zl = max(Ki/last)+1,C_(i,zl-1)}
	  ))
)
*}
decomposeCohomologyTable1 = method()
decomposeCohomologyTable1 CohomologyTally := C->(
     tzs :=topZeroSequence C;
     K := keys C;
     range := toList(min(K/last)..max(K/last));
     Z := tzs/first;
--     if not isStrictlyIncreasing L then print "NOT IN THIS SIMPLEX OF PURE BETTI DIAGRAMS";
     t := symbol t;
     T := ZZ[t];
     p := product(Z, z ->t-z);
     n := 0; -- -#tzs;
     val := 0;
     Ctop := new CohomologyTally from apply(reverse range, d -> (
	       if (val = abs sub(p, t=>d)) == 0 then n = n+1;
	       (n,d)=>val));
     cornersOfCtop := apply(tzs/(m -> (first m)-1), d->abs sub(p, t=>d));
     denoms := cornersOfCtop;
     nums := tzs/last;
     ratio :=  min apply(#nums, i-> if denoms_i != 0 then nums_i/denoms_i else infinity );
     (Ctop, ratio, merge(C,Ctop, (i,j)->i-ratio*j))
--     new CohomologyTally from 
--     apply(keys C, k -> k=>(C_k - ratio*Ctop_k))
     )

decomposeCohomologyTable = method()
decomposeCohomologyTable CohomologyTally := C -> (
     B1 := new CohomologyTally from C;
--     B1:= new MutableHashTable from B;
     ratio := 1;
     Ztop := {};
     while min values B1 >= 0 and max values B1 > 0 list (
	  (Ztop, ratio, B1) = decomposeCohomologyTable1 B1;
	  {ratio, topZeroSequence Ztop/first}))

dct = decomposeCohomologyTable
TEST///
S = ZZ/101[a..d]
C1 = cohomologyTable (sheaf coker koszul(3, vars S), -3,3)
C2 =(cohomologyTable (sheaf coker koszul(3, vars S), -4,2))(-1)
C3 =(cohomologyTable (sheaf image matrix"a,b,c", -4,2))(-1)
C = C1
assert(isVectorBundleTally (C2+C1)==true)
assert(isVectorBundleTally (C3) == false)
assert(dim C1 == 3)
assert(toString decomposeCohomologyTable(C1+C2) == "{{1/2, {-1, 0, 2}}, {1/2, {-2, -1, 1}}}")
///

dim CohomologyTally := C -> max ((keys C)/first)

isVectorBundleTally = method(TypicalValue => Boolean)
isVectorBundleTally CohomologyTally := C ->(
     --Assumes the Cohomology tally is the betti table of a Tate resolution over the exterior algebra.
     --Note that script returns "false" if the table doesn't include regularity and coregularity or isn't 1+dim steps wide.
     n := dim C;
     K := keys C;
     if min (K/first) != 0 then return false; -- no H^0 present
     (lo,hi) := range C;
--     lo := min (K/last)+n;
--     hi := max (K/last);
     if #(select(K, k -> last k + first k == lo and first k < n and C_k !=0)) !=0 then return false;--lo > coregularity
     if #(select(K, k -> last k + first k == hi and first k >0 and C_k !=0)) !=0 then return false;--hi <regularity     
     return true)
     

----------


range =method()
range CohomologyTally := C ->(
     n := dim C;
     K := keys C;
     if min (K/first) != 0 then return false; -- no H^0 present
     lo := min (K/last)+n;
     hi := max (K/last);
     (lo,hi))

eulerCharacteristic=method()
eulerCharacteristic(CohomologyTally, ZZ) := (C,d) ->(
     sum(1+dim C, i-> (-1)^i*C_(i,d)))

interpolate = method()
interpolate(Ring, List) := (T,L) ->(
     --L is a list of (argument, value) pairs
     t := T_0;
     if #L != #unique(L/first) then error"arguments not distinct";
     sum(L, l-> (last l)*product(select(L, l1->first l1 != first l), l1-> (t - first l1)/(first l-first l1))
	  ))
///
interpolate(QQ[t], {{0,-1}, {1,0}, {2,3}})
sub(oo, t=>-1)
///

eulerPolynomial = method()
eulerPolynomial(PolynomialRing, CohomologyTally) := (T,C) ->(
     --T should be a polynomial ring over QQ
     --C should be the cohom tally OF A VECTOR BUNDLE
     if not isVectorBundleTally C then error"Not a vector bundle tally";
     n := dim C;
     lo :=0;
     hi :=0;
     (lo,hi) = range C;
     interpolate(T, apply(toList(hi-n..hi), d -> {d, eulerCharacteristic(C,d)}))
	       )
 
extendCohomologyTable=method()
extendCohomologyTable(CohomologyTally,ZZ,ZZ) := (C,lo,hi) ->(
     if not isVectorBundleTally C then error "table not a sufficiently wide cohomology tally of a vector bundle";
     lo1 := 0;
     hi1 := 0;
     (lo1, hi1) = range C;
     n := dim C;
     if lo-n <lo1  or hi> hi1 then (
	  t:=symbol t; T:=QQ[t];
	  p:=eulerPolynomial(T,C););
     K:=keys C;
     K1:=apply(lo1-lo+n,j->(n,lo-n+j));     
     K2:=apply(hi-hi1,j->(0,hi1+j+1));
     K0:=select(K,k->(k_0+k_1>=lo and k_0+k_1 <= hi));	        
     D:= new MutableHashTable;     
     L0:=apply(K0,k-> k => C_k) ;     
     L1:=apply(K1,k-> k=> (-1)^n*sub(p,t=>(k_1)_QQ));
     L2:=apply(K2,k-> k=> sub(p,t=>(k_1)_QQ));
     new CohomologyTally from join(L1,L0,L2))

beilinsonData=method()

beilinsonData(CohomologyTally,ZZ):=(C,d)->(
     n:=dim C;
     Cd:=(extendCohomologyTable(C,d-n,d+n))(d);
     Kd:=select(keys Cd,k->last k<=0 and last k>=-n); 
     Md:=new CohomologyTally from apply(Kd,k-> k=>Cd_k))

///
     Md1:=select(flatten apply(n+1,i->apply(toList(-n..n),j->(i-j,j,Md_(i,j-i)))),t->t_2 !=0)
     sort(Md1,k->k_1)
     homologicalRange := sort unique apply(Md1,k->k_1)
     Qs=apply(n+1,i->image koszul(i+1,vars S)**S^{i})     
     F:= new ChainComplex
     F.ring=S
     Fs=apply(homologicalRange,j->(j,(directSum(apply(select(Md1,k->k_1==j),k->directSum(apply(k_2,g->Qs_(k_0))))))**S^{-d}))
     apply(Fs,m->(m_0,betti m_1))
///



///
restart
loadPackage ("BGG", Reload => true)
loadPackage ("BoijSoederbergExtension", Reload => true)

///
TEST///
S = ZZ/101[a..d]
C1 = cohomologyTable (sheaf coker koszul(3, vars S), -3,3)
C2 =(cohomologyTable (sheaf coker koszul(3, vars S), -4,2))(+1)
C3 =(cohomologyTable (sheaf image matrix"a,b,c", -4,2))
C1++C3
C4=C1++C2
decomposeCohomologyTable C4
C=C1
beilinsonData(C,-2)
beilinsonData(C4,2)
///


///
S=ZZ/101[a..d] -- P^3
LF={-1,-3,-4},LG={-1,-4,-5}

C=cohomologyTable(sheaf supernatural(S,LG),-5,5)

MG=supernatural(S,LG);cG=cohomologyTable(sheaf MG,-5,5)
MF=supernatural(S,LF);cF=cohomologyTable(sheaf MF,-5,5)
time cFG=cohomologyTable(sheaf (MF**MG), -5,5)

zeroesOfMonadTensorSupernatural(S,C,2,LF) --does not work for H^2(-4)
zeroesOfMonadTensorSupernatural(S,C,1,LF) --does not work for H^2(-4)
zeroesOfMonadTensorSupernatural(S,C,0,LF) --does not work for H^2(-4)
zeroesOfMonadTensorSupernatural(S,C,-1,LF) --does not work for H^2(-4)
zeroesOfMonadTensorSupernatural(S,C,-2,LF) --does not work for H^2(-4)
zeroesOfMonadTensorSupernatural(S,C,-3,LF) --works for H^2(-4)==0 since 
-- 0-> fg->F0 -> F1 ->0 gives 
--                               H^1 F1(-4)=0
--     H^2fg(-4)->H^2 F0(-4)=0
zeroesOfMonadTensorSupernatural(S,C,-3,LF) --work for H^3(-6)==0 
beilinsonData(C,-4)
zeroesOfMonadTensorSupernatural(S,C,-4,LF) --work for H^3(-6)==0 
zeroesOfMonadTensorSupernatural(S,C,-10,LF) --does not work for H^3(-6)==0 
C
///

///
S=ZZ/101[a..e] -- P^4
LF={-1,-2,-4,-5},LG={-1,-2,-5,-6}

C=cohomologyTable(sheaf supernatural(S,LG),-5,5)

MG=supernatural(S,LG);cG=cohomologyTable(sheaf MG,-5,5)
MF=supernatural(S,LF);cF=cohomologyTable(sheaf MF,-5,5)
time cFG=cohomologyTable(sheaf (MF**MG), -5,5)
C
beilinsonData(C,-3)
time zeroesOfMonadTensorSupernatural(S,C,-3,LF) --works for H^3(-5)==0 since 
-- 0-> fg-> F0 -> F1 -> F2 ->0 gives
--                                                H^1 F2(-5)=0 (across the border but !)
--                               x ->H^2 F1(-5)=0
--     H^3fg(-5)->H^3 F0(-5)=0
zeroesOfMonadTensorSupernatural(S,C,-3,LF) --work for H^4(-7)==0 

///

///
--H^i End E on P^2
S=ZZ/101[a..c]
lambda=4
L={-1,-lambda-2}
M=supernatural(S,L);
C=cohomologyTable(sheaf M, -5,5)
cohomologyTable(sheaf Hom(M,M),-5,5)
M1=ker random(S^lambda,S^{lambda+2:-1})**S^{lambda+1};
C1=cohomologyTable(sheaf M1, -5,5)
cohomologyTable(sheaf Hom(M1,M1),-5,5)
///

///
--H^i End E on P^3
S=ZZ/101[a..d]
L={-1,-3,-6}
M=supernatural(S,L);
C=cohomologyTable(sheaf M, -5,5)
time cohomologyTable(sheaf Hom(M,M),-5,5)  -- used 7.42552 seconds
L={-1,-4,-7}
M=supernatural(S,L);
C=cohomologyTable(sheaf M, -5,5)
time cohomologyTable(sheaf Hom(M,M),-5,5)  -- used 31.02 seconds
L={-1,-5,-8}
M=supernatural(S,L);
C=cohomologyTable(sheaf M, min L+2,2)
time cohomologyTable(sheaf Hom(M,M),-5,5)  -- used 96.4511 seconds
L={-1,-5,-9}
M=supernatural(S,L);
C=cohomologyTable(sheaf M, min L+2,2)
time cohomologyTable(sheaf Hom(M,M),-5,5)
{*     -- used 285.486 seconds
           -5  -4  -3  -2  -1   0   1   2   3   4   5
o132 = 3: 385 150  27   8   1   .   .   .   .   .   .
       2: 330 387 404 336 220  81  40  11   .   .   .
       1:   .   .  11  40  81 220 336 404 387 330 205
       0:   .   .   .   .   .   1   8  27 150 385 756
*}
///
zeroesOfMonadTensorSupernatural=method()
zeroesOfMonadTensorSupernatural(Ring,CohomologyTally,ZZ,List):=(S,C,k,L)->(
     n:=dim S-1;
     Qs:=apply(n+1,i->image (koszul(n-i+1, vars S))**S^{n-i+1});
 --    apply(Qs,Q->cohomologyTable(sheaf Q,-5,5))
     lo:=min L-2,hi:=1;
     M:=supernatural(S,L) ;
     cMQs:=apply(Qs,Q->cohomologyTable(prune sheaf( Q**M),lo,hi)) ;   
     Md:=beilinsonData(C,k);
     Md1:=select(flatten apply(toList(-n..n),j->apply(n+1,i->(n-i+j,j,Md_(i,j-i)))),t->t_2 !=0);
     homologicalRange := sort unique apply(Md1,k->k_1);
     zeroes:=apply(homologicalRange,j->(j,(sum(apply(select(Md1,kk->kk_1==j),
			 kk->kk_2*cMQs_(kk_0))))(-k-1)
	       ));
     zeroes
     )

supernatural = method()
supernatural(Ring, List) := (S,Z) -> (
maxZ := max Z;
Z0 := apply(Z, z -> -z + maxZ);
n := numgens S-1;
if n != #Z then error"wrong number of zeros";
kk := coefficientRing S;
(R,L) := projectiveProduct(kk,toList(n:1));
R0 := R;
gensIdeals := {ideal gens R0}| apply(n-1, i-> (
     	                             R0 = coefficientRing R0;
                                     promote(ideal gens R0,R)));
G:= gens product(n, i-> (gensIdeals_i)^(Z0_i));
H:= syz(map(R^{apply(Z0, i->i+1)}, R^(n+1) ** source G, L**G), DegreeLimit => 0);
HS := sub(H,S);
S^{-maxZ-1}**coker( ((vars S)**(S^(rank source G)))*HS)
)
--input: a BettiTally or a similar hash table
--output: a triple, 
--First element: the first summand in the (conjectural) Boij-Soederberg decomposition
--second element: the multiplier
--third element: the result of subtracting it.

topZeroSequence = method()
topZeroSequence CohomologyTally := C ->(
     K := keys C;
     K = select(K, k-> C_k !=0);
     n := max(K/first);
     Ki :={};
     zl := 0;
     apply(reverse toList(1..n), i-> (
	       Ki = select(K, k -> first k == i);
	       if Ki == {} then {zl = zl+1,0} else {zl = max(Ki/last)+1,C_(i,zl-1)}
	  ))
)

decomposeC1 = method()
decomposeC1 CohomologyTally := C->(
     tzs :=topZeroSequence C;
     K := keys C;
     range := toList(min(K/last)..max(K/last));
     Z := tzs/first;
--     if not isStrictlyIncreasing L then print "NOT IN THIS SIMPLEX OF PURE BETTI DIAGRAMS";
     t := symbol t;
     T := ZZ[t];
     p := product(Z, z ->t-z);
     n := 0; -- -#tzs;
     val := 0;
     Ctop := new CohomologyTally from apply(reverse range, d -> (
	       if (val = abs sub(p, t=>d)) == 0 then n = n+1;
	       (n,d)=>val));
     cornersOfCtop := apply(tzs/(m -> (first m)-1), d->abs sub(p, t=>d));
     denoms := cornersOfCtop;
     nums := tzs/last;
     ratio :=  min apply(#nums, i-> if denoms_i != 0 then nums_i/denoms_i else infinity );
     (C, ratio, merge(C,Ctop, (i,j)->i-ratio*j))
--     new CohomologyTally from 
--     apply(keys C, k -> k=>(C_k - ratio*Ctop_k))
     )

decomposeC = method()
decomposeC CohomologyTally := C -> (
     B1 := new CohomologyTally from C;
--     B1:= new MutableHashTable from B;
     ratio := 1;
     Ztop := {};
     while min values B1 >= 0 and max values B1 > 0 list (
	  (Ztop, ratio, B1) = decomposeC1 B1;
	  {ratio, topZeroSequence Ztop/first}))

end
///

restart
loadPackage ("BGG", Reload =>true)
S = ZZ/101[a,b,c,d] -- P^3
cohomologyTable(F136 = sheaf (M124 = supernatural(S,{-1,-2,-4})), -7, 7)
cohomologyTable(F125 = sheaf (M125=supernatural(S,{-1,-2,-5})), -5, 5) 
C = cohomologyTable(sheaf prune (M125**M124), -7,7)
decomposeC C

S = ZZ/101[a,b,d] -- P^2
W = {-2,-4}
M=supernatural(S,W)
cohomologyTable(sheaf M, -5, 5) 
C = cohomologyTable(sheaf prune (M**M), -6,5)
decomposeC C

C = cohomologyTable(sheaf supernatural(S,{-1,-2}), -5, 5) 
cohomologyTable(sheaf supernatural(S,{-3,-2}), -5, 5) 
isHomogeneous M

S = ZZ/101[a,b,c,d] -- P^3
C=cohomologyTable(F124 = sheaf (M124 = supernatural(S,{-1,-2,-4})), -5, 5) 


cohomologyTable(F125 = sheaf (M125=supernatural(S,{-1,-2,-5})), -5, 5) 
cohomologyTable(sheaf prune Hom(M125, M124), -5,5)
cohomologyTable(sheaf prune Hom(M124, M125), -5,5)
cohomologyTable(sheaf prune (M125**M124), -5,5)

cohomologyTable(F136 = sheaf (M136 = supernatural(S,{-1,-3,-6})), -7, 7)
cohomologyTable(F125 = sheaf (M125=supernatural(S,{-1,-2,-5})), -5, 5) 

cohomologyTable(sheaf prune Hom(M136, M125), -5,5)

C = cohomologyTable(sheaf prune (M125**M136), -5,5)
decomposeC1 C
cohomologyTable(F135 = sheaf (M135 = supernatural(S,{-1,-3,-5})), -7, 7)
cohomologyTable(F125 = sheaf (M125=supernatural(S,{-1,-2,-5})), -5, 5) 
cohomologyTable(sheaf prune Hom(M125, M135), -5,5)-- 6 homoms
cohomologyTable(sheaf prune Hom(M135, M125), -5,5) 
cohomologyTable(sheaf prune (M125**M135), -5,5) 
aut = map(S,S,(vars S)_{3,2,0,1})
cohomologyTable(sheaf prune Hom(M125,coker aut presentation M135), -5,5) -- 6 homoms??

cohomologyTable(sheaf (M = S^{2}**prune ker random(S^2,S^{2+3: -1})), -5,5)
cohomologyTable(F024 = sheaf (M024=supernatural(S,{0,-2,-4})), -5, 5) 
cohomologyTable(sheaf prune Hom(M024, M), -5,5)
cohomologyTable(sheaf prune Hom(M,M024), -5,5)
cohomologyTable(sheaf prune (M125**M135), -5,5)


///
restart

viewHelp BGG
viewHelp PackageExports
