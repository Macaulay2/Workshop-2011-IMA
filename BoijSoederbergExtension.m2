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
     "eulerPolynomial1",
     "decomposeCohomologyTable",
     "extendCohomologyTable",
     "isVectorBundleTally",
     "eulerCharacteristic",
     "eulerPolynomial",
     "interpolate",
     "range"
     }

QQ * CohomologyTally := (d,C) -> applyValues(C, v -> d*v)
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
--eulerPolynomial1=method()

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

///
restart
loadPackage ("BGG", Reload => true)
loadPackage ("BoijSoederbergExtension", Reload => true)

///
TEST///

p=interpolate(QQ[t], {{0,-1}, {1,0}, {2,3/2}}) 
sub(p, t=>-1) -- NOTE that the value should be made a QQ, as follows:
sub(p, t=>(-1)_QQ)


S = ZZ/101[a..d]
C1 = cohomologyTable (sheaf coker koszul(3, vars S), -3,3)
C2 =(cohomologyTable (sheaf coker koszul(3, vars S), -4,2))
C3 =(cohomologyTable (sheaf image matrix"a,b,c", -4,2))
C1+C3
C1+C2


C = cohomologyTable (sheaf coker koszul(3, vars S), -3,3)
assert(toString extendCohomologyTable(C,-9,5)==toString cohomologyTable (sheaf coker koszul(3, vars S), -9,5))

C3C=extendCohomologyTable(C(3),-9,2)+extendCohomologyTable(C,-9,2)
decomposeCohomologyTable C3C
///


end

tensorTest = method()
tensorTest(Ring,List,List) := (S,L1,L2)->(
     M1:=supernatural(S,L1);
     M2:=supernatural(S,L2);
     lo:=min(L1)+min(L2)+dim S;hi:=1;
     C1:=cohomologyTable(sheaf M1,lo,hi);C2:=cohomologyTable(sheaf M2,lo,hi);
     C12:=cohomologyTable(sheaf (M1**M2),lo,hi);
     (reverse sort (decomposeCohomologyTable C12)_0_1,C12,C1,C2))

TEST///
S = ZZ/101[a,b,c,d] -- P^3
L={-1,-4,-5}
time Ct=tensorTest(S,L,L)
C=Ct_2
///

beilinsonWindow=method()
beilinsonWindow(CohomologyTally,ZZ) := (C,k) ->(
     n:=max(keys C/first);
     extendCohomologyTable(C k, -n,n))
///
beilinsonWindow(C,-1)

k=-3
///
beilinsonMonadTable=method()
beilinsonMonadTable(CohomologyTally,ZZ) := (C,k)->(
     n:=max(keys C/first);
     D:=beilinsonWindow(C,k);
     L:=flatten apply(toList(-n..n),e->apply(n+1,i->(i,e-i,D_(i,e-i))));
     B:=select(L,c->c_1<=0 and c_1 >=-n and c_2 !=0);
     B1:=apply(B,c->(-c_1,2*c_1+c_0,c_2));
     new CohomologyTally from apply(B1,b-> (b_0,b_1) => b_2)
)
beilinsonMonadTable(C,-3)
C
beilinsonMonadTable(C,-4)
B=beilinsonMonadTable(C,-6)
n
zeroSequencesOfSuperMonad =(B,n)->(
     B1:=apply(keys B,b->(b_0,b_1+b_0));
     range:=sort( B1/last);
     L:=toList(-n-1..-1);Li:={};d:=0;
     apply(range,i->(
	       d=(select(B1,b->b_1==i)/first)_0;
	       Li=select(L,l->-l!=d);
     	       if #Li != n then Li=toList(-n-1..-2);
	       (i,reverse Li,B_(d,i-d))))
     )
zeroSequencesOfSuperMonad(B,3)       
B
zeroesOfSuperMonadTensorSupernatural=method()
L1={-1,-4,-5}, k=0,L2={-1,-3,-4} 
C = cohomologyTable(sheaf supernatural(S,L1),-5,5)  	       
zeroesOfSuperMonadTensorSupernatural(Ring, CohomologyTally,ZZ,List) := (S,C,k,L2)->(
     -- zeroes of the monad tensor supernatural with homology C \tensor L2 
     n:=dim S-1;
     --M1:=supernatural(S,L1);
     B:=beilinsonMonadTable(C,k);
     Ls:=zeroSequencesOfSuperMonad(B,n);
     apply(Ls,iL->(iL_0,iL_2,((tensorTest(S,iL_1,L2))_1) (-1)))
     )          
beilinsonMonadTable(C,0)
 