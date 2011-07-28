{*
makeTensorProductMap = method()
makeTensorProductMap (List,Module,Module) := (f,Tsource, Ttarget) ->(
     --given a list of maps f_i: F_i \to G_i, make the tensor product.
     --assume that Tsource = makeTensorProduct (L/source), and similarly for Ttarget.
	       F := f/source;
	       if F != underlyingModules Tsource then error "bad source";
	       G := f/target;
	       if G != underlyingModules Ttarget then error "bad target";	       	       
     map(Ttarget, Tsource, (i,j) -> (
	       I := (fromOrdinal Tsource) j;
	       J := (fromOrdinal Ttarget) i;
	       product apply(#I, u->(f_u)_(((toOrdinal G_u) (J_u)), (toOrdinal F_u) (I_u))))
	  )
     )

makeTensorProductMap (List) := f ->(
     --given a list of maps f_i: F_i \to G_i, make the tensor product.
     --creates Tsource = makeTensorProduct (f/source), and similarly for Ttarget.
	       F := f/source;
	       G := f/target;
     	       Tsource := makeTensorProduct F;
     	       Ttarget := makeTensorProduct G;	       
     map(Ttarget, Tsource, (i,j) -> (
	       I := (fromOrdinal Tsource) j;
	       J := (fromOrdinal Ttarget) i;
	       product apply(#I, u->(f_u)_(((toOrdinal G_u) (J_u)), (toOrdinal F_u) (I_u))))
	  )
     )

*}

///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c,d,e,f]
F1 = makeExplicitFreeModule(S,2)
F2 = makeExplicitFreeModule(S,2)
G1= makeExplicitFreeModule(S,2)
G2= makeExplicitFreeModule(S,1)
Ts = makeTensorProduct {F1,F2}
Tt = makeTensorProduct {G1,G2}
f1 = map(G1,F1, {{a,b},{c,d}})
f2 = map(G2,F2, {{e,f}})

makeTensorProductMap ({f1,f2},Ts,Tt)
makeTensorProductMap ({f2,f1})
f1
f2
///





{*makeTensor1 = method()
makeTensor1(List) := (L) ->(
     --make the tensor product module F = \otimes L_i
     --with 
     --F.cache.modules = L
     --F.cache.Lranks list of ranks
     --F.cache.toOrdinal 
     --     a function that takes a list I of ZZ with I_j<rank L_i 
     --	    and returns the ordinal position of the corresponding basis vector of F
     --F.cache.fromOrdinal 
     --     a function that takes an integer and returns the index set I
     --     of the basis vector in that ordinal position.
     
     --eventually the L_i might also be modules with structure of this type.
     n := #L;
     Lranks := L/rank;
     LToOrdinal = apply(L, G -> 
	  if not G.cache.?toOrdinal then G.cache.toOrdinal = i->i);
     LFromOrdinal = apply(L, G -> 
	  if not G.cache.?fromOrdinal then G.cache.fromOrdinal = i->i);
     --make list whose i-th term is the product of all but the last i+1 elements of L,
     --with i starting at 0. (thus Lprods_(n-1) = 1, the empty product.)
     Lprods = for i from 0 to n-1 list product (Lranks_{i+1..n-1});
     F := (ring L_0)^(product Lranks);
     F.cache.modules = L;
     F.cache.ranks = Lranks;
     F.cache.toOrdinal = I -> sum apply(#I, j->(L_j).cache.toOrdinal(I#j)*(Lprods#j));
     F.cache.fromOrdinal = p -> reverse (for i from 0 to n-1 list(
     	                         pcomponent = p%Lranks#(n-1-i);
					 p = (p-pcomponent)//Lranks#(n-1-i);
					 (L#(n-1-i)).cache.fromOrdinal pcomponent));
    F )
///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk= ZZ/101
S = kk[a,b,c]

L = {S^2, S^3, S^5}
F = makeTensor1(L)
F.cache.toOrdinal {1,2,4}
for d from 0 to 29 do print (d == F.cache.toOrdinal F.cache.fromOrdinal d)
///
*}



     F0 = makeTensorProduct(
	  for i from 2 to n list 
	     makeSymmetricPower(B_i,d_(i-1)));
     minorsf = gens minors(b#1, f);
     wedgeb1Sourcef := makeExteriorPower(source f, b#1);
     G3 = makeTensorProduct {wedgeb1A,wedgeb1Sourcef,F0};
     F0G3 = map(F0,G3, (i,j) -> (
	       i1 := (fromOrdinal F0)i;
	       j1 := (fromOrdinal G3)j;
	       detrownumbers := (toOrdinal A)(j1_0);
	       detcolnumbers = (j1_1)/(toOrdinal source f);
--problem in the following lines:       
               if (fromOrdinal F0)i == j1/(k->k_2) then
	       det(f_detcols^detrows)*F0_i 
	       else 0_F0)
	  );
     error""



{*
DtoTensor = method()
DtoTensor (Module) := F -> (
     --Assumes F = D^b G;
     --returns map D^b G --> G\otimes...\otimes G.
     G := (underlyingModules F)#0;
     g := rank G;
     b:=0;
     while binomial(g+b-1,g)<rank F do b = b+1;
     s := signs rank F;
     P = permutations rank F;
     tG := makeTensorProduct(splice{b:G});
     map(tG,F,(i,j) -> )

signs = n->(
     --list the signs of the permutations, in the order they
     --are produced by permuations n. SLOW for n>=7.
          ZF := ZZ^n;
          (permutations n)/(p-> det ZF_p))
*}
///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
signs 3

time for n from 0 to 8 do print time (signs n;)
kk = ZZ/101
S = kk[a,b,c]
F2 = S^2
F = makeSymmetricPower(F2, 3)
DtoTensor F
4+4

8+8
///

wedgeDToWedge = method()
wedgeDToWedge (Module, Module) := (F,G) -> (
     --requires 
     -- F =  wedge^b F0 \otimes D^b(F1)
     --and 
     -- G = wedge^b(F0\otimes F1).
     --creates the equivariant embedding F->G.
     
     --sort out the underlying modules and ranks
     S := ring F;
     rankF := rank F;
     WbF0 := (underlyingModules F)#0;
     wbf0 := rank WbF0;
     F0 := (underlyingModules WbF0)#0;
     f0 := rank F0;

     DbF1 := (underlyingModules F)#1;
     dbf1 := rank DbF1;
     F1 := (underlyingModules DbF1)#0;
     f1 := rank F1;     

     F0F1 := (underlyingModules G)#0;

     --find b
     b := 0;     
     while binomial(f1+b-1,b)<dbf1 do b = b+1;
     
     --check setup
     if F0 != (underlyingModules F0F1)#0 then error"bad underlying module 0";
     if F1 != (underlyingModules F0F1)#1 then error"bad underlying module 1";
     if rank F0F1 != f0*f1 then error"bad module F0F1";     
     if rank G != binomial(rank F0F1, b) then error"bad module G";
     if rank WbF0 != binomial(f0,b) then error "bad module wedge b F0";     
     if rank DbF1 != binomial(f1+b-1,b) then error "bad module DbF1";          
     if rank F != binomial(f0,b) *binomial(f1+b-1,b) then error "bad module F";    

     --make the map
--     I := id_(S^(binomial(f1,b)));
	  
     map(G,F,(i,j)->(
     BG = (fromOrdinal G) i;
     BF = (fromOrdinal F) j;
     BG0 = BG/first; -- corresponds to an element of wedge^b F0
     BG1 = BG/last; -- corresponds to an element of wedge^b F1
     BF0 =  first BF; -- element of wedge^b F0
     BF1 = last BF;-- corresponds to an element of D^b F1
     if BG0 == BF0 and BF1 == sort BG1 then 1_S else 0_S))
)


///
--map of wedge^d A \otimes Sym^d B to wedge^d(A\otimes B).
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
kk = ZZ/101
S = kk[x,y,z]
b = 2 
r0=3
r1 = 4

test = (b, r0,r1) ->(
F0 = S^r0;
F1 = S^r1;
WbF0 = makeExteriorPower(F0,b);
DbF1 = makeSymmetricPower(F1, b);
F = makeTensorProduct{WbF0, DbF1};
G = makeExteriorPower(makeTensorProduct{F0,F1},b);
print(rank F, rank G);
time A = wedgeDToWedge(F,G);
rank A == rank source A)

test(3,5,3)

///


--this could presumably be done faster by creating a sparse matrix and filling in where the 1's are.
--the number of 1's is 
-- binomial(f0, b) * (f1)^b (these correspond to a subset of the basis of G)
--while the number of elements of the matrix is 
--binomial(f0*f1,b)*binomial(f0,b)*binomial(f1+b-1, b).


wedgeDToWedgeSparse = method()
wedgeDToWedgeSparse (Module, Module) := (F,G) -> (
     --requires 
     -- F =  wedge^b F0 \otimes D^b(F1)
     --and 
     -- G = wedge^b(F0\otimes F1).
     --creates the equivariant injection F -> G.
     
     --sort out the underlying modules and ranks
     S := ring F;
     rankF := rank F;
     WbF0 := (underlyingModules F)#0;
     F0 := (underlyingModules WbF0)#0;
     f0 := rank F0;
     wbf0 := rank WbF0;
     DbF1 := (underlyingModules F)#1;
     dbf1 := rank DbF1;
     F1 := (underlyingModules DbF1)#0;
     f1 := rank F1;     
     F0F1 := (underlyingModules G)#0;
     if F0 != (underlyingModules F0F1)#0 then error"bad modules";
     if F1 != (underlyingModules F0F1)#1 then error"bad modules";     

     --find b
     b:=0;     
     while binomial(f1+b-1,b)<dbf1 do b = b+1;
     
{*     map(G,F,(i,j)->(
     BG = (fromOrdinal G) i;
     BF = (fromOrdinal F) j;
     BG0 = BG/first; -- corresponds to an element of wedge^b F0
     BG1 = BG/last; -- corresponds to an element of wedge^b F1
     BF0 =  first BF; -- element of wedge^b F0
     BF1 = last BF;-- corresponds to an element of D^b F1
     if BG0 == BF0 and BF1 == sort BG1 then 1_S else 0_S))
*}
     P0 := basisList WbF0; -- list of strictly ordered b-tuples of basis elements of F0
     P1 := productList toList(b:basisList F1); -- list of unordered b-tuples of basis elements of F1
     --make the map as a sparse matrix, with a 1 for each element (p,q) \in P0 x P1, in position corresponding
     --to the position of the basis element 
     -- (p0 wedge p1..) \otimes product q  in F and 
     --(p0\otimes q0) \wedge (p1\otimes q1)...  in G.
     entryList := flatten apply(P0,p -> apply(P1, q-> (
		    i := (toOrdinal G) apply(#p, i->{p_i,q_i});
		    j := (toOrdinal F) {p,sort q};
		    (i,j) => 1_S)));
     print entryList;
--     error();
     map(G,F, entryList)
)
///

--map of wedge^d A \otimes Sym^d B to wedge^d(A\otimes B).
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
kk = ZZ/101
S = kk[x,y,z]
b = 2 
r0 = 3
r1 = 3

F0 = S^r0;
F1 = S^r1;
makeExplicitFreeModule F0
makeExplicitFreeModule F1
productList toList (2:basisList F1)
WbF0 = makeExteriorPower(F0,b);
DbF1 = makeSymmetricPower(F1, b);
F = makeTensorProduct{WbF0, DbF1};
G = makeExteriorPower(makeTensorProduct{F0,F1},b);
A = wedgeDToWedgeSparse(F,G);

rank A
rank F
rank G


test = (b, r0,r1) ->(
F0 = S^r0;
F1 = S^r1;
WbF0 = makeExteriorPower(F0,b);
DbF1 = makeSymmetricPower(F1, b);
F = makeTensorProduct{WbF0, DbF1};
G = makeExteriorPower(makeTensorProduct{F0,F1},b);
print(rank F, rank G);
time A = wedgeDToWedgeSparse(F,G);
print (rank A == rank source A);
time A = wedgeDToWedge(F,G);
rank A == rank source A
)
test(3,5,3)
///






kk = ZZ/101
S = kk[x,y,z]
ab = {3,2,1,3}
mods = prep(S, ab)
twist(mods_0,1)
tensormods = twist(makeTensorProduct(drop(mods,1)), -1)
f = random(mods#0,tensormods)
source f
TC1(S,f)
F0G1;
minorsf
f
n
b
d
F0
F1
uM F1

{*Make the first map of a generic tensor complex:
Given (over a ring R)
a map A <--- \otimes_j Bj,
and integers bi >= 1, 
set d = (d0=0, d1=b1, d2 = b1+b2...). 
The desired map is the composite

F0= wedge^b1 A ** wedge^b1 B1* ** \otimes_{i\geq 2} S^{d_{j-1}-b1} Bj
by "trace" to 

G1 = wedge^b1 A ** wedge^b1 B1* ** 
     [ (\otimes_{j\geq 2} S^b1 Bj)*
     **(\otimes_{j\geq 2} S^b1 Bj)] 
     **\otimes_{i\geq 2} S^{d_{j-1}-b1} Bj
to (by reassociating)

G2 = wedge^b1 A ** [wedge^b1 B1* ** (\otimes_{j\geq 2} S^b1 Bj)*] 
       ** [(\otimes_{j\geq 2} S^b1 Bj)]  
       ** \otimes_{i\geq 2} S^{d_{j-1}-b1} Bj]
to (by the wedge ** sym to wedge map and multiplication in Sym

G3 = wedge^b1 A ** \wedge_b1(\otimes_{j\geq 1} Bj*] 
     ** \otimes_{i\geq 2} S^{d_{j-1}} Bj]
to (by the minors)

F0 = R ** \otimes_{i\geq 2} S^{d_{j-1}} Bj]
*}



TC1 = method()
TC1(Ring, Matrix) := (S,f) ->(
     --f: f: A --> B1** B2** ... Bn
     --makes the map G1 <- F1 as above.
     --if f is not balanced, we should  be doing something else (swimming)
     if not isBalanced f then error"map is not balanced";
     B  = {S^0}|underlyingModules target f;
     A = source f;
     n = #B-1;
     b = B/rank; -- {0, b1, b2,..,bn}
     d = accumulate(plus,{0}|b); --{0, b1, b1+b2...}
--     wedgeb1A = makeExteriorPower(A,b_1);
     L11 = {makeExteriorPower(A,b_1),makeExteriorPower(B_1,b_1)};
     L12 = apply(toList(2..n), j->makeSymmetricPower(B_j,d_(j-1)-b#1));
     F1 = makeTensorProduct(L11 | L12);

     G11 = makeTensorProduct apply(toList(2..n), j->makeSymmetricPower(B_j,b#1));
     T = makeTrace G11;
     T**id_F1
     )

