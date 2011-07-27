{*Make the first map of a generic tensor complex:
Given (over a ring R)
free modules Bi of ranks bi\geq 1,
a free module A, of rank a = sum bi.
a map A <--- \otimes_j Bj,
set d = (d0=0, d1=b1, d2 = b1+b2...). 

The desired map is the composite

F1= wedge^b1 A ** wedge^b1 B1* ** \otimes_{i\geq 2} S^{d_{j-1}-b1} Bj
by "trace" to 

G1=wedge^b1 A ** wedge^b1 B1* ** [ (\otimes_{j\geq 2} S^b1 Bj)* ** (\otimes_{j\geq 2} S^b1 Bj)]  \otimes_{i\geq 2} S^{d_{j-1}-b1} Bj
to (by reassociating)

G2=wedge^b1 A ** [wedge^b1 B1* **  (\otimes_{j\geq 2} S^b1 Bj)*] ** [(\otimes_{j\geq 2} S^b1 Bj)]  \otimes_{i\geq 2} S^{d_{j-1}-b1} Bj]
to (by the wedge ** sym to wedge map and multiplication in Sym

G3=wedge^b1 A ** [wedge^b1 \wedge_b1(\otimes_{j\geq 1} Bj*] ** \otimes_{i\geq 2} S^{d_{j-1}} Bj]
to (by the minors)

F0=R ** \otimes_{i\geq 2} S^{d_{j-1}} Bj]


----------Implementation:

not yet done:

**change to function(ZZ, module) 

Not needed now, but would be nice:
exterior multiplication and contraction and trace
functoriality for exterior product
functoriality for symmetric product

Note that explict free modules can be identified with their duals!
*}
---
--ExplicitFreeModule = new Type of HashTable

makeExplicitFreeModule = method() -- Could add: TypicalValue => ExplicitFreeModule

makeExplicitFreeModule(Ring,ZZ) := (S,r) -> (
     --Explicit free modules have cache data about:
     --underlying free module or modules,
     --a list of objects that name basis elements (typically integer lists)
     --a function that takes a basis object and returns its ordinal position,
     --and a function that takes an ordinal and returns a basis object.
     E := S^r;
     E.cache.underlyingModules = {S^r};
     E.cache.basisList = splice {0..r-1};
     E.cache.fromOrdinal = j -> j;
     E.cache.toOrdinal = j -> j;
     E)

makeExplicitFreeModule Module := F -> (
     --if F is not yet an "explicit" free module (as witnessed by the
     --absence of F.cache.basisList), make it into one.
     if F.cache.?basisList then F else (
     F.cache.underlyingModules = {F};
     F.cache.basisList = splice {0..rank F -1};
     F.cache.fromOrdinal = j -> j;
     F.cache.toOrdinal = j -> j;
     F))

--shortcuts:
underlyingModules = E -> E.cache.underlyingModules; uM = underlyingModules
basisList = E -> E.cache.basisList ; bL = basisList
fromOrdinal = E -> E.cache.fromOrdinal; fO = fromOrdinal
toOrdinal = E -> E.cache.toOrdinal; tO = toOrdinal

///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
path
kk = ZZ/101
S = kk[a,b,c]
F = makeExplicitFreeModule(S,4)
basisList F
E = makeExplicitFreeModule(S^5)
basisList E
E = makeExplicitFreeModule F

///

makeExteriorPower = method()

makeExteriorPower(Module, ZZ) := (F,d) ->(
     --make the exterior power free module, with cache similar to makeTensor.
     --generators are given in revlex order. NOTE: that the basisList is 
     --a list of  subsets of basisList F, NOT a list of 0-1 lists.
     --Can convert back and forth with multisetToMonomial and monomialToMultiset
     makeExplicitFreeModule F;
     E := (ring F)^(binomial(rank F,d));
          E.cache.underlyingModules = {F};     
          E.cache.basisList = subsets(basisList F, d);
     	  E.cache.fromOrdinal = j -> (basisList E)#j;
          E.cache.toOrdinal = I -> position(basisList E, J->J==I);
          E)
///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F = makeExplicitFreeModule(S,4)
E = makeExteriorPower(F,2)
basisList E
E2 = makeExteriorPower(E,2)
basisList E2

F = makeTensorProduct{S^1,S^1}
uM F
F1 = makeExteriorPower(F,1)
uM F
uM F1
///

multiSubsets = method()
multiSubsets (List,ZZ) := (L,d) -> (
     --(ordered) d element subsets allowing repetition, given in revlex order
     ss := subsets(#L+d-1,d);
     ss1 := ss/(I -> apply(#I, i-> I_i-i));
     apply(ss1, I-> apply(I, i-> L#i))
     )
///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
L = {A, {1,2}}
multiSubsets(L,2)
multiSubsets({0,1,2},2)
///

makeSymmetricPower = method()
makeSymmetricPower(Module, ZZ) := (F,d) ->(
     --make the symmetric power free module, with cache similar to makeTensor.
     makeExplicitFreeModule F;
     E := (ring F)^(binomial(rank F+d-1, d));
     E.cache.underlyingModules = {F};
     E.cache.basisList = multiSubsets(basisList F,d);
     E.cache.fromOrdinal = j -> (basisList E)#j;
     E.cache.toOrdinal = I -> position(basisList E, J->J==I);
     E)

multisetToMonomial=method();
multisetToMonomial(List, List) := (L, mL) -> 
     --changes a list mL of elements of L, with repetitions, to a list of
     --integers, of length #L whose i-th entry is the number of times L_i
     --occurs in mL
      apply(L, i-> #positions(mL, j-> j==i))

monomialToMultiset=method()
monomialToMultiset(List, List) := (L,mm) ->(
     --changes a list mm of integers to a list of elements of L
     --where the i-th element of L is repeated m_i times
     flatten apply(#mm, i-> splice{mm_i:L_i}))
///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F = makeExplicitFreeModule(S,4)
E = makeSymmetricPower(F,2)
basisList E
N=(basisList E)/(I->multisetToMonomial(basisList F, I))
N/(I->monomialToMultiset(basisList F, I))
(toOrdinal E) {0,3}
(fromOrdinal E) 7
E = makeSymmetricPower(S^4, 2)
basisList E
(toOrdinal E) {0,3}
(fromOrdinal E) 7

E=makeSymmetricPower(F,0)

///



productList = method()
productList(List):= L->(
     --takes a list of lists, and forms  list of  tuples of elements, in order
     --{0,0}, {0,1}, ... (that is, lexicographically).
     Pp := if #L == 0 then {}
     else if #L == 1 then apply(L#0, i->{i})
     else if #L == 2 then flatten (apply(L_0,i->apply(L_1, j->{i,j})))
     else (
	  P0 := productList drop (L, -1);
	  P1 := last L;
	  Pp = (apply(P0,a->apply(P1,b->append(a,b))));
	  --the following line removes the outermost-but-one set of parens
	  splice(Pp/toSequence));
--     for i from 1 to #L-2 do Pp = flatten Pp;
     Pp)
///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
L0 = {}
productList L0
L1 = {toList(0..1)}
productList L1
L2 = {toList(0..1),toList(0..2)}
productList L2
bL makeTensorProduct{QQ^2}

L3 = {toList(0..1),toList(0..2),toList(0..2)}
P = productList L3

L4 = {toList(0..1),toList(0..2),toList(0..1),toList(0,1)}
productList L4


M1= {{0, 0}, {0, 1}}
M2 = {{0, 2}, {1, 2}}
L = {M1,M2}
productList L
M3 = {A,B}
L = {M1,M2,M3}
productList L


///

makeTensorProduct = method()
makeTensorProduct List := L ->(
     --L is a list of free modules (possibly explicit) over the same ring.
     L/makeExplicitFreeModule;
     E := (ring L_0)^(product (L/rank));
     E.cache.underlyingModules = L;
     E.cache.basisList = productList(L/basisList);
     E.cache.fromOrdinal = j -> (basisList E)#j;
     E.cache.toOrdinal = I -> position(basisList E, J->J==I);
     E)
makeTensorProduct Module := M -> makeTensorProduct{M}
makeTensorProduct (Module, Module) := (M1,M2) -> makeTensorProduct{M1,M2}
makeTensorProduct (Module, Module,Module) := (M1,M2,M3) -> makeTensorProduct{M1,M2,M3}
///
--Note: this is automatically associative!! the commutativity iso is just permuting
--the basis elements.
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F1 = makeExplicitFreeModule(S,2)
F2 = makeExplicitFreeModule(S,3)
F3 = makeExplicitFreeModule(S,5)
E = makeTensorProduct {F1,F2,F3}
makeTensorProduct(F1,F2,F3)
makeTensorProduct {S^1,F2}
uM oo
--E = makeTensorProduct {S^1,S^2,S^3}
basisList E
(toOrdinal E) {0,2,3}
(fromOrdinal E) 5

E = makeTensorProduct(S^2,S^1)
basisList E
(toOrdinal E){0,0}
///

makeTrace = method()
makeTrace Module := F ->(
     --make the map S^1 \to F \otimes F
     --where S = ring F and we identify F and F^*
     makeExplicitFreeModule F;
     S := ring F;
     T := makeTensorProduct{F,F};
     S1 := makeExplicitFreeModule(S^1);
     map(T, S1, (i,j) ->(
	   I := (fromOrdinal T)i;
	   if I_0 == I_1 then 1_S else 0_S
	   )))


///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
makeTrace(S^3)
T = makeTensorProduct{S^3, S^3}
///

makeSymmetricMultiplication = method()
makeSymmetricMultiplication(Module,ZZ, ZZ) := (F, d,e) ->(
     --make the map Sym^d(F)\otimes Sym^e F \to Sym^(d+e) F
     --Caveat: for large examples it would probably be better to make this as a sparse matrix!
     Sd := makeSymmetricPower(F,d);
     Se := makeSymmetricPower(F,e);
     Sde := makeSymmetricPower(F,d+e);
     SdSe := makeTensorProduct{Sd,Se};
     toMonomial := (M,I)->multisetToMonomial(basisList((underlyingModules M)#0),I);
--     error();
     map(Sde,SdSe , (i,j) -> if
       toMonomial(Sde,(fromOrdinal Sde)i) == toMonomial(SdSe,(fromOrdinal SdSe)j)
            		    then 1_S else 0_S
	)
     )

{*     if underlyingModule SdF != underlyingModule SeF then error"bad modules";
     if SdF != makeSymmetricPower(F,d) then error"bad first module";
     if SeF != makeSymmetricPower(F,e) then error"bad second module";
*}    
///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
makeSymmetricMultiplication(S^2, 1,1)
makeSymmetricMultiplication(S^2, 2,1)
d = 2;e=1;
E=S^2
F=makeTensorProduct{E,E}
bL F
bL makeSymmetricPower(E,2)

///

///
--Associativity:
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F2 = S^2
F3 = S^3
F5 = S^5
F = makeTensorProduct{F2,F3,F5}
F1 = makeTensorProduct{F3,F2,F5}
G = makeTensorProduct{makeTensorProduct{F2,F3},F5}
basisList F
basisList F1
basisList G
///


makeCauchy = method()
makeCauchy(ZZ,Module) := (b,E)->(
     	  --E is thought of as E0 ** ... ** Em
	  --produces the map
	  --wedge^b(E) -> wedge^b(E0) ** Sym^b E1 ** Sym^b E2 ** ...
     sour := makeExteriorPower(E,b);
     L := underlyingModules E;
     L10 := {makeExteriorPower(L_0,b)};
     L11 := apply(#L-1, j-> makeSymmetricPower(L_(j+1), b));
     L1 := L10 | L11;
     tar := makeTensorProduct L1;
     M := mutableMatrix(ring E, rank tar, rank sour);
     j := {};
     scan(basisList sour, i->(
	       j = transpose i;
	       if j_0 == unique j_0 then(
		    j = apply(j, ji->sort ji);
	       	    M_((toOrdinal tar) j, (toOrdinal sour) i) = 1;
		    )
	       ));
     map(tar, sour, matrix M)
     )

///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F2 = S^2
F3 = S^3
F5 = S^5
F = makeTensorProduct{F2,F3,F5} --{F2,F3}
FF = makeTensorProduct{F2,S^1}
makeCauchy(1,FF)
makeCauchy(2,F)
rank oo
///

---  L is the ranks of A, B_1, and up to B_n
---  S=Sym(A**B_1**..**B_n)
---  this is the map (A*)**S(-1)-->(B_1**B_2**..**B_n)**S obtained 
---  by flattening the generic tensor
---  I don't know when we want to define the ring S (before the code or in the code).

flattenedGenericTensor = (L,kk)->(
     --make ring of generic tensor
     inds := productList(apply(#L,i->(toList(0..((L#i)-1)))));
     vrbls := apply(inds,i->( x_(toSequence(i))));
     S := kk[vrbls];
     --make generic tensor (flattened)
     B := apply(#L,i->makeExplicitFreeModule S^(L_i));
     --Btotal = tensor product of all but B0
     Btotal := makeTensorProduct(apply(#L-1,i->(B_(i+1))));     
     f := map(Btotal,B_0,(i,j)->(
	       x_(toSequence( {(fromOrdinal B_0)(j)}|(fromOrdinal Btotal)(i)))
	       ))
--     return {PHI,S}
     );

isBalanced = f-> rank source f == sum ((underlyingModules target f)/rank)

makeMinorsMap = method()
makeMinorsMap(Matrix, ZZ):=(f,b)->(
     E1 := source(f);
     E2 := target(f);
     F2 := makeTensorProduct(
	  makeExteriorPower(E1,b),
	  makeExteriorPower(E2,b)
	                     );
     J := basisList F2;
     matrix{apply(rank F2,i->(
	    cols := apply((J#i)#0,l->( (toOrdinal E1)(l)));
	    rows := apply((J#i)#1,k->( (toOrdinal E2)(k)));   
	    determinant(submatrix(f,rows,cols)) 
	       ))}
     );
makeMinorsMap(Matrix, Module):=(f,E)->(
     --Assumes that E has the form 
     --E = wedge^b((source f)^*) ** wedge^b(target f)
     --where source f and target f are explicit free modules.
     S := ring f;
     b := #((basisList E)_0_0);
     if b != #((basisList E)_0_1) or #((basisList E)_0) !=2
               then error "E doesn't have the right format";
     J := basisList E;
     sour := (underlyingModules((underlyingModules E)_0))_0;
     tar := (underlyingModules((underlyingModules E)_1))_0;
     map(S^1, E, (i,j)->(p := J_j;
	   determinant submatrix(
		f,p_1/(toOrdinal tar),p_0/(toOrdinal sour)
		                )
	   	     	 )
        )
      )

///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
kk=ZZ/101
f=flattenedGenericTensor({7,2,2},kk)
S=ring f

E = makeTensorProduct(
     makeExteriorPower(source f, 2), 
     makeExteriorPower(target f, 2))
g = makeMinorsMap(f,2)
g1 = makeMinorsMap(f,E)
0 == g-matrix(g1)
matrix(g)==matrix(g1)
///

twist = method()
twist(Module,ZZ) := (M,d) -> (
     makeExplicitFreeModule M;
     E := M**S^{d};
     E.cache.underlyingModules = M.cache.underlyingModules;
     E.cache.basisList = M.cache.basisList;
     E.cache.fromOrdinal = M.cache.fromOrdinal;
     E.cache.toOrdinal = M.cache.toOrdinal;
     E)

prep = (S,intlist) ->apply(intlist , i->S^i)

--the following has a problem at the end (4/17/2011)
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
TC12 = method()
TC12(Ring, Matrix) := (S,f) ->(
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
     G1 = makeTensorProduct(target T, F1);
     tc1=map(G1,F1,T**id_F1);
     G1mods = flatten(((uM target T)|{F1})/uM);
     perm=join({2*n-2, 2*n-1}, 
	         toList(0..n-2), 
		 flatten apply(n-1, j->{j+n-1, j+2*n})
		 );
     H1 = makeTensorProduct G1mods;
     H2 =  makeTensorProduct G1mods_perm;
     permMatrix = mutableMatrix(S, rank H2, rank H1);
     scan(basisList H1, 
	  J -> 
	  permMatrix_((toOrdinal H2) J_perm, (toOrdinal H1) J)=1
     	  );
     
     permMap = map(H2, H1, matrix permMatrix) 
	       )


///
restart
path = append(path, "~/src/IMA-2011/TensorComplexes/")
load "TensorComplexes.m2"
kk=ZZ/101
--f=flattenedGenericTensor({7,1,2,1,2,1},kk)
--f=flattenedGenericTensor({7,2,2},kk)
f=flattenedGenericTensor({6,2,2,2},kk)
--f=flattenedGenericTensor({8,2,2,2,2},kk)
S=ring f
TC12(S,f);
tc12 = oo;
rank oo

Ttar = target T
blTtar = bL Ttar
flatten (blTtar_0)
Ttar1 = makeTensorProduct flatten((uM(Ttar))/uM)
map(Ttar1,Ttar, (i,j) ->
     if (fromOrdinal Ttar1) i == flatten ((fromOrdinal Ttar) j) then 1 else 0)
((bL Ttar1)_0) == flatten ((bL Ttar)_0)

Ttar2 = makeTensorProduct 
           apply(n-1, i->
		 makeTensorProduct{(uM Ttar1)_i, (uM Ttar1)_(n-1+i)})
F1 = source tc1
uM((uM F1)_1)
///

end

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
