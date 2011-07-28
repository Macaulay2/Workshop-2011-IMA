-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
-- Copyright 2011  David Eisenbud, Daniel Erman, Gregory G. Smith and Dumitru Stamate
--
-- This program is free software: you can redistribute it and/or modify it under
-- the terms of the GNU General Public License as published by the Free Software
-- Foundation, either version 3 of the License, or (at your option) any later
-- version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
-- FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
-- details.
--
-- You should have received a copy of the GNU General Public License along with
-- this program.  If not, see <http://www.gnu.org/licenses/>.
--------------------------------------------------------------------------------
newPackage(
  "LabeledModules",
  AuxiliaryFiles => false,
  Version => "1.0",
  Date => "28 July 2011",
  Authors => {
    {	 
      Name => "David Eisenbud", 
      Email => "de@msri.org", 
      HomePage => "http://www.msri.org/~de/"},
    {
      Name => "Daniel Erman", 
      Email => "derman@math.stanford.edu", 
      HomePage => "http://math.stanford.edu/~derman/"},	     
    {
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "http://www.mast.queensu.ca/~ggsmith"},
    {
      Name => "Dumitru Stamate", 
      Email => "dumitru.stamate@fmi.unibuc.ro"}},
  Headline => "multilinear algebra with labeled bases",
  DebuggingMode => true
  )

export {
  "LabeledModule",
  "LabeledModuleMap",
  "labeledModule",
  "underlyingModules",
  "basisList",
  "fromOrdinal",
  "toOrdinal",
  "multiSubsets",
  "tensorFold",
  "tensorProduct",
  "symmetricMultiplication",
  "cauchyMap",
  "traceMap",
  "flattenedGenericTensor",
  "minorsMap"
  }

--------------------------------------------------------------------------------
-- CODE
--------------------------------------------------------------------------------
-- constructing labeled modules
LabeledModule = new Type of HashTable
LabeledModule.synonym = "free module with labeled basis"

labeledModule = method(TypicalValue => LabeledModule)
labeledModule Module := M -> (
  if not isFreeModule M then error "expected a free module";
  new LabeledModule from {
    symbol module => M,
    symbol underlyingModules => {},
    symbol basisList => apply(rank M, i -> i),
    symbol cache => new CacheTable})
labeledModule Ring := S -> (
  new LabeledModule from {
    symbol module => S^1,
    symbol underlyingModules => {},
    symbol basisList => {{}},
    symbol cache => new CacheTable})

net LabeledModule := E -> net module E
LabeledModule#{Standard,AfterPrint} = LabeledModule#{Standard,AfterNoPrint} = E -> (
  << endl;				  -- double space
  << concatenate(interpreterDepth:"o") << lineNumber << " : free ";
  << ring E << "-module with labeled basis" << endl;)

module LabeledModule := E -> E.module
ring LabeledModule := E -> ring module E
rank LabeledModule := E -> rank module E
underlyingModules = method(TypicalValue => List)
underlyingModules LabeledModule := E -> E.underlyingModules
basisList = method(TypicalValue => List)
basisList LabeledModule := E -> E.basisList
fromOrdinal = method(TypicalValue => List)
fromOrdinal(ZZ, LabeledModule) := (i, E) -> (basisList E)#i
toOrdinal = method(TypicalValue => ZZ)
toOrdinal(Thing, LabeledModule) := (l, E) -> (
  position(basisList E, j -> j === l))

LabeledModule == LabeledModule := (E,F) -> (
  module E === module F 
  and underlyingModules E === underlyingModules F
  and basisList E === basisList F)

exteriorPower (ZZ, LabeledModule) := options -> (d,E) -> (
  S := ring E;
  r := rank E;
  if d < 0 or d > r then labeledModule S^0
  else if d === 0 then labeledModule S
  else new LabeledModule from {
      symbol module => S^(binomial(rank E, d)),
      symbol underlyingModules => {E},
      symbol basisList => subsets(basisList E, d),
      symbol cache => new CacheTable})

tomultisubset = x -> apply(#x, i -> x#i - i)
multiSubsets = method(TypicalValue => List)
multiSubsets (ZZ,ZZ) := (n,d) -> apply(subsets(n+d-1,d), tomultisubset)
multiSubsets (List,ZZ) := (L,d) -> apply(multiSubsets(#L,d), i -> L_i)

symmetricPower (ZZ, LabeledModule) := (d,E) -> (
  S := ring E;
  if d < 0 then labeledModule S^0
  else if d === 0 then labeledModule S
  else new LabeledModule from {
    symbol module => (ring E)^(binomial(rank E + d - 1, d)),
    symbol underlyingModules => {E},
    symbol basisList => multiSubsets(basisList E, d),
    symbol cache => new CacheTable})

productList = L -> (
     --L is supposed to be a list of lists
  n := #L;
  if n === 0 then {}
  else if n === 1 then apply(L#0, i -> {i})
  else if n === 2 then flatten table(L#0, L#1, (i,j) -> {i} | {j})
  else flatten table(productList drop(L,-1), last L, (i,j) -> i | {j}))

tensorFold = method(TypicalValue => LabeledModule)
     --this is the tensor product of labeled modules. 
     --Rename when M2's tensorProduct works for (at least) pairs of modules.
tensorFold List := L -> (
  n := #L;
  if n < 0 then error "-- expected a nonempty list";
  S := ring L#0;
  if n === 0 then labeledModule S
  else (
    if any(L, l -> ring l =!= S) then error "expected modules over the same ring";
    new LabeledModule from {
      symbol module => S^(product apply(L, l -> rank l)),
      symbol underlyingModules => L,
      symbol basisList => productList apply(L, l -> basisList l),
      symbol cache => new CacheTable}))

-- This code probably belongs in the core of Macaulay2
tensorProduct = method(Dispatch => Thing)
tensorProduct List := args -> tensorProduct toSequence args
tensorProduct Sequence := args -> (
  if #args === 0 then error "expected more than 0 arguments";
  y := youngest args;
  key := (tensorProduct, args);
  if y =!= null and y#?key then y#key else (
    type := apply(args, class);
    if not same type then error "incompatible objects in tensor product";
    type = first type;
    meth := lookup(symbol tensorProduct, type);
    if meth === null then error "no method for tensor product";
    S := meth args;
    if y =!= null then y#key = S;
    S))
tensor(Matrix, Matrix) := Matrix => options -> (f,g) -> f**g;


LabeledModule.tensorProduct = T -> (
  L := toList T;
  num := #L;
  if num < 0 then error "expected a nonempty list";
  S := ring L#0;
  if num === 0 then labeledModule S
  else (
    if any(L, l -> ring l =!= S) then error "expected modules over the same ring";
    new LabeledModule from {
      symbol module => S^(product apply(L, l -> rank l)),
      symbol underlyingModules => L,
      symbol basisList => productList apply(L, l -> basisList l),
      symbol cache => new CacheTable}))
LabeledModule ** LabeledModule := tensorProduct
tensor(LabeledModule, LabeledModule) := LabeledModule => o -> (F,E) -> F ** E

LabeledModuleMap = new Type of HashTable
LabeledModuleMap.synonym = "map of labeled modules"
ring LabeledModuleMap := f->f.ring
source LabeledModuleMap := f->f.source
target LabeledModuleMap := f->f.target
matrix LabeledModuleMap := o-> f->f.matrix

map(LabeledModule, LabeledModule, Matrix) := o-> (E,F,f)->
    new LabeledModuleMap from {
       symbol ring => ring F,
       symbol source => F,
       symbol target => E,
       symbol matrix => map(module E,module F,f)
       }
map(LabeledModule, LabeledModule, Function) := o-> (E,F,f)->
    new LabeledModuleMap from {
       symbol ring => ring F,
       symbol source => F,
       symbol target => E,
       symbol matrix => map(module E,module F,f)
       }
map(LabeledModule, LabeledModule, List) := o-> (E,F,L)->
    new LabeledModuleMap from {
       symbol ring => ring F,
       symbol source => F,
       symbol target => E,
       symbol matrix => map(module E,module F,L)
       }
net LabeledModuleMap := g -> net matrix g

transpose LabeledModuleMap := LabeledModuleMap => o-> f->
     map(source f,target f, transpose matrix f)

traceMap = method()
traceMap LabeledModule := LabeledModuleMap => E -> (
  S := ring E;
  T := E ** E;
  map(T, labeledModule S^1, (i,j) -> (
      I := fromOrdinal(i,T);
      if I_0 == I_1 then 1_S else 0_S)))

{*multisetToMonomial = (l,m) -> (
  seen := new MutableHashTable;
  scan(m, i -> if seen#?i then seen#i = seen#i +1 else seen#i = 1);
  apply(l, i -> if seen#?i then seen#i else 0))
monomialToMultiset = (l,e) -> flatten apply(#e, i -> toList(e#i:l#i))
*}


symmetricMultiplication = method(TypicalValue => LabeledModuleMap)
symmetricMultiplication (LabeledModule,ZZ,ZZ) := (F,d,e) -> (
     --make the map Sym^d(F)\otimes Sym^e F \to Sym^(d+e) F
     --Caveat: for large examples it would probably be better to make this as a sparse matrix!
     S := ring F;
     Sd := symmetricPower(d,F);
     Se := symmetricPower(e,F);
     Sde := symmetricPower(d+e,F);
     SdSe := tensorFold {Sd,Se};
     map(Sde,SdSe , (i,j) -> if
       fromOrdinal (i,Sde) == sort flatten fromOrdinal(j, SdSe)
            		    then 1_S else 0_S
	)
     )

cauchyMap = method(TypicalValue => LabeledModuleMap)
cauchyMap (ZZ, LabeledModule) := (b,E) -> (
  sour := exteriorPower(b,E);
  L := underlyingModules E;
  L10 := {exteriorPower(b,L#0)};
  L11 := apply(#L-1, j -> symmetricPower(b,L#(j+1)));
  L = L10 | L11;
  targ := tensorFold L;
  M := mutableMatrix(ring E, rank targ, rank sour);
  local j;
  for i in basisList sour do (
    j = transpose i;
    if j#0 == unique j#0 then (
      j = apply(j, l -> sort l);
      M_(toOrdinal(j,targ), toOrdinal(i,sour)) = 1));
  map(targ, sour, matrix M))

flattenedGenericTensor = method()
flattenedGenericTensor (List, Ring) := LabeledModuleMap => (L,kk)->(
     --make ring of generic tensor
     inds := productList apply(#L, i -> toList(0..L#i-1));
     x := symbol x;
     vrbls := apply(inds,i -> x_(toSequence i));
     S := kk[vrbls];
     --make generic tensor (flattened)
     Blist := apply(#L, i->labeledModule S^(L_i));
     --B = tensor product of all but Blist_0
     B := tensorFold apply(#L-1,i-> Blist_(i+1));     
     f := map(B,Blist_0,(i,j)->(
	       x_(toSequence({fromOrdinal(j, Blist_0)}|
			     fromOrdinal(i, B)
			     ))))
     )



minorsMap = method()
minorsMap(Matrix, LabeledModule):= LabeledModuleMap => (f,E)->(
     --Assumes that E has the form 
     --E = wedge^b((source f)^*) ** wedge^b(target f)
     --where source f and target f are labeled free modules.
     S := ring f;
     b := #((basisList E)_0_0);
     if b != #((basisList E)_0_1) or #((basisList E)_0) !=2
               then error "E doesn't have the right format";
     J := basisList E;
     sour := (underlyingModules((underlyingModules E)_0))_0;
     tar := (underlyingModules((underlyingModules E)_1))_0;
     map(labeledModule S, E, (i,j)->(
	        p := J_j;
	   det submatrix(f,
		apply(p_1, k-> toOrdinal(k, tar)),
	        apply(p_0, k-> toOrdinal(k, sour))		
             	                )))
      )

minorsMap(LabeledModuleMap, LabeledModule) := LabeledModuleMap => (ff,E) ->
     minorsMap(matrix ff, E)


tensor(LabeledModuleMap,LabeledModuleMap) := LabeledModuleMap => options -> (m,n) -> 
     map((target m)**(target n), (source m)**(source n), (matrix m)**(matrix n))

isBalanced = f-> rank source f == sum ((underlyingModules target f)/rank)
///
----TO FIX:
tensorComplex1 = method()
tensorComplex1(Ring, Matrix) := (S,f) ->(
     --f: f: A --> B1** B2** ... Bn
     --makes the map F0 <- F1 as above.
     --if f is not balanced, we should  be doing something else 
     if not isBalanced f then error"map is not balanced";
     B := {S^0}|underlyingModules target f;
     A := source f;
     n := #B-1;
     b := B/rank; -- {0, b1, b2,..,bn}
     d := accumulate(plus,{0}|b); --{0, b1, b1+b2...}
     L11 := {makeExteriorPower(A,b_1),makeExteriorPower(B_1,b_1)};
     L12 := apply(toList(2..n), j->makeSymmetricPower(B_j,d_(j-1)-b#1));
     F1 := makeTensorProduct(L11 | L12);
     F0 := makeTensorProduct apply(n-1, j-> makeSymmetricPower(B_(j+2), d_(j+1)));
     G11 := makeTensorProduct apply(toList(2..n), j->makeSymmetricPower(B_j,b#1));
     T := makeTrace G11;
     G1 := makeTensorProduct(target T, F1);
     tc1 := map(G1,F1,T**id_F1);
     G1mods := flatten(((uM target T)|{F1})/uM);
     perm := join({2*n-2, 2*n-1}, 
	         toList(0..n-2), 
		 flatten apply(n-1, j->{j+n-1, j+2*n})
		 );
     H1 := makeTensorProduct G1mods;
     G2factors := G1mods_perm;
     G2 := makeTensorProduct G2factors;
     permMatrix := mutableMatrix(S, rank G2, rank H1);
     scan(basisList H1, 
	  J -> 
	  permMatrix_((toOrdinal G2) J_perm, (toOrdinal H1) J)=1
     	  );
     permMap := map(G2, H1, matrix permMatrix);
     tc12 := permMap*tc1;
     G2A := G2factors_0;
     G2L := makeTensorProduct G2factors_(toList(1..n));
     G2R := makeTensorProduct G2factors_(toList(n+1..#G2factors-1));
     TC3Rmatrix := fold(tensor, 
	  apply (n-1, j-> makeSymmetricMultiplication(B_(j+2), b_1, d_(j+1)-b_1))
	  );
     TC3R := map (F0 ,G2R, TC3Rmatrix);
     tpB := makeTensorProduct apply(n,i->B_(i+1));
     tarTC3L := makeExteriorPower(tpB, b_1);
     TC3L := map (tarTC3L, G2L, transpose makeCauchy(b_1, tpB));
     TC4L := makeMinorsMap(f, makeTensorProduct(G2A, tarTC3L));
     map(F0, F1**S^{ -b_1 }, ((TC4L * (id_G2A ** TC3L))**TC3R)*tc12)
     )
///
--------------------------------------------------------------------------------
-- DOCUMENTATION
--------------------------------------------------------------------------------
beginDocumentation()

document { 
  Key => LabeledModules,
  Headline => "multilinear algebra with labeled basis",
  "Blah, blah, blah.",
  }

-------------------------------------------------------------------------------- 
-- TEST
--------------------------------------------------------------------------------

-- test 0
TEST ///
S = ZZ/101[a,b,c];
E = labeledModule S^4
assert(basisList E  == apply(4, i -> i))
assert(underlyingModules E == {})
assert(module E == S^4)
assert(fromOrdinal(2,E) == 2)
assert(toOrdinal(1,E) == 1)
F = labeledModule S
assert(basisList F == {{}})
assert(rank F == 1)
F' = labeledModule S^0
assert(basisList F' == {})
///

-- test 1
TEST ///
S = ZZ/101[a,b,c];
F = labeledModule S^4
E = exteriorPower(2,F)
assert(rank E == 6)
assert(#basisList E == 6)
assert(exteriorPower(0,E) == labeledModule S)
assert(basisList exteriorPower(1,E) == apply(basisList E, i -> {i}))
assert(exteriorPower(-1,E) == labeledModule S^0)
E' = exteriorPower(2,E)
assert(#basisList E' == 15)
assert(#multiSubsets(basisList E,2) == binomial(6+2-1,2))
assert(#multiSubsets({0,1,2},2) == binomial(3+2-1,2))
///

-- test 2
TEST ///
S = ZZ/101[a,b,c];
F = labeledModule S^4
E = symmetricPower(2,F)
assert(#basisList E == binomial(4+2-1,2))
assert(toOrdinal({0,3},E) == 6)
assert(fromOrdinal(7,E) == {1,3})
assert(symmetricPower(0,E) == labeledModule S)
assert(symmetricPower(-1,E) == labeledModule S^0)
assert(basisList symmetricPower(1,E) == apply(basisList E, i -> {i}))
///

-- test 3
TEST ///
S = ZZ/101[a,b,c];
F1 = labeledModule S^2
F2 = labeledModule S^3
F3 = labeledModule S^5
assert(tensor(F1,F2) == F1 ** F2)
E = tensorProduct {F1,F2,F3}
assert(rank E == product {rank F1, rank F2, rank F3})
assert(basisList E == sort basisList E)
assert((underlyingModules E)#0 == F1)
assert((underlyingModules E)#1 == F2)
assert((underlyingModules E)#2 == F3)
F = tensorProduct {labeledModule S^1, F2}
assert(F != F2)
assert((underlyingModules F)#0 == labeledModule S^1)
assert((underlyingModules F)#1 == F2)
assert(toOrdinal({0,1}, F) == 1)
assert(fromOrdinal(5,E) == {0,1,0})
///

-- test 4
TEST ///
S = ZZ/101[a,b,c];
F = labeledModule S^2
assert(matrix symmetricMultiplication(F,1,1) == matrix{{1_S,0,0,0},{0,1,1,0},{0,0,0,1}})
assert(rank matrix symmetricMultiplication(F,2,1) == 4)
assert(matrix symmetricMultiplication(F,2,0) == id_(S^3))
///

-- test 5
TEST ///
S = ZZ/101[a,b,c];
F2 = labeledModule S^2;
F3 = labeledModule S^3;
F5 = labeledModule S^5;
F30 = tensorProduct {F2,F3,F5}
assert(rank matrix cauchyMap(2,F30)== 90)
F2' =  tensorProduct {F2, labeledModule S^1}
assert(matrix cauchyMap(1,F2') == id_(S^2))
///

--test 6
TEST///
kk=ZZ/101
f=flattenedGenericTensor({6,2,2,2},kk)
S=ring f
E = tensorProduct(exteriorPower(2,source f), exteriorPower(2,target f))
g = minorsMap(matrix f,E)

///

end
--------------------------------------------------------------------------------
-- SCRATCH SPACE
--------------------------------------------------------------------------------

restart
uninstallPackage "LabeledModules"
installPackage "LabeledModules"
check "LabeledModules"

kk=ZZ/101
S = kk[a,b,c]
M = labeledModule S^1
N =  labeledModule S^2
map(N,M,matrix{{a,b}})
map(N,M,{{a,b}})
map(N,M,(i,j) -> (i+j)_S)
