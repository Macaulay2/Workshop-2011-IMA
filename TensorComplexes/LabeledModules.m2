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
{*Not needed now, but would be nice:
kk as an optional second argument
handdling of rings (out put of pairs, so that ring name can be set)
facility for making tensors
exterior multiplication and contraction
Schur Functors
functoriality 
*}


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
  "tensorProduct",
  "symmetricMultiplication",
  "cauchyMap",
  "traceMap",
  "flattenedGenericTensor",
  "minorsMap",
  "tensorComplex1",
  "flattenedESTensor",
  "hyperdeterminant",
  "pureResTC1",
  "pureResTC",
  "pureResES1",
  "pureResES"
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
LabeledModule#{Standard,AfterPrint} = 
LabeledModule#{Standard,AfterNoPrint} = E -> (
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

-- This code probably belongs in the core of Macaulay2
tensorProduct = method(Dispatch => Thing)
tensorProduct List := args -> tensorProduct toSequence args
tensorProduct Sequence := args -> (
  if #args === 0 then  error "expected more than 0 arguments"; -- note: can't return, since we don't know the ring!
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




map(LabeledModule, LabeledModule, Matrix) := o-> (E,F,f) ->
new LabeledModuleMap from {
  symbol ring => ring F,
  symbol source => F,
  symbol target => E,
  symbol matrix => map(module E,module F,f)}
map(LabeledModule, LabeledModule, Function) := o-> (E,F,f) ->
new LabeledModuleMap from {
  symbol ring => ring F,
  symbol source => F,
  symbol target => E,
  symbol matrix => map(module E,module F,f)}
map(LabeledModule, LabeledModule, List) := o -> (E,F,L) ->
new LabeledModuleMap from {
  symbol ring => ring F,
  symbol source => F,
  symbol target => E,
  symbol matrix => map(module E,module F,L)}
map(LabeledModule,LabeledModule,ZZ) := LabeledModuleMap => o -> 
(E,F,i) -> map(E,F,matrix map(module E, module F, i))
map(LabeledModule,LabeledModule,LabeledModuleMap) := LabeledModuleMap => o -> 
(E,F,f) -> map(E,F, matrix f)

net LabeledModuleMap := g -> net matrix g
LabeledModuleMap#{Standard,AfterPrint} = 
LabeledModuleMap#{Standard,AfterNoPrint} = f -> (
  << endl;				  -- double space
  << concatenate(interpreterDepth:"o") << lineNumber << " : Matrix";
  << " " << target f << " <--- " << source f;
  << endl;)

coker LabeledModuleMap := Module => f -> coker matrix f
rank LabeledModuleMap := ZZ => f -> rank matrix f
transpose LabeledModuleMap := LabeledModuleMap => f ->
map(source f,target f, transpose matrix f)

LabeledModule#id = E -> map(E,E,1)

LabeledModuleMap * LabeledModuleMap := LabeledModuleMap => (f,g) -> 
map(target f, source g, matrix f * matrix g)

tensor(LabeledModuleMap,LabeledModuleMap) := LabeledModuleMap => o -> (m,n) -> 
map((target m)**(target n), (source m)**(source n), (matrix m)**(matrix n))
LabeledModuleMap ** LabeledModuleMap := LabeledModuleMap => (f,g) -> tensor(f,g)

LabeledModuleMap.tensorProduct = T -> fold(tensor, T)
     
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
  SdSe := tensorProduct {Sd,Se};
  map(Sde,SdSe, 
    (i,j) -> if fromOrdinal (i,Sde) == sort flatten fromOrdinal(j, SdSe) 
    then 1_S else 0_S))

cauchyMap = method(TypicalValue => LabeledModuleMap)
cauchyMap (ZZ, LabeledModule) := (b,E) -> (
  sour := exteriorPower(b,E);
  L := underlyingModules E;
  L10 := {exteriorPower(b,L#0)};
  L11 := apply(#L-1, j -> symmetricPower(b,L#(j+1)));
  L = L10 | L11;
  targ := tensorProduct L;
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
  if #L === 0 then error "expected a nonempty list";
  inds := productList apply(#L, i -> toList(0..L#i-1));
  x := symbol x;
  vrbls := apply(inds,i -> x_(toSequence i));
  local S;
  if #L === 1 then S=kk[x_0..x_(L_0-1)] 
  else S = kk[vrbls];
  --make generic tensor (flattened)
  Blist := apply(#L, i->labeledModule S^(L_i));
  --B = tensor product of all but Blist_0
  if #L === 1 then map(labeledModule S,Blist_0, vars S)
  else(
    B := tensorProduct apply(#L-1, i -> Blist_(i+1));     
    map(B, Blist_0, 
      (i,j) -> x_(toSequence({fromOrdinal(j, Blist_0)}| fromOrdinal(i, B))))))

minorsMap = method()
-- Since we may not need the "full" minors map, we may be able
-- to speed up this method.
minorsMap(Matrix, LabeledModule):= LabeledModuleMap => (f,E) -> (
  --Assumes that E has the form 
  --E = wedge^b((source f)^*) ** wedge^b(target f)
  --where source f and target f are labeled free modules.
  S := ring f;
  b := #((basisList E)_0_0);
  if b != #((basisList E)_0_1) or #((basisList E)_0) != 2
  then error "E doesn't have the right format";
  J := basisList E;
  sour := (underlyingModules((underlyingModules E)_0))_0;
  tar := (underlyingModules((underlyingModules E)_1))_0;
  map(labeledModule S, E, (i,j)-> (
      p := J_j;
      det submatrix(f, apply(p_1, k-> toOrdinal(k, tar)),
	apply(p_0, k-> toOrdinal(k, sour))))))

minorsMap(LabeledModuleMap, LabeledModule) := LabeledModuleMap => (f,E) ->
     minorsMap(matrix f, E)


isBalanced = f-> rank source f == sum ((underlyingModules target f)/rank)

tensorComplex1 = method()


{*
FIX: things have a little.
Make the first map of a generic tensor complex:
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
*}


tensorComplex1 LabeledModuleMap := LabeledModuleMap => f -> (
  -- NOTE: local variables names following the notation from the
  -- Berkesch-Erman-Kummini-Sam "Tensor Complexes" paper
  -- 
  -- f: A --> B1** B2** ... Bn
  -- makes the map F0 <- F1 as above.
  -- if f is not balanced, we should  be doing something else 
  if not isBalanced f then error "map is not balanced";
  S := ring f;  
  B := {S^0} | underlyingModules target f;
  A := source f;
  n := #B-1;
  b := B / rank; -- {0, b1, b2,..,bn}
  d := accumulate(plus, {0} | b); --{0, b1, b1+b2...}
  if n === 0 then f
  else if n === 1 then 
    map(exteriorPower(b_1,B_1),exteriorPower(b_1,A)**labeledModule(S^{ -d_1}),{{det matrix f}})
  else(
    -- source of output map
    F1 := tensorProduct({exteriorPower(b_1,A), exteriorPower(b_1,B_1)} |
      apply(toList(2..n), j-> symmetricPower(d_(j-1)-b_1,B_j)));
    -- target of output map
    F0 := tensorProduct apply(n-1, j-> symmetricPower(d_(j+1), B_(j+2)));
    trMap := traceMap tensorProduct apply(toList(2..n), 
      j -> symmetricPower(b_1,B_j));
    G1 := tensorProduct(target trMap, F1);
    g0 := map(G1, F1, trMap ** id_F1); -- tc1
    G1factors := flatten(
      ((underlyingModules target trMap) | {F1}) / underlyingModules );
    -- G2 and G1 are isomorphic as free modules with ordered basis but different
    -- as labeled modules
    G2 := tensorProduct G1factors;
    -- g1 is the map induced by dropping all parentheses in the tensor product  
    g1 := map(G2, G1, id_(S^(rank G1)));
    perm := join({2*n-2, 2*n-1}, toList(0..n-2), 
      flatten apply(n-1, j -> {j+n-1, j+2*n}));
    G3factors := G1factors_perm;
    G3 := tensorProduct G3factors;
    -- g2 is an isomorphism obtain by reordering the factors of a tensor product.
    -- The reordering is given by the permutation 'perm'  
    permMatrix := mutableMatrix(S, rank G3, rank G2);
    for J in basisList G2 do permMatrix_(toOrdinal(J_perm,G3),toOrdinal(J,G2)) = 1;
    g2 := map(G3, G2, matrix permMatrix);
    G3a := G3factors_0;
    G3b := tensorProduct G3factors_(toList(1..n));
    G3c := tensorProduct G3factors_(toList(n+1..#G3factors-1));
    prodB := tensorProduct apply(n,i -> B_(i+1));  
    G4b := exteriorPower(b_1, prodB);
    dualCauchyMap := map (G4b, G3b, transpose cauchyMap(b_1, prodB));
    g3 := id_(G3a) ** dualCauchyMap ** id_(G3c); 
    symMultMap := map(F0, G3c, tensorProduct apply(n-1, 
      	j -> symmetricMultiplication(B_(j+2),b_1,d_(j+1)-b_1)));
    minMap := minorsMap(f, tensorProduct(G3a, G4b));
    g4 := minMap ** symMultMap;
    map(F0, F1 ** labeledModule S^{ -b_2}, g4 * g3 * g2 * g1 * g0)))


-- When f is a balanced tensor, then this reproduces the tensor
-- used by Eisenbud and Schreyer in their original construction of
-- pure resolutions.  For instance tensorComplex f will equal to their
-- pure resolution.  However, this function works even in the nonbalanced
-- case.  In that case, it produces the `natural' analogue of their tensor.

flattenedESTensor = method()
flattenedESTensor (List, Ring) := LabeledModuleMap => (L,kk)->(
  --make ring of generic tensor
  if #L === 0 then error "expected a nonempty list";
  if #L === 1 then error "expected a balanced tensor";
  n:=#L-1;
  x:=symbol x;
  S:=kk[x_0..x_(n-1)];
  Blist := apply(#L, i->labeledModule S^(L_i));
  --B = tensor product of all but Blist_0
  B := tensorProduct apply(#L-1, i -> Blist_(i+1));     
  map(B, Blist_0, 
      (i,j) -> if 0<=j-sum fromOrdinal(i,B) then if j-sum fromOrdinal(i,B)<n 
      then x_(j-sum fromOrdinal(i,B)) else 0 else 0)
 )


tensorComplex1 (LabeledModuleMap,List) := LabeledModuleMap => (f,w) -> (
  -- NOTE: local variables names following the notation from the
  -- Berkesch-Erman-Kummini-Sam "Tensor Complexes" paper
  -- 
  -- f: A --> B1** B2** ... Bn
  -- makes the map F0 <- F1 as above.
  -- if f is not balanced, we should  be doing something else 
  -- w = (0,w1,...)
  if not w_0 == 0 and w_1 >=0 and min apply(toList(2..#w), i-> w_i-w_(i-1)) > 0 then 
      error "w not of the form (0,non-neg,increasing)";
  
  S := ring f;  
  B := {S^0} | underlyingModules target f;
  A := source f;
  a := rank A;
  n := #B-1;
  if #w != n+1 then error"weight vector has wrong length";
  b := B / rank; -- {0, b1, b2,..,bn}
  
  d1 := if w_1>0 then 1 else b_1;
  r1 := # select(w, wj -> wj < d1);
  if r1>2 then error "r1>2 is a case we can't handle";
  if n === 0 or n===1 and r1 ===1 then return f;
  if n === 1 and r1 === 2
      then return map(exteriorPower(b_1,B_1),exteriorPower(b_1,A)**labeledModule(S^{ -d1}),{{det matrix f}});

    F1 := tensorProduct({exteriorPower(d1,A)}|
	 apply(toList(1..r1-1),j-> exteriorPower(b_j,B_j)) | -- r1 = 1 or 2
      apply(toList(r1..n), j-> symmetricPower(w_j-d1,B_j)));
    -- target of output map
    F0 := tensorProduct apply(n, j-> symmetricPower(w_(j+1), B_(j+1)));
    trMap := id_(labeledModule S);
--  I don't think these n>1 workarounds are needed anymore.  There's another one below.
    if n>1 then trMap = traceMap tensorProduct apply(toList(r1..n), 
      j -> symmetricPower(d1,B_j));
    G1 := tensorProduct(target trMap, F1);
    g0 := map(G1, F1, trMap ** id_F1);
    G1factors := flatten(
      ((underlyingModules target trMap) | {F1}) / underlyingModules );
    -- G2 and G1 are isomorphic as free modules with ordered basis but different
    -- as labeled modules
    G2 := tensorProduct G1factors;
    -- g1 is the map induced by dropping all parentheses in the tensor product  
---
    g1 := map(G2, G1, id_(S^(rank G1)));
    perm := {};
    if r1==2 then perm = join({2*n-2, 2*n-1}, toList(0..n-2), 
      flatten apply(n-1, j -> {j+n-1, j+2*n}))
    else  perm ={2*n}|toList(0..n-1)|flatten apply(n, j -> {j+n, j+2*n+1});
    G3factors := G1factors_perm;
    G3 := tensorProduct G3factors;
    -- g2 is an isomorphism obtain by reordering the factors of a tensor product.
    -- The reordering is given by the permutation 'perm'  
    permMatrix := mutableMatrix(S, rank G3, rank G2);
    for J in basisList G2 do permMatrix_(toOrdinal(J_perm,G3),toOrdinal(J,G2)) = 1;
    g2 := map(G3, G2, matrix permMatrix);
    G3a := G3factors_0;
    G3b := tensorProduct G3factors_(toList(1..n));
    G3c := labeledModule S; -- case n==1
    if n>1 then
        G3c = tensorProduct G3factors_(toList(n+1..#G3factors-1));
    prodB := tensorProduct apply(n,i -> B_(i+1));  
    G4b := exteriorPower(d1, prodB);
    dualCauchyMap := map (G4b, G3b, transpose cauchyMap(d1, prodB));
    g3 := id_(G3a) ** dualCauchyMap ** id_(G3c); 
--if r1 > n then symMultMap := id
    symMultMap := map(F0, G3c, tensorProduct apply(toList(r1..n), 
      	j -> symmetricMultiplication(B_j,d1,w_j-d1)));

    minMap := minorsMap(f, tensorProduct(G3a, G4b));
    g4 := minMap ** symMultMap;
    map(F0, F1 ** labeledModule S^{ -d1}, g4 * g3 * g2 * g1 * g0))

hyperdeterminant = method()
hyperdeterminant LabeledModuleMap := f -> (
     --hyperdeterminant of a boundaryformat tensor f
     --check boundary format
     b := apply(underlyingModules target f, M -> rank M);
     if not rank source f == 1 + sum b - #b then
     	  error"not boundary format!";
     w := {0,1}|apply(toList(2..#b), i-> sum(toList(0..i-2), j-> b_j)-(i-2));
     det matrix tensorComplex1 (f,w))

-- There is a bijection between degree sequences and balanced tensor complexes.
-- This code takes a degree sequence to the first map of the corresponding
-- balanced tensor complex.
pureResTC1=method()     
pureResTC1 (List,Ring) := LabeledModuleMap =>(d,kk)->(
     b := apply(#d-1,i-> d_(i+1)-d_i);
     if min b<=0 then error"d is not strictly increasing";
     a := d_(#b) - d_0;
     f := flattenedGenericTensor({a}|b,kk);
     tensorComplex1(f)
     )


pureResTC=method()
pureResTC (List,Ring):=ChainComplex => (d,kk)->(
     res coker matrix pureResTC1(d,kk)
     ) 

pureResES1=method()     
pureResES1 (List,Ring) := LabeledModuleMap =>(d,kk)->(
     b := apply(#d-1,i-> d_(i+1)-d_i);
     if min b<=0 then error"d is not strictly increasing";
     a := d_(#b) - d_0;
     f := flattenedESTensor({a}|b,kk);
     tensorComplex1(f)
     )

pureResES=method()
pureResES (List,Ring):=ChainComplex => (d,kk)->(
     res coker matrix pureResES1(d,kk)
     ) 

--------------------------------------------------------------------------------
-- DOCUMENTATION
--------------------------------------------------------------------------------
beginDocumentation()

document { 
  Key => LabeledModules,
  Headline => "multilinear algebra with labeled basis",
  "Blah, blah, blah.",
  }

document { 
  Key => LabeledModule,
  Headline => "???",
  "Blah, blah, blah.",
  }

undocumented { (net, LabeledModule), (net, LabeledModuleMap) }

document { 
  Key => {labeledModule, (labeledModule,Module), (labeledModule,Ring)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {underlyingModules, (underlyingModules, LabeledModule)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {basisList, (basisList, LabeledModule)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {fromOrdinal, (fromOrdinal, ZZ, LabeledModule)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {toOrdinal, (toOrdinal, Thing, LabeledModule)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (ring, LabeledModule),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (module, LabeledModule),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (rank, LabeledModule),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (symbol ==, LabeledModule, LabeledModule),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (exteriorPower, ZZ, LabeledModule),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {multiSubsets, (multiSubsets, ZZ, ZZ), (multiSubsets, List, ZZ)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (symmetricPower, ZZ, LabeledModule),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {tensorProduct, (tensorProduct, List), (tensorProduct, Sequence)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {(symbol **, LabeledModule, LabeledModule), 
    (tensor,LabeledModule, LabeledModule)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {symmetricMultiplication, 
    (symmetricMultiplication, LabeledModule, ZZ, ZZ)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {cauchyMap, (cauchyMap, ZZ, LabeledModule)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {traceMap, (traceMap, LabeledModule)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {minorsMap, (minorsMap, LabeledModuleMap, LabeledModule), 
    (minorsMap, Matrix, LabeledModule)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {flattenedGenericTensor, 
    (flattenedGenericTensor, List, Ring)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => LabeledModuleMap,
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {(map,LabeledModule,LabeledModule,Matrix),
    (map,LabeledModule,LabeledModule,List),    
    (map,LabeledModule,LabeledModule,Function)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (source, LabeledModuleMap),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (target, LabeledModuleMap),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (matrix, LabeledModuleMap),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (ring, LabeledModuleMap),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (rank, LabeledModuleMap),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (transpose, LabeledModuleMap),
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => {(tensor, LabeledModuleMap, LabeledModuleMap),
    (symbol **, LabeledModuleMap, LabeledModuleMap)},
  Headline => "???",
  "Blah, blah, blah.",
  }

document { 
  Key => (symbol *, LabeledModuleMap, LabeledModuleMap),
  Headline => "???",
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
assert(matrix symmetricMultiplication(F,1,1) == matrix{
    {1_S,0,0,0},{0,1,1,0},{0,0,0,1}})
assert(rank symmetricMultiplication(F,2,1) == 4)
assert(matrix symmetricMultiplication(F,2,0) == id_(S^3))
///

-- test 5
TEST ///
S = ZZ/101[a,b,c];
F2 = labeledModule S^2;
F3 = labeledModule S^3;
F5 = labeledModule S^5;
F30 = tensorProduct {F2,F3,F5}
assert(rank cauchyMap(2,F30)  == 90)
F2' =  tensorProduct {F2, labeledModule S^1}
assert(matrix cauchyMap(1,F2') == id_(S^2))
///

--test 6
TEST///
kk=ZZ/101;
f=flattenedGenericTensor({4,1,2,1},kk);
BD=new BettiTally from {(0,{0},0) => 2, (1,{1},1) => 4, (2,{3},3) => 4, (3,{4},4) => 2};
assert(betti res coker matrix tensorComplex1 f==BD)
f=flattenedESTensor({4,1,2,1},kk);
assert(betti res coker matrix tensorComplex1 f==BD)
assert(betti pureResTC({0,1,3,4},kk)==BD)
assert(betti pureResES({0,1,3,4},kk)==BD)
f = flattenedGenericTensor({3,3},kk)
assert( (betti res coker tensorComplex1 f) === new BettiTally from {(1,{3},3) => 1, (0,{0},0) => 1} )
f = flattenedGenericTensor({3,2,2},kk)
assert(hyperdeterminant f ==  det matrix tensorComplex1 (f,{0,1,2}))
f = flattenedGenericTensor({3,3},kk)
assert(hyperdeterminant f ==  det matrix tensorComplex1 (f,{0,1}))
assert(hyperdeterminant f ==  det matrix tensorComplex1 (f,{0,0}))
f=flattenedESTensor({3,2,2},kk)
assert(hyperdeterminant f ==  det matrix tensorComplex1 (f,{0,1,2}))

///

end
--------------------------------------------------------------------------------
-- SCRATCH SPACE
--------------------------------------------------------------------------------

restart
uninstallPackage "LabeledModules"
installPackage "LabeledModules"
check "LabeledModules"

f = flattenedGenericTensor({3,3},kk)
betti res coker tensorComplex1 (f, {0,0})

betti pureResTC({0,1,3,4,6,7},ZZ/101)
hyperdeterminant  flattenedESTensor({5,3,2,2},ZZ/2) 

kk = ZZ/101;
f=flattenedESTensor({4,2,2},kk)
tensorComplex1 f
betti res coker tensorComplex1 f

f=flattenedESTensor({7,1,2,1,2,1},kk)
betti res coker tensorComplex1 f


f = flattenedGenericTensor({3,3},kk)
betti res coker tensorComplex1 f

f = flattenedGenericTensor({3},kk)
betti res coker tensorComplex1 f

g = tensorComplex1 f

betti res coker matrix g
cokermatrix f


S = ZZ/101[a,b,c,d];
L = {6,2,2,2};
Blist = apply(#L, i-> labeledModule S^(L_i));
B = tensorProduct apply(#L-1, i -> Blist_(i+1));     
f = map(B, Blist_0, (i,j) -> random(1,S))
g = tensorComplex1 f;
time betti res coker matrix g

EN = (a,c,kk) -> (
  f:=flattenedGenericTensor({a,c} | apply(a-c, i-> 1), kk);
  f1 := tensorComplex1 f;
  betti res coker f1)
EN(10,3,ZZ/101)

a = 10
c = 3
f = flattenedGenericTensor({a,c} | apply(a-c, i-> 1), kk);
time eagonNorthcott matrix f
?eagonNorthcott
