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
  Date => "27 July 2011",
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
  "symmetricMultiplication",
  "cauchyMap",
  "traceMap"
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
    if any(L, l -> ring l =!= S) then error "-- expected modules over the same ring";
    new LabeledModule from {
      symbol module => S^(product apply(L, l -> rank l)),
      symbol underlyingModules => L,
      symbol basisList => productList apply(L, l -> basisList l),
      symbol cache => new CacheTable}))
LabeledModule ** LabeledModule := LabeledModule => (E,F) -> tensorFold {E,F}
tensor(LabeledModule,LabeledModule) := options -> (E,F) -> tensorFold {E,F}

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
  



{*makeSymmetricMultiplication = method()
makeSymmetricMultiplication(Module,ZZ, ZZ) := (F, d,e) ->(
     --make the map Sym^d(F)\otimes Sym^e F \to Sym^(d+e) F
     --Caveat: for large examples it would probably be better to make this as a sparse matrix!
     S := ring F;
     Sd := makeSymmetricPower(F,d);
     Se := makeSymmetricPower(F,e);
     Sde := makeSymmetricPower(F,d+e);
     SdSe := makeTensorProduct{Sd,Se};
     map(Sde,SdSe , (i,j) -> if
       (fromOrdinal Sde)i == sort flatten ((fromOrdinal SdSe)j)
            		    then 1_S else 0_S
	)
     )
*}
{*symmetricMultiplication = method(TypicalValue => Matrix)
symmetricMultiplication (LabeledModule,ZZ,ZZ) := (E,d,e) -> (
  S := ring E;
  Sd := symmetricPower(d,E);
  Se := symmetricPower(e,E);
  Sde := symmetricPower(d+e,E);
  SdSe := Sd ** Se;
  toMono := (F,l) -> multisetToMonomial(basisList((underlyingModules F)#0),l);
  map(Sde,SdSe, 
    (i,j) -> if toMono(Sde, fromOrdinal(i,Sde)) == toMono(SdSe, fromOrdinal(j,SdSe))
      then 1_S else 0_S))
*}
cauchyMap = method(TypicalValue => Matrix)
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
assert(basisList F == {0})
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
assert(exteriorPower(0,E) == labeledModule S^1)
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
assert(symmetricPower(0,E) == labeledModule S^1)
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
E = tensorFold {F1,F2,F3}
assert(rank E == product {rank F1, rank F2, rank F3})
assert(basisList E == sort basisList E)
assert((underlyingModules E)#0 == F1)
assert((underlyingModules E)#1 == F2)
assert((underlyingModules E)#2 == F3)
F = tensorFold {labeledModule S^1, F2}
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

matrix symmetricMultiplication(F,2,0) 
basisList symmetricPower(0,F)
///

-- test 5
TEST ///
S = ZZ/101[a,b,c];
F2 = labeledModule S^2;
F3 = labeledModule S^3;
F5 = labeledModule S^5;
F30 = tensorFold {F2,F3,F5}
assert(rank cauchyMap(2,F30) == 90)
F2' =  tensorFold {F2, labeledModule S^1}
assert(cauchyMap(1,F2') == id_(S^2))
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
