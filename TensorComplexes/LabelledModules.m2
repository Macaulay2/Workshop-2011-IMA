-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
-- Copyright 2011  Daniel Erman
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
  "LabelledModules",
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
  Headline => "multilinear algebra with labelled bases",
  DebuggingMode => true
  )

export {
  "LabelledModule",
  "labelledModule",
  "underlyingModules",
  "basisList",
  "fromOrdinal",
  "toOrdinal",
  "multiSubsets",
  "tensorFold",
  "symmetricMultiplication",
  "cauchyMap"
  }

--------------------------------------------------------------------------------
-- CODE
--------------------------------------------------------------------------------
-- constructing explicit modules
LabelledModule = new Type of HashTable
LabelledModule.synonym = "free module with labelled basis"

labelledModule = method(TypicalValue => LabelledModule)
labelledModule Module := M -> (
  if not isFreeModule M then error "expected a free module";
  L := apply(rank M, i -> i);
  new LabelledModule from {
    symbol module => M,
    symbol underlyingModules => {},
    symbol basisList => L,
    symbol cache => new CacheTable})
labelledModule Ring := S -> (
  new LabelledModule from {
    symbol module => S^1,
    symbol underlyingModules => {},
    symbol basisList => {0},
    symbol cache => new CacheTable})

net LabelledModule := E -> net module E
LabelledModule#{Standard,AfterPrint} = LabelledModule#{Standard,AfterNoPrint} = E -> (
  << endl;				  -- double space
  << concatenate(interpreterDepth:"o") << lineNumber << " : free ";
  << ring E << "-module with labelled basis" << endl;)

module LabelledModule := E -> E.module
ring LabelledModule := E -> ring module E
rank LabelledModule := E -> rank module E
underlyingModules = method(TypicalValue => List)
underlyingModules LabelledModule := E -> E.underlyingModules
basisList = method(TypicalValue => List)
basisList LabelledModule := E -> E.basisList
fromOrdinal = method(TypicalValue => List)
fromOrdinal(ZZ, LabelledModule) := (i, E) -> (basisList E)#i
toOrdinal = method(TypicalValue => ZZ)
toOrdinal(Thing, LabelledModule) := (l, E) -> (
  position(basisList E, j -> j === l))

LabelledModule == LabelledModule := (E,F) -> (
  module E === module F 
  and underlyingModules E === underlyingModules F
  and basisList E === basisList F)

exteriorPower (ZZ, LabelledModule) := options -> (d,E) -> (
  S := ring E;
  r := rank E;
  if d < 0 or d > r then labelledModule S^0
  else if d === 0 then labelledModule S^1
  else new LabelledModule from {
      symbol module => S^(binomial(rank E, d)),
      symbol underlyingModules => {E},
      symbol basisList => subsets(basisList E, d),
      symbol cache => new CacheTable})

tomultisubset = x -> apply(#x, i -> x#i - i)
multiSubsets = method(TypicalValue => List)
multiSubsets (ZZ,ZZ) := (n,d) -> apply(subsets(n+d-1,d), tomultisubset)
multiSubsets (List,ZZ) := (L,d) -> apply(multiSubsets(#L,d), i -> L_i)

symmetricPower (ZZ, LabelledModule) := (d,E) -> (
  S := ring E;
  if d < 0 then labelledModule S^0
  else if d === 0 then labelledModule S^1
  else new LabelledModule from {
    symbol module => (ring E)^(binomial(rank E + d - 1, d)),
    symbol underlyingModules => {E},
    symbol basisList => multiSubsets(basisList E, d),
    symbol cache => new CacheTable})

productList = L -> (
  n := #L;
  if n === 0 then {}
  else if n === 1 then apply(L#0, i -> {i})
  else if n === 2 then flatten table(L#0, L#1, (i,j) -> {i} | {j})
  else flatten table(productList drop(L,-1), last L, (i,j) -> i | {j}))

tensorFold = method(TypicalValue => LabelledModule)
tensorFold List := L -> (
  n := #L;
  if n < 1 then error "-- expected a nonempty list";
  S := ring L#0;
  if n === 0 then labelledModule S^0
  else (
    if any(L, l -> ring l =!= S) then error "-- expected modules over the same ring";
    new LabelledModule from {
      symbol module => S^(product apply(L, l -> rank l)),
      symbol underlyingModules => L,
      symbol basisList => productList apply(L, l -> basisList l),
      symbol cache => new CacheTable}))
LabelledModule ** LabelledModule := LabelledModule => (E,F) -> tensorFold {E,F}
tensor(LabelledModule,LabelledModule) := options -> (E,F) -> tensorFold {E,F}

map(LabelledModule,LabelledModule,Function) := Matrix => o -> (E,F,f) -> (
  map(module E, module F, f))
map(LabelledModule,LabelledModule,Matrix) := Matrix => o -> (E,F,f) -> (
  map(module E, module F, f))

trace LabelledModule := Matrix => E -> (
  S := ring E;
  T := E ** E;
  map(T, labelledModule S^1, (i,j) -> (
      I := fromOrdinal(i,T);
      if I_0 == I_1 then 1_S else 0_S)))

multisetToMonomial = (l,m) -> (
  seen := new MutableHashTable;
  scan(m, i -> if seen#?i then seen#i = seen#i +1 else seen#i = 1);
  apply(l, i -> if seen#?i then seen#i else 0))
monomialToMultiset = (l,e) -> flatten apply(#e, i -> toList(e#i:l#i))

symmetricMultiplication = method(TypicalValue => Matrix)
symmetricMultiplication (LabelledModule,ZZ,ZZ) := (E,d,e) -> (
  S := ring E;
  Sd := symmetricPower(d,E);
  Se := symmetricPower(e,E);
  Sde := symmetricPower(d+e,E);
  SdSe := Sd ** Se;
  toMono := (F,l) -> multisetToMonomial(basisList((underlyingModules F)#0),l);
  map(Sde,SdSe, 
    (i,j) -> if toMono(Sde, fromOrdinal(i,Sde)) == toMono(SdSe, fromOrdinal(j,SdSe))
      then 1_S else 0_S))

cauchyMap = method(TypicalValue => Matrix)
cauchyMap (ZZ, LabelledModule) := (b,E) -> (
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
  Key => LabelledModules,
  Headline => "multilinear algebra with labelled basis",
  "Blah, blah, blah.",
  }

-------------------------------------------------------------------------------- 
-- TEST
--------------------------------------------------------------------------------

-- test 0
TEST ///
S = ZZ/101[a,b,c];
E = labelledModule S^4
assert(basisList E  == apply(4, i -> i))
assert(underlyingModules E == {})
assert(module E == S^4)
assert(fromOrdinal(2,E) == 2)
assert(toOrdinal(1,E) == 1)
F = labelledModule S
assert(basisList F == {0})
assert(rank F == 1)
F' = labelledModule S^0
assert(basisList F' == {})
///

-- test 1
TEST ///
S = ZZ/101[a,b,c];
F = labelledModule S^4
E = exteriorPower(2,F)
assert(rank E == 6)
assert(#basisList E == 6)
assert(exteriorPower(0,E) == labelledModule S^1)
assert(basisList exteriorPower(1,E) == apply(basisList E, i -> {i}))
assert(exteriorPower(-1,E) == labelledModule S^0)
E' = exteriorPower(2,E)
assert(#basisList E' == 15)
assert(#multiSubsets(basisList E,2) == binomial(6+2-1,2))
assert(#multiSubsets({0,1,2},2) == binomial(3+2-1,2))
///

-- test 2
TEST ///
S = ZZ/101[a,b,c];
F = labelledModule S^4
E = symmetricPower(2,F)
assert(#basisList E == binomial(4+2-1,2))
assert(toOrdinal({0,3},E) == 6)
assert(fromOrdinal(7,E) == {1,3})
assert(symmetricPower(0,E) == labelledModule S^1)
assert(symmetricPower(-1,E) == labelledModule S^0)
assert(basisList symmetricPower(1,E) == apply(basisList E, i -> {i}))
///

-- test 3
TEST ///
S = ZZ/101[a,b,c];
F1 = labelledModule S^2
F2 = labelledModule S^3
F3 = labelledModule S^5
assert(tensor(F1,F2) == F1 ** F2)
E = tensorFold {F1,F2,F3}
assert(rank E == product {rank F1, rank F2, rank F3})
assert(basisList E == sort basisList E)
assert((underlyingModules E)#0 == F1)
assert((underlyingModules E)#1 == F2)
assert((underlyingModules E)#2 == F3)
F = tensorFold {labelledModule S^1, F2}
assert(F != F2)
assert((underlyingModules F)#0 == labelledModule S^1)
assert((underlyingModules F)#1 == F2)
assert(toOrdinal({0,1}, F) == 1)
assert(fromOrdinal(5,E) == {0,1,0})
///

-- test 4
TEST ///
S = ZZ/101[a,b,c];
F = labelledModule S^2
assert(symmetricMultiplication(F,1,1) == matrix{{1_S,0,0,0},{0,1,1,0},{0,0,0,1}})
assert(symmetricMultiplication(F,2,1) == 0)
///

-- test 5
TEST ///
S = ZZ/101[a,b,c];
F2 = labelledModule S^2;
F3 = labelledModule S^3;
F5 = labelledModule S^5;
F30 = tensorFold {F2,F3,F5}
assert(rank cauchyMap(2,F30) == 90)
F2' =  tensorFold {F2, labelledModule S^1}
assert(cauchyMap(1,F2') == id_(S^2))
///

end
--------------------------------------------------------------------------------
-- SCRATCH SPACE
--------------------------------------------------------------------------------

restart
uninstallPackage "LabelledModules"
installPackage "LabelledModules"
check "LabelledModules"



