-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
-- Copyright 2011  Gregory G. Smith
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
  Date => "26 July 2011",
  Authors => {
    {
      Name => "Daniel Erman", 
      Email => "derman@math.stanford.edu", 
      HomePage => "http://math.stanford.edu/~derman/"},
    {	 
      Name => "David Eisenbud", 
      Email => "de@msri.org", 
      HomePage => "http://www.msri.org/~de/"},	     
    {
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "http://www.mast.queensu.ca/~ggsmith"}},
  Headline => "multilinear algebra with labelled bases",
  DebuggingMode => false
  )

export {
  "LabelledModule",
  "labelledModule",
  "underlyingModules",
  "basisList",
  "fromOrdinal",
  "toOrdinal",
  "multiSubsets"
  }

--------------------------------------------------------------------------------
-- CODE
--------------------------------------------------------------------------------
-- constructing explicit modules
LabelledModule = new Type of HashTable
LabelledModule.synonym = "free module with labelled basis"

labelledModule = method(TypicalValue => LabelledModule)
labelledModule Module := F -> (
  if not isFreeModule F then error "expected a free module"
  else (
    L := apply(rank F, i -> {i});
    new LabelledModule from {
      symbol module => F,
      symbol underlyingModules => {F},
      symbol basisList => L,
      symbol cache => new CacheTable}))
labelledModule Ring := S -> (
  L := apply(1, i -> {i});
  new LabelledModule from {
    symbol module => S^1,
    symbol underlyingModules => {S^1},
    symbol basisList => L,
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
toOrdinal(List, LabelledModule) := (l, E) -> (
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
  else if d === 1 then E
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
  else if d === 1 then E
  else new LabelledModule from {
    symbol module => (ring E)^(binomial(rank E + d - 1, d)),
    symbol underlyingModules => {E},
    symbol basisList => multiSubsets(basisList E, d),
    symbol cache => new CacheTable})


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
assert(basisList E  == apply(4, i -> {i}))
assert(underlyingModules E == {S^4})
assert(module E == S^4)
assert(fromOrdinal(2,E) == {2})
assert(toOrdinal({1},E) == 1)
E = labelledModule S
assert(rank E == 1)
///

-- test 1
TEST ///
S = ZZ/101[a,b,c];
F = labelledModule S^4
E = exteriorPower(2,F)
assert(rank E == 6)
assert(#basisList E == 6)
assert(exteriorPower(0,E) == labelledModule S^1)
assert(exteriorPower(1,E) == E)
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
assert(toOrdinal({{0},{3}},E) == 6)
assert(fromOrdinal(7,E) == {{1},{3}})
assert(symmetricPower(0,E) == labelledModule S^1)
assert(symmetricPower(-1,E) == labelledModule S^0)
assert(symmetricPower(1,E) == E)
///

end
--------------------------------------------------------------------------------
-- SCRATCH SPACE
--------------------------------------------------------------------------------

restart
uninstallPackage "LabelledModules"
installPackage "LabelledModules"
check "LabelledModules"

productList = method(TypicalValue => List)
productList List := L -> (
  n := #L;
  if n === 0 then {}
  else if n === 1 then L
  else (
    flatten table(L#0,
    )
  )

productList' = method()
productList'(List):= L->(
     --takes a list of lists, and forms  list of  tuples of elements, in order
     --{0,0}, {0,1}, ... (that is, lexicographically).
     Pp := if #L == 0 then {}
     else if #L == 1 then apply(L#0, i->{i})
     else if #L == 2 then flatten (apply(L_0,i->apply(L_1, j->{i,j})))
     else (
	  P0 := productList' drop (L, -1);
	  P1 := last L;
	  Pp = (apply(P0,a->apply(P1,b->append(a,b))));
	  --the following line removes the outermost-but-one set of parens
	  splice(Pp/toSequence));
--     for i from 1 to #L-2 do Pp = flatten Pp;
     Pp)


L0 = {}
productList' L0
L1 = {toList(0..1)}
productList' L1
L2 = {toList(0..1),toList(0..2)}
productList' L2
bL makeTensorProduct{QQ^2}
L3 = {toList(0..1),toList(0..2),toList(0..2)}
P = productList' L3
#P
2*3*3
L4 = {toList(0..1),toList(0..2),toList(0..1),toList(0,1)}
productList' L4
productList' drop(L3,-1)
last L3
flatten(productList' drop(L3,-1), last L3, (i,j) -> {i} | {j})
flatten table(L2#0,L2#1, (i,j) -> {i} | {j})
flatten table(L2#0,L2#1, (i,j) -> {i} | {j})
