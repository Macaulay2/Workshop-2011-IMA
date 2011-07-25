newPackage ("EnumeratedSets", DebuggingMode => true)

ithsubset0 = (i,n,p) -> (
     -- i-th subset of cardinality p in a set of cardinality n
     if p === 0 then return ();
     if p === 1 then return 1:i;
     m := 0;
     for j from p-1 do (
	  k := binomial(j,p-1);
	  if k > i-m then return (ithsubset0(i-m,j,p-1),j);
	  m = m+k;
	  ))
ithsubset1 = x -> toList deepSplice ithsubset0 x
indexofsubset0 = (n,x) -> (
     -- index of x in the list of subsets of its cardinality in a set of cardinality n
     p := #x;
     if p === 0 then return 0;
     if p === 1 then return x#0;
     j := x#-1;
     x' := drop(x,-1);
     sum(p-1 .. j-1, j -> binomial(j,p-1)) + indexofsubset0(j,x'))
frommultisubset = x -> apply(#x, i -> x#i + i)
tomultisubset   = x -> apply(#x, i -> x#i - i)

export "subset"
subset = method()
subset(ZZ,ZZ,ZZ) := (i,n,p) -> (
     -- i-th subset of cardinality p in a set of cardinality n
     if n < 0 or p < 0 or i < 0 or i >= binomial(n,p) then error "arguments out of range";
     ithsubset1(i,n,p))

export "subsetIndex"
subsetIndex = method()
subsetIndex(ZZ,List) := (n,x) -> (
     -- index of x in the list of subsets of its cardinality in a set of cardinality n
     if #x > n
     or not all(x, i -> instance(i,ZZ))
     or not all(x, i -> 0 <= i and i < n)
     or not all(#x-1, i -> x#i < x#(i+1))
     then error("expected a (sorted) subset of 0..",toString(n-1));
     indexofsubset0(n,x))

export "multiSubset"
multiSubset = method()
multiSubset(ZZ,ZZ,ZZ) := (i,n,p) -> (
     -- i-th multi-subset of cardinality p in a set of cardinality n
     if n < 0 or p < 0 or i < 0 or i >= binomial(n+p-1,p) then error "arguments out of range";
     tomultisubset ithsubset1(i,n+p-1,p))

export "multiSubsetIndex"
multiSubsetIndex = method()
multiSubsetIndex(ZZ,List) := (n,x) -> (
     -- index of x in the list of multi-subsets of its cardinality in a set of cardinality n
     if not all(x, i -> instance(i,ZZ))
     or not all(x, i -> 0 <= i and i < n)
     or not all(#x-1, i -> x#i <= x#(i+1))
     then error("expected a (sorted) multi-subset of 0..",toString(n-1));
     indexofsubset0(n,frommultisubset x))

export "multiSubsets",
multiSubsets = method()     --(ordered) d element subsets allowing repetition
multiSubsets(ZZ,ZZ) := (n,p) -> apply(subsets(n+p-1,p), tomultisubset)
multiSubsets(List,ZZ) := (L,p) -> apply(multiSubsets(#L,p), x-> L_x)

export "EnumeratedSet"
EnumeratedSet = new Type of HashTable
                --   size => ZZ (later on, we might allow infinity here)
		--   isLabel => Function
		--   toLabel => Function
		--   fromLabel => Function
		--   elements => Function
protect symbol toElement
export "toElement"
net EnumeratedSet := L -> concatenate("<<an enumerated set of size ",toString L.size,">>")

export "enumeratedSet"
enumeratedSet = method(TypicalValue => EnumeratedSet)
enumeratedSet List := elems -> (
     n := #elems;
     elems' := new HashTable from apply(n, i -> elems#i => i);
     if #elems' < n then error "expected elements to be distinct";
     new EnumeratedSet from {
	  symbol size => n,
	  symbol isElement => x -> elems'#?x,
	  symbol toElement => i -> (
	       if i < 0 or i >= n then error ("index out of range 0 ..< ", toString n);
	       elems#i),
	  symbol index => x -> ( if not elems'#?x then error "expected an element"; elems'#x ),
	  symbol elements => () -> elems
	  }
     )
size EnumeratedSet := L -> L.size
size Set := x -> #x
-- set is not a method function, sigh:
-- set EnumeratedSet := L -> set elements L
EnumeratedSet _ ZZ := (L,i) -> L.toElement i
index(Thing,EnumeratedSet) := (x,L) -> L.index x
EnumeratedSet == EnumeratedSet := (L,M) -> size L === size M and (
     for i to size L - 1 do if L_i =!= M_i then return false;
     true)

export "isElement"
isElement = method(TypicalValue => Boolean)
isElement(Thing,EnumeratedSet) := (x,L) -> L.isElement x
elements EnumeratedSet := L -> L.elements ()
subsets(ZZ,EnumeratedSet) := EnumeratedSet => (p,L) -> (
     numL := size L;
     num := binomial(numL, p);
     new EnumeratedSet from {
	  symbol size => num,
	  symbol isElement => x -> instance(x,List) and #x === p and (
	       i := -1;
	       for t in x do (
		    if not isElement(t,L) then return false;
		    j := index(t,L);
		    if not (i < j) then return false;
		    i = j;
		    );
	       true),
	  symbol toElement => i -> (
	       if i < 0 or i >= num then error ("index out of range 0 ..< ", toString num);
     	       apply(subset(i,numL,p),j -> L_j)),
	  symbol index => x -> (
	       if not instance(x,List) or not ( #x === p ) then error "expected an element";
	       i := -1;
	       subsetIndex(numL,
		    for t in x list (
			 if not isElement(t,L) then error "expected an element";
			 j := index(t,L);
			 if not (i < j) then error "expected an element";
			 i = j
			 ))),
	  symbol elements => () -> (
	       e := elements L;
	       apply(subsets(numL,p), J -> e_J))
	  }
     )
multiSubsets(ZZ,EnumeratedSet) := EnumeratedSet => (p,L) -> (
     numL := size L;
     num := binomial(numL+p-1, p);
     new EnumeratedSet from {
	  symbol size => num,
	  symbol isElement => x -> instance(x,List) and #x === p and (
	       i := -1;
	       for t in x do (
		    if not isElement(t,L) then return false;
		    j := index(t,L);
		    if not (i <= j) then return false;
		    i = j;
		    );
	       true),
	  symbol toElement => i -> (
	       if i < 0 or i >= num then error ("index out of range 0 ..< ", toString num);
     	       apply(multiSubset(i,numL,p),j -> L_j)),
	  symbol index => x -> (
	       if not instance(x,List) or not ( #x === p ) then error "expected an element";
	       i := -1;
	       multiSubsetIndex(numL,
		    for t in x list (
			 if not isElement(t,L) then error "expected an element";
			 j := index(t,L);
			 if not (i <= j) then error "expected an element";
			 i = j
			 ))),
	  symbol elements => () -> (
	       e := elements L;
	       apply(multiSubsets(numL,p), J -> e_J))
	  }
     )
EnumeratedSet.directSum = x -> (
     num := #x;
     sizes := size \ x;
     sizesums := accumulate(plus, 0, prepend(0,sizes));
     sumsize := last sizesums;
     isElement' := t -> instance(t,Sequence) and #t === 2 and instance(t#0,ZZ) and 0 <= t#0 and t#0 < num and isElement(t#1,x#(t#0));
     new EnumeratedSet from {
	  symbol size => sumsize,
	  symbol isElement => isElement',
	  symbol toElement => i -> (
	       if i < 0 or i >= sumsize then error ("index out of range 0 ..< ", toString (sumsize-1));
     	       m := for j from 1 do if i < sizesums#j then break j-1;
	       (m,x#m.toElement(i-sizesums#m))),
	  symbol index => t -> (
	       if not isElement' t then error "expected an element";
	       index(t#1,x#(t#0)) + sizesums#(t#0)),
	  symbol elements => () -> flatten apply(num, j -> apply(elements x#j, t -> (j,t)))
	  }
     )
EnumeratedSet ++ EnumeratedSet := directSum

export "tensorProduct"
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
EnumeratedSet ** EnumeratedSet := tensorProduct
EnumeratedSet.tensorProduct = T -> (
     num := #T;
     sizes := size \ T;
     sizeprods := reverse accumulate(times, 1, prepend(1,drop(reverse sizes,-1)));
     prodsize := times sizes;
     isElement' := x -> instance(x,Sequence) and #x === num and all(num,i -> isElement(x#i,T#i));
     new EnumeratedSet from {
	  symbol size => prodsize,
	  symbol isElement => isElement',
	  symbol toElement => toEl := i -> (
	       if i < 0 or i >= prodsize then error ("index out of range 0 ..< ", toString prodsize);
	       apply(0 ..< num, j -> T#j _ (i // sizeprods#j % sizes#j))),
	  symbol index => x -> (
	       if not isElement' x then error "expected an element";
	       product apply(sizeprods,apply(num, i -> index(x#i,T#i)))),
	  symbol elements => () -> apply(prodsize, toEl)
	  }
     )

oldTensorProduct := lookup(symbol **, Module , Module )
if not match("/modules2.m2",first locate lookup(symbol **, Module , Module )) then error "EnumeratedSets cannot be reloaded"
Module.tensorProduct = X -> (
     if #X === 0 then error "tensor product expected at least one factor";
     M := fold(oldTensorProduct, X);
     if all(X,isFreeModule) then (
     	  E := tensorProduct (enumerate \ X);
	  if #X > 1 then enumerate(E,M);
	  );
     M)
Module ** Module := Module.tensorProduct

export "enumerate"
enumerate = method()
enumerate(EnumeratedSet,Module) := EnumeratedSet => (X,M) -> (
     M = cover M;
     if size X =!= numgens M then error("expected module to have ",toString size X, " generators");
     if M.cache.?enumerate then error "generators of module already have an enumeration";
     M.cache.enumerate = X)
enumerate Module := Module => (M) -> (
     M = cover M;
     if M.cache.?enumerate then M.cache.enumerate
     else M.cache.enumerate = enumerate(enumeratedSet toList ( 0 ..< numgens M ), M))

oldExteriorPower = lookup(exteriorPower, ZZ, Module)
if not match("/multilin.m2",first locate oldExteriorPower) then error "EnumeratedSets cannot be reloaded"
exteriorPower(ZZ, Module) := opts -> (p,M) -> (
     N := (oldExteriorPower opts)(p,M);
     enumerate(subsets(p,enumerate M), N);
     N)

oldSymmetricPower = lookup(symmetricPower, ZZ, Module)
symmetricPower(ZZ, Module) := (p,M) -> (
     N := oldSymmetricPower(p,M);
     enumerate(multiSubsets(p,enumerate M), N);
     N)

export "basisLabels"
basisLabels = method()
basisLabels Module := M -> elements enumerate M

TEST ///
      assert( ((L = enumeratedSet {a,b,c,d};)) === null )
      assert( (elements L) === {a,b,c,d} )
      assert( (size L) === 4 )
      assert( (apply(size L, i -> L_i)) === {a,b,c,d} )
      assert( (apply(elements L, x -> isElement(x,L))) === {true,true,true,true} )
      assert( ((M = enumeratedSet {e,f,g};)) === null )
      assert( (elements M) === {e,f,g} )
      assert( (size M) === 3 )
      assert( (apply(size M, i -> M_i)) === {e,f,g} )
      assert( (apply(elements M, x -> isElement(x,M))) === {true,true,true} )
      assert( ((N = subsets(2,L);)) === null )
      assert( (elements N) === {{a,b},{a,c},{b,c},{a,d},{b,d},{c,d}} )
      assert( (size N) === 6 )
      assert( (apply(size N, i -> N_i)) === {{a,b},{a,c},{b,c},{a,d},{b,d},{c,d}} )
      assert( (apply(elements N, x -> isElement(x,N))) === {true,true,true,true,true,true} )
      assert( ((P = L ++ M;)) === null )
      assert( (elements P) === {(0,a),(0,b),(0,c),(0,d),(1,e),(1,f),(1,g)} )
      assert( (size P) === 7 )
      assert( (apply(size P, i -> P_i)) === {(0,a),(0,b),(0,c),(0,d),(1,e),(1,f),(1,g)} )
      assert( (apply(elements P, x -> isElement(x,P))) === {true,true,true,true,true,true,true} )
      assert( ((Q = L ** M;)) === null )
      assert( (elements Q) === {(a,e),(a,f),(a,g),(b,e),(b,f),(b,g),(c,e),(c,f),(c,g),(d,e),(d,f),(d,g)} )
      assert( (size Q) === 12 )
      assert( (apply(size Q, i -> Q_i)) === {(a,e),(a,f),(a,g),(b,e),(b,f),(b,g),(c,e),(c,f),(c,g),(d,e),(d,f),(d,g)} )
      assert( (apply(elements Q, x -> isElement(x,Q))) === {true,true,true,true,true,true,true,true,true,true,true,true} )
      assert( ((Q = tensorProduct(L,M,M);)) === null )
      assert( (elements Q) === {(a,e,e),(a,e,f),(a,e,g),(a,f,e),(a,f,f),(a,f,g),(a,g,e),(a,g,f),(a,g,g),(b,e,e),(b,e,f),(b,e,g),(b,f,e),(b,f,f),(b,f,g),(b,g,e),(b,g,f),(b,g,g),(c,e,e),(c,e,f),(c,e,g),(c,f,e),(c,f,f),(c,f,g),(c,g,e),(c,g,f),(c,g,g),(d,e,e),(d,e,f),(d,e,g),(d,f,e),(d,f,f),(d,f,g),(d,g,e),(d,g,f),(d,g,g)} )
      assert( (size Q) === 36 )
      assert( (apply(size Q, i -> Q_i)) === {(a,e,e),(a,e,f),(a,e,g),(a,f,e),(a,f,f),(a,f,g),(a,g,e),(a,g,f),(a,g,g),(b,e,e),(b,e,f),(b,e,g),(b,f,e),(b,f,f),(b,f,g),(b,g,e),(b,g,f),(b,g,g),(c,e,e),(c,e,f),(c,e,g),(c,f,e),(c,f,f),(c,f,g),(c,g,e),(c,g,f),(c,g,g),(d,e,e),(d,e,f),(d,e,g),(d,f,e),(d,f,f),(d,f,g),(d,g,e),(d,g,f),(d,g,g)} )
      assert( (apply(elements Q, x -> isElement(x,Q))) === {true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true} )
      assert( ((R = multiSubsets(2,L);)) === null )
      assert( (elements R) === {{a,a},{a,b},{b,b},{a,c},{b,c},{c,c},{a,d},{b,d},{c,d},{d,d}} )
      assert( (size R) === 10 )
      assert( (apply(size R, i -> R_i)) === {{a,a},{a,b},{b,b},{a,c},{b,c},{c,c},{a,d},{b,d},{c,d},{d,d}} )
      assert( (apply(elements R, x -> isElement(x,R))) === {true,true,true,true,true,true,true,true,true,true} )
      assert( (E = QQ^3) === QQ^3 )
      assert( (F = QQ^4) === QQ^4 )
      assert( ((enumerate(L,F);)) === null )
      assert( (basisLabels ( E ** F )) === {(0,a),(0,b),(0,c),(0,d),(1,a),(1,b),(1,c),(1,d),(2,a),(2,b),(2,c),(2,d)} )
      assert( (G = exteriorPower_2 F) === QQ^6 )
      assert( (basisLabels G) === {{a,b},{a,c},{b,c},{a,d},{b,d},{c,d}} )
      assert( (G' = exteriorPower_2 QQ^4) === QQ^6 )
      assert( (basisLabels G') === {{0,1},{0,2},{1,2},{0,3},{1,3},{2,3}} )
      assert( (H = symmetricPower_2 F) === QQ^10 )
      assert( (basisLabels H) === {{a,a},{a,b},{b,b},{a,c},{b,c},{c,c},{a,d},{b,d},{c,d},{d,d}} )
      assert( (H' = symmetricPower_2 QQ^4) === QQ^10 )
      assert( (basisLabels H') === {{0,0},{0,1},{1,1},{0,2},{1,2},{2,2},{0,3},{1,3},{2,3},{3,3}} )
///

end

generateAssertions ///
(L = enumeratedSet {a,b,c,d};)
elements L
size L
apply(size L, i -> L_i)
apply(elements L, x -> isElement(x,L))
(M = enumeratedSet {e,f,g};)
elements M
size M
apply(size M, i -> M_i)
apply(elements M, x -> isElement(x,M))
(N = subsets(2,L);)
elements N
size N
apply(size N, i -> N_i)
apply(elements N, x -> isElement(x,N))
(P = L ++ M;)
elements P
size P
apply(size P, i -> P_i)
apply(elements P, x -> isElement(x,P))
(Q = L ** M;)
elements Q
size Q
apply(size Q, i -> Q_i)
apply(elements Q, x -> isElement(x,Q))
(Q = tensorProduct(L,M,M);)
elements Q
size Q
apply(size Q, i -> Q_i)
apply(elements Q, x -> isElement(x,Q))
(R = multiSubsets(2,L);)
elements R
size R
apply(size R, i -> R_i)
apply(elements R, x -> isElement(x,R))
E = QQ^3
F = QQ^4
(enumerate(L,F);)
basisLabels ( E ** F )
G = exteriorPower_2 F
basisLabels G
G' = exteriorPower_2 QQ^4
basisLabels G'
H = symmetricPower_2 F
basisLabels H
H' = symmetricPower_2 QQ^4
basisLabels H'
///
