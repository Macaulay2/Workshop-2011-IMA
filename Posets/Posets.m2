-- Copyright 2011: David Cook II, Sonja Mapes, Gwyn Whieldon
-- You may redistribute this file under the terms of the GNU General Public
-- License Version 2 as published by the Free Software Foundation.

------------------------------------------
-- Header 
------------------------------------------

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    )

newPackage select((
    "Posets",
        Version => "1.0.1", 
        Date => "01. August 2011",
        Authors => {
            {Name => "Sonja Mapes", Email => "smapes@math.duke.edu", HomePage => "http://www.math.duke.edu/~smapes/"},
            {Name => "Gwyn Whieldon", Email => "whieldon@math.cornell.edu", HomePage => "http://www.math.cornell.edu/People/Grads/whieldon.html"},
            {Name => "David Cook II", Email => "dcook@ms.uky.edu", HomePage => "http://www.ms.uky.edu/~dcook/"}
        },
        Headline => "Package for processing posets and order complexes",
        DebuggingMode => true,
        if version#"VERSION" > "1.4" then PackageExports => {"SimplicialComplexes", "Graphs"}
        ), x -> x =!= null)

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    )

export {
    --
    -- Data type & constructor
    "Poset",
        "GroundSet",
        "RelationMatrix",
        "Relations",
    "poset",
    "transitiveClosure",
    --
    -- Derivative combinatorial structures
    "comparabilityGraph",
    "hasseDiagram",
    "incomparabilityGraph",
    "orderComplex",
        "VariableName",
    --
    -- Derivative posets
    "closedInterval",
    "dualPoset",
    "filter",
    "flagPoset",
    "openInterval",
    "orderIdeal",
    "subPoset",
    --
    -- Operations
    "adjoinMax",
    "adjoinMin",
    "augmentPoset",
    "dropElements",
    "mergePoset",
    "posetDiamondProduct",
    "posetProduct",
    --
    -- Enumerators
    "divisorPoset",
    "facePoset",
    "intersectionLattice",
    "lcmLattice",
    "partitionLattice",
        "setPartition",
    "projectivizeArrangement",
    --
    -- TeX
    "displayPoset",
    "outputTexPoset",
    "texPoset",
        "SuppressLabels",
        "PDFViewer",
    --
    -- Vertices & vertex properties
    "atoms",
    "compare",
    "joinExists",
    "maximalElements",
    "meetExists",
    "meetIrreducibles",
    "minimalElements",
    "posetJoin",
    "posetMeet",
    "rankPoset",
        "Ranking",
    --
    -- Relations & relation properties
    "allRelations",
    "antichains",
    "coveringRelations",
    "flagChains",
    "isAntichain",
    "maximalChains",
    --
    -- Enumerative invariants
    "fvector",
    "moebiusFunction",
    --
    -- Properties
  --"height", -- exported by Core
    "isAtomic",
    "isBounded",
    "isConnected",
    "isDistributive",
    "isEulerian",
    "isGraded",
    "isLattice",
    "isRanked"
    }

------------------------------------------
-- Non-exported, strongly prevalent functions
------------------------------------------
indexElement := (P,A) -> position(P.GroundSet, i -> i === A);

------------------------------------------
-- Data type & constructor
------------------------------------------
Poset = new Type of HashTable

poset = method()
poset(List,List,Matrix) := (I,C,M) -> (
    if rank M =!= #I then error("Antisymmetry fails");
    new Poset from {
        symbol GroundSet => I,
        symbol Relations => C,
        symbol RelationMatrix => M,
        symbol cache => new CacheTable
        })
poset (List,List) := (I, C) -> poset(I, C, transitiveClosure(I, C))
poset List := C -> poset(unique flatten C, C);

--input: (I,C).  I=List of vertices.  C=List of pairs (edges)
--output: matrix where 1 in (i,j) position where i <= j, 0 otherwise
transitiveClosure = method()
transitiveClosure (List,List) := (I, C) -> (
     idx := hashTable apply(#I, i-> I_i => i);
     G := floydWarshall digraph hashTable apply(I, v -> idx#v => set apply(select(C, e -> e_0 === v),e -> idx#(e_1)));
     matrix apply(I, u -> apply(I, v -> if G#(idx#u, idx#v) < 1/0. then 1 else 0))
     )

------------------------------------------
-- Derivative combinatorial structures
------------------------------------------

comparabilityGraph = method()
comparabilityGraph Poset := P -> (
    E := flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list
        if P.RelationMatrix_i_j == 1 or P.RelationMatrix_j_i == 1 then {P.GroundSet_i, P.GroundSet_j} else continue;
    fE := unique flatten E;
    graph(E, Singletons => select(P.GroundSet, p -> not member(p, fE)))
    )

hasseDiagram = method()
hasseDiagram Poset := P -> (
    cr := coveringRelations P;
    digraph hashTable apply(P.GroundSet, v -> v => set apply(select(cr, e -> e_0 === v), e -> e_1))
    )

incomparabilityGraph = method()
incomparabilityGraph Poset := P -> (
    E := flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list
        if P.RelationMatrix_i_j == 0 and P.RelationMatrix_j_i == 0 then {P.GroundSet_i, P.GroundSet_j} else continue;
    fE := unique flatten E;
    graph(E, Singletons => select(P.GroundSet, p -> not member(p, fE)))
    )

orderComplex = method(Options => { symbol VariableName => getSymbol "v", symbol CoefficientRing => QQ })
orderComplex (Poset) := opts -> (P) -> (
    s := opts.VariableName;
    R := (opts.CoefficientRing)(monoid [s_0..s_(#P.GroundSet - 1)]);
    variableMap := hashTable apply(#P.GroundSet, i -> P.GroundSet#i => R_i);
    simplicialComplex apply(maximalChains P, c -> product apply(c, x -> variableMap#x))
    )

------------------------------------------
-- Derivative posets
------------------------------------------

-- input:  poset, and two elements
-- output:  the induced poset with minimal element and maximal element corresponding to the 2 given elements
closedInterval = method()
closedInterval (Poset, Thing, Thing) := (P, elt1, elt2) ->(
    if compare(P, elt1, elt2) then subPoset(P, select(P.GroundSet, elt -> compare(P, elt1, elt) and compare(P, elt, elt2)))
    else if compare(P, elt2, elt1) then subPoset(P, select(P.GroundSet, elt -> compare(P, elt2, elt) and compare(P, elt, elt1)))
    else error "these elements are uncomparable"
    )

dualPoset = method()
dualPoset Poset := P -> poset(P.GroundSet, P.Relations/reverse)

-- input: a poset, and an element from I
-- output:  the filter of a, i.e. all elements in the poset that are <= a
filter = method()
filter (Poset, Thing) := (P, a) -> P.GroundSet_(positions(first entries(P.RelationMatrix^{indexElement(P, a)}), i -> i != 0))

flagPoset = method()
flagPoset (Poset, List) := (P, L)-> subPoset(P, flatten ((rankPoset P)_L))

-- input: poset and two elements
-- output: the induced poset coming from the poset with minimal element and maximal element corresponding to the 2 given elements with these 2 elements removed 
openInterval = method()
openInterval (Poset, Thing, Thing) := (P, elt1, elt2) -> dropElements(closedInterval(P, elt1, elt2), {elt1, elt2})

-- input: a poset, and an element from I
-- output: the order ideal of a, i.e. all elements in the poset that are >= a
orderIdeal = method()
orderIdeal (Poset, Thing) := (P, a) -> P.GroundSet_(positions(flatten entries(P.RelationMatrix_{indexElement(P, a)}), i -> i != 0))

-- inputs:  a poset P and a list L of elements from P to "keep"
-- outputs:  induced poset the list L
subPoset = method()
subPoset (Poset, List) := Poset => (P, L) -> dropElements(P, toList(set P.GroundSet - set L))

------------------------------------------
-- Operations
------------------------------------------
--inputs:  Poset P, Thing a
--outputs:  new Poset P' with a as label for max or min
adjoinMax = method()
adjoinMax (Poset,Thing):= (P,a)-> poset(P.GroundSet | {a}, P.Relations | apply(P.GroundSet, g-> {g,a}))
adjoinMax Poset := P -> adjoinMax(P, {1})

adjoinMin = method()
adjoinMin (Poset,Thing):= (P,a)-> poset(P.GroundSet | {a}, P.Relations | apply(P.GroundSet, g-> {a,g}))
adjoinMin Poset := P -> adjoinMin(P, {0})

augmentPoset = method()
augmentPoset (Poset, Thing, Thing) := (P, a, b) -> adjoinMin(adjoinMax(P, b), a)
augmentPoset Poset := P -> adjoinMin adjoinMax P

-- inputs:  poset P and a list L of elements to drop
-- outputs: P without L
dropElements = method()
dropElements (Poset, List) := (P, L) -> (
    keptIndices := select(toList(0..#P.GroundSet-1), i-> not member(P.GroundSet#i,L));
    newGroundSet := apply(keptIndices, i-> P.GroundSet#i);
    newRelationMatrix := P.RelationMatrix_keptIndices^keptIndices;
    newRelations := select(allRelations P, r -> not member(first r, L) and not member(last r, L));
    poset(newGroundSet, newRelations, newRelationMatrix)
    )
dropElements (Poset, Function) := (P, f) -> (
    keptIndices := select(toList(0..#P.GroundSet-1), i-> not f(P.GroundSet#i));
    newGroundSet := apply(keptIndices, i-> P.GroundSet#i);
    newRelationMatrix := P.RelationMatrix_keptIndices^keptIndices;
    newRelations := select(allRelations P, r -> not f(first r) and not f(last r));
    poset(newGroundSet, newRelations, newRelationMatrix)
    )

mergePoset = method()
mergePoset (Poset, Poset) := (P, Q) -> poset(unique join(P.GroundSet,Q.GroundSet), unique join(P.Relations,Q.Relations))

posetDiamondProduct = method()
posetDiamondProduct (Poset,Poset) := (P,Q)->(
    if isLattice P and isLattice Q then (
        P':=posetProduct(dropElements(P, minimalElements P),dropElements(Q, minimalElements Q));
        poset(prepend({first minimalElements P, first minimalElements Q}, P'.GroundSet), 
              join(apply(minimalElements P', p -> ({first minimalElements P, first minimalElements Q}, p)), P'.Relations))
    ) else error "P and Q must be lattices"
    )

posetProduct = method()
posetProduct (Poset,Poset) := (P,Q) -> 
    poset(flatten for p in P.GroundSet list for q in Q.GroundSet list {p, q},
          join(flatten for c in P.Relations list for q in Q.GroundSet list ({c_0, q}, {c_1, q}),
           flatten for c in Q.Relations list for p in P.GroundSet list ({p, c_0}, {p, c_1})))

------------------------------------------
-- Enumerators
------------------------------------------
-- input:  a monomial m (and an ideal I)
-- output: lattice of all monomials dividing m (and contained in I)
divisorPoset = method()
divisorPoset RingElement := Poset => m -> (
    allMultiDegreesLessThan := d -> (
        L := {{}};
        for i from 0 to #d - 1 do L = flatten apply(L, H -> apply(d#i + 1, i -> H | {i}));
        L
        );
    makeMonomialFromDegree := (R, d) -> product apply(numgens R, i-> R_i^(d#i));
    d := flatten exponents m;
    Ground := apply(allMultiDegreesLessThan d, e -> makeMonomialFromDegree(ring m, e));
    Rels :=  unique flatten apply (Ground, r-> apply(Ground, s-> if s % r == 0 then (r,s)));
    Rels = select(Rels, r -> r =!= null);
    RelsMatrix :=  matrix apply (Ground, r-> apply(Ground, s-> if s%r == 0 then 1 else 0));
    poset (Ground, Rels, RelsMatrix)
    )

divisorPoset ZZ := Poset => m -> (
    if m < 0 then ( print "Did you mean |m|?"; m=-m; );
    M := toList \ toList factor m;
    p := local p;
    Pset := apply(#M, i-> p_i);
    R := QQ[Pset];
    numHash := hashTable apply(#M, i-> R_i=>first M_i);
    P := product apply(#M, p-> R_p^(last M_p));
    subFunc := apply(pairs numHash, q-> q_0=>q_1);
    Q := divisorPoset P;
    G := sort apply(Q.GroundSet, g-> sub(g,subFunc));
    L := apply(Q.Relations, g-> {sub(first g, subFunc),sub(last g, subFunc)});
    poset(G,L)
    )

--This method takes a pair of monomials: first element should divide second.
divisorPoset (RingElement, RingElement):= Poset =>(m, n) -> (
    if ring m === ring n then (
        if n % m === sub(0, ring m) then (
            P := divisorPoset (n//m);
            poset(apply(P.GroundSet, v -> v * m), apply(P.Relations, r -> (m * first r, m * last r)), P.RelationMatrix)
            ) else error "First monomial does not divide second."
        ) else error "Monomials must be in same ring."
    )

--This method takes a pair of exponent vectors a,b and computes divisorPoset x^a,x^b
divisorPoset (List, List, PolynomialRing):= Poset => (m, n, R) -> (
    makeMonomialFromDegree := (R, d) -> product apply(numgens R, i-> R_i^(d#i));
    if #m === #n and #n === numgens R then divisorPoset(makeMonomialFromDegree(R, m), makeMonomialFromDegree(R, n))
    else error "Wrong number of variables in first or second entry."
    )

facePoset = method()
facePoset(SimplicialComplex):=Poset=>(D)->(
    testmax := L -> min apply(L, j->#j) > 1;
    faceset := apply(flatten apply(toList(0..dim D), i-> toList flatten entries faces(i, D)), r -> support r);
    chainheads := apply(flatten entries facets D, i-> support i);
    maxchains := apply(chainheads, i-> {i});
    while any(maxchains, testmax) do (
        nextstage:={};
        holdover:=select(maxchains,c-> not testmax c);
        for m in select(maxchains,testmax) do (
            minsize:=min apply(m, i-> #i);
            minset:=first select(m, i-> #i == minsize);
            coveredfaces:=subsets(minset,minsize-1);
            nextstage=join(nextstage,apply(coveredfaces, c->append(m,c)))
            );
        maxchains = join(nextstage,holdover);
        );    
    poset(faceset, unique flatten apply(maxchains, i-> apply(subsets(i,2),reverse)))
    )

-- Hyperplane Arrangement Lattice: 
-- As written, this would most likely work for any type of arrangement lattice.
-- Given a set of linear forms defining the hyperplanes in the arrangement, returns set of intersection ideals.

-- Inputs:
--      L = equations defining hyperplanes
--      R = ring
-- Outputs: List of ideals of intersections, excluding the intersection of no hyperplanes and intersections which are empty.
hyperplaneEquivalence = method()
hyperplaneEquivalence(List,Ring) := (L,R) -> (
    allideals:=unique drop(apply(subsets L, h-> ideal gens gb ideal h),1);
    select(allideals, I-> not I == ideal(sub(1,R)))
    )

-- Inputs:
--      L = list of ideals produced by method hyperplaneEquivalence
--      R = ring
-- Outputs: Pairs of ideals (I,J), with I < J if J contains I
hyperplaneInclusions = method()
hyperplaneInclusions(List,Ring) := (L,R) -> (
    H:=apply(L, l-> sub(l,R));
    coverPairs:={};
    for l from 1 to #H-1 do
        for k to #H-1 do 
            if unique apply(flatten entries gens H_k, f-> f % gens H_l) === {sub(0,R)} then 
                coverPairs = append(coverPairs,{L_k,H_l});
    coverPairs
    )

-- Inputs:
--      L = equations defining arrangement
--      R = ring
-- Outputs: Intersection poset of hyperplane arrangement.
-- In theory, this should work on arrangements of hypersurfaces.  In practice, throws an error saying "antisymmetry fails."
intersectionLattice = method()
intersectionLattice(List,Ring):=(L,R)-> (
    G:=hyperplaneEquivalence(L,R);
    rel:=hyperplaneInclusions(G,R);
    poset(G,rel)
    )

-- ***TODO*** Needs thorough cleaning.
-- input:  generators of a monomial ideal
-- output: lcm lattice of that monomial ideal
-- potential problem:  subsets dies when a set is too big (> 18)
lcmLattice = method( Options => { Strategy => 1 })
lcmLattice (Ideal) := Poset => opts -> (I) -> lcmLattice(monomialIdeal I, opts)
lcmLattice(MonomialIdeal) := Poset => opts -> (M) -> (
    L := flatten entries gens M;
    Ground := null;
    if opts.Strategy === 0 then (
        subsetsL := flatten apply(#L, i-> subsets (L,i+1));
        Ground = unique flatten apply (subsetsL, r-> lcm(r));
        Ground = prepend(1_(ring M), Ground);
        ) 
    else (
        Ground = lcmLatticeProduceGroundSet L;
        Ground = apply(Ground, D -> product apply(numgens ring M, i-> (ring M)_i^(D#i)));
        );
    Rels := select(unique flatten apply (Ground, r-> apply(Ground, s-> if s % r == 0 then (r,s))), i -> i =!= null);
    RelsMatrix :=  matrix apply (Ground, r-> apply(Ground, s-> if s%r == 0 then 1 else 0));
    poset (Ground, Rels, RelsMatrix)
    )

protect next
-- Makes a pair storing a multi-degree and a list of multi-degrees which are to be joined with this degree.
degreeNextPair = (D, nextDegrees) -> hashTable {symbol degree => D, symbol next => nextDegrees}

--Takes the lcm of two degrees and determines which 
--of the lowerNexts can later be joined to newDegree
--and change its multidegree. Note that the lower nexts are not
--all multi-degrees. They have already been chosen so that they 
--would not change the degrees of the first i variables where
--i appears in the for loop of lcmLatticeProduceGroundSet.
joinDegrees = (A,B, lowerNexts) ->  (
    C := lcmDegree {A.degree, B};
    nexts := select(lowerNexts, D -> not dividesDegree(D, C));
    degreeNextPair( C, nexts )
    )

--Checks if D divides E as multidegrees
dividesDegree = (D,E) -> all(E-D, i-> i >= 0)

--Takes the lcm of two multidegrees
lcmDegree = L -> apply(transpose L, l -> max l)

--Take a list of degreeNextPairs and drop duplicate degrees
uniqueMultiDegrees = L -> (
    P := partition(D -> (D.degree) , L);
    apply(keys P, d -> first P#d)
    )

--Builds the possible multidegrees by changes in variable i.
determineLCMsForVariable = (lcmDegrees, i) -> (
    VERBOSE := false;
    newLCMDegrees := flatten apply(lcmDegrees, D -> (
        if VERBOSE then << "Working on " << D.degree << endl << D.next << endl;
        -- Take D's nexts are partition them by the exponent 
        -- of the i-th variable. Store in P.
        P := partition(E -> E#i, D.next);
        -- Partition the possible degrees of the i-th variable
        -- into those that change multi-degree D in the i-th coordinate
        -- and those that don't. Store in Q.
        Q := partition(d -> d > (D.degree)#i, keys P);
        --Restrict P to only those which change the degree the i-th variable of D.
        upperPartition := hashTable apply(if Q#?true then Q#true else {}, d -> d => P#d);
        if VERBOSE then << "Upper Partition" << endl << upperPartition << endl;
        -- The lowerNexts are those multi degrees that can change D in
        -- the indices larger than i, but not in i itself.
        lowerNexts := flatten apply(if Q#?false then Q#false else {},  d -> P#d);
        newD := degreeNextPair( D.degree, lowerNexts ); -- D with fewer nexts
        newMultiDegrees := flatten apply(keys upperPartition, d -> (
            lowerNexts = lowerNexts | upperPartition#d; -- build these as we go
            apply(upperPartition#d, E -> joinDegrees(D,E,lowerNexts))
            )
        );
        {newD } | newMultiDegrees 
        )
    );
    newLCMDegrees = select(newLCMDegrees, D -> D =!= null);
    uniqueMultiDegrees newLCMDegrees
)

lcmLatticeProduceGroundSet = G -> (
    VERBOSE := false;
    initialExps := flatten apply(G, m -> exponents m);
    n := if #initialExps === 0 then 0 else #(first initialExps);
    lcmDegrees := { degreeNextPair(apply(n, i -> 0), initialExps) };
    for i from 0 to n-1 do (
        if VERBOSE then << "Variable " << i << endl;
--        if VERBOSE then printDegreeList L;
        -- lcmDegrees contains all possible multi-degrees restricted
        -- to the first i varibles. For each of these multi-degrees
        -- we have a list of "nexts" which are atoms which could
        -- affect degrees of variables after i without changing 
        -- the degrees of variables before i.
        lcmDegrees = determineLCMsForVariable(lcmDegrees, i);
    );
    sort apply(lcmDegrees, D -> D.degree)
    )

partitionLattice = method()
partitionLattice ZZ := n -> (
     L := toList (1..n);
     G := setPartition L;
     R := flatten apply(G, i-> partitionRefinementPairs i);
     poset(G,R)
     )

partitionRefinementPairs = method()
partitionRefinementPairs List := (L)-> (
    m := unique apply(L, l-> #l);
    M := local M;
    N := local N;
    MM := apply(m, i-> (symbol M)_i);
    NN := apply(m, i-> (symbol N)_i);
    for i in m do (
        subS := subsets toList(0..i-1);
        M_i = take(subS,{1,#subS-2});
        N_i = unique apply(M_i, r-> sort {r, select(toList(0..i-1), k-> not member(k,r))});
        );
    dropPart := apply(#L, i-> drop(L,{i,i}));
    coverSet := flatten for i from 0 to #L-1 list(
        splitPairs:=apply(N_(#L_i), m-> {(L_i)_(first m),(L_i)_(last m)});
        apply(splitPairs, j-> sort join(dropPart_i,j))
    );
    apply(coverSet, i -> {L,i})
    )

setPartition = method()
setPartition ZZ := n -> (
    L := {{{1}}};
    for i from 2 to n do (
        L = flatten for lambda in L list (
            lambdaparts := apply(#lambda, l-> for k to #lambda-1 list if k=!=l then lambda_k else continue);
            append(apply(#lambda, p-> lambdaparts_p | {lambda_p | {i}}), join(lambda,{{i}}))
            );
        );
    apply(L, sort)
    )
setPartition List := S -> (
    L := {{{first S}}};
    for s in drop(S,1) do (
        L = flatten for lambda in L list(
            dropPart := apply(#lambda, i-> drop(lambda,{i,i}));
            protoLevelSet := apply(#lambda, l-> join(dropPart_l,{lambda_l|{s}}));
            join(protoLevelSet, {lambda|{{s}}})
            );
        );
    apply(L,sort)
    )

-- Inputs:
--      L = equations defining (possibly nonprojective) arrangement
--      R = ring
-- Outputs: Intersection poset of projectivized hyperplane arrangement.
-- ***TODO***: Alternate method: Which is better?  Could also use "adjoinMax".
projectivizeArrangement = method()
projectivizeArrangement(List,Ring):=(L,R)->(
    Z := local Z;
    S := coefficientRing R[gens R|{(symbol Z)}];
    newL := apply(L, h->homogenize(sub(h,S),Z));
    G := hyperplaneEquivalence(newL,S);
    rel := hyperplaneInclusions(G,S);
    poset(G,rel)
    )

------------------------------------------
-- TeX
------------------------------------------

displayPoset=method(Options => { symbol SuppressLabels => true, symbol PDFViewer => "open" })
displayPoset(Poset):=opts->(P)->(
    if not instance(opts.PDFViewer, String) then error("Option PDFViewer must be a string.");
    name := temporaryFileName();
    outputTexPoset(P, concatenate(name, ".tex"), symbol SuppressLabels => opts.SuppressLabels);
    run concatenate("pdflatex -output-directory /tmp ", name, " 1>/dev/null");
    run concatenate(opts.PDFViewer, " ", name,".pdf");
    )

outputTexPoset = method(Options => {symbol SuppressLabels => true});
outputTexPoset(Poset,String):= opts -> (P,name)->(
    fn:=openOut name;
    fn << "\\documentclass[8pt]{article}"<< endl;
    fn << "\\usepackage{tikz}" << endl;
    fn << "\\begin{document}" << endl << endl;
    fn << texPoset(P, opts) << endl;
    fn << "\\end{document}" << endl;
    close fn;
    get name
    )

texPoset = method(Options => {symbol SuppressLabels => true})
texPoset (Poset) := opts -> (P) -> (
    C := maximalChains P;
    --hash table of variable labels:
    idx:= hashTable apply(#P.GroundSet, i-> P.GroundSet_i=> i);
    --edge list to be read into TikZ:
    edgelist:= apply(coveringRelations P, r-> concatenate(toString idx#(first r),"/",toString idx#(last r)));
    --height of poset:
    L := max apply(C, c-> #c) - 1;
    heightpairs := apply(P.GroundSet, g -> {g, L - max flatten apply(C, c-> positions(reverse c, i-> g === i))});
    protoH := partition(g-> last g, heightpairs);
    H := hashTable apply(keys protoH, k-> k=>apply(protoH#k, h-> first h));
    levelsets := apply(values H, v-> #v-1);
    scalew := min{1.5,15/ (1 + max levelsets)};
    scaleh := min{2/scalew,15/(L+1)};
    halflevelsets := apply(levelsets, j-> scalew*j/2.0);
    spacings := apply(toList(0..L), j-> scalew*toList(0..levelsets_j));
    -- The TeX String
    "\\begin{tikzpicture}[scale=1, vertices/.style={draw, fill=black, circle, inner sep=0pt}]\n" |
        concatenate(
            for i from 0 to L list for j from 0 to levelsets_i list
                {"\t\\node [vertices", if opts.SuppressLabels then "]" else (", label=right:{" | tex (values H)_i_j | "}]"),
                 " (",toString idx#((values H)_i_j),") at (-",toString halflevelsets_i,"+",
                 toString spacings_i_j,",",toString (scaleh*i),"){};\n"}
            ) |
    concatenate("\\foreach \\to/\\from in ", toString edgelist, "\n\\draw [-] (\\to)--(\\from);\n\\end{tikzpicture}\n")
    )

------------------------------------------
-- Vertices & vertex properties
------------------------------------------

-- input:  poset
-- output: list of elements covering minimal elements
atoms = method()
atoms Poset := List => P -> unique apply(select(coveringRelations P, R -> any(minimalElements P, elt -> (elt === R#0))), rels-> rels_1)

compare = method()
compare(Poset, Thing, Thing) := Boolean => (P,A,B) -> (
    Aindex := indexElement(P,A);
    Bindex := indexElement(P,B);
    P.RelationMatrix_Bindex_Aindex != 0
    )

joinExists = method()
joinExists (Poset,Thing,Thing) := (P,a,b) -> (
    OIa := filter(P, a);     
    OIb := filter(P, b);
    upperBounds := toList (set(OIa)*set(OIb));
    if upperBounds == {} then false else (
        M := P.RelationMatrix;
        heightUpperBounds := flatten apply(upperBounds, element-> sum entries M_{indexElement(P,element)});
        #(select(heightUpperBounds, i-> i == min heightUpperBounds)) <= 1
        )
    )

-- input: poset
-- output:  list of maximal elements
maximalElements = method()
maximalElements Poset := P -> (
    if P.cache.?maximalElements then return P.cache.maximalElements;
    L := select(#P.GroundSet, i -> all(#P.GroundSet, j -> P.RelationMatrix_(i,j) == 0 or i == j));
    P.cache.maximalElements = P.GroundSet_L
    )

meetExists = method()
meetExists (Poset, Thing, Thing) := (P,a,b) -> (
    Fa:= orderIdeal(P, a);
    Fb:= orderIdeal(P, b);
    lowerBounds:= toList (set(Fa)*set(Fb));
    if lowerBounds == {} then false else (
        M := P.RelationMatrix;
        heightLowerBounds := flatten apply(lowerBounds, element-> sum entries M_{indexElement(P,element)});
        #(select(heightLowerBounds, i-> i == max heightLowerBounds)) <= 1
        )
    )

-- input:  poset
-- output:  meet irreducibles of poset
meetIrreducibles = method()
meetIrreducibles Poset := P -> (
    -- want to compute meets only for non-comparable elements
    if not isLattice P then error "P is not a lattice";
    nonComparablePairs := select(subsets(P.GroundSet,2), posspair -> compare(P, posspair#0,posspair#1) == false and compare(P,posspair#1,posspair#0)== false);
    meets := select(unique flatten apply(nonComparablePairs, posspair -> if meetExists(P, posspair#0, posspair#1) == true then posetMeet(P,posspair#0, posspair#1)), i -> i =!= null); 
    toList (set P.GroundSet - set meets)
    )

-- input:  poset
-- output:  list of minimal elements
minimalElements = method()
minimalElements Poset := P -> (
    if P.cache.?minimalElements then return P.cache.minimalElements;
    L := select(#P.GroundSet, i -> all(#P.GroundSet, j -> P.RelationMatrix_(j,i) == 0 or i == j));
    P.cache.minimalElements = P.GroundSet_L
    )

posetJoin = method()     
posetJoin (Poset,Thing,Thing) := (P,a,b)  -> (
    OIa := filter(P, a);     
    OIb := filter(P, b);
    upperBounds := toList (set(OIa)*set(OIb));
    if upperBounds == {} then error "your elements do not share any upper bounds"
    else (
        M := P.RelationMatrix;
        heightUpperBounds := flatten apply(upperBounds, element-> sum entries M_{indexElement(P,element)});
        if #(select(heightUpperBounds, i-> i == min heightUpperBounds)) > 1 then error "join does not exist, least upper bound not unique" 
        else(upperBounds_{position (heightUpperBounds, l -> l == min heightUpperBounds)})
        )
    )

-- iputs:  P a poset, and 2 elements of P.GroundSet
--outputs:  the element in P.GroundSet that is the meet of these, or "not comparable" or "not unique"
-- usage:  MeetExits used in isLattice
posetMeet = method()
posetMeet (Poset,Thing,Thing) := (P,a,b) ->(
    Fa := orderIdeal(P,a);
    Fb := orderIdeal(P,b);
    lowerBounds:= toList (set(Fa)*set(Fb));
    if lowerBounds == {} then error "your elements do not share any lower bounds"
    else (
        M := P.RelationMatrix;
        heightLowerBounds := flatten apply(lowerBounds, element-> sum entries M_{indexElement(P,element)});
        if #(select(heightLowerBounds, i-> i == max heightLowerBounds)) > 1 then error "meet does not exist, greatest lower bound not unique" 
        else lowerBounds_{position (heightLowerBounds, l -> l == max heightLowerBounds)}
        )
    )

-- DC2: Working on as of 1452, 01. August 2011
-- Ranked:  There exists an integer ranking-function r on the groundset of P
--          such that for each x and y in P: if y covers x then r(y)-r(x) = 1.
rankPoset = method()
rankPoset Poset := P -> (
    if P.cache.?Ranking then return P.cache.Ranking;
    P.cache.Ranking = null
    )

------------------------------------------
-- Relations & relation properties
------------------------------------------

allRelations = method()
allRelations Poset := P -> flatten for i to numrows P.RelationMatrix - 1 list for j to numrows P.RelationMatrix - 1 list if P.RelationMatrix_i_j == 1 then {P.GroundSet#i, P.GroundSet#j} else continue

antichains = method()
antichains Poset := P -> (
    v := local v;
    R := (ZZ/2)(monoid [v_1..v_(#P.GroundSet)]);
    S := simplicialComplex monomialIdeal flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list if P.RelationMatrix_i_j == 1 or P.RelationMatrix_j_i == 1 then R_i * R_j else continue;
    apply(flatten apply(1 + dim S, d -> flatten entries faces(d, S)), a -> P.GroundSet_(indices a))
    )

coveringRelations = method()
coveringRelations Poset := P -> (
    if P.cache.?coveringRelations then return P.cache.coveringRelations;
    P.cache.coveringRelations = if #P.Relations === 0 then {} else (
        edgeset := flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list
            if P.RelationMatrix_i_j == 1 then {P.GroundSet_j, P.GroundSet_i} 
            else if P.RelationMatrix_j_i == 1 then {P.GroundSet_i, P.GroundSet_j} 
            else continue;
        testpairs:=flatten apply(edgeset, r-> apply(select(edgeset, s-> last r === first s), p-> {r,p}));
        nonCovers:=apply(testpairs, p-> {first first p, last last p});
        select(edgeset, p-> not member(p,nonCovers))
        )    
    )

flagChains = method()
flagChains (Poset,List) := (P,L) -> maximalChains flagPoset(P,L)

--input: P a poset and L a list of elements of the poset
--output: whether L is an antichain in P
isAntichain = method()
isAntichain (Poset, List) := (P, L) -> (
    Q := subPoset(P, L);
    minimalElements(Q) == maximalElements(Q)
    )

maximalChains = method()
maximalChains Poset := P -> (
    if P.cache.?maximalChains then return P.cache.maximalChains;
    nonMaximalChains := apply(minimalElements(P), x -> {x});
    maxChains := {};
    while #nonMaximalChains =!= 0 do (
        nonMaximalChains = flatten apply(nonMaximalChains, c -> (
                nexts := select(coveringRelations P, r -> first r === last c);
                if #nexts == 0 then maxChains = append(maxChains, c);
                apply(nexts, r -> c | {last r})
                )
            )
        );
    P.cache.maximalChains = maxChains
    )

------------------------------------------
-- Enumerative invariants
------------------------------------------

-- ***TODO*** Is this right?
fvector = method()
fvector Poset := P -> apply(rankPoset P, G -> #G)

moebiusFunction = method()
moebiusFunction Poset := HashTable => P -> ( 
    if #minimalElements P > 1 then error "this poset has more than one minimal element - specify an interval";
    M := (P.RelationMatrix)^(-1);
    k := position(P.GroundSet,v->v === (minimalElements P)_0);
    hashTable apply(#P.GroundSet,i->{P.GroundSet_i,M_(k,i)})
    )
moebiusFunction (Poset, Thing, Thing) := HashTable => (P, elt1, elt2) -> moebiusFunction(closedInterval(P,elt1,elt2))

------------------------------------------
-- Properties
------------------------------------------

-- Method given in Core
height Poset := Poset => P -> -1 + max apply (maximalChains P, s-> #s)

-- P is atomic if every non-minimal, non-atom element is greater than some atom
isAtomic = method()
isAtomic Poset := P -> (
    if P.cache.?isAtomic then return P.cache.isAtomic;
    atm := atoms P;
    P.cache.isAtomic = all(toList(set P.GroundSet - set minimalElements P - set atm), v -> any(atm, a -> compare(P, a, v)))
    )

isBounded = method()
isBounded Poset := P -> #minimalElements P == 1 and #maximalElements P == 1

isConnected = method()
isConnected Poset := P -> (
    if P.cache.?isConnected then return P.cache.isConnected;
    J := {};
    J' := first maximalChains P;
    while #J' != 0 do (
        J = J | J';
        J' = select(P.GroundSet, v -> not member(v, J) and any(P.Relations, r -> (v === first r and member(last r, J)) or (v === last r and member(first r, J))));
        );
    P.cache.isConnected = (#J == #P.GroundSet)
    )

isDistributive = method()
isDistributive (Poset) := P->(
    if P.cache.?isDistributive then return P.cache.isDistributive;
    if not isLattice P then error "Poset must be a lattice";
    P.cache.isDistributive = all(subsets(P.GroundSet, 3), G -> posetMeet(P, G_0, first posetJoin(P, G_1, G_2)) == posetJoin(P, first posetMeet(P, G_0, G_1), first posetMeet(P, G_0, G_2)))
    )

-- ***TODO*** Terribly inefficient--fix it!
isEulerian = method()
isEulerian Poset := Boolean => P -> (
    if P.cache.?isEulerian then return P.cache.isEulerian;
    if not isRanked P then error "Poset must be ranked.";
    P.cache.isEulerian = all(P.GroundSet, a -> 
        all(P.GroundSet, b -> (
                if compare(P, a, b) then (
                    ci := closedInterval(P, a, b);
                    (moebiusFunction ci)#b === (-1)^(height ci)
                    ) else true
                )
            )
        )
    )

-- Graded:  All maximal chains are the same length.
isGraded = method()
isGraded Poset := P -> (
    if P.cache.?isGraded then return P.cache.isGraded;
    P.cache.isGraded = #unique apply(maximalChains P, c -> #c) == 1
    )

--inputs: a poset P
--output:  boolean value for whether or not it is a lattice
isLattice = method()
isLattice Poset := P -> (
    if P.cache.?isLattice then return P.cache.isLattice;
    --P.cache.isLattice = all(P.GroundSet, a -> all(P.GroundSet, b -> joinExists(P, a, b) and meetExists(P, a, b)))
    P.cache.isLattice = all(0..#P.GroundSet-1, i -> all(i+1..#P.GroundSet-1, j -> joinExists(P, P.GroundSet#i, P.GroundSet#j) and meetExists(P, P.GroundSet#i, P.GroundSet#j)))
    )

-- Ranked:  There exists an integer ranking-function r on the groundset of P
--          such that for each x and y in P: if y covers x then r(y)-r(x) = 1.
isRanked = method()
isRanked Poset := P -> rankPoset P =!= null

------------------------------------------
-- Documentation
------------------------------------------

beginDocumentation()

---------
-- front page
---------
document { 
  Key => Posets,
  Headline => "a package for working with posets",
  PARA{},
  "The ", EM "Posets", " package defines Poset as a new data type and provides 
   routines which use or produce posets.  A poset or a partially ordered set 
   is a set together with a binary relation satisfying reflexivity, antisymmetry, and transitivity.",
  SUBSECTION "Contributors",
  "The following people have generously contributed code or worked on our code.",
  UL {
    {HREF("http://people.math.gatech.edu/~jyu67/Josephine_Yu/Main.html","Josephine Yu")},
    {HREF("http://www.math.purdue.edu/~nkummini/","Manoj Kumminni")},
    {HREF("http://www.math.cornell.edu/People/Grads/fisher.html","Kristine Fisher")},
    {HREF("http://www.mathstat.dal.ca/~handrew/","Andrew Hoefel")},
    {HREF("mailto:stephen.sturgeon@uky.edu", "Stephen Sturgeon")} 
    },
  }


--doc ///
--     Key
--           Posets
--     Headline
--          A package for working with posets. 
--     Description
--          Text
--           {\em Posets} package defines Poset as a new data type and provides 
--           routines which use or produce posets.   A poset or a partially ordered set is a set together with a binary relation satisfying reflexivity, antisymmetry, and transitivity.
--           Contributors
--           The following people have contributed code or have worked on this package.
--           {HREF("http://people.math.gatech.edu/~jyu67/Josephine_Yu/Main.html","Josephine Yu"")},     
           
--///
     
---------
-- types
----------           
doc ///
     Key
           Poset
     Headline
           a class for partially ordered sets (posets)
     Description
          Text
               This class is a type of HashTable which represents finite posets.  It consists of a ground 
               set, a set of sequences (a,b) representing relationships where a is less than or 
               equal to b, a matrix encoding these relations. 
      Example
          G = {a,b,c,d,e}; -- the ground set
          R = {(a,b),(b,c),(a,c),(a,d),(d,e)}; --a set of sequences representing relations that "generate" all other relations
          P = poset (G,R) -- the matrix encoding these relations is computed by calling this function       
     SeeAlso
          poset
          GroundSet
          Relations
          RelationMatrix       
///     

-------------
-- constructors
-------------

doc ///
     Key
           poset
      (poset, List, List)
      (poset, List, List, Matrix)
     Headline
           creating a poset
     Usage
       P = poset (G,R)
       P = poset (G,R,M)
     Inputs
      G : List 
           elements in the ground set of P
      R : List 
           sequences (a,b) which indicate that a is less than or equal to b
      M : Matrix
           with entries ij equal to one when the jth element in G is less than or equal to the ith element in G
     Outputs
      P : Poset
           a poset consisting of the elements in G, with the order relations determined by R 
           and or M
     Description
        Text
           This function allows one to create a poset by defining the set and giving the order relations between the elements in the set.
           The function assumes that each element in the defining list given is distinct, and operates by taking the transitive and reflexive 
            closure of the relations that it is given.  The function returns an error
            if the input relations are incompatible with creating a poset.
       Example
           G = {a,b,c,d};
            R = {(a,b), (a,c), (c,d)};
            P = poset (G,R)    
       Text
           Sometimes in finding "enough" relations one inadverdently finds all of the relations in the poset.  In this case, the user
        can bypass having the function poset calculate the transitive closure of the relations by entering the matrix encoding the
        relations in when calling the poset function.  In this scenario, the function does not check that the resulting object is 
        actually a poset because in order to do this, the function needs to compute the transitive closure of the relations and check
        that this matches the matrix given.  The purpose of entering a matrix is to bypass that computation.
       Example
           S = QQ[x,y,z];
        G = {x^2, x*y, z^2, x^2*y*z, x*y*z^3, x^2*y^2*z^3};
            R = select((flatten apply (G, g-> apply (G, h-> if h % g == 0 then (g,h)))), i -> i =!= null) -- finds all pairs where g divides h
        M = matrix apply (G, g-> apply (G, h-> if h % g == 0 then 1 else 0)) 
        P = poset(G,R,M) 
        
     SeeAlso
           Poset
      GroundSet
      Relations
      RelationMatrix
///
  
-----------
-- finding relations
-----------

doc ///
     Key
           transitiveClosure
      (transitiveClosure, List, List)
     Headline
           computes the transitive closure of a given set of relations.  
     Usage
           M = transitiveClosure(I,R)
     Inputs
      I : List
           ground set 
      R : List
           of pairs of elements in the ground set I.
     Outputs
      M : Matrix 
           whose (i,j) entry is 1 if (i,j) is a relation and 0 otherwise.
     Description
       Text
           This function uses the floydWarshall method from the Graphs package and is used by the poset constructor to compute RelationMatrix from Relations in a Poset.
       Example
           I = {a,b,c,d,e}; -- the ground set
           R = {(a,b),(b,c),(a,c),(a,d),(d,e)}; -- relations
                transitiveClosure(I,R)
     Caveat
        `       Output matrix is over RR.
     SeeAlso
           Poset
      poset
      Relations
      RelationMatrix
/// 
 
 
---------
-- poset routines
---------
 
doc ///
     Key
           compare
          (compare, Poset,Thing,Thing)
     Headline
          returns boolean value for whether an element is less than another 
     Usage
          compare(P,a,b)
     Inputs
           P : Poset
      a : Thing
      b : Thing
           a and b are elements of P
     Outputs
       true : Boolean
          if a is less than or equal to b
       false : Boolean
           otherwise
     Description
      Text
           This function simply looks at two elements in P, and determines what if any relation exists between them.
      Example
           P = poset ({a,b,c}, {(a,b), (a,c)});
           compare (P,a,c)
           compare (P,c,a)
           compare (P,b,c)
     Caveat
           Note that if two elements are not comparable, compare still returns a value of false.       
/// 
  
 
doc ///
     Key
           filter
          (filter,Poset,Thing)
     Headline
           returns a principal filter generated by the given element
     Usage 
           F = filter (P,a)
     Inputs
      P : Poset
      a : Thing
           a is an element of P
     Outputs
       F : List
           a list of all elements in P that are greater than or equal to a
     Description
       Example
           G = {a,b,c,d};
           R = {(a,b), (a,c), (c,d)};
           P = poset (G,R);
           F = filter (P,d)
     SeeAlso
           orderIdeal           
/// 

doc ///
     Key
           orderIdeal
          (orderIdeal, Poset, Thing)
     Headline
           returns a principal order ideal generated by the given element
     Usage 
           O = orderIdeal (P,a)
     Inputs
      P : Poset
      a : Thing
           a is an element of P
     Outputs
      O : List
           a list of all elements in P that are less than or equal to a
     Description
      Example
           G = {a,b,c,d};
           R = {(a,b), (a,c), (c,d)};
           P = poset (G,R);
           O = orderIdeal (P,c)
     SeeAlso
           filter    
/// 
 
 
doc ///
     Key
           posetMeet
      (posetMeet, Poset, Thing, Thing)
     Headline
           returns the meet of two elements
     Usage
          m = posetMeet (P,a,b)
     Inputs
           P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
       m : Thing
           m is the meet of a and b in P
     Description 
       Text
           This function returns the greatest element that is less than both a and b in P.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           posetMeet (P, d,e)
     Caveat
             This function returns an error if the meet does not exist.  To check if the meet exists use meetExists.
     SeeAlso
             meetExists
       posetJoin
       joinExists
/// 



doc ///
     Key
           posetJoin
      (posetJoin, Poset, Thing, Thing)
     Headline
           returns the join of two elements
     Usage
          j = posetJoin (P,a,b)
     Inputs
           P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
      j : Thing
           j is the join of a and b in P
     Description 
      Text
           This function returns the least element that is greater than both a and b in P.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           posetJoin (P, a,b)
     Caveat
             This function returns an error if the join does not exist.  To check if the join exists use joinExists.
     SeeAlso
             joinExists
       posetMeet
       meetExists
/// 
   
   
doc ///
     Key
           meetExists
      (meetExists, Poset, Thing, Thing)
     Headline
           determines if the meet exists
     Usage
          meetExists (P,a,b)
     Inputs
      P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
      true : Boolean
           the meet of a and b in P exists
      false : Boolean
           otherwise
     Description 
      Text
          This function determines if greatest element that is less than both a and b in P exists.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           meetExists (P,d,e)
                meetExists(P,a,b)
     Caveat
            If the meet exists, to find it use posetMeet.
     SeeAlso
             posetMeet
       posetJoin
       joinExists    
/// 

doc ///
     Key
           joinExists
      (joinExists, Poset, Thing,Thing)
     Headline
           determines if the join exists
     Usage
          joinExists (P,a,b)
     Inputs
      P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
      true : Boolean
           the join of a and b in P exists
      false : Boolean
           otherwise
     Description 
      Text
           This function determines if least element that is greater than both a and b in P exists.
      Example
           P = poset ({a,b,c,d,e}, {(a,d),(b,d),(b,e),(c,e)});
           joinExists (P,d,e)
                joinExists(P,a,b)
     Caveat
            If the join exists, to find it use posetJoin.
     SeeAlso
       posetJoin
       posetMeet
       meetExists  
/// 
 
doc ///
     Key
      isLattice
      (isLattice,Poset)
     Headline
           determines if a poset is a lattice
     Usage
           isLattice (P)
     Inputs
           P: Poset
     Outputs
      true : Boolean
           if P is a lattice
      false : Boolean
           otherwise
     Description 
      Text
           This function examines the entire poset to determine whether or not every pair of elements has both a meet and a join.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           isLattice (P)
      Text
           And by adding an element to the above example, we can create a poset which is a lattice.     
      Example
           P = poset ({a,b,c,d,e,f,x}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f), (x,a), (x,b), (x,c)});   
               isLattice (P)       
    
/// 

     
---------
-- LCM lattices
---------

doc ///
     Key
           lcmLattice
      (lcmLattice,Ideal)
      (lcmLattice, MonomialIdeal)
     Headline
           returns the LCM lattice of an ideal
     Usage
           lcmLattice (I)
      lcmLattice (M)
     Inputs 
      I : Ideal
      M : MonomialIdeal
     Outputs
      L : Poset
     Description
      Text
           This command allows for fast computation of LCM lattices, which are particularly useful in the study of resolutions of monomial ideals.
           Specifically the LCM lattice is the set of all lcms of subsets of the generators of the ideal, partially ordered by divisability.  
      Example
           S = QQ[a,b,c,d];
           I = ideal (b^2-a*d, a*d-b*c, c^2-b*d);
           M = monomialIdeal (b^2, b*c, c^2);
           L = lcmLattice (I);
           L.GroundSet
           L.RelationMatrix
           LM = lcmLattice (M);
           LM.GroundSet
           LM.RelationMatrix
     Caveat           
           Note, that at present this command does not efficiently handle ideals with large numbers of generators.  This is a problem that should be
        fixed by the next release of this package.     
/// 

     
-----------------
-- divisorPoset
-----------------

doc ///
    Key
        divisorPoset
        (divisorPoset,RingElement)
    Headline
        returns the poset of all divisors of a given monomial
    Usage
        divisorPoset (M)
    Inputs 
        M : RingElement
    Outputs
        P : Poset
    Description
        Text
            This command computes the poset of all divisors of a given monomial. For two monomials,
            u and v with u strictly dividing v, we have u < v in this poset.
        Example
            S = QQ[a,b,c,d];
            P = divisorPoset(a*b^2*d^3)
/// 

     

-----------------
-- coveringRelations
-----------------

doc ///
    Key
        coveringRelations
        (coveringRelations,Poset)
    Headline
        returns a list of all relations (a < b) with no intermediates
    Usage
        coveringRelations (P)
    Inputs 
        P : Poset
    Outputs
        C : List
            all pairs (a,b) of elements of P where a < b and there is no c with a < c < b
    Description
        Text
            This command computes the list of all covering relations of a poset P. 
            A relation (a,b) is said to be a covering relation if a < b and there
            is no element c with a < c < b. The result of this method is cached.
        Example
            S = QQ[a,b,c,d];
            P = divisorPoset(a*b^2*d);
            P.GroundSet
            P.Relations
            C = coveringRelations P
/// 

-----------------
-- dropElements
-----------------

doc ///
    Key
        dropElements
        (dropElements,Poset,List)
        (dropElements,Poset,Function)
    Headline
        returns the poset obtained by removing a list of elements 
    Usage
        dropElements (P, L)
        dropElements (P, f)
    Inputs 
        P : Poset
        L : List
            elements of P
        f : Function
            boolean valued giving true on those elements to be removed
    Outputs
        Q : Poset
            on elements of P that are not in L (or for which f is false) and all induced relations
    Description
        Text
            This command take a poset P and returns a new poset that
            contains all elements in P that are not in L.
            The relations on the remaining elements are all relations that held in P.

            Alternately, if a boolean function is given as input instead of a list, all 
            elements for which the function returns true are removed from P.

        Example
            S = QQ[a,b];
            P = divisorPoset(a*b^2);
            P.GroundSet
            Q = dropElements(P, {a,a*b^2})
            R = dropElements(P, m -> first degree m === 2)
/// 

-----------------
-- maximalChains
-----------------

doc ///
    Key
        maximalChains
        (maximalChains,Poset)
    Headline
        returns all maximal chains of a poset
    Usage
        maximalChains (P)
    Inputs 
        P : Poset
    Outputs
        C : List
            of maximal chains of P
    Description
        Text
            The maximal chains of P are totally orders subsets of P which are not properly contained
            in any other totally ordered subsets.

            This method returns a list of all maximal chains. The maximal chains are themselves
            lists of elements in P ordered from smallest to largest.

            The results of this method are cached.

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b^2*c);
            C = maximalChains P
/// 

-----------------
-- minimalElements
-----------------

doc ///
    Key
        minimalElements
        (minimalElements,Poset)
    Headline
        returns all minimal elements of a poset
    Usage
        minimalElements (P)
    Inputs 
        P : Poset
    Outputs
        L : List
            of all minimal elements of P
    Description
        Text
            This method returns a list of all minimal elements of P.
            The results of this method are cached.

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b^2*c);
            minimalElements P
            Q = dropElements(P, minimalElements(P));
            minimalElements Q
/// 

-----------------
-- maximalElements
-----------------

doc ///
    Key
        maximalElements
        (maximalElements,Poset)
    Headline
        returns all maximal elements of a poset
    Usage
        maximalElements (P)
    Inputs 
        P : Poset
    Outputs
        L : List
            of all maximal elements of P
    Description
        Text
            This method returns a list of all maximal elements of P.
            The results of this method are cached.

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b^2*c);
            maximalElements P
            Q = dropElements(P, maximalElements(P));
            maximalElements Q
/// 

-----------------
-- adjoinMax
-----------------

doc ///
    Key
        adjoinMax
        (adjoinMax,Poset)
        (adjoinMax,Poset,Thing)
    Headline
        returns new Poset with new maximal element
    Usage
        adjoinMax P
        adjoinMax(P,a)
    Inputs 
        P : Poset
        a : Thing
    Outputs
        Q : Poset
    Description
        Text
            This method returns a new poset with maximal element adjoined.
            If no element specified, uses {1}.

        Example
            G = {1,2,3,4}
            R = {{1,2},{1,3},{2,4},{3,4}}
            P = poset(G,R)
            Q = adjoinMax P
            Q = adjoinMax(P,5)
    SeeAlso
             adjoinMin
        maximalElements
        minimalElements
/// 

-----------------
-- adjoinMax
-----------------

doc ///
    Key
        adjoinMin
        (adjoinMin,Poset)
        (adjoinMin,Poset,Thing)
    Headline
        returns new Poset with new minimal element
    Usage
        adjoinMin P
        adjoinMin(P,a)
    Inputs 
        P : Poset
        a : Thing
    Outputs
        Q : Poset
    Description
        Text
            This method returns a new poset with minimal element adjoined.
            If no element specified, uses {0}.

        Example
            G = {1,2,3,4}
            R = {{1,2},{1,3},{2,4},{3,4}}
            P = poset(G,R)
            Q = adjoinMin P
            Q = adjoinMin(P,0)
    SeeAlso
             adjoinMax
        maximalElements
        minimalElements
/// 
-----------------
-- orderComplex
-----------------

doc ///
    Key
        orderComplex
        (orderComplex,Poset)
    Headline
        returns the simplicial complex with faces given by chains
    Usage
        orderComplex (P)
    Inputs 
        P : Poset
    Outputs
        D : SimplicialComplex
            the order complex of P
    Description
        Text
            This method returns the order complex of a poset P. The order
            complex is the simplicial complex whose faces are chains of P
            (and whose facets are maximal chains of P).

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b*c);
            C = maximalChains P
            D = orderComplex P
/// 


-----------------
-- closedInterval
-----------------
doc ///
    Key
        closedInterval
        (closedInterval,Poset, Thing, Thing)
    Headline
        returns the closed interval in the poset between two elements
    Usage
        closedInterval(P,a,b)
    Inputs 
        P : Poset
        a : Thing
        b : Thing 
    Outputs
        I : Poset
            the closed interval between a and b 
    Description
        Text
             This routine returns the interval between the elements a and b in P, 
                     including a and b,
             and an error message if the two elements are not comparable in P.

        Example
             P = poset({a,b,c,d},{(a,b),(b,c),(b,d)});
             closedInterval(P,a,d)      
/// 

----------------
--openInterval
----------------

doc ///
    Key
        openInterval
        (openInterval,Poset,Thing,Thing)
    Headline
        returns the open interval in the poset between two elements
    Usage
        openInterval(P,a,b)
    Inputs
        P : Poset
        a : Thing
        b : Thing
    Outputs
        I : Poset
    Description
         Text
              This routine returns the intreval between the elements a and b in P, not including a and b,
              and an error message if the two elements are not comparable in P.
      
        Example
                     P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
              openInterval(P,a,g)
///

-----------------
-- hasseDiagram
-----------------
doc  ///
    Key
              hasseDiagram
         (hasseDiagram,Poset)
    Headline
             returns Hasse diagram for the poset
    Usage
              hasseDiagram(P)
        Inputs
              P : Poset
        Outputs
         G : Digraph
              Directed graph whose edges correspond to covering relations in P
        Description
              Text 
              This routine returns the Hasse diagram which is a directed graph (defined in the Graphs package)
              whose edges correspond to the covering relations in P.  Specifically, the vertices in the graph 
              correspond to the elements in the ground set of P, and two vertices a and b have a directed edge 
              from a to b if a > b.
         Example
              P = poset ({a,b,c,d},{(a,b), (b,c), (b,d)})
              G = hasseDiagram(P)    
        SeeAlso
             displayGraph
///


-----------------
-- moebiusFunction
-----------------
doc///
     Key
           moebiusFunction
      (moebiusFunction,Poset)
     Headline
           returns the Moebius function values for the unique minimal element to each element of the poset
     Usage
           moebiusFunction(P)
     Inputs
           P : Poset
     Outputs
      M : HashTable
           Moebius function values for the minimal element of the poset to each element of the poset
     Description
       Text 
           This routine returns the Moebius function values for the unique minimal element to each element of the poset.
           If {\tt P} has more than one minimal element, an error will be signalled.
           In this example, $a$ is the minimal element of $P$; $M$ lists the Moebius function values from $a$ to each element of $P$.
      Example
           P = poset ({a,b,c,d},{(a,b), (b,c), (b,d)})
           M = moebiusFunction(P)    
     SeeAlso
           (moebiusFunction,Poset,Thing,Thing)
      Poset
///

doc///
     Key
      (moebiusFunction,Poset,Thing,Thing)
     Headline
           returns the Moebius function values for the minimal element of a closed interval to each element of the interval
     Usage
           moebiusFunction(P,a,b)
     Inputs
      P : Poset
      a : Thing
           a is an element of P
      b : Thing
           b is an element of P
     Outputs
       M : HashTable
           Moebius function values for the lesser of a and b to each element of the interval between a and b           
     Description
      Text
           For elements a and b of a poset P, this routine returns the Mobius function values for the minimal element in the closed 
           interval between elements a and b to each element of the interval between a and b. The routine handles both of the cases a<b and b<a.
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           moebiusFunction(P,b,g)
           moebiusFunction(P,g,b)           
     SeeAlso
           (moebiusFunction,Poset)
      Poset
///      

-----------------
-- subPoset
-----------------
doc///
     Key
           subPoset
      (subPoset,Poset,List)
     Headline
           returns the subposet supported on elements in a given list
     Usage
           subPoset(P,L)
     Inputs
      P : Poset
      L : List
           L consists of element in P
     Outputs
      Q : Poset
           subposet of P supported on elements in L           
     Description
        Text
               This command take a poset P and returns a new poset that
            contains all elements in P that are in L.
            The relations on the remaining elements are all relations that held in P.
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           subPoset(P, {a,e,g})           
     SeeAlso
          dropElements
///

-----------------
-- atoms
-----------------
doc///
     Key
           atoms
      (atoms,Poset)
     Headline
           returns the atoms of a poset
     Usage
           A = atoms(P)
     Inputs
           P : Poset
     Outputs
        A : List
          subset of the ground set of P consisting of elements covering minimal elements           
     Description
           Text
               This routine returns a list of elements which cover any minimal elements in P, these are known
                as the atoms of P.
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           atoms(P)           
///    


--------------
-- meetIrreducibles
--------------
doc///
     Key
           meetIrreducibles
      (meetIrreducibles,Poset)
     Headline
           returns the meet-irreducibles of a poset
     Usage
           L = meetIrreducibles(P)
     Inputs
           P : Poset
     Outputs
       L : List
          subset of the ground set of P consisting of meet-irreducible elements           
     Description
       Text
               An element a of a poset P is meet irreducible if it is not the meet of any set of elements (not containing a).  
                This routine returns a list of all such elements in the poset P.  
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           meetIrreducibles(P)           
///



doc ///
     Key 
           GroundSet
     Headline
           underlying set of a poset
     Usage
           G = P.GroundSet
     Inputs
           P : Poset
     Outputs
        G : List
           list of elements in P without the data of how they are partially ordered
     Description
           Text
                Since any poset is in fact a HashTable this symbol denotes the data in the HashTable consisting of the elements of the set.
      Example
           S = QQ[a,b,c,d];
           M = monomialIdeal (b^2, b*c, c^2);
           L = lcmLattice (M);
           L.GroundSet
     SeeAlso
           RelationMatrix
      Relations
      poset
      Poset
///
 
 
doc ///
     Key 
           RelationMatrix
     Headline
           the matrix expressing all of the relations between elements in a Poset
     Usage
           M = P.RelationMatrix
     Inputs
           P : Poset
     Outputs
        M : Matrix
           where the ijth entry indicates whether or not the jth element in the set is less than or equal to the ith element
     Description
           Text
                Since any poset is in fact a HashTable this symbol denotes the data in the HashTable containing all possible relations between elements.
      Example
           S = QQ[a,b,c,d];
           M = monomialIdeal (b^2, b*c, c^2);
           L = lcmLattice (M);
           L.GroundSet
           L.RelationMatrix
     SeeAlso
           GroundSet
      Relations
      poset
      Poset
/// 
 
doc ///
     Key 
           Relations
     Headline
           a set of relations in the poset that generates all other relations
     Usage
           R = P.Relations
     Inputs
           P : Poset
     Outputs
           R : List
            list of pairs of elements in P where (a,b) means a is less than or equal to b
     Description
           Text
                Since any poset is in fact a HashTable this symbol denotes the data in the HashTable which will describe all of the relations
            between elements in P.
      Example
           P = poset ({a,b,c,d,e,f},{(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           P.Relations --note there is not a one to one correspondence between these and entries in the RelationMatrix
           P.RelationMatrix
     Caveat
           Typically, the relations are the data entered in by the user and by no means account for every relation.  The RelationMatrix is usually computed
       from this set and thus is a better descriptor of the relations in P.
     SeeAlso
           RelationMatrix
      GroundSet
      poset
      Poset
///

doc///
     Key
           isAntichain
      (isAntichain, Poset, List)
     Headline
           checks whether a subposet is an anti-chain
     Usage
           isAntichain(P, L)
     Inputs
         P : Poset
         L : List
           a list of elements of P 
     Outputs
          true : Boolean
               if L is an antichain in P
         false : Boolean
             otherwise
     Description
           Text
            This function determines whether a list of elements of a poset is an anti-chain.
             
      Example
           P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           isAntichain(P2, {a,b})     
           isAntichain(P2, {b,c,d}) 
///

doc///
     Key
           intersectionLattice
        (intersectionLattice, List, Ring)
     Headline
           computes intersection lattice of an arrangement
     Usage
           intersectionLattice(H,R)
     Inputs
         H : List
             a list of elements of R
         R : PolynomialRing 
     Outputs
          P : Poset
     Description
      Text
           Given a set of equations f defining hyperplanes or hypersurfaces,
           computes the intersection lattice of the f.
          
      Example
           R=QQ[x,y]
           H={y+x,y-x,y-x-1,y}
           L=intersectionLattice(H,R)
      Text
           This code will produce intersection arrangement for hypersurfaces.
      Example
           R=QQ[x,y,z]
           H={x^2+y^2+z^2-9, z-1, x,y}
           L=intersectionLattice(H,R)
     SeeAlso
           projectivizeArrangement
           
///     

------------------------------------------
-- Tests
------------------------------------------

-- TEST 0
-- a lattice, B_3
TEST ///
I ={a,b,c,d,e,f,g,h};
C ={(a,b),(a,c),(a,d),(b,e),(b,f),(c,e),(c,g),(d,f),(d,g),(e,h),(f,h),(g,h)};
P=poset(I,C);
M = matrix {{1,1,1,1,1,1,1,1},
        {0,1,0,0,1,1,0,1},
        {0,0,1,0,1,0,1,1},
        {0,0,0,1,0,1,1,1},
        {0,0,0,0,1,0,0,1},
        {0,0,0,0,0,1,0,1},
        {0,0,0,0,0,0,1,1},
        {0,0,0,0,0,0,0,1}};
assert (entries P.RelationMatrix == entries M)
assert (posetJoin(P,a,b) == {b})
assert (posetJoin(P,b,d) == {f})
assert (posetMeet(P,a,b) == {a})
assert (posetMeet(P,f,g) == {d})
assert (filter(P,a) == {a,b,c,d,e,f,g,h})
assert (filter(P,b) == {b,e,f,h})
assert (orderIdeal(P,a) == {a})
assert (orderIdeal(P,g) == {a,c,d,g})
assert (isLattice(P))
///


-- TEST 1
-- two equivllaent non lattices with different initial data
TEST ///
I1={a,b,c,d,e,f};
C1={(a,c),(a,d),(b,c),(b,d),(c,e),(d,e),(e,f)};
P1=poset(I1,C1);

--Poset P1 with additional relations (a,e) and (a,f) added
I2={a,b,c,d,e,f};
C2={(a,c),(a,d),(b,c),(b,d),(c,e),(d,e),(a,e),(a,f),(e,f)};
P2=poset(I2,C2);

assert (P1.RelationMatrix == P2.RelationMatrix)    
assert (orderIdeal(P1,b) == {b})
assert (orderIdeal(P1,c) == {a,b,c})
assert (filter (P1,b) == {b,c,d,e,f})
assert (isLattice (P1) == false)
-- do joins and meets
///

-- do an LCM lattice
-- do order ideal

-- TEST 2
-- failing test commented out by dan:
-- TEST ///
-- V = {a,b,c,d,e};
-- E = {(a,b),(a,d),(b,c),(b,e),(c,e),(d,e)};
-- G = poset (V,E);
-- A = adjacencyMatrix(G);
-- D = allPairsShortestPath(A);
-- T = transitiveClosure(V,E);

-- assert(A_(0,1)==1 and A_(0,3)==1 and A_(1,2)==1 and A_(1,4)==1 and A_(2,4)==1 and A_(3,4)==1)
-- assert(D_(0,4)==2 and D_(4,0)==1/0. and D_(3,3)==0)
-- --assert(T== promote(matrix {{1, 1, 1, 1, 1}, {0, 1, 1, 0, 1}, {0, 0, 1, 0, 1}, {0, 0, 0, 1, 1}, {0, 0, 0, 0, 1}}, RR))

-- D1 =allPairsShortestPath(matrix({{0,1,1/0.,4},{1/0.,0,1/0.,2},{1,1/0.,0,1/0.},{1/0.,1/0.,1,0}})); -- digraph with a cycle
-- assert(D1 ==  promote(matrix {{0, 1, 4, 3}, {4, 0, 3, 2}, {1, 2, 0, 4}, {2, 3, 1, 0}}, RR))

-- ///


-- TEST 3
TEST ///
P1 = poset ({a,b,c,d},{(a,b), (b,c), (b,d)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, x*y, y^3, y*z);
L = lcmLattice I;
M = new HashTable from {x^2*y^3*z => 0, y^3*z => 1, x^2*y*z => 0, y^3 => -1, x*y^3*z => -1, y*z => -1, x^2 => -1,
      x*y => -1, x*y^3 => 1, x^2*y^3 => 0, 1 => 1, x^2*y => 1, x*y*z => 1}; 

assert ((moebiusFunction L)#(x^2*y^3) === M#(x^2*y^3)) 
assert ((moebiusFunction L)#(x*y*z) === M#(x*y*z)) 
assert( (moebiusFunction(P2, b,g)) === new HashTable from {e => -1, b => 1, g => 0} )
assert( (moebiusFunction(P1)) === new HashTable from {a => 1, b => -1, c => 0, d => 0} )
///

-- TEST 4
TEST ///
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);
L2 = divisorPoset(x^2*y^3);

--testing divisorPoset and LCM lattices
assert( (L.GroundSet) == {1,z^2,y^2,y^2*z^2,x^2,x^2*z^2,x^2*y^2,x^2*y^2*z^2} )
assert( (L.Relations) == {(1,1),(1,z^2),(1,y^2),(1,y^2*z^2),(1,x^2),(1,x^2*z^2),(1,x^2*y^2),(1,x^2*y^2*z^2),(z^2,z^2),(z^2,y^2*z^2),(z^2,x^2*z^2),(z^2,x^2*y^2*z^2),(y^2,y^2),(y^2,y^2*z^2),(y^2,x^2*y^2),(y^2,x^2*y^2*z^2),(y^2*z^2,y^2*z^2),(y^2*z^2,x^2*y^2*z^2),(x^2,x^2),(x^2,x^2*z^2),(x^2,x^2*y^2),(x^2,x^2*y^2*z^2),(x^2*z^2,x^2*z^2),(x^2*z^2,x^2*y^2*z^2),(x^2*y^2,x^2*y^2),(x^2*y^2,x^2*y^2*z^2),(x^2*y^2*z^2,x^2*y^2*z^2)} )
assert( (L.RelationMatrix) === map(ZZ^8,ZZ^8,{{1, 1, 1, 1, 1, 1, 1, 1}, {0, 1, 0, 1, 0, 1, 0, 1}, {0, 0, 1, 1, 0, 0, 1, 1}, {0, 0, 0, 1, 0, 0, 0, 1}, {0, 0, 0, 0, 1, 1, 1, 1}, {0, 0, 0, 0, 0, 1, 0, 1}, {0, 0, 0, 0, 0, 0, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 1}}) )
assert( (L2.GroundSet) == {1,y,y^2,y^3,x,x*y,x*y^2,x*y^3,x^2,x^2*y,x^2*y^2,x^2*y^3} )
assert( (L2.Relations) == {(1,1),(1,y),(1,y^2),(1,y^3),(1,x),(1,x*y),(1,x*y^2),(1,x*y^3),(1,x^2),(1,x^2*y),(1,x^2*y^2),(1,x^2*y^3),(y,y),(y,y^2),(y,y^3),(y,x*y),(y,x*y^2),(y,x*y^3),(y,x^2*y),(y,x^2*y^2),(y,x^2*y^3),(y^2,y^2),(y^2,y^3),(y^2,x*y^2),(y^2,x*y^3),(y^2,x^2*y^2),(y^2,x^2*y^3),(y^3,y^3),(y^3,x*y^3),(y^3,x^2*y^3),(x,x),(x,x*y),(x,x*y^2),(x,x*y^3),(x,x^2),(x,x^2*y),(x,x^2*y^2),(x,x^2*y^3),(x*y,x*y),(x*y,x*y^2),(x*y,x*y^3),(x*y,x^2*y),(x*y,x^2*y^2),(x*y,x^2*y^3),(x*y^2,x*y^2),(x*y^2,x*y^3),(x*y^2,x^2*y^2),(x*y^2,x^2*y^3),(x*y^3,x*y^3),(x*y^3,x^2*y^3),(x^2,x^2),(x^2,x^2*y),(x^2,x^2*y^2),(x^2,x^2*y^3),(x^2*y,x^2*y),(x^2*y,x^2*y^2),(x^2*y,x^2*y^3),(x^2*y^2,x^2*y^2),(x^2*y^2,x^2*y^3),(x^2*y^3,x^2*y^3)} )
assert( (L2.RelationMatrix) === map(ZZ^12,ZZ^12,{{1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}, {0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1}, {0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1}, {0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1}, {0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1}, {0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1}, {0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1}}) )
///


-- TEST 5
-- failing test commented out by dan:
-- TEST ///
-- P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
-- R = QQ[x,y,z];
-- L = lcmLattice ideal (x^2, y^2, z^2);

-- -- testing hasseDiagram
-- assert((hasseDiagram P1)#a === set {})
-- assert((hasseDiagram P1)#b === set {})
-- assert((hasseDiagram P1)#c === set {a,b})
-- assert((hasseDiagram P1)#d === set {a,b})
-- assert((hasseDiagram P1)#e === set {c,d})
-- assert( toString sort pairs (hasseDiagram L) === toString sort pairs new Digraph from {x^2*y^2*z^2 => new Set from {x^2*y^2, x^2*z^2, y^2*z^2}, x^2*y^2 => new Set from {x^2, y^2}, x^2*z^2 => new Set from {x^2, z^2}, x^2 => new Set from {1}, y^2*z^2 => new Set from {y^2, z^2}, 1 => new Set from {}, z^2 => new Set from {1}, y^2 => new Set from {1}} )

-- ///

-- TEST 6
TEST ///
P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);
--testing max/min elts
assert( (maximalElements P1) === {e} )
assert( (maximalElements L) === {x^2*y^2*z^2} )
assert( (minimalElements P1) === {a,b} )
assert( (minimalElements L) == {1} )

--testing atoms
assert( (atoms(P1) ) === {c,d} )
assert( (atoms(L)) === {z^2,y^2,x^2} )
///

-- TEST 7
TEST /// 
P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
P2 = poset({a,b,c,d,e,f,g,h},{(h,a),(h,b),(h,c),(h,d),(a,e),(b,e),(e,f),(c,f),(f,g),(d,g)});
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);
L2 = divisorPoset(x^2*y^3);

--testing subPoset
assert( ((subPoset(P1, {a,b,e})).GroundSet) === {a,b,e} )
assert( ((subPoset(P1, {a,b,e})).Relations) === {(a,a),(a,e),(b,b),(b,e),(e,e)} )
assert( ((subPoset(P1, {a,b,e})).RelationMatrix) === map(ZZ^3,ZZ^3,{{1, 0, 1}, {0, 1, 1}, {0, 0, 1}}) )
assert( ((subPoset(P2, {a,e,f,d})).GroundSet) === {a,d,e,f} )
assert( ((subPoset(P2, {a,e,f,d})).Relations) === {(a,a),(a,e),(a,f),(d,d),(e,e),(e,f),(f,f)} )
assert( ((subPoset(P2, {a,e,f,d})).RelationMatrix) === map(ZZ^4,ZZ^4,{{1, 0, 1, 1}, {0, 1, 0, 0}, {0, 0, 1, 1}, {0, 0, 0, 1}}) )
assert( ((subPoset(L, {x^2,y^2,x^2*y^2})).GroundSet) === {y^2,x^2,x^2*y^2} )
assert( ((subPoset(L, {x^2,y^2,x^2*y^2})).Relations) === {(y^2,y^2),(y^2,x^2*y^2),(x^2,x^2),(x^2,x^2*y^2),(x^2*y^2,x^2*y^2)} )
assert( ((subPoset(L, {x^2,y^2,x^2*y^2})).RelationMatrix) === map(ZZ^3,ZZ^3,{{1, 0, 1}, {0, 1, 1}, {0, 0, 1}}) )

-- testing dropElements
assert( ((dropElements(P1, {a,c})).GroundSet) === {b,d,e} )
assert( ((dropElements(P1, {a,c})).Relations) === {(b,b),(b,d),(b,e),(d,d),(d,e),(e,e)} )
assert( ((dropElements(P1, {a,c})).RelationMatrix          ) === map(ZZ^3,ZZ^3,{{1, 1, 1}, {0, 1, 1}, {0, 0, 1}}) )
assert( ((dropElements(L2, m-> first degree m > 2)).GroundSet) == {1,y,y^2,x,x*y,x^2} )
assert( ((dropElements(L2, m-> first degree m > 2)).Relations) == {(1,1),(1,y),(1,y^2),(1,x),(1,x*y),(1,x^2),(y,y),(y,y^2),(y,x*y),(y^2,y^2),(x,x),(x,x*y),(x,x^2),(x*y,x*y),(x^2,x^2)} )
assert( ((dropElements(L2, m-> first degree m > 2)).RelationMatrix) === map(ZZ^6,ZZ^6,{{1, 1, 1, 1, 1, 1}, {0, 1, 1, 0, 1, 0}, {0, 0, 1, 0, 0, 0}, {0, 0, 0, 1, 1, 1}, {0, 0, 0, 0, 1, 0}, {0, 0, 0, 0, 0, 1}}) )

///


-- TEST 8
TEST ///
P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);

S = QQ[v_0..v_4]
T = QQ[v_0..v_7]
assert( toString ((orderComplex P1).facets) === toString (use S; map(S^1,S^{{-3},{-3},{-3},{-3}},{{v_1*v_3*v_4, v_0*v_3*v_4, v_1*v_2*v_4, v_0*v_2*v_4}})) )
assert( toString ((orderComplex L).facets) === toString (use T; map(T^1,T^{{-4},{-4},{-4},{-4},{-4},{-4}},{{v_0*v_4*v_6*v_7, v_0*v_2*v_6*v_7, v_0*v_4*v_5*v_7, v_0*v_1*v_5*v_7, v_0*v_2*v_3*v_7, v_0*v_1*v_3*v_7}})) )
///

-- TEST 9
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)})
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
R = QQ[x,y,z,w]
I = ideal(x^2, x*y, y^3, y*z)
L = lcmLattice I
assert( (isAntichain(P1, {j, k})) === true )
assert( (isAntichain(P1, {j, k, h})) === false )
assert( (isAntichain(P2, {a, b, g})) === false )
assert( (isAntichain(P2, {b, c, d})) === true )
assert( (isAntichain(L, {y*z, y^3, x*y})) === true )
assert( (isAntichain(L, {y*z, x^2*y, x*y*x})) === true )
///


-- TEST 10
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, x*y, y^3, y*z);
L = lcmLattice I;

assert( (maximalChains(P1)) === {{h,i,j},{h,i,k}} )
assert( (maximalChains(P2)) === {{a,b,e,g},{a,c,e,g},{a,c,f,g},{a,d,f,g}})
assert( (maximalChains(L)) == {{1,y*z,y^3*z,x*y^3*z,x^2*y^3*z},{1,y*z,x*y*z,x*y^3*z,x^2*y^3*z},{1,y*z,x
      *y*z,x^2*y*z,x^2*y^3*z},{1,y^3,y^3*z,x*y^3*z,x^2*y^3*z},{1,y^3,x*y^3,x*y^
      3*z,x^2*y^3*z},{1,y^3,x*y^3,x^2*y^3,x^2*y^3*z},{1,x*y,x*y*z,x*y^3*z,x^2*y
      ^3*z},{1,x*y,x*y*z,x^2*y*z,x^2*y^3*z},{1,x*y,x*y^3,x*y^3*z,x^2*y^3*z},{1,
      x*y,x*y^3,x^2*y^3,x^2*y^3*z},{1,x*y,x^2*y,x^2*y*z,x^2*y^3*z},{1,x*y,x^2*y
      ,x^2*y^3,x^2*y^3*z},{1,x^2,x^2*y,x^2*y*z,x^2*y^3*z},{1,x^2,x^2*y,x^2*y^3,
      x^2*y^3*z}} )
///

-- TEST 11
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, x*y, y^3, y*z);
L = lcmLattice I;


meetIrreducibles L
assert( (try meetIrreducibles P1  else oops) === oops )
assert( set meetIrreducibles P2 === set {e,f,g,b,d} )
assert( (set meetIrreducibles L) === set {x^2, y^3*z, x*y^3*z, x^2*y*z, x^2*y^3, x^2*y^3*z} )
///

-- TEST 12
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, y^2, z^2);
L = lcmLattice I;
assert( (coveringRelations P1) === {{h,i},{i,j},{i,k}} )
assert( (coveringRelations P2) === {{a,b},{a,c},{a,d},{b,e},{c,e},{c,f},{d,f},{e,g},{f,g}} )
assert( (coveringRelations L) == 
        {{1,z^2}, {1,y^2}, {1,x^2}, {z^2,y^2*z^2}, {z^2,x^2*z^2}, {y^2,y^2*z^2}, {y^2,x^2*y^2}, {y^2*z^2,x^2*y^2*z^2}, {x^2,x^2*z^2}, {x^2,x^2*y^2},
        {x^2*z^2,x^2*y^2*z^2}, {x^2*y^2,x^2*y^2*z^2}} )
///

-- TEST 13
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});

assert( ((openInterval(P1,h,j)).Relations) === {(i,i)} )
assert( ((closedInterval(P1,i,k)).Relations) === {(i,i),(i,k),(k,k)} )
assert( ((openInterval(P2,a,e)).Relations) === {(b,b),(c,c)} )
assert( ((closedInterval(P2,c,g)).Relations) === {(c,c),(c,e),(c,f),(c,g),(e,e),(e,g),(f,f),(f,g),(g,g)} )

///

-- TEST 14
--TEST ///
--B = booleanLattice(2)   
--assert( toString (B.GroundSet) === toString {1,x_2,x_1,x_1*x_2} )
--assert( (B.RelationMatrix) === map(ZZ^4,ZZ^4,{{1, 1, 1, 1}, {0, 1, 0, 1}, {0, 0, 1, 1}, {0, 0, 0, 1}}) )
--assert( toString (B.Relations) === toString {(1,1),(1,x_2),(1,x_1),(1,x_1*x_2),(x_2,x_2),(x_2,x_1*x_2),(x_1,x_1),(x_1, x_1*x_2),(x_1*x_2,x_1*x_2)} )
--///


end;


loadPackage("Posets",FileName=>"./Posets.m2")
