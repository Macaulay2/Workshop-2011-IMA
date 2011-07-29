needsPackage "Graphs";
newPackage (
    "GraphIsom",
    Version => "0.1",
    Date => "29. July 2011",
    Authors => {{Name => "David W. Cook II",
                 Email => "dcook@ms.uky.edu",
                 HomePage => "http://www.ms.uky.edu/~dcook"}},
    Headline => "Graph isomorphisms via Nauty",
    Configuration => {"path" => ""},
    DebuggingMode => false
);
needsPackage "Graphs";

nauty'path = (options GraphIsom).Configuration#"path";
if nauty'path == "" then nauty'path = prefixDirectory | currentLayout#"programs";

export { "areIsomorphic", "graphToString", "relabelGraph", "stringToList", "stringToGraph" };
    
-- Determines if two graphs are isomorphic. 
areIsomorphic = method()
areIsomorphic (String, String) := Boolean => (G, H) -> (#callNauty("shortg -q", {G, H})) == 1
areIsomorphic (Graph, Graph) := Boolean => (G, H) -> areIsomorphic(graphToString G, graphToString H)

-- Converts a graph to a string in Graph6 format.
graphToString = method()
graphToString (List, ZZ) := String => (E, n) -> (
    if n < 1 then error("graphToString: nauty does not like graphs with non-positive numbers of vertices.");
    if n > 68719476735 then error("graphToString: nauty does not like too many vertices (more than 68719476735).");
    if any(E, e -> #e != 2) or any(E, e -> first e == last e) or max(flatten E) >= n then error("graphToString: Edges are malformed.");
    N := take(reverse apply(6, i -> (n // 2^(6*i)) % 2^6), if n < 63 then -1 else if n < 258047 then -3 else -6);

    B := new MutableList from toList(6*ceiling(binomial(n,2)/6):0);
    -- the edges must be in {min, max} order, so sort them
    for e in apply(E, sort) do B#(binomial(last e, 2) + first e) = 1;
    ascii apply(N | apply(pack(6, toList B), b -> fold((i,j) -> i*2+j, b)), l -> l + 63)
)
graphToString MonomialIdeal := String => I -> graphToString(apply(first entries generators I, indices), #gens ring I)
graphToString Ideal := String => I -> graphToString monomialIdeal I
graphToString Graph := String => G -> (
    --graphToString(apply(edges G, e -> apply(e, index)), #vertices G)
    V := vertices G;
    idx := hashTable apply(#V, i-> V_i => i);
    E := apply((edges G)/toList, e -> {idx#(e_0), idx#(e_1)});
    graphToString(E, #V)
);
graphToString String := String => S -> S

-- Relabels a graph using a canonical labelling.
relabelGraph = method()
relabelGraph (String, ZZ, ZZ) := String => (S, i, a) -> (
    if i > 15 or i < 0 then error("relabelGraph: The invariant selected is invalid.");
    if a < 0 then error("relabelGraph: The invariant argument must be nonnegative.");
    r := callNauty("labelg -qg -i" | toString i | " -K" | toString a, {S});
    if #r != 0 then first r else error("relabelGraph: The graph is in an incorrect format.")
)
relabelGraph (String, ZZ) := String => (S, i) -> relabelGraph(S, i, 3)
relabelGraph String := String => S -> relabelGraph(S, 0, 3)
relabelGraph (Graph, ZZ, ZZ) := Graph => (G, i, a) -> stringToGraph relabelGraph(graphToString G, i, a)
relabelGraph (Graph, ZZ) := Graph => (G, i) -> relabelGraph(G, i, 3)
relabelGraph Graph := Graph => G -> relabelGraph(G, 0, 3)

-- Converts a graph given by a string in either Sparse6 or Graph6 format to a list
stringToList = method()
stringToList String := List => str -> (
    -- basic parse
    if #str == 0 then return;
    sparse := str_0 == ":";
    A := apply(ascii str, l -> l - 63);
    if sparse then A = drop(A, 1);
    if min A < 0 or max A > 63 then error("stringToList: Not a Sparse6/Graph6 string.");

    -- get number of vertices
    p := 0;
    n := if A_0 < 63 then (
             p = 1;
             A_0
         ) else if A_1 < 63 then ( 
             if #A < 4 then error("stringToList: Not a Sparse6/Graph6 string.");
             p = 4;
             fold((i,j) -> i*2^6+j, take(A, {1,3}))
         ) else (
             if #A < 8 then error("stringToList: Not a Sparse6/Graph6 string.");
             p = 8;
             fold((i,j) -> i*2^6+j, take(A, {2,7}))
         );

    bits := flatten apply(drop(A, p), n -> ( n = n*2; reverse for i from 1 to 6 list (n=n//2)%2 ));
    c := 0;

    {n, if sparse then (
        -- Sparse6 format
        k := ceiling(log(n) / log(2));
        v := 0;
        xi := 0;
        while c + k < #bits list (
            if bits_c == 1 then v = v + 1;
            xi = fold((i,j) -> 2*i+j, take(bits, {c+1,c+k})); 
            c = c + k + 1;
            if xi > v then ( v = xi; continue ) else {xi, v}
        )
    ) else ( 
        -- Graph6 format
        if #A != p + ceiling(n*(n-1)/12) then error("stringToList: Not a Graph6 string.");
        c = -1;
        flatten for i from 1 to n - 1 list for j from 0 to i - 1 list ( c = c + 1; if bits_c == 1 then {i, j} else continue)
    )}
)

-- Converts a string to a graph object
stringToGraph = method()
stringToGraph String := Graph => str -> (
    L := stringToList str;
    V := toList(0..(first L - 1));
    V' := unique flatten last L;
    if #V' == #V then graph last L else graph(last L, Singletons => select(V, v -> not member(v, V')))
);
                                          
-- External call to nauty
callNauty = method();
callNauty (String, List) := List => (cmdStr, dataList) -> (
    infn := temporaryFileName();
    erfn := temporaryFileName();
    -- output the data to a file
    o := openOut infn;
    scan(dataList, d -> o << d << endl);
    close o;
    -- try to harvest the lines
    r := lines try get openIn ("!" | nauty'path | cmdStr | " <" | infn | " 2>" | erfn)
    else (
        -- nauty errored, harvest the error
        e := last separate(":", first lines get openIn erfn);
        removeFile infn;
        removeFile erfn;
        -- special cases 
        if e == " not found" then error("callNauty: nauty could not be found on the path [" | nauty'path | "].");
	    error("callNauty: nauty terminated with the error [", e, "].");
    );
    removeFile infn;
    removeFile erfn;
    r
)

undocumented { 
    areIsomorphic,
    (areIsomorphic, Graph, Graph),
    (areIsomorphic, String, String),
    graphToString, 
    (graphToString, List, ZZ),
    (graphToString, MonomialIdeal),
    (graphToString, Ideal),
    (graphToString, Graph),
    (graphToString, String),
    stringToList,
    (stringToList, String),
    stringToGraph,
    (stringToGraph, String)
};

beginDocumentation()
doc ///
    Key
        GraphIsom
    Headline
        Graph isomorphism via Nauty
///

doc ///
    Key
        relabelGraph
        (relabelGraph, String, ZZ, ZZ)
        (relabelGraph, String, ZZ)
        (relabelGraph, String)
        (relabelGraph, Graph, ZZ, ZZ)
        (relabelGraph, Graph, ZZ)
        (relabelGraph, Graph)
    Headline
        applies a vertex invariant based refinement to a graph
    Usage
        T = relabelGraph(S, i, a)
        T = relabelGraph(S, i)
        T = relabelGraph S
        H = relabelGraph(G, i, a)
        H = relabelGraph(G, i)
        H = relabelGraph G
    Inputs
        S:String
            a graph encoded in either Sparse6 or Graph6 format
        G:Graph
        i:ZZ
            a choice of invariant to order by ($0 \leq i \leq 15$, default is $0$)
        a:ZZ
            a non-negative argument passed to nauty, (default is $3$)
    Outputs
        T:String
            a graph isomorphic to $S$ encoded in either Sparse6 or Graph6 format
        H:Graph
            a graph isomorphic to $G$
    Description
        Text
            This method applies one of sixteen vertex invariant based refinements to a 
            graph.  See the nauty documentation for a more complete description
            of each and how the argument $a$ is used.

            The sixteen vertex invariants are:
            @UL ({
                "$i = 0$: none,",
                "$i = 1$: twopaths,",
                "$i = 2$: adjtriang(K),",
                "$i = 3$: triples,",
                "$i = 4$: quadruples,",
                "$i = 5$: celltrips,",
                "$i = 6$: cellquads,",
                "$i = 7$: cellquins,",
                "$i = 8$: distances(K),",
                "$i = 9$: indsets(K),",
                "$i = 10$: cliques(K),",
                "$i = 11$: cellcliq(K),",
                "$i = 12$: cellind(K),",
                "$i = 13$: adjacencies,",
                "$i = 14$: cellfano, and",
                "$i = 15$: cellfano2."
            } / TEX) @
        Example
            G = graph {{a,e}, {e,c}, {c,b}, {b,d}, {d,a}};
            relabelGraph G
        Text
            Note that on most small graphs, all sixteen orderings produce the same result.
///
