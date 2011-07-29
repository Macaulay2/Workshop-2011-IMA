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

export { "areIsomorphic", "graphToString" };
    
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
    GraphIsom,
    areIsomorphic,
    (areIsomorphic, Graph, Graph),
    (areIsomorphic, String, String),
    graphToString, 
    (graphToString, List, ZZ),
    (graphToString, MonomialIdeal),
    (graphToString, Ideal),
    (graphToString, Graph),
    (graphToString, String)
};
