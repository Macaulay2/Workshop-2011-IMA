-- -*- coding: utf-8 -*-

needsPackage "Graphs"

newPackage(
     "GraphicalModels",
     Version => "1.0",
     Date => "August 2012",
     Authors => {
	  {Name => "Luis Garcia-Puente",
	   Email => "lgarcia@shsu.edu",
	   HomePage => "http://www.shsu.edu/~ldg005"},
          {Name=> "Sonja Petrovic", 
	   Email=> "sonja@psu.edu",
	   HomePage=>"http://www.personal.psu.edu/sxp61"}, 
	  {Name => "Mike Stillman",
	   Email => "mike@math.cornell.edu",
	   HomePage => "http://www.math.cornell.edu/~mike/"},
          {Name=> "Seth Sullivant", 
	   Email=> "smsulli2@ncsu.edu",
	   HomePage=>"http://www4.ncsu.edu/~smsulli2/"}
          --{Name=> "Contributing authors and collaborators: Alexander Diaz, Shaowei Lin, David Murrugarra", 
	  -- Email=> "",
	  -- HomePage=>""}      
	  },
     Headline => "A package for discrete and Gaussian graphical models",
     DebuggingMode => true
     )
export {bidirectedEdgesMatrix,
       Coefficients,
       conditionalIndependenceIdeal,
       covarianceMatrix,
       directedEdgesMatrix,
       discreteVanishingIdeal,
       gaussianMatrices,
       gaussianParametrization,
       gaussianVanishingIdeal,
       gaussianRing, 
       globalMarkov,
       hiddenMap,
       identifyParameters, 
       inverseMarginMap,
       localMarkov,
       markovMatrices, 
       markovRing,        
       marginMap, 
       pairMarkov, 
       trekIdeal, 
       trekSeparation,
       SimpleTreks,
       undirectedEdgesMatrix,
       VariableName,
       sVariableName,
       kVariableName,
       lVariableName,
       pVariableName
       	} 
     
needsPackage "Graphs"

markovRingData = local markovRingData
markovVariables = local markovVariables
gaussianRingData = local gaussianRingData
gaussianVariables = local gaussianVariables
numberOfEliminationVariables = local numberOfEliminationVariables  --entry stored inside gaussianRing



--**************************--
--  INTERNAL ROUTINES        	  --
--**************************--

--*************************************--
--  Functions used by Markov methods   --
--*************************************--


--------------------------------------------
-- bayesBall
-- A is a set in 1..n (n = #G)
-- C is a set in 1..n (the "blocking set")
-- G is a DAG
-- Returns the subset B of 1..n which is independent of A given C.
-- The algorithm is the Bayes Ball algorithm, as implemented by Luis Garcia-Puente, 
-- after the paper of Ross D. Shachter.
--------------------------------------------

bayesBall = (A,C,G) -> (
     V := sort vertices G;
     visited := new MutableHashTable from apply(V, k-> k=>false);
     blocked :=  new MutableHashTable from apply(V, k-> k=>false);
     up :=  new MutableHashTable from apply(V, k-> k=>false);
     down := new MutableHashTable from apply(V, k-> k=>false);
     top :=  new MutableHashTable from apply(V, k-> k=>false);
     bottom := new MutableHashTable from apply(V, k-> k=>false);
     vqueue := toList A;
     -- Now initialize vqueue, set blocked
     scan(vqueue, a -> up#a = true);
     scan(toList C, c -> blocked#c = true);
     local pa;
     local ch;
     while #vqueue > 0 do (
	  v := vqueue#-1;
	  vqueue = drop(vqueue,-1);
	  visited#v = true;
	  if not blocked#v and up#v
	  then (
	       if not top#v then (
		    top#v = true;
		    pa = toList parents(G,v);
		    scan(pa, i -> up#i = true);
		    vqueue = join(vqueue,pa);
		    );
	       if not bottom#v then (
		    bottom#v = true;
		    ch = toList children(G,v);
		    scan(ch, i -> down#i = true);
		    vqueue = join(vqueue,ch);
		    );
	       );
	  if down#v
	  then (
	       if blocked#v and not top#v then (
		    top#v = true;
		    pa = toList parents(G,v);
		    scan(pa, i -> up#i = true);
		    vqueue = join(vqueue,pa);
		    );
	       if not blocked#v and not bottom#v then (
		    bottom#v = true;
		    ch = toList children(G,v);
		    scan(ch, i -> down#i = true);
		    vqueue = join(vqueue,ch);
		    );
	       );
	  );
     set toList select(V, i -> not blocked#i and not bottom#i)     
     )     

--*************************************--
--  Functions used throughout          --
--*************************************--

-- NOTE:
-- /// FIX ME /// DELETE ME /// DO SOMETHING! ///
--  ALL THE FUNCTIONS (in this section) BELOW ARE DECLARED GLOBAL INSTEAD OF LOCAL
-- FOR THE REASON THAT LOCAL DEFINITIONS WOULD INEXPLICABLY 
-- CREATE ERRORS. --Amelia? Luis? ---this is an old error message?! check this!



---------------------------------------------------------------
-- cartesian
-- cartesian({d_1,...,d_n}) returns the cartesian product 
-- of {0,...,d_1-1} x ... x {0,...,d_n-1}
---------------------------------------------------------------

cartesian = (L) -> (
     if #L == 1 then 
	return toList apply (L#0, e -> 1:e);
     L0 := L#0;
     Lrest := drop (L,1);
     C := cartesian Lrest;
     flatten apply (L0, s -> apply (C, c -> prepend (s,c))))



--------------------------------------------
-- position of an element x in a list h
--------------------------------------------

pos = (h, x) -> position(h, i->i===x)



--------------------------------------------------------------------------
-- possibleValues ((d_1,...,d_n),A) returns the cartesian product 
-- of all d_i's such that the vertex i is a member of the list A
-- it assumes that the list A is a list of integers.
--------------------------------------------------------------------------
possibleValues = (d,A) ->
     cartesian (toList apply(0..#d-1, i -> 
	       if member(i,A) 
	       then toList(1..d#i) 
	       else {0}))
     
     
     
-------------------------------------------------------
-- prob((d_1,...,d_n),(s_1,dots,s_n))
-- Note: this function assumes that R is a markovRing
-------------------------------------------------------

prob = (R,s) -> (
     d := R.markovRingData;
     p := i -> R.markovVariables#i;
     L := cartesian toList apply (#d, i -> 
	   if s#i === 0 
	   then toList(1..d#i) 
	   else {s#i});
     sum apply (L, v -> p v))



-------------------------------------------------------------------------------
-- takes a list A, and a sublist B of A, and converts 
-- the membership sequence of 0's and 1's of elements of B in A to binary
-------------------------------------------------------------------------------

setToBinary = (A,B) -> sum(toList apply(0..#A-1, i->2^i*(if (set B)#?(A#i) then 1 else 0)))



-------------------------------------------------------
-- returns all subsets of B which contain A:
-------------------------------------------------------

subsetsBetween = (A,B) -> apply(subsets ((set B) - A), i->toList (i+set A))




--***********************************************************************************--
--  Functions used within Markov relation routines to remove redundant CI statements --
--***********************************************************************************--


--------------------------------------------------------------------------------------
-- Removing redundant statements:                              
-- called from local, global, and pairwise Markov methods.     
--
-- A conditional independence statement is a list {A,B,C}
-- where A,B,C are (disjoint) subsets of labels for nodes in the graph.
-- It should be interpreted as: A independent of B given C.
-- A dependency list is a list of dependencies.
-- 
-- We have several simple routines to remove the most obvious redundant elements, 
-- but a more serious attempt to remove dependencies could be made.
--------------------------------------------------------------------------------------

equivStmts = (S,T) -> S#2 === T#2 and set{S#0,S#1} === set{T#0,T#1} 
     -- If S and T represent exactly the same dependency, return true.

setit = (d) -> {set{d#0,d#1},d#2} 
     -- More serious removal of redundancies.  

under = (d) -> (
           d01 := toList d_0;
           d0 := toList d01_0;
           d1 := toList d01_1;
           d2 := toList d_1;
           e0 := subsets d0;
           e1 := subsets d1;
           z1 := flatten apply(e0, x -> apply(e1, y -> (
      		    {set{d01_0 - set x, d01_1 - set y}, set x + set y +  d_1})));-- see comment at removeRedundants
           z2 := flatten apply(e0, x -> apply(e1, y -> (
      		    {set{d01_0 - set x, d01_1 - set y},  d_1})));-- see comment at removeRedundants
           z := join(z1,z2);
           z = select(z, z0 -> not member(set{}, z0_0));
           set z
           )

sortdeps = Ds -> (
     -- input: ds
     -- first make list where each element is {-a*b, set{A,B}, set C}
     -- sort the list
     -- remove the first element
     i := 0;
     ds := apply(Ds, d -> (x := toList d#0; i=i+1; { - #x#0 * #x#1, i, d#0, d#1}));
     ds = sort ds;
     apply(ds, d -> {d#2, d#3})
     )

normalizeStmt = (D) -> (
     -- D has the form: {set{set{A},set{B}},set{C}}
     -- output is {A,B,C}, where A,B,C are sorted in increasing order
     --  and A#0 < B#0
     D0 := sort apply(toList(D#0), x -> sort toList x);
     D1 := toList(D#1);
     {D0#0, D0#1, D1}
     )

minimize = (Ds) -> (
     -- each element of Ds should be a list {A,B,C}
     answer := {};
     -- step 1: first make the first two elements of each set a set
     Ds = Ds/setit;
     while #Ds > 0 do (
	  Ds = sortdeps Ds;
	  f := Ds_0;
	  funder := under f;
	  answer = append(answer, f);
	  Ds = set Ds - funder;
	  Ds = toList Ds;
	  );
     apply(answer, normalizeStmt))

--------------------------------------------------------------------------------------
-- removeRedundants: the general function
-- Ds is a list of triples of sets {A,B,C}
-- test1: returns true if D1 can be removed
-- Return a sublist of Ds which removes any that test1 declares not necessary.
-- 
--  **CAVEAT**
--  This works just fine when used internally, e.g. from localMarkov. 
--  However, if we export it and try to use it, there is a problem: we seem to be 
--  attempting to add a List to a Set in 2 lines of "under".
--------------------------------------------------------------------------------------

removeRedundants = (Ds) -> (
     test1 := (D1,D2) -> (D1_2 === D2_2 and 
                          ((isSubset(D1_0, D2_0) and isSubset(D1_1, D2_1))
	               or (isSubset(D1_1, D2_0) and isSubset(D1_0, D2_1))));
     Ds = apply(Ds, d -> {set{d#0,d#1}, d#2});
     Ds = unique Ds;      -- first remove non-unique elements, if any.
     Ds = apply(Ds, d -> append(toList(d#0), d#1));
     c := toList select(0..#Ds-1, i -> (
	       a := Ds_i;
	       D0 := drop(Ds,{i,i});
	       all(D0, b -> not test1(a,b))));
     minimize(Ds_c))



--**************************--
--  METHODS 	      	   	  --
--**************************--

--****************************************************************************************--
--  Methods for creating conditional independence statements from graphs and digraphs	  --
--****************************************************************************************--

----------------------------------------------------
-- pairMarkov
-- pairMarkov Graph does the following:
-- given a graph G, returns a list of triples {A,B,C}
-- where A,B,C are disjoint sets of the form:
-- for all non-edges {i,j}:  {i,j, all other vertices} 
-- pairMarkov Digraph does the following:
-- given a digraph G, returns a list of triples {A,B,C}
-- where A,B,C are disjoint sets, and for every vertex v
-- and non-descendent w of v,
-- {v, w, nondescendents(G,v) - w}
----------------------------------------------------

pairMarkov = method()
pairMarkov Graph := List => (G) -> (
     removeRedundants flatten apply(sort vertices G, v -> (
     	  apply(toList nonneighbors(G,v), non-> (
		    {set {v}, set {non}, set vertices G - set {v} - set {non}}
		    )
	       )
	  )
     )
)

pairMarkov Digraph := List => (G) -> (
     if isCyclic G then error("digraph must be acyclic");
     removeRedundants flatten apply(sort vertices G, v -> (
    	       ND := nondescendents(G,v);
     	       W := ND - parents(G,v);
     	       apply(toList W, w -> {set {v}, set{w}, ND - set{w}}))))
    

----------------------------------------------------
-- localMarkov Graph
-- localMarkov Digraph
-- Given a graph G, return a list of triples {A,B,C}
-- of the form {v, nonneighbors of v, all other vertices }
-- Given a digraph G, return a list of triples {A,B,C}
-- of the form {v, nondescendents - parents, parents}
----------------------------------------------------

localMarkov = method()
localMarkov Graph := List =>  (G) -> (
     removeRedundants apply(sort vertices G, v -> (
	   {set {v},  nonneighbors(G,v), set vertices G - set {v} - nonneighbors(G,v)}
		    )
	       )
	  )		
     	 
localMarkov Digraph := List =>  (G) -> (
     if isCyclic G then error("digraph must be acyclic");
     result := {};
     scan(sort vertices G, v -> (
	       ND := nondescendents(G,v);
	       P := parents(G,v);
	       if #(ND - P) > 0 then
	         result = append(result,{set{v}, ND - P, P})));
     removeRedundants result)


------------------------------------------------------------------------------
-- globalMarkov Graph
-- globalMarkov Digraph
-- Given a graph G, return a list of triples {A,B,C}
-- of the form {A,B,C} if C separates A and B in the graph.
-- Given a graph G, return a complete list of triples {A,B,C}
-- so that A and B are d-separated by C (in the graph G).
-- If G is large, this should maybe be rewritten so that
-- one huge list of subsets is not made all at once
------------------------------------------------------------------------------

globalMarkov = method()
globalMarkov Graph := List => (G) ->(
     AX := subsets vertices G;
     AX = drop(AX,1); -- drop the empty set
     AX = drop(AX,-1); -- drop the entire set
     -- product should apply * to entire list. note that  * of sets is intersection.
     statements := for A in AX list (
	  B:=product apply(A, v-> nonneighbors(G,v) ); --this is the list of all B's 
	  if #B === 0 then continue; -- need both A and B to be nonempty
     	  C := (vertices G) - set A - B ;
     	  {set A,  B, set C}
	  );
    removeRedundants  statements
    ) 
 
globalMarkov Digraph := List => (G) -> (
     V := sort vertices G;
     result := {};
     AX := subsets V;
     AX = drop(AX,1); -- drop the empty set
     AX = drop(AX,-1); -- drop the entire set
     scan(AX, A -> (
	       A = set A;
	       Acomplement := toList(set V - A);
	       CX := subsets Acomplement;
	       CX = drop(CX,-1); -- we don't want C to be the entire complement
	       scan(CX, C -> (
			 C = set C;
			 B := bayesBall(A,C,G);
			 if #B > 0 then (
			      B1 := {A,B,C};
			      if all(result, B2 -> not equivStmts(B1,B2))
			      then 
			          result = append(result, {A,B,C});
	       )))));
     removeRedundants result
     )



--*************************************************************************
--  Methods for creating polynomial rings that carry information about   --
--  random variables and/or underlying graph, digraph or mixed graph     --
--*************************************************************************

------------------------------------------------------------------------------------------------
-- markovRing Sequence
-- outputs a polynomial ring of ....***********************....??????????????????????????????????????????????????????
-- d should be a sequence of integers di >= 1
--
-- NOTE: there is a mutable hash table of all Markov rings created, so as to not re-create rings!
-- the hashtable is indexed by the sequence d, the coefficient ring kk, and the variable name p, 
-- as this information identifies the Markov ring uniquely. 
------------------------------------------------------------------------------------------------

markovRingList := new MutableHashTable;

markovRing = method(Dispatch=>Thing, Options=>{Coefficients=>QQ,VariableName=>getSymbol "p"})
markovRing Sequence := Ring => opts -> d -> (
     if any(d, di -> not instance(di,ZZ) or di <= 0)
     then error "markovRing expected positive integers";
     kk := opts.Coefficients;
     p := opts.VariableName;
     if (not markovRingList#?(d,kk,toString p)) then (
     	  start := (#d):1;
	  vlist := start .. d;
	  R := kk(monoid [p_start .. p_d, MonomialSize=>16]);
	  R.markovRingData = d;
	  H := new HashTable from apply(#vlist, i -> vlist#i => R_i);
	  R.markovVariables = H;
	  markovRingList#(d,kk,toString p) = R;
	  );
     markovRingList#(d,kk,toString p))



------------------------------------------------------------------
-- gaussianRing ZZ
-- gaussianRing Graph 
-- gaussianRing Digraph
-- gaussianRing MixedGraph
-- NOTE: the mutable hash table of all gaussian rings created is indexed by:
--     (coefficient field, variable name, number of r.v.'s) --in case of ZZ input
--     (coefficient field, variable name, vertices of the directed graph) --in case of Digraph input
--     (coefficient field, variable name, whole undirected graph) --in case of Graph input
------------------------------------------------------------------

gaussianRingList := new MutableHashTable;

gaussianRing = method(Dispatch=>Thing, Options=>{Coefficients=>QQ, sVariableName=>getSymbol "s", lVariableName=>getSymbol "l", 
	  pVariableName=>getSymbol "p", kVariableName=>getSymbol "k",})
gaussianRing ZZ :=  Ring => opts -> (n) -> (
     -- s_{1,2} is the (1,2) entry in the covariance matrix.
     -- this assumes r.v.'s are labeled by integers.
     s := if instance(opts.sVariableName,Symbol) then opts.sVariableName else opts.sVariableName;
     kk := opts.Coefficients;
     if (not gaussianRingList#?(kk,s,n)) then ( 
	  --(kk,s,n) uniquely identifies gaussianRing in case of ZZ input.
     w := flatten toList apply(1..n, i -> toList apply(i..n, j -> (i,j)));
     v := apply (w, ij -> s_ij);
     R := kk(monoid [v, MonomialSize=>16]);
     R.gaussianRingData = n; 
     H := new HashTable from apply(#w, i -> w#i => R_i); 
     R.gaussianVariables = H;
     gaussianRingList#((kk,s,n)) = R;); 
     gaussianRingList#((kk,s,n))
     )

gaussianRing Graph := Ring => opts -> (g) -> (
    bb := graph g;
    vv := sort vertices g;
    s := opts.sVariableName;
    k := opts.kVariableName;
    kk := opts.Coefficients;
    if (not gaussianRingList#?(kk,s,k,bb)) then ( 
	 --(kk,s,k,bb) uniquely identifies gaussianRing in case of Graph input.
    sL := delete(null, flatten apply(vv, x-> apply(vv, y->if pos(vv,x)>pos(vv,y) then null else s_(x,y))));
    kL := join(apply(vv, i->k_(i,i)),delete(null, flatten apply(vv, x-> apply(toList bb#x, y->if pos(vv,x)>pos(vv,y) then null else k_(x,y)))));
    m := #kL; --eliminate the k's 
    R := kk(monoid [kL,sL,MonomialOrder => Eliminate m, MonomialSize=>16]); 
    R#numberOfEliminationVariables = m;
    R.gaussianRingData = {#vv,s,k};
    R.graph = g;
    gaussianRingList#((kk,s,k,bb)) = R;); 
    gaussianRingList#((kk,s,k,bb))
    )

gaussianRing Digraph :=  Ring => opts -> (G) -> (
     -- Input is a Digraph G, 
     -- we read off the list of labels from the vertices.
     -- This is done to avoid any ordering confusion. 
     s := if instance(opts.sVariableName,Symbol) then opts.sVariableName else opts.sVariableName;
     kk := opts.Coefficients;
     vv := sort vertices G; 
     if (not gaussianRingList#?(kk,s,vv)) then ( 
	  --(kk,s,vv) uniquely identifies gaussianRing in case of Digraph input.
     w := delete(null, flatten apply(vv, i -> apply(vv, j -> if pos(vv,i)>pos(vv,j) then null else (i,j))));
     v := apply (w, ij -> s_ij);
     R := kk(monoid [v, MonomialSize=>16]);
     R.gaussianRingData = #vv;
     H := new HashTable from apply(#w, i -> w#i => R_i); 
     R.gaussianVariables = H;
     R.digraph = G; --changed 8sep2011-sonja ---this is new. we use this a lot for the undirected case so why not try this too... --- sonja 28july2011
     gaussianRingList#((kk,s,vv)) = R;); 
     gaussianRingList#((kk,s,vv))
     )


gaussianRing MixedGraph := Ring => opts -> (g) -> (
     G := graph collateVertices g;
     dd := graph G#Digraph;
     bb := graph G#Bigraph;
     vv := sort vertices g;
     s := opts.sVariableName;
     l := opts.lVariableName;
     p := opts.pVariableName;
     kk := opts.Coefficients;          
     if (not gaussianRingList#?(kk,s,l,p,vv)) then ( 
	  --(kk,s,l,p,vv) uniquely identifies gaussianRing in case of MixedGraph input.
     sL := delete(null, flatten apply(vv, x-> apply(vv, y->if pos(vv,x)>pos(vv,y) then null else s_(x,y))));
     lL := delete(null, flatten apply(vv, x-> apply(toList dd#x, y->l_(x,y))));	 
     pL := join(apply(vv, i->p_(i,i)),delete(null, flatten apply(vv, x-> apply(toList bb#x, y->if pos(vv,x)>pos(vv,y) then null else p_(x,y)))));
     m := #lL+#pL;
     R := kk(monoid [lL,pL,sL,MonomialOrder => Eliminate m, MonomialSize=>16]);
     R#numberOfEliminationVariables = m;
     R.gaussianRingData = {#vv,s,l,p};
     R.mixedGraph = g;
     gaussianRingList#((kk,s,l,p,vv)) = R;); 
     gaussianRingList#((kk,s,l,p,vv))
     )




--************************************************************************
--  Methods for creating matrices relevant for the graphical models     --
-- (covariance matrix, matrices whose minors vanish on the model)       --
--************************************************************************

------------------------------------------------------------------
-- undirectedEdgesMatrix Ring 
------------------------------------------------------------------

undirectedEdgesMatrix = method()
undirectedEdgesMatrix Ring := Matrix =>  R -> (
     if not (R.?graph or R.?gaussianRingData) then error "expected a ring created with gaussianRing graph";
     g := R.graph;
     bb:= graph g;
     vv := sort vertices g;
     n := R.gaussianRingData#0; --number of vertices
     p := value R.gaussianRingData#2;-- this p is actually k in this case (in name).
     PM := mutableMatrix(R,n,n);
     scan(vv,i->PM_(pos(vv,i),pos(vv,i))=p_(i,i));
     scan(vv,i->scan(toList bb#i, j->PM_(pos(vv,i),pos(vv,j))=if pos(vv,i)<pos(vv,j) then p_(i,j) else p_(j,i)));
     matrix PM) 



------------------------------------------------------------------
-- directedEdgesMatrix Ring 
------------------------------------------------------------------

directedEdgesMatrix = method()
directedEdgesMatrix Ring := Matrix => R -> (
     if not R.?gaussianRingData then error "expected a ring created with gaussianRing";     
     g := R.mixedGraph;
     G := graph collateVertices g;
     dd := graph G#Digraph;
     vv := sort vertices g;
     n := R.gaussianRingData#0;
     l := value R.gaussianRingData#2;
     LM := mutableMatrix(R,n,n);
     scan(vv,i->scan(toList dd#i, j->LM_(pos(vv,i),pos(vv,j))=l_(i,j)));
     matrix LM) 


------------------------------------------------------------------
-- bidirectedEdgesMatrix Ring
------------------------------------------------------------------

bidirectedEdgesMatrix = method()
bidirectedEdgesMatrix Ring := Matrix => R -> (
     if not R.?gaussianRingData then error "expected a ring created with gaussianRing";
     g := R.mixedGraph;     
     G := graph collateVertices g;
     bb := graph G#Bigraph;
     vv := sort vertices g;
     n := R.gaussianRingData#0;
     p := value R.gaussianRingData#3;
     PM := mutableMatrix(R,n,n);
     scan(vv,i->PM_(pos(vv,i),pos(vv,i))=p_(i,i));
     scan(vv,i->scan(toList bb#i, j->PM_(pos(vv,i),pos(vv,j))=if pos(vv,i)<pos(vv,j) then p_(i,j) else p_(j,i)));
     matrix PM) 
 
 
 
------------------------------------------------------------------
-- markovMatrices(Ring,List,List) 
-- markovMatrices(Ring,List)
------------------------------------------------------------------

markovMatrices = method()
markovMatrices(Ring,List,List) := (R,VarNames,Stmts) -> (
     -- R should be a markovRing, G a digraph 
     -- and Stmts is a list of
     -- independence statements
     if not R.?markovRingData then error "expected a ring created with markovRing";
     d := R.markovRingData;
     if not isSubset ( set unique flatten flatten Stmts,  set VarNames)  then error "variables names in statements do not match list of random variable names";
     flatten apply(Stmts, stmt -> (
	       Avals := possibleValues(d, apply( stmt#0, i ->  pos( VarNames,i)) );
	       Bvals := possibleValues(d, apply( stmt#1, i ->  pos( VarNames,i)) );
	       Cvals := possibleValues(d, apply( stmt#2, i ->  pos( VarNames,i)) );
     	       apply(Cvals, c -> (
                  matrix apply(Avals, 
		       a -> apply(Bvals, b -> (
				 e := toSequence(toList a + toList b + toList c);
		      		 prob(R,e))))))))
    )

markovMatrices(Ring,List) := (R,Stmts) -> (
     -- R should be a markovRing, G a digraph 
     -- and Stmts is a list of
     -- independence statements
     if not R.?markovRingData then error "expected a ring created with markovRing";
     d := R.markovRingData;
     if not isSubset ( set unique flatten flatten Stmts,  set( 1..#d) )  then error "variables names in statements do not match list of random variable names";
     VarNames := toList (1..#d);
     flatten apply(Stmts, stmt -> (
	       Avals := possibleValues(d, apply( stmt#0, i ->  pos( VarNames,i)) );
	       Bvals := possibleValues(d, apply( stmt#1, i ->  pos( VarNames,i)) );
	       Cvals := possibleValues(d, apply( stmt#2, i ->  pos( VarNames,i)) );
     	       apply(Cvals, c -> (
                  matrix apply(Avals, 
		       a -> apply(Bvals, b -> (
				 e := toSequence(toList a + toList b + toList c);
		      		 prob(R,e))))))))
    )



------------------------------------------------------------------
-- covarianceMatrix(Ring)
------------------------------------------------------------------

covarianceMatrix = method()
covarianceMatrix(Ring) := Matrix => (R) -> (
       if not R.?gaussianRingData then error "expected a ring created with gaussianRing";    
       if R.?graph then (  
     	    g:=R.graph;
	    vv := sort vertices g;
     	    n := R.gaussianRingData#0;
     	    s := value R.gaussianRingData#1;
     	    SM := mutableMatrix(R,n,n);
     	    scan(vv,i->scan(vv, j->SM_(pos(vv,i),pos(vv,j))=if pos(vv,i)<pos(vv,j) then s_(i,j) else s_(j,i)));
     	    matrix SM	    
	    ) 
       else if R.?mixedGraph then (  
     	    g = R.mixedGraph;
	    vv = sort vertices g;
     	    n = R.gaussianRingData#0;
     	    s = value R.gaussianRingData#1;
     	    SM = mutableMatrix(R,n,n);
     	    scan(vv,i->scan(vv, j->SM_(pos(vv,i),pos(vv,j))=if pos(vv,i)<pos(vv,j) then s_(i,j) else s_(j,i)));
     	    matrix SM	    
	    ) 
       else (
	    n =R.gaussianRingData; 
	    genericSymmetricMatrix(R,n)
	    )
  )



------------------------------------------------------------------
-- gaussianMatrices(Ring,List)
------------------------------------------------------------------

gaussianMatrices = method()
gaussianMatrices(Ring,List) := List =>  (R,Stmts) -> (
        if not (R.?gaussianRingData) then error "expected a ring created with gaussianRing";
        if R.?graph then (
	   g := R.graph;
           vv := sort vertices g;
	   if not isSubset ( set unique flatten flatten Stmts,  set vv)  then error "variables names in statements do not match list of random variable names";
           SM := covarianceMatrix(R);
           apply(Stmts, s -> 
	       submatrix(SM, apply(s#0,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) , 
		    apply(s#1,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) ) ) 
          )
        else if R.?digraph then (
	   g= R.digraph;
           vv = sort vertices g;
	   if not isSubset ( set unique flatten flatten Stmts,  set vv)  then error "variables names in statements do not match list of random variable names";
           SM = covarianceMatrix(R);
           apply(Stmts, s ->  
	       submatrix(SM, apply(s#0,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) , 
		    apply(s#1,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) ) ) 
          )
        else (
           vv = toList (1..R.gaussianRingData);
	   if not isSubset ( set unique flatten flatten Stmts,  set vv)  then error "variables names in statements do not match list of random variable names";
	   SM = covarianceMatrix(R);
           apply(Stmts, s->  
	       submatrix(SM, apply(s#0,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) , 
		    apply(s#1,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) ) )
	  )
     
     )


--******************************************************************--
--  Methods for creating ideals that vanish for a graphical model   --
--******************************************************************--

------------------------------------------------------------------
-- conditionalIndependenceIdeal (Ring,List)
-- conditionalIndependenceIdeal (Ring,List,List)
------------------------------------------------------------------
 
conditionalIndependenceIdeal=method()
conditionalIndependenceIdeal (Ring,List) := Ideal => (R,Stmts) ->(
     if not (R.?gaussianRingData or R.?markovRingData) then error "expected a ring created with gaussianRing or markovRing";
     if #Stmts === 0 then (ideal(0_R))
     else ( 
     	  if R.?gaussianRingData then (      
               if R.?graph then (
     		    if not isSubset ( set unique flatten flatten Stmts,  set vertices(R.graph))  then error "variables names in statements do not match variable names in the Gaussian ring";
	   	    g := R.graph;
           	    vv := sort vertices g;
           	    SM := covarianceMatrix(R);
           	    sum apply(Stmts, s -> minors(#s#2+1, 
	       		      submatrix(SM, apply(s#0,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) , 
		    		   apply(s#1,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) ) )) 
          	    )
               else if R.?digraph then (
     		    if not isSubset ( set unique flatten flatten Stmts,  set vertices(R.digraph))  then error "variables names in statements do not match variable names in the Gaussian ring";
	   	    g= R.digraph;
           	    vv = sort vertices g;
           	    SM = covarianceMatrix(R);
           	    sum apply(Stmts, s -> minors(#s#2+1, 
	       		      submatrix(SM, apply(s#0,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) , 
		    		   apply(s#1,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) ) )) 
          	    )
	       else if R.?mixedGraph then (
     		    if not isSubset ( set unique flatten flatten Stmts,  set vertices(R.mixedGraph))  then error "variables names in statements do not match variable names in the Gaussian ring";
	   	    g= R.mixedGraph;
           	    vv = sort vertices g;
           	    SM = covarianceMatrix(R);
           	    sum apply(Stmts, s -> minors(#s#2+1, 
	       		      submatrix(SM, apply(s#0,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) , 
		    		   apply(s#1,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) ) )) 
          	    )
               else (
	   	    vv = toList (1..R.gaussianRingData);
     		    if not isSubset ( set unique flatten flatten Stmts,  set vv)  then error "variables names in statements do not match variable names in the Gaussian ring";
	   	    SM = covarianceMatrix(R);
           	    sum apply(Stmts, s -> minors(#s#2+1, 
	       		      submatrix(SM, apply(s#0,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) , 
		    		   apply(s#1,x->pos(vv,x)) | apply(s#2,x->pos(vv,x)) ) ))
	  	    )
               )
     	  else (
               if not isSubset ( set unique flatten flatten Stmts,  set toList (1..#R.markovRingData))  then error "variables names in statements do not match variable names in the markov ring.";
	       M := markovMatrices(R,Stmts);
	       sum apply(M, m -> minors(2,m)) 
	       )
     	  )	   
)     

conditionalIndependenceIdeal (Ring,List,List) := Ideal => (R,VarNames,Stmts) ->(
     if not R.?markovRingData then error "expected a ring created with markovRing";
     if not isSubset ( set unique flatten flatten Stmts,  set VarNames)  then error "variables names in statements do not match list of random variable names";
     if #Stmts === 0 then ideal(0_R)
     else (	  	
     	  M := markovMatrices(R,VarNames,Stmts);
     	  sum apply(M, m -> minors(2,m)) 
     	  )
     )	   



------------------------------------------------------------------
-- gaussianParametrization (Ring,MixedGraph)
------------------------------------------------------------------

gaussianParametrization = method(Options=>{SimpleTreks=>false})
gaussianParametrization (Ring,MixedGraph) := Matrix => opts -> (R,g) -> (
     if not R.?gaussianRingData then error "expected a ring created with gaussianRing";     
     S := covarianceMatrix R;    
     W := bidirectedEdgesMatrix R;     
     L := directedEdgesMatrix R;
     Li := inverse(1-matrix(L));
     M := transpose(Li)*matrix(W)*Li;
     if opts.SimpleTreks then (
       n := R.gaussianRingData#0;
       P := matrix {apply(n,i->W_(i,i)-M_(i,i)+1)};
       Q := apply(n,i->W_(i,i)=>P_(0,i));
       scan(n,i->P=sub(P,Q));
       sub(M,apply(n,i->W_(i,i)=>P_(0,i))))
     else
       M)



------------------------------------------------------------------
-- gaussianVanishingIdeal Ring
------------------------------------------------------------------

gaussianVanishingIdeal=method()
gaussianVanishingIdeal Ring := Ideal => R -> (
    if not (R.?gaussianRingData) then error "expected a ring created with gaussianRing";
    if R.?graph then ( 
       --currently works on really small examples! future work to make faster...    
       K:= undirectedEdgesMatrix R;
       adjK := sub(det(K)*inverse(sub(K,frac R)), R);
       Itemp:=saturate(ideal (det(K)*covarianceMatrix(R) - adjK), det(K));
       ideal selectInSubring(1, gens gb Itemp))
    else if R.?digraph then (
       G := R.digraph;
       vv := sort vertices G;
       n := #vv;
       v := (topSort G)#map;
       v = hashTable apply(keys v, i->v#i=>i);
       v = apply(n,i->v#(i+1));
       P := toList apply(v, i -> toList parents(G,i));
       nx := # gens R;
       ny := max(P/(p->#p));
       x := local x;
       y := local y;
       S := (coefficientRing R)[x_0 .. x_(nx-1),y_0 .. y_(ny-1)];
       newvars := apply(ny, i -> y_i);
       L := keys R.gaussianVariables;
       s := hashTable apply(nx,i->L#i=>x_i);
       sp := (i,j) -> if pos(vv,i) > pos(vv,j) then s#(j,i) else s#(i,j);
       I := trim ideal(0_S);
       for i from 1 to n-1 do (
     	   J := ideal apply(i, j -> sp(v#j,v#i) - sum apply(#P#i, k ->y_k * sp(v#j,P#i#k)));
     	   I = eliminate(newvars, I + J););
       F := map(R,S,apply(nx,i->x_i=>R.gaussianVariables#(L_i))|apply(newvars,i->i=>0));
       F(I))
     else if R.?mixedGraph then (
       G = R.mixedGraph;
       if (#edges(G#graph#Graph) > 0) then error "This function is currently only implemented for mixed graphs without undirected part"; 
       if (isCyclic G#graph#Digraph == true) then error "Directed part of mixed graph must be acyclic";
       S = covarianceMatrix R;    
       W := bidirectedEdgesMatrix R;     
       L = directedEdgesMatrix R;
       Li := inverse(1-matrix(L));
       M := transpose(Li)*matrix(W)*Li;
       tempideal := ideal(S-M);
       m:= (R#numberOfEliminationVariables)-1;
       elimvarlist := flatten entries (vars(R))_{0..m};
       I = trim ideal(0_R);
       I = eliminate(elimvarlist,tempideal)
     )
)

------------------------------------------------------------------
-- discreteVanishingIdeal (Ring,Digraph)
------------------------------------------------------------------

discreteVanishingIdeal=method()
discreteVanishingIdeal (Ring, Digraph)  := Ideal => (R, G) -> (
     if not (R.?markovRingData) then error "expected a ring created with markovRing";
     d := R.markovRingData;
     n := #d; 
     if not (#vertices(G) == n) then error "Number of vertices of graph does not match size of ring";
     H := topSort G;
     shuffle := apply(sort vertices G, v -> H#map#v);
     dshuff := toSequence d_(shuffle - toList (n:1));
     R1 := markovRing(dshuff , VariableName => getSymbol"p");     
     p := j -> R1.markovVariables#j;
     I := trim ideal(0_R1);     
     SortedG := H#"newDigraph"; --Note: "" is there because Graphs.m2 is silly and this key is an unexported string!~Sonja
     a := local a;
     S := local S;
     apply(2..n, i -> (
         familyi := append(toList parents(SortedG,i),i);
         tempd := toSequence dshuff_(familyi - toList (#familyi: 1));
	 F := inverseMarginMap(i,R1);
	 I = F(I);
         S = markovRing( tempd, VariableName => getSymbol"a");	
	 a = j1 -> S.markovVariables#j1;
	 T := R1**S;
	 newI := sub(I, T);
	 di := toSequence flatten toList append( dshuff_(toList(0..(i-1))), toList ((n-i):1));
	 indexset :=  (n:1)..di;
	 newI = newI + ideal apply(indexset, j ->  (
		  ajindex := toSequence j_(familyi - toList (#familyi: 1));
		  sub(p j,T) - (sum apply(apply(dshuff_(i-1), k -> replace(i-1, k+1, j)), 
			    l-> sub(p l,T)))*sub(a ajindex,T)) );
	 indexset = (#tempd:1)..tempd;
	 newI = newI + ideal apply(indexset, j -> 1 - sum(apply(apply(dshuff_(i-1), k-> replace(#tempd-1,k+1,j)), 
			    l -> sub(a l, T))));
         J := eliminate(flatten entries sub(vars S, T), newI);
	 I = sub(J,R1)        
	 )     
      );
      inverseshuff := toList apply(1..n, i -> pos(shuffle,i));
      q := j -> R.markovVariables#j;
      F1 := map(R,R1, toList apply((n:1)..dshuff, j ->  q (toSequence j_inverseshuff)));
      F1(I)   
)
 
------------------------------------------------------------------
-- trekSeparation MixedGraph
------------------------------------------------------------------

trekSeparation = method()
trekSeparation MixedGraph := List => (g) -> (
    G := graph collateVertices g;
    dd := graph G#Digraph;
    bb := graph G#Bigraph; 
    vv := sort vertices g;
    -- Construct canonical double DAG cdG associated to mixed graph G:
    cdG:= digraph join(
      apply(vv,i->{(1,i),join(
        apply(toList parents(G#Digraph,i),j->(1,j)),
        {(2,i)}, apply(toList bb#i,j->(2,j)))}),
      apply(vv,i->{(2,i),apply(toList dd#i,j->(2,j))}));
    aVertices := apply(vv, i->(1,i));
    bVertices := apply(vv, i->(2,i));
    allVertices := aVertices|bVertices;
    statements := {};
    cdC0 := new MutableHashTable;
    cdC0#cache = new CacheTable from {};
    cdC0#graph = new MutableHashTable from apply(allVertices,i->{i,cdG#graph#i});
    cdC := new Digraph from cdC0;
    for CA in (subsets aVertices) do (
      for CB in (subsets bVertices) do (
	CAbin := setToBinary(aVertices,CA);
	CBbin := setToBinary(bVertices,CB);
	if CAbin <= CBbin then (
          C := CA|CB;
	  scan(allVertices,i->cdC#graph#i=cdG#graph#i);
          scan(C, i->scan(allVertices, j->(
	    cdC#graph#i=cdC#graph#i-{j};
	    cdC#graph#j=cdC#graph#j-{i};)));
	  Alist := delete({},subsetsBetween(CA,aVertices));
          while #Alist > 0 do (
	    minA := first Alist;
	    pC := reachable(cdC,set minA);
	    A := toList ((pC*(set aVertices)) + set CA);
	    Alist = Alist - (set subsetsBetween(minA,A));
	    B := toList ((set bVertices) - pC);
	    -- remove redundant statements:
	    if #CA+#CB < min{#A,#B} then (
	    if not ((CAbin==CBbin) and (setToBinary(aVertices,A) > setToBinary(bVertices,B))) then (
	      nS := {apply(A,i->i#1),apply(B,i->i#1),apply(CA,i->i#1),apply(CB,i->i#1)};
	      appendnS := true;
	      statements = select(statements, cS->
		if cS#0===nS#0 and cS#1===nS#1 then (
		  if isSubset(cS#2,nS#2) and isSubset(cS#3,nS#3) then 
		    (appendnS = false; true)
		  else if isSubset(nS#2,cS#2) and isSubset(nS#3,cS#3) then 
		    false
		  else
		    true)
		else if cS#2===nS#2 and cS#3===nS#3 then (
		  if isSubset(cS#0,nS#0) and isSubset(cS#1,nS#1) then 
		    false
		  else if isSubset(nS#0,cS#0) and isSubset(nS#1,cS#1) then 
		    (appendnS = false; true)
		  else
		    true)		  
		else true);
              if appendnS then statements = append(statements, nS);););););););
    statements)


------------------------------------------------------------------
-- trekIdeal (Ring,MixedGraph)
-- trekIdeal (Ring,Graph)
-- trekIdeal (Ring,Digraph)
-- NOTE: currently, trekSeparation only works with directed and bidirected edges, which affects this function
------------------------------------------------------------------

trekIdeal = method()
trekIdeal (Ring,MixedGraph) := Ideal => (R,g) -> (
     if not R.?gaussianRingData  then error "expected a ring created with gaussianRing";
     if R.?mixedGraph then (
         if not sort (vertices (R.mixedGraph))  === sort (vertices (g)) then 
	     error "vertex labels of graph do not match labels in ring")
     else if R.?graph then (
         if not sort (vertices (R.graph))  === sort (vertices (g)) then 
	     error "vertex labels of graph do not match labels in ring")
     else if R.?digraph then (
         if not sort (vertices (R.digraph))  === sort (vertices (g)) then 
	     error "vertex labels of graph do not match labels in ring")
     else if not ( 1..R.gaussianRingData === sort vertices(g))  then 
         error "variables names in mixedGraph do not match variable names in the Gaussian ring";
     Stmts:= trekSeparation g;
     vv := sort vertices g;
     SM := covarianceMatrix R ;	
     sum apply(Stmts,s->minors(#s#2+#s#3+1, submatrix(SM,apply(s#0,x->pos(vv,x)),apply(s#1,x->pos(vv,x)))))
     )

trekIdeal (Ring,Graph) := Ideal => (R,g) -> (
     conditionalIndependenceIdeal(R,globalMarkov(g)) -- equivalent to trek ideal for undirected graphs
          )

trekIdeal (Ring,Digraph) := Ideal => (R,g) ->(
      trekIdeal (R, mixedGraph(g))
      )          



--********************************************************************************************************************************--
--  Methods for manipulating polynomial maps frequently used in graphical models
--********************************************************************************************************************************--

------------------------------------------------------------------
-- marginMap(ZZ,Ring)
-- Return the ring map F : R --> R such that
--   F p_(u1,u2,..., +, ,un) = p_(u1,u2,..., 1, ,un)
-- and
--   F p_(u1,u2,..., j, ,un) = p_(u1,u2,..., j, ,un), for j >= 2.
-- NOTE:      -- R should be a Markov ring
-----------------------------------------------------------------

marginMap = method()
marginMap(ZZ,Ring) := RingMap => (v,R) -> (
     if (not R.?markovRingData) then error "expected a ring created with markovRing";
     v = v-1;
     d := R.markovRingData;
     p := i -> R.markovVariables#i;
     F := toList apply(((#d):1) .. d, i -> (
	       if i#v > 1 then p i
	       else (
		    i0 := drop(i,1);
		    p i - sum(apply(toList(2..d#v), j -> (
			      newi := join(take(i,v), {j}, take(i,v-#d+1));
			      p newi))))));
     map(R,R,F))



------------------------------------------------------------------
-- inverseMarginMap(ZZ,Ring) 
-- Note: R should be a Markov ring
------------------------------------------------------------------

inverseMarginMap = method()
inverseMarginMap(ZZ,Ring) := RingMap => (v,R) -> (
     if (not R.?markovRingData) then error "expected a ring created with markovRing";
     v = v-1;
     d := R.markovRingData;
     p := i -> R.markovVariables#i;
     F := toList apply(((#d):1) .. d, i -> (
	       if i#v > 1 then p i
	       else (
		    i0 := drop(i,1);
		    p i + sum(apply(toList(2..d#v), j -> (
			      newi := join(take(i,v), {j}, take(i,v-#d+1));
			      p newi))))));
     map(R,R,F))


------------------------------------------------------------------
-- hiddenMap(ZZ,Ring)
-- creates a ring map inclusion F : S --> A.
--
-- what a TERRIBLE NONDESCRIPTIVE NAME!!!! ----
--
------------------------------------------------------------------

hiddenMap = method()
hiddenMap(ZZ,Ring) := RingMap => (v,A) -> (
     v = v-1;
     p := i -> A.markovVariables#i;
     if not A.?markovRingData then error "expected a ring created with markovRing";
     d := A.markovRingData;
     e := drop(d, {v,v});
     S := markovRing (e);
     dv := d#v;
     F := toList apply(((#e):1) .. e, i -> (
	       sum(apply(toList(1..dv), j -> (
			      newi := join(take(i,v), {j}, take(i,v-#d+1));
			      p newi)))));
     map(A,S,F))


------------------------------------------------------------------
-- identifyParameters (Ring,MixedGraph)
------------------------------------------------------------------

identifyParameters = method()
identifyParameters (Ring,MixedGraph) := HashTable => (R,g) -> (
     J := ideal unique flatten entries (covarianceMatrix(R)-gaussianParametrization(R,g));
     G := graph g;
     m := #edges(G#Digraph)+#edges(G#Bigraph)+#vertices(g);
     plvars := toList apply(0..m-1,i->(flatten entries vars R)#i);
     new HashTable from apply(plvars,t->{t,eliminate(delete(t,plvars),J)}))










     

--******************************************--
-- DOCUMENTATION     	       	    	    -- 
--******************************************--

beginDocumentation()

doc ///
  Key
    GraphicalModels
  Headline
    A package for discrete and Gaussian statistical graphical models 
  Description
  
    Text
      {\bf Graphical Models} is a package for algebraic statistics, it constructs ideals of discrete and 
      Gaussian graphical models. This package extends Markov.m2.
       
      This package constructs ideals of discrete Bayesian networks (directed acyclic graphs)
      as described in several places, including the paper: Luis David Garcia, Michael Stillman and Bernd Sturmfels,
      {\em The algebraic geometry of Bayesian networks}, J. Symbolic Comput., 39(3-4):331–355, 2005. 
      
      It also constructs ideals of Gaussian Bayesian networks and Gaussian graphical models 
      (graphs containing both directed and bidirected edges), as described in the papers:
      Seth Sullivant, {\em Algebraic geometry of Gaussian Bayesian networks}, Adv. in Appl. Math. 40 (2008), no. 4, 482--513; and 
      Seth Sullivant, Kelli Talaska and Jan Draisma, "Trek separation for Gaussian graphical models", 
      Annals of Statistics 38 no.3 (2010) 1665--1685. 
          
      The package also contains some procedures to solve the identifiability problem for 
      Gaussian graphical models as described in the paper: 
      Luis D. Garcia-Puente, Sarah Spielvogel and Seth Sullivant, {\em Identifying causal effects with computer algebra}, 
      Proceedings of the $26^{th}$ Conference of Uncertainty in Artificial Intelligence.
          
      Here is a typical use of this package.  We create the ideal in 16 variables whose zero set 
      represents the probability distributions on four binary random variables which satisfy the
      conditional independence statements coming from the "diamond" graph $4 \to 3, 2 \to 1$.
      
    Example
       G = digraph  {{1,{}},{2,{1}},{3,{1}},{4,{2,3}}}
       R = markovRing (2,2,2,2) -- this ring corresponds to four binary random variables
       S = globalMarkov G  
       I = conditionalIndependenceIdeal (R,S);
       netList pack(2,I_*)     
       
    Text
      Sometimes an ideal can be simplified by changing variables.  Very often, 
      by using @TO marginMap@
      such ideals can be transformed to binomial ideals.  This is the case here.
      
    Example
       F = marginMap (1,R)        
       J = F I; 
       netList pack (2,J_*)
       
    Text
      This ideal has 5 primary components.  The first component is the one that has statistical significance.
      It is the defining ideal of the variety parameterized by the 
      the factorization of the probability distributions 
      according to the graph G. The remaining components lie on the boundary of the simplex.
      
    Example  
      netList primaryDecomposition J
      
    Text
      The ideal in the next example correspond to a Gaussian graphical model on a graph with directed and bidirected edges.
      The method @TO trekIdeal@ computes the ideal based on the trek separation statements of the mixed graph.
      
    Example
      G = mixedGraph (digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
      R = gaussianRing G
      J = trekIdeal (R,G) 
      
    Text
      The following ideal corresponds to a set of conditional statements of 5 Gaussian random variables.
      
    Example
      R=gaussianRing 5
      S={{{1},{2},{3,4}}, {{2,3},{1},{5}}}
      I=conditionalIndependenceIdeal (R,S)    
      
    Text
      The following people have generously contributed their time and effort to this project:  
      
      Alexander Diaz,
      
      Shaowie Lin<@HREF"http://math.berkeley.edu/~shaowei/"@>,
      
      David Murrugarra<@HREF"http://www.math.vt.edu/people/davidmur/Home.html"@>.
      
  Caveat
     This package requires Graphs.m2, as a consequence it can do computations with graphs
     whose vertices are not necessarily labeled by integers. This could potentially create some confusion 
     regarding the joint probability distribution of discrete random variables. In order to avoid any ambiguity on
     the meaning of the symbol  
     $p_{i_1i_2\cdots i_n}$, GraphicalModels orders the vertices lexicographically. So 
     $p_{i_1i_2\cdots i_n} = p(X_1 = i_1, X_2 = i_2, \dots, X_n = i_n)$ where the labels
     $X_1,X_2,\dots,X_n$ have been ordered lexicographically. Therefore, the user is encouraged
     to label the vertices in a consistent way (all numbers, or all letters, etc).
///;

--------------------------------
-- Documentation pairMarkov ----
--------------------------------

doc ///
  Key
    pairMarkov
    (pairMarkov,Graph)
    (pairMarkov,Digraph)
  Headline
    Pairwise Markov statements for a graph or a  directed graph.
  Usage
    pairMarkov G
  Inputs
    G: 
      @ofClass {Graph,Digraph}@
  Outputs
    :List
      whose entries are triples $\{A,B,C\}$ representing pairwise Markov  conditional independence statements of the form
      ``$A$ is independent of $B$ given $C$'' that hold for $G$.
  Description
  
    Text
      Given an undirected graph $G$, pairwise Markov statements are statements of the form 
      \{$v$, $w$, all other vertices\}\   
      for each pair of non-adjacent vertices $v$ and $w$ of $G$.
      
      For example, for the undirected 5-cycle graph $G$, that is, the graph on $5$ vertices with edges 
      $a---b---c---d---e--a$, 
      we get the following pairwise Markov statements:
      
    Example
      G = graph({{a,b},{b,c},{c,d},{d,e},{e,a}})
      pairMarkov G
      
    Text
      Given a directed graph $G$, pairwise Markov statements are statements of the form \{$v$, $w$, nondescendents($G,v$)-$w$\}\ 
      for each vertex $v$ of $G$ and each non-descendent vertex $w$ of $v$. In other words, for every vertex $v$ of $G$ and each nondescendent $w$ of $v$, 
      this method returns the statement: $v$ is independent of $w$ given all other nondescendents. 
      
      For example, given the digraph $D$ on $7$ vertices with edges $1 \to 2, 1 \to 3, 2 \to 4, 2 \to 5, 3 \to 5, 3 \to 6, 4 \to 7, 5 \to 7$, and $6\to 7$, 
      we get the following pairwise Markov statements:
      
    Example
      D = digraph {{1,{2,3}}, {2,{4,5}}, {3,{5,6}}, {4,{7}}, {5,{7}},{6,{7}},{7,{}}}
      netList pack (3, pairMarkov D)
      
    Text
      Note that the method displays only non-redundant statements.
      
  SeeAlso
    localMarkov 
    globalMarkov
///

--------------------------------
-- Documentation localMarkov ---
--------------------------------

doc ///
  Key
    localMarkov
    (localMarkov,Graph)
    (localMarkov,Digraph)
  Headline
    Local Markov statements for a graph or a directed graph.
  Usage
    localMarkov G
  Inputs
    G:
      @ofClass {Graph,Digraph}@ 
  Outputs
    :List
      whose entries are triples $\{A,B,C\}$ representing local Markov  conditional independence statements of the form
      ``$A$ is independent of B given C'' that hold for G.
  Description
  
    Text
      Given an undirected graph $G$, a local Markov statement is of the form
      \{$v$, non-neighbours($v$), neighbours($v$)\} .
      That is, 
      every vertex $v$ of $G$ is independent of its non-neighbours given its neighbours.
      
      For example, for the undirected  5-cycle graph $G$, that is, the graph on 5 vertices with 
      $a---b---c---d---e---a$, 
      we get the following local Markov statements:
      
    Example
      G = graph({{a,b},{b,c},{c,d},{d,e},{e,a}})
      localMarkov G
      
    Text
      Given a directed graph $G$, local Markov statements are of the form
      \{$v$, nondescendents($v$) - parents($v$), parents($v$)\} .
      In other words, 
      every vertex $v$ of $G$ is independent of its nondescendents (excluding parents) given its parents. 
      
      For example, given the digraph $D$ on $7$ vertices with edges $1 \to 2, 1 \to 3, 2 \to 4, 2 \to 5, 3 \to 5, 3 \to 6, 4 \to 7, 5 \to 7$, and $6\to 7$, 
      we get the following local Markov statements:
      
    Example
      D = digraph {{1,{2,3}}, {2,{4,5}}, {3,{5,6}}, {4,{7}}, {5,{7}},{6,{7}},{7,{}}}
      netList pack (3, localMarkov D) 
      
    Text
      Note that the method displays only non-redundant statements.
  SeeAlso
    pairMarkov
    globalMarkov
///

--------------------------------
-- Documentation globalMarkov --
--------------------------------

doc ///
  Key
    globalMarkov
    (globalMarkov,Digraph)
    (globalMarkov,Graph)
  Headline
    Global Markov statements for a graph or a directed graph.
  Usage
    globalMarkov G
  Inputs
    G:
      @ofClass {Graph,Digraph}@     
  Outputs
    :List
      whose entries are triples {A,B,C} representing global Markov  conditional independence statements of the form
      ``A is independent of B given C'' that hold for G.
  Description
  
    Text
      Given an undirected graph $G$, a global Markov statement is of the form
      $\{A, B, C\}$, where the subset $C$ separates the subset $A$ from the subset $B$ in the graph $G$.
      
      For example, for the undirected  5-cycle graph $G$, that is, the graph on 5 vertices with 
      $a---b---c---d---e---a$, 
      we get the following global Markov statements:
      
    Example
      G = graph({{a,b},{b,c},{c,d},{d,e},{e,a}})
      globalMarkov G
      
    Text
      Given a directed graph $G$, global Markov states that      
      $A$ is independent of $B$ given $C$ for every triple of sets of vertices $A$, $B$, and $C$, 
      such that $A$ and $B$ are $d$-separated by $C$ (in the graph $G$).\break
       
      The global independent statements are computed using the Bayes ball algorithm,
      as described in the paper {\em Bayes-Ball: The Rational Pastime (for Determining Irrelevance and Requisite Information
      in Belief Networks and Influence Diagrams)} by Ross D. Shachter.
      
      For example, given the digraph $D$ on $7$ vertices with edges $1 \to 2, 1 \to 3, 2 \to 4, 2 \to 5, 3 \to 5, 3 \to 6, 4 \to 7, 5 \to 7$, and $6\to 7$, 
      we get the following global Markov statements:
      
    Example
      D = digraph {{1,{2,3}}, {2,{4,5}}, {3,{5,6}}, {4,{7}}, {5,{7}},{6,{7}},{7,{}}}
      netList pack (3, globalMarkov D) 
      
    Text
    
      Note that the method displays only non-redundant statements.
  Caveat
    -- If G is large, this should maybe be rewritten so that
    -- one huge list of subsets is not made all at once
  SeeAlso
    localMarkov
    pairMarkov
///

--------------------------------
-- Documentation marginMap    --
--------------------------------

doc ///
  Key
    marginMap
    (marginMap,ZZ,Ring)
  Headline
    Generates a linear map on joint distributions for discrete random variables replacing marginals for indeterminates.
  Usage
    marginMap(i,R)
  Inputs
    i:ZZ
      the index of the variable to marginalize
    R:Ring
      a markovRing
  Outputs
    :RingMap
  Description
    Text
      Let $p_{u_1,u_2,\dots, +,\dots,u_n}$ denote the linear form $p_{u_1,u_2,\dots, 1,\dots,u_n} + \dots + p_{u_1,u_2,\dots, d_i,\dots,u_n}$, where $d_i$ is the number of
      states of random variable $X_i$.
      
      The method marginMap returns the ring map $F : R \to R$ such that
      $ F(p_{u_1,u_2,\dots, +,\dots,u_n}) = p_{u_1,u_2,\dots,1,\dots,u_n}$ and
      $ F(p_{u_1,u_2,\dots, j,\dots,u_n}) = p_{u_1,u_2,\dots, j,\dots,u_n} $, for all $j\geq 2$.
      
    Example
      marginMap(1,markovRing(3,2))
      
    Text
      This linear transformation simplifies ideals and/or polynomials involving 
      $ p_{u_1,u_2,..., +,...,u_n} $. In some cases, the resulting ideals are toric 
      ideals as the example below shows. For more details 
      see the paper "Algebraic Geometry of Bayesian Networks" by Garcia, Stillman, and
      Sturmfels.
      
    Example
      G = digraph  {{1,{}},{2,{1}},{3,{1}},{4,{2,3}}}
      R = markovRing (2,2,2,2)
      S = globalMarkov G
      I = conditionalIndependenceIdeal (R,S)	
      F = marginMap(1,R)
      F I  
      
  SeeAlso
    hiddenMap
///

--------------------------------
-- Documentation hiddenMap    --
--------------------------------`

doc ///
  Key
    hiddenMap
    (hiddenMap,ZZ,Ring)
  Headline
    Creates a linear map from a ring of probability distributions among observed discrete random variables into a ring of probability distributions among observed variables and one hidden variable specified by the integer input.
  Usage
    phi = hiddenMap(i,R)
  Inputs
    i:ZZ
      the index corresponding to the hidden random variable
    R:Ring
      a Markov ring
  Outputs
    phi:RingMap
  Description
    Text
      A linear map from a ring of probability distributions among observed discrete random variables into 
      a ring of probability distributions among observed variables and one hidden variable specified by the integer input. 
      This method is used to work with Bayesian networks with hidden variables.
      For more details see the paper "Algebraic Geometry of Bayesian Networks"
      by Garcia, Stillman, and Sturmfels.
    Example
      hiddenMap(1,markovRing(2,3,2)) 
  SeeAlso
    marginMap
///

--------------------------------
-- Documentation markovRing   --
--------------------------------

doc ///
  Key
    markovRing
    (markovRing,Sequence)
    [markovRing, Coefficients]
    [markovRing, VariableName]
  Headline
    Ring of probability distributions on several discrete random variables.
  Usage
    markovRing(d) or markovRing(d,Coefficients=>Ring) or markovRing(d,Variable=>Symbol)
  Inputs
    d:Sequence
      with positive integer entries (d1,...,dr)
  Outputs
    R:Ring
      A polynomial ring with d1*d2*...*dr variables $p_{i_1,...,i_r}$,
      with each $i_j$ satisfying $1\leq i_j \leq d_j$.
  Consequences
    Item
      Information about this sequence of integers is placed into the ring, and is used 
      by other functions in this package.  Also, at most one ring for each such sequence
      is created: the results are cached.
  Description
    Text 
      The sequence $d$ represents the number of states each discrete random variable can take.
      For example, if there are four random variables with the following state space sizes
    Example
      d=(2,3,4,5)
    Text 
      the corresponding ring will have as variables all the possible joint 
      probability distributions for the four variables:
    Example
      R = markovRing d;
      numgens R
      R_0, R_1, R_119 --here are some of the variables in the ring
    Text
      If no coefficient choice is specified, the polynomial ring is created over the rationals. 
    Example
      coefficientRing R
    Text 
      If we prefer to have a different base field, the following command can be used:
    Example
      Rnew = markovRing (d,Coefficients=>CC); 
      coefficientRing Rnew
    Text
      We might prefer to give different names to our variables. The letter ''p'' suggests a joint probability, 
      but it might be useful to create a new ring where the variables have changed. This can easily be done
      with the following option:
    Example
      d=(1,2);
      markovRing (d,VariableName=>q);
      vars oo --here is the list of variables.
    Text
      -- The LIST OF FNS USING THIS FUNCTION SHOULD BE INSERTED AS WELL.
  SeeAlso
///

------------------------------------
-- Documentation Coefficients     --
------------------------------------

doc ///
  Key
    Coefficients
  Headline
    Optional input to choose the base field.
  Description
    Text
      Put {\tt Coefficients => r} for a choice of ring(field) r as an argument in 
      the function @TO markovRing@ or @TO gaussianRing@ 
  SeeAlso
    markovRing
    gaussianRing
///

------------------------------------
-- Documentation VariableName     --
------------------------------------

doc ///
  Key
    VariableName
  Headline
    Optional input to choose the letter for the variable name.
  Description
    Text
      Put {\tt VariableName => s} for a choice of a symbol s as an argument in 
      the function @TO markovRing@
  SeeAlso
    markovRing
///

------------------------------------
-- Documentation markovMatrices   --
------------------------------------

doc ///
  Key
    markovMatrices
    (markovMatrices,Ring,List)
    (markovMatrices,Ring,List,List) 
  Headline
    The matrices whose minors form the ideal associated to the list of independence statements of the graph.
  Usage
    markovMatrices(R,VarNames,S)
    markovMatrices(R,S)
  Inputs
    R:Ring
      R must be a markovRing
    VarNames:List
      of names of random variables in conditional independence statements in S.  If this is omited 
      it is assumed that these are integers 1 to n where n is the number of variables in the declaration of markovRing 
    S:List 
      of conditional independence statements that are true for the DAG G
  Outputs
    :List 
      whose elements are instances of Matrix. Minors of these matrices form the independence ideal for the independent statements of the Digraph.
  Description
    Text
      List of matrices encoding the independent statements of the Digraph G. The 2x2 minors of each matrix generate the ideal of 
      independence constraints of the Digraph G. the  This method 
      is used in markovIdeals. But it is exported to be able to see constraints not as 
      polynomials but as minors of matrices in this list. 
    Example
      VarNames = {a,b,c,d}
      S = {{{a},{c},{d}}}
      R = markovRing (4:2)
      L = markovMatrices (R,VarNames, S)
    Text
      Here is an example where the independence statements are extracted from a graph
    Example  
      G = graph{{a,b},{b,c},{c,d},{a,d}}
      S = localMarkov G
      R = markovRing (4:2)
      L = markovMatrices (R,vertices G,S)   
  SeeAlso
    markovRing
///

------------------------------------
-- Documentation gaussianRing     --
------------------------------------

doc ///
  Key 
    gaussianRing
    (gaussianRing,ZZ)
    (gaussianRing, Graph)
    (gaussianRing, Digraph)
    (gaussianRing, MixedGraph)
    [gaussianRing, Coefficients]
    [gaussianRing, sVariableName]
    [gaussianRing, lVariableName]
    [gaussianRing, pVariableName]
    [gaussianRing, kVariableName]
  Headline
    ring of gaussian correlations on n random variables
  Usage
    gaussianRing n 
    gaussianRing G 
    gaussianRing(n,Coefficients=>Ring) 
    gaussianRing(n,sVariableName=>Symbol)
  Inputs
    n:ZZ
      the number of random variables
    G:Graph
      @ofClass Graph@, or a directed acyclic graph @ofClass Digraph@, 
      or @ofClass MixedGraph@ with directed and bidirected edges
  Outputs
    :Ring
      a ring with indeterminates $s_{(i,j)}$ for $1 \leq i \leq j \leq n$, and
      additionally $l_{(i,j)}, w_{(i,j)}$ for mixed graphs
  Description
    Text
      The routines  @TO conditionalIndependenceIdeal@, @TO trekIdeal@, @TO covarianceMatrix@, 
      @TO undirectedEdgesMatrix@, @TO directedEdgesMatrix@, @TO bidirectedEdgesMatrix@, and
      @TO gaussianParametrization@ require that the ring be created by this function. 
    Example
      R = gaussianRing 5;
      gens R
      covarianceMatrix R
      
    Text
      For undirected graphs, ...
    Example
      G = graph({{a,b},{b,c},{c,d},{a,d}})
      R = gaussianRing G
      gens R
    Text
      Recovering the graph from the gaussian ring
    Example
      -- R#gaussianRing
      --R.graph  
      covarianceMatrix R
      undirectedEdgesMatrix R
    Text
      For directed graphs......
    Example
      G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}};
      R = gaussianRing G;
      --R.digraph --the digraph gets stored in the ring --CAN'T ACCESS IT; BUT CAN PEEK!
    Text
      For mixed graphs, there is a variable $l_{(i,j)}$ for
      each directed edge i->j, a variable $w_{(i,i)}$ for each node i, and a variable $w_{(i,j)}$ 
      for each bidirected edge i<->j.
    Example
      G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
      R = gaussianRing G
      gens R
      covarianceMatrix R
      directedEdgesMatrix R
      bidirectedEdgesMatrix R
  SeeAlso
    conditionalIndependenceIdeal
    covarianceMatrix
    directedEdgesMatrix
    bidirectedEdgesMatrix
    trekIdeal
///



---------------------------------------
-- Documentation gaussianMatrices    --
---------------------------------------

doc///
   Key
     gaussianMatrices
     (gaussianMatrices,Ring,List)
   Headline
     Matrices whose minors form the ideal corresponding to the conditional independence ideal
   Usage
     gaussianMatrices(R,S)
   Inputs
     R:Ring
       must be a gaussianRing
     G:Digraph
       a directed acyclic graph
     S:List
       of conditional independence statements
   Outputs
     :Matrix
       whose minors  form the ideal corresponding to the conditional independence ideal
   Description 
     Text
       This method displays a list of matrices whose minors generate the conditional independence ideal.  
       Some people might find this useful.
     Example
       R = gaussianRing 4;
       Stmts = {{{1,2},{3},{4}}, {{1},{3},{}}}
       gaussianMatrices(R,Stmts)
     Text
       If the gaussianRing is created with a graph G, then random variable names are obtained from the vertex labels of G:
     Example
       G = graph({{a,b},{b,c},{c,d},{d,e},{e,a}}) 
       R = gaussianRing G
       gaussianMatrices (R,globalMarkov G)
     Text
       If the gaussianRing is created with a digraph G, then random variable names are obtained from the vertex labels of G:
     Example
       G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
       R = gaussianRing G
       gaussianMatrices (R,globalMarkov G)
   SeeAlso
     gaussianRing
     conditionalIndependenceIdeal
///

---------------------------------------
-- Documentation covarianceMatrix    --
---------------------------------------

doc/// 
   Key
     covarianceMatrix
     (covarianceMatrix,Ring)
   Headline
     the covariance matrix of a gaussian graphical model
   Usage
     covarianceMatrix R
   Inputs
     R:Ring
       which should be a gaussianRing
   Outputs
     :Matrix
       the $n \times{} n$ covariance matrix of symbols where n is the number of vertices in $G$
   Description 
     Text
       If this function is called without a graph G, it is assumed that R is the gauss ring of a directed acyclic graph.
     Example
       G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
       R = gaussianRing G
       S = covarianceMatrix R
     Text
       Note that the covariance matrix is symmetric in the symbols.
     Example
       G = graph({{a,b},{b,c},{c,d},{a,d}})
       R = gaussianRing G
       S = covarianceMatrix R       
     Text
       Note that the covariance matrix is symmetric in the symbols.
     Example
       G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
       R = gaussianRing G
       S = covarianceMatrix R
   SeeAlso
     gaussianRing
     gaussianParametrization
     bidirectedEdgesMatrix
     directedEdgesMatrix
///

--------------------------------------------
-- Documentation bidirectedEdgesMatrix    --
--------------------------------------------

doc/// 
   Key
     bidirectedEdgesMatrix
     (bidirectedEdgesMatrix,Ring)
   Headline
     the matrix corresponding to the bidirected edges of a mixed graph
   Usage
     W = bidirectedEdgesMatrix R
   Inputs
     R:Ring
       which should be a gaussianRing
   Outputs
     S:Matrix
       the n x n symmetric matrix of symbols where we have $w_{(i,i)}$ for each vertex i, 
       $w_{(i,j)}$ if there is a bidirected edge between i and j, and 0 otherwise.
   Description 
     Text
       Note that this matrix is symmetric in the symbols.
     Example
       G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
       R = gaussianRing G
       S = bidirectedEdgesMatrix R
   SeeAlso
     gaussianRing
     gaussianParametrization
     covarianceMatrix
     directedEdgesMatrix
///

------------------------------------------
-- Documentation directedEdgesMatrix    --
------------------------------------------

doc/// 
   Key
     directedEdgesMatrix
     (directedEdgesMatrix,Ring)
   Headline
     the matrix corresponding to the directed edges of a mixed graph
   Usage
     L = directedEdgesMatrix R
   Inputs
     R:Ring
       which should be a gaussianRing
   Outputs
     L:Matrix
       the n x n matrix of symbols where we have $l_{(i,j)}$ if there is a directed edge i-->j, and 0 otherwise.
   Description 
     Text
       Note that this matrix is NOT symmetric in the symbols.
     Example
       G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
       R = gaussianRing G
       S = directedEdgesMatrix R
   SeeAlso
     gaussianRing
     gaussianParametrization
     covarianceMatrix
     bidirectedEdgesMatrix
///

----------------------------------------------
-- Documentation gaussianParametrization    --
----------------------------------------------

doc/// 
   Key
     gaussianParametrization
     (gaussianParametrization,Ring,MixedGraph)
     [gaussianParametrization, SimpleTreks]
   Headline
     the parametrization of the covariance matrix in terms of treks
   Usage
     M = gaussianParametrization(R,G)
   Inputs
     R:Ring
       which should be a gaussianRing
     G:MixedGraph
       mixed graph with directed and bidirected edges
   Outputs
     M:Matrix
       the parametrization of the covariance matrix in terms of treks
   Description 
     Text
       Given a mixed graph G with directed and bidirected edges, let L be the matrix corresponding to 
       the directed edges (see @TO directedEdgesMatrix@) and let W be the matrix corresponding to 
       the bidirected edges (see @TO bidirectedEdgesMatrix@). Then, the covariance matrix S 
       (see @TO covarianceMatrix@) of the random variables in the gaussian graphical model corresponding
       to the mixed graph G can be parametrized by the matrix equation $S = (I-L)^{-T}W(I-L)^{-1}$, where
       I is the identity matrix.
       
       The entry $S_{(i,j)}$ of the covariance matrix can also be written as the sum of all monomials corresponding
       to treks between vertices i and j. See @TO trekSeparation@ for the definition of a trek. The monomial corresponding
       to a trek is the product of all parameters associated to the directed and bidirected edges on the trek.
       
       The following example shows how to compute the ideal of the model using the parametrization.
     Example
       G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
       R = gaussianRing G
       S = covarianceMatrix(R)
       L = directedEdgesMatrix(R)
       W = bidirectedEdgesMatrix(R)       
       M = gaussianParametrization(R,G)
       J = delete(0_R, flatten entries (L|W))
       eliminate(J, ideal(S-M))
     Text
       This next example shows how to use the option @TO SimpleTreks@ to compute a parametrization using simple treks 
       instead of all treks. The resulting covariance matrix has diagonal entries equal to 1.
     Example
       G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
       R = gaussianRing G
       M = gaussianParametrization(R,G,SimpleTreks=>true)
   SeeAlso
     covarianceMatrix
     directedEdgesMatrix
     bidirectedEdgesMatrix
     trekSeparation
///

----------------------------------
-- Documentation SimpleTreks    --
----------------------------------

doc ///
  Key
    SimpleTreks
  Headline
    optional input to choose the type of parametrization in @TO gaussianParametrization@
  Description
    Text
      Put {\tt SimpleTreks => true} as an argument in the function @TO gaussianParametrization@ to compute 
      a parametrization of the covariance matrix S=(s_{(i,j)}) where s_{(i,j)} is the sum of monomials corresponding
      to simple treks between vertices i and j. Here, a simple trek is a trek (P_L,P_R) where the paths P_L and P_R 
      do not have any common vertices except perhaps at their source. See @TO trekSeparation@ for the definition of a trek.
      
      If the option {\tt SimpleTreks => false} is used, then the sum is over 
      all treks, and not just simple treks. 
  SeeAlso
    gaussianParametrization
///

-----------------------------------------
-- Documentation identifyParameters    --
-----------------------------------------

doc/// 
   Key
     identifyParameters
     (identifyParameters,Ring,MixedGraph)
   Headline
     solving the identifiability problem: expressing each parameter in terms of covariances 
   Usage
     H = identifyParameters(R,G)
   Inputs
     R:Ring
       which should be a gaussianRing
     G:MixedGraph
       mixed graph with directed and bidirected edges
   Outputs
     H:HashTable
       where H#p is the ideal of equations involving only the parameter p and the covariances s_{(i,j)}
   Description 
     Text
       If H#p contains a linear equation a*p+b where a is always nonzero, then p is identifiable.
       
       If H#p contains a linear equation a*p+b where a may be zero, then p is generically identifiable.
       
       If H#p contains a polynomial in p of degree d, then p is algebraically d-identifiable.
       
       If H#p does not contain any polynomial in p, then p is not generically identifiable.
     Example
       G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
       R = gaussianRing G
       H = identifyParameters(R,G)
   SeeAlso
     gaussianRing
///

--------------------------------
-- Documentation trekIdeal    --
--------------------------------

doc/// 
   Key
     trekIdeal
     (trekIdeal,Ring,MixedGraph)
     (trekIdeal,Ring,Digraph)
     (trekIdeal,Ring,Graph)
   Headline
     The trek separation ideal of a mixed graph ---IN PROCESS OF CHANGING THIS
   Usage
     I = trekIdeal(R,G) 
   Inputs
     R:Ring
       which should be a gaussianRing
     G:Graph
      @ofClass Graph@, or a directed acyclic graph @ofClass Digraph@, 
      or @ofClass MixedGraph@ with directed and bidirected edges
   Outputs
     I:Ideal
       the ideal of determinantal trek separation statements implied by the graph G.
   Description 
     Text  
       For mixed graphs, the ideal corresponding to all trek separation statements {A,B,CA,CB} (where A,B,CA,CB
       are disjoint lists of vertices of G) is generated by the r+1 x r+1 minors of the submatrix of the covariance matrix M = (s_{(i,j)}), whose
       rows are in A, and whose columns are in B, and where r = #CA+#CB.
       
       These ideals are described in more detail by Sullivant, Talaska and Draisma in "Trek Separation for Gaussian Graphical Models"
       and give all determinantal constraints on the covariance matrix of a gaussian graphical model.        
     Example
       G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
       R = gaussianRing G
       T = trekIdeal(R,G)
       ideal gens gb T
   Caveat
       trekSeparation is currently only implemented with mixedGraphs that have directed and 
       bidirected edges.  For undirected graphs G, the trekIdeal(R,G) is the same as 
       conditionalIndependenceIdeal(R,globalMarkov(G)), which is how the function is currently
       implemented in that case. 
   SeeAlso
     trekSeparation
///

-------------------------------------
-- Documentation trekSeparation    --
-------------------------------------

doc/// 
   Key
     trekSeparation
     (trekSeparation,MixedGraph)
   Headline
     the trek separation statements of a mixed graph 
   Usage
     trekSeparation(G)
   Inputs
     G:MixedGraph
       mixed graph with directed and bidirected edges
   Outputs
     :List
        of lists \{A,B,CA,CB\}, where (CA,CB) trek-separates A from B
   Description 
     Text
       A trek between vertices i and j in a mixed graph G with directed and bidirected edges is a triple 
       (P_L,P_R) where P_L is a directed path of directed edges with sink i and source k, P_R is a directed path
       of directed edges with sink j and source l, and either k=l or there is a bidirected edge between k and l.
       Let A,B,CA,CB be subsets of vertices of G. 
       
       We say that (CA,CB) trek-separates A from B in G if for every trek 
       (P_L,P_R) from a vertex in A to a vertex in B, either P_L contains a vertex in CA or P_R contains a vertex in CB.
       
       The function @TO trekSeparation@ returns a list of trek separation statements \{A,B,CA,CB\}\,where 
       #CA + #CB < min(#A, #B). Each statement is maximal in the ordering where \{A1,B1,CA,CB\}\,<\,\{A2,B2,CA,CB\}\,if A1 is a 
       subset of A2 and B1 is a subset of B2. Each statement is also unique up to symmetry, since \{B,A,CB,CA\}\,is a 
       trek separation statement if and only if \{A,B,CA,CB\}.
     Example
       G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
       S = trekSeparation G
   Caveat
       trekSeparation G is only implemented for mixedGraphs with directed and bidirected edges.    
   SeeAlso
     trekIdeal
///

------------------------------------
-- Documentation sVariableName     --
------------------------------------

doc ///
  Key
    sVariableName
  Headline
    Optional input to choose the letter for the variable name.
  Description
    Text
      Put {\tt sVariableName => stilde} for a choice of a symbol s as an argument in 
      the function @TO gaussianRing@
  SeeAlso
    gaussianRing
///
doc ///
  Key
    lVariableName
  Headline
    Optional input to choose the letter for the variable name.
  Description
    Text
      Put {\tt lVariableName => ltilde} for a choice of a symbol l as an argument in 
      the function @TO gaussianRing@
  SeeAlso
    gaussianRing
///
doc ///
  Key
    pVariableName
  Headline
    Optional input to choose the letter for the variable name.
  Description
    Text
      Put {\tt pVariableName => ptilde} for a choice of a symbol p as an argument in 
      the function @TO gaussianRing@
  SeeAlso
    gaussianRing
///
doc ///
  Key
    kVariableName
  Headline
    Optional input to choose the letter for the variable name.
  Description
    Text
      Put {\tt kVariableName => ktilde} for a choice of a symbol k as an argument in 
      the function @TO gaussianRing@
  SeeAlso
    gaussianRing
///

--------------------------------------------
-- Documentation conditionalIndependenceIdeal
--------------------------------------------
doc///
  Key
    conditionalIndependenceIdeal
    (conditionalIndependenceIdeal, Ring, List)
    (conditionalIndependenceIdeal, Ring, List, List)
  Headline
    the ideal of CI relations for a given list of CI statements
  Usage
    conditionalIndependenceIdeal(R,Stmts)
    conditionalIndependenceIdeal(R,VarNames,Stmts)
  Inputs
    R:Ring
      which must be a gaussianRing or a markovRing (error will be returned otherwise)
    Stmts:List
      of conditional independence statements
    VarNames:List
       of names of random variables in conditional independence statements in S.  If this is omited
       it is assumed that these are integers 1 to n where n is the number of variables in the
       declaration of markovRing or gaussianRing
  Outputs
    :Ideal
      of CI relations
  Description
    Text
      conditionalIndependenceIdeal computes the CI ideal of a set of statements:
    Example
      G = graph({{a,b},{b,c},{c,d},{d,a}})
      R=gaussianRing G
      S={{{a},{c},{b,d}}}
      I=conditionalIndependenceIdeal (R,S)
    Text
      If the gaussianRing was created without a graph, this still works:
    Example
      R=gaussianRing 5
      S={{{1},{2},{3,4}}, {{2,3},{1},{5}}}
      I=conditionalIndependenceIdeal (R,S)
    Text
      However, the set of labels on the graph nodes should match those used in the statements:
    Example
      R=gaussianRing 4
      G = graph({{a,b},{b,c},{c,d},{d,a}})  --I=conditionalIndependenceIdeal (R,G)        --UNCOMMENT WHEN DEBUG MODE => FALSE!
    Text
      conditionalIndependenceIdeal also works in the discrete case for both graphs, digraphs and with lists of statements.
    Example    
      R = markovRing (2,2,2,2)
      VarNames = {c,d,e,f}
      Stmts = { {{c,d},{e},{}}, {{d,e},{c},{f}}}
      conditionalIndependenceIdeal(R,VarNames,Stmts)
    Text
     If you want the CI ideal with statements associated to a graph, use the following commands
    Example
      G = graph({{a,b},{b,c},{c,d},{d,a}})
      R=gaussianRing G
      I=conditionalIndependenceIdeal (R,globalMarkov(G))

  SeeAlso
///

--------------------------------------------
-- Documentation undirectedEdgesMatrix------
--------------------------------------------

doc/// 
   Key
     undirectedEdgesMatrix
     (undirectedEdgesMatrix,Ring)
   Headline
     the matrix corresponding to the edges of an undirected graph
   Usage
     undirectedEdgesMatrix(R)
   Inputs
     R:Ring
       which should be created with @TO gaussianRing@ created with a Graph
   Outputs
     :Matrix
       the n x n symmetric matrix ... EXPLAIN!!
   Description 
     Text
       Note that this matrix is symmetric in the symbols.
     Example
       G = graph({{a,b},{b,c},{c,d},{a,d}})
       R = gaussianRing G
       M = undirectedEdgesMatrix(R)
   SeeAlso
     gaussianRing
     gaussianParametrization
     covarianceMatrix
     directedEdgesMatrix
///

-----------------------------------------
-- Documentation gaussianVanishingIdeal--
-----------------------------------------

doc ///
   Key
     gaussianVanishingIdeal
     (gaussianVanishingIdeal,Ring)
   Headline
     the vanishing ideal of the gaussian graphical model 
   Usage
     gaussianVanishingIdeal(R)
   Inputs
     R:Ring
       created with @TO gaussianRing@ and using a Graph or a Digraph
   Outputs
     :Ideal
        in R, of polynomial relations on the covariance matrices of a graphical model for G
   Description
     Text
       input: a polynomial ring R created by gaussianRing (!)
       output: the vanishing ideal of hte parametrization

       These ideals were first written down by Seth Sullivant, in "Algebraic geometry of Gaussian Bayesian networks". 
       The routines in this package involving Gaussian variables are all based on that paper.
     Example
       G = graph({{a,b},{b,c},{c,d},{a,d}})
       R = gaussianRing G 
       J = gaussianVanishingIdeal(R) 
       transpose gens J
     Text
       here is old text: 
       The ideal corresponding to a conditional independence statement {A,B,C} (where A,B,C,
       are disjoint lists of integers in the range 1..n (n is the number of random variables)
       is the #C+1 x #C+1 minors of the submatrix of the generic symmetric matrix M = (s_{(i,j)}), whose
       rows are in A union C, and whose columns are in B union C.  In general, this ideal need not be prime.
     Example
       G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
       R = gaussianRing G
       gaussianVanishingIdeal(R) 
   Caveat 
     The code for Graph is super-slow for any larger example, unfortunately. But the Digraph case is faster. 
   SeeAlso
     globalMarkov
     localMarkov
     gaussianRing
     gaussianMatrices
     trekIdeal
///


-----------------------------------------
-- Documentation discreteVanishingIdeal--
-----------------------------------------
doc/// 
   Key
     discreteVanishingIdeal
     (discreteVanishingIdeal,Ring,Digraph) 
   Headline
     the vanishing ideal of the discrete graphical model 
   Usage
     discreteVanishingIdeal(R,G)
   Inputs
     R:Ring
       created with @TO markovRing@ 
     G:Digraph
   Outputs
     :Ideal
       in R, of homogeneous polynomial relations on the joint probabilities of random variables represented by the vertices of G
   Description 
     Text
       Here is a small example for a graph on four vertices. The random variables a,b,c and d have 2,3,4, and 2 states, respectively. 
     Example
       G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
       R = markovRing (2,3,4,2)
       I = discreteVanishingIdeal (R,G);
     Text
       The vanishing ideal is generated by 84 quadrics, which we don't display.
     Example
       betti I 
   SeeAlso
     markovRing
///



--******************************************--
-- TESTS     	       	    	      	    --
--******************************************--

--------------------------
---- TEST pairMarkov  ----
--------------------------

TEST ///
G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
S = pairMarkov G
S = apply(S,s -> {sort s#0, sort s#1, sort s#2}) 
L = {{{c}, {d}, {a, b}}, {{a}, {d}, {b, c}}}
assert(S === L)
///

--------------------------
---- TEST localMarkov  ---
--------------------------

TEST ///
-- G = digraph { {1, {2,3}}, {2, {4}}, {3, {4}} }
-- S = localMarkov G
-- L = {{{2}, {3}, {1}}, {{1}, {4}, {2, 3}}}
-- assert(S === L)
G = digraph { {1,{2,3,4}}, {5,{2,3,4}} }
S = localMarkov G
S = apply(S,s -> {sort s#0, sort s#1, sort s#2}) 
L = {{{2}, {3, 4}, {1, 5}}, {{2, 3}, {4}, {1, 5}}, {{2, 4}, {3}, {1, 5}}, {{1}, {5}, {}}} 
assert(S === L)
///

--------------------------
--- TEST globalMarkov  ---
--------------------------

TEST ///
G = digraph { {2, {1}}, {3,{2}}, {4,{1,3}} }
S = globalMarkov G
S = apply(S,s -> {sort s#0, sort s#1, sort s#2}) 
L = {{{1}, {3}, {2, 4}}, {{2}, {4}, {3}}}
assert(S === L)
///

--------------------------
--- TEST marginMap     ---
--------------------------

TEST ///
R = markovRing (3,2)
F = marginMap(1,R) 
m = matrix {{p_(1,1)-p_(2,1)-p_(3,1), p_(1,2)-p_(2,2)-p_(3,2), p_(2,1), p_(2,2), p_(3,1), p_(3,2)}}
assert(F.matrix === m)
///

--------------------------
--- TEST hiddenMap     ---
--------------------------

TEST ///
R = markovRing (2,3,2)
F = hiddenMap(1,R) 
m = matrix {{p_(1,1,1)+p_(2,1,1), p_(1,1,2)+p_(2,1,2), p_(1,2,1)+p_(2,2,1), p_(1,2,2)+p_(2,2,2), p_(1,3,1)+p_(2,3,1), p_(1,3,2)+p_(2,3,2)}}
assert(F.matrix === m)
///

--------------------------
--- TEST markovRing    ---
--------------------------

TEST ///
d = (2,2,2)
R = markovRing (d, Coefficients=>CC, VariableName=>q)
V = {q_(1,1,1), q_(1,1,2), q_(1,2,1), q_(1,2,2), q_(2,1,1), q_(2,1,2), q_(2,2,1), q_(2,2,2)}
assert(gens R === V)
///

------------------------------
--- TEST markovMatrices    ---
------------------------------

TEST ///
G = digraph { {1, {2,3}}, {2, {4}}, {3, {4}} }
S = localMarkov G
R = markovRing (2,2,2,2)
L = markovMatrices (R,S) 
M = L#1
m = matrix {{p_(2,1,1,1)+p_(2,1,1,2), p_(2,1,2,1)+p_(2,1,2,2)},{p_(2,2,1,1)+p_(2,2,1,2), p_(2,2,2,1)+p_(2,2,2,2)}} 
assert(M === m)
///


-----------------------------------------------
--- TEST Gaussian Directed Graphical Models ---
-----------------------------------------------

----------------------------------------------------------------------------------------------
--27 JULY 2011
-----------------------------------------------
--- TESTs for undirected methods:-------------- 
-----------------------------------------------
 
-----------------------------------------------
--- TEST gaussianRing--------------------------
-----------------------------------------------

TEST /// 
G = graph({{a,b},{b,c},{c,d},{a,d}}) 
R = gaussianRing G
correctOutput = {{k_(a,a), k_(b,b), k_(c,c), k_(d,d), k_(a,d), k_(a,b),k_(b,c), k_(c,d), s_(a,a), s_(a,b), s_(a,c), s_(a,d), s_(b,b),s_(b,c), s_(b,d), s_(c,c), s_(c,d), s_(d,d)}}
assert(0 == vars R - matrix correctOutput )
/// 

-----------------------------------------------
--- TEST undirectedEdgesMatrix-----------------
-----------------------------------------------

TEST ///
G = graph({{a,b},{b,c},{c,d},{a,d}}) 
R=gaussianRing G 
M=undirectedEdgesMatrix(R)
correctOutput = {{k_(a,a), k_(a,b), 0, k_(a,d)}, {k_(a,b), k_(b,b), k_(b,c),0}, {0, k_(b,c), k_(c,c), k_(c,d)}, {k_(a,d), 0, k_(c,d),k_(d,d)}}
assert(0 == M - matrix correctOutput )
///

-----------------------------------------------
--- TEST covarianceMatrix(R,G)-----------------
-----------------------------------------------

TEST ///
G = graph({{a,b},{b,c},{c,d},{a,d}}) 
R=gaussianRing G 
cov=covarianceMatrix R
correctOutput = {{s_(a,a), s_(a,b), s_(a,c), s_(a,d)}, {s_(a,b), s_(b,b),s_(b,c), s_(b,d)}, {s_(a,c), s_(b,c), s_(c,c), s_(c,d)},{s_(a,d), s_(b,d), s_(c,d), s_(d,d)}}
assert(0 == cov - matrix correctOutput )
///

-----------------------------------------------
--- TEST gaussianVanishingIdeal-----------------
-----------------------------------------------

TEST ///
G = graph({{a,b},{b,c},{c,d},{a,d}}) 
R=gaussianRing G 
I = gaussianVanishingIdeal R
correctOutput = {s_(a,d)*s_(b,c)*s_(b,d)-s_(a,c)*s_(b,d)^2-s_(a,d)*s_(b,b)*s_(c,d)+s_(a,b)*s_(b,d)*s_(c,d)+s_(a,c)*s_(b,b)*s_(d,d)-s_(a,b)*s_(b,c)*s_(d,d),s_(a,c)*s_(a,d)*s_(b,c)-s_(a,c)^2*s_(b,d)-s_(a,b)*s_(a,d)*s_(c,c)+s_(a,a)*s_(b,d)*s_(c,c)+s_(a,b)*s_(a,c)*s_(c,d)-s_(a,a)*s_(b,c)*s_(c,d), s_(a,b)*s_(a,d)*s_(b,d)*s_(c,c)-s_(a,a)*s_(b,d)^2*s_(c,c)-s_(a,c)*s_(a,d)*s_(b,b)*s_(c,d)+s_(a,a)*s_(b,c)*s_(b,d)*s_(c,d)+s_(a,c)^2*s_(b,b)*s_(d,d)-s_(a,b)*s_(a,c)*s_(b,c)*s_(d,d), s_(a,b)*s_(a,c)*s_(b,d)^2*s_(c,c)-s_(a,a)*s_(b,c)*s_(b,d)^2*s_(c,c)-s_(a,c)^2*s_(b,b)*s_(b,d)*s_(c,d)+s_(a,a)*s_(b,c)^2*s_(b,d)*s_(c,d)-s_(a,b)^2*s_(b,d)*s_(c,c)*s_(c,d)+s_(a,a)*s_(b,b)*s_(b,d)*s_(c,c)*s_(c,d)+s_(a,b)*s_(a,c)*s_(b,b)*s_(c,d)^2-s_(a,a)*s_(b,b)*s_(b,c)*s_(c,d)^2+s_(a,c)^2*s_(b,b)*s_(b,c)*s_(d,d)-s_(a,b)*s_(a,c)*s_(b,c)^2*s_(d,d)-s_(a,b)*s_(a,c)*s_(b,b)*s_(c,c)*s_(d,d)+s_(a,b)^2*s_(b,c)*s_(c,c)*s_(d,d)}
assert( I == ideal correctOutput)
///

TEST ///
G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
R = gaussianRing G
I = gaussianVanishingIdeal(R) 
correctOutput = { -s_(a,d)*s_(b,b)+s_(a,b)*s_(b,d), s_(b,c)*s_(b,d)-s_(b,b)*s_(c,d), s_(a,d)*s_(b,c)-s_(a,b)*s_(c,d) }
assert( I == ideal correctOutput)
///
--------------------------
---- TEST pairMarkov  ----
--------------------------

TEST /// 
G = graph({{a,b},{b,c},{c,d},{d,e},{e,a}})
S = pairMarkov G
Ssorted = apply(S, s-> replace(2,sort(s_2),s) )
L = {{{a}, {d}, sort {e, b, c}}, {{c}, {e}, sort {d, a, b}}, {{b}, {d},sort {e,a, c}}, {{b}, {e},sort {d, a, c}}, {{a}, {c},sort {d, e, b}}}
assert(sort Ssorted === sort L)
/// 

--------------------------
---- TEST localMarkov  ---
--------------------------

TEST ///
G = graph({{a,b},{b,c},{c,d},{d,e},{e,a}})
S = localMarkov G
L = {{{a}, {c, d},sort {e, b}}, {{a, b}, {d},sort {e, c}}, {{a, e}, {c},sort {d, b}}, {{b, c}, {e}, sort{d, a}}, {{b}, {d, e}, sort{a, c}}}
Ssorted = apply(S, s-> replace(2,sort(s_2),s) )
assert(sort Ssorted === sort L)
///

----------------------------------------------------------------------------------------------


----------------------------
--- TEST gaussianRing    ---
----------------------------

TEST ///
R = gaussianRing 4
B = gens R
L = {s_(1,1), s_(1,2), s_(1,3), s_(1,4), s_(2,2), s_(2,3), s_(2,4), s_(3,3), s_(3,4), s_(4,4)}
assert(B === L)
///
     
TEST /// 
G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
assert(toString gaussianRing G === "QQ[s_(a,a), s_(a,b), s_(a,c), s_(a,d), s_(b,b), s_(b,c), s_(b,d), s_(c,c), s_(c,d), s_(d,d)]")
///

-----------------------------
--- TEST covarianceMatrix ---
-----------------------------

TEST /// 
G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
R = gaussianRing G
S = covarianceMatrix R
assert(0==S-matrix {{s_(a,a), s_(a,b), s_(a,c), s_(a,d)}, {s_(a,b), s_(b,b), s_(b,c), s_(b,d)}, {s_(a,c), s_(b,c), s_(c,c), s_(c,d)}, {s_(a,d), s_(b,d), s_(c,d), s_(d,d)}})
///



------------------------------
--- TEST gaussianMatrices  ---
------------------------------

TEST ///
G = digraph { {1,{2}}, {2,{3}}, {3,{4,5}},{4,{5}} } ;
R = gaussianRing G
S = localMarkov G
L = gaussianMatrices(R,S)
M1 = matrix {{s_(1,4), s_(1,3)}, {s_(2,4), s_(2,3)}, {s_(3,4), s_(3,3)}}
M2 = matrix {{s_(1,5), s_(1,4), s_(1,3)},{s_(2,5), s_(2,4), s_(2,3)},{s_(4,5), s_(4,4), s_(3,4)}, {s_(3,5), s_(3,4), s_(3,3)}}
M3 = matrix {{s_(1,3), s_(1,2)},{s_(2,3), s_(2,2)}}
assert({M1,M2,M3} === L)
///

TEST ///
G = digraph { {1,{2}}, {2,{3}}, {3,{4,5}},{4,{5}} } ;
R = gaussianRing G
L = gaussianMatrices(R,{{{1},{3},{4,2,5}}})
M = matrix{{s_(1,3), s_(1,4), s_(1,2), s_(1,5)},{s_(3,4), s_(4,4), s_(2,4), s_(4,5)},{ s_(2,3), s_(2,4) ,s_(2,2), s_(2,5)}, { s_(3,5), s_(4,5), s_(2,5) ,s_(5,5) }}
assert({M} === L)
///

-----------------------
--- TEST trekIdeal  ---
-----------------------

--TEST ///
--G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
--R = gaussianRing G
--I = trekIdeal(R,G)
--assert(I==ideal(s_(b,c)*s_(b,d)-s_(b,b)*s_(c,d),s_(a,d)*s_(b,c)-s_(a,b)*s_(c,d),s_(a,d)*s_(b,b)-s_(a,b)*s_(b,d)))
--///

-----------------------------------------------
--- TEST Gaussian Mixed Graphical Models ------
-----------------------------------------------

-------------------------
--- TEST gaussianRing ---
-------------------------

TEST ///
G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
R = gaussianRing G
assert(flatten entries vars R ==={l_(b,c), l_(b,d), l_(c,d), p_(a,a), p_(b,b), p_(c,c), p_(d,d), p_(a,d), s_(a,a), s_(a,b), s_(a,c), s_(a,d), s_(b,b), s_(b,c), s_(b,d), s_(c,c), s_(c,d), s_(d,d)})
///  --- THIS TEST SOMETIMES FAILS BUT I HAVE NO IDEA WHY, WHEN RUN BY HAND IT ALWAYS RETURNS TRUE!! HELP!!

-----------------------------
--- TEST covarianceMatrix ---
-----------------------------

TEST ///
G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
R = gaussianRing G
S = covarianceMatrix R
assert(0 == S-matrix {{s_(a,a), s_(a,b), s_(a,c), s_(a,d)}, {s_(a,b), s_(b,b), s_(b,c), s_(b,d)}, {s_(a,c), s_(b,c), s_(c,c), s_(c,d)}, {s_(a,d), s_(b,d), s_(c,d), s_(d,d)}})
///

--------------------------------
--- TEST directedEdgesMatrix ---
--------------------------------

TEST ///
G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
R = gaussianRing G
L = directedEdgesMatrix R
assert(0 == L-matrix {{0, 0, 0, 0}, {0, 0, l_(b,c), l_(b,d)}, {0, 0, 0, l_(c,d)}, {0, 0, 0, 0}})
///

----------------------------------
--- TEST bidirectedEdgesMatrix ---
----------------------------------

TEST ///
G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
R = gaussianRing G
W = bidirectedEdgesMatrix R
assert(0 == W-matrix {{p_(a,a), 0, 0, p_(a,d)}, {0, p_(b,b), 0, 0}, {0, 0, p_(c,c), 0}, {p_(a,d), 0, 0, p_(d,d)}})
///

------------------------------------
--- TEST gaussianParametrization ---
------------------------------------

TEST ///
G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
R = gaussianRing G
M = gaussianParametrization(R,G)
assert(0 == M-matrix {{p_(a,a), 0, 0, p_(a,d)}, {0, p_(b,b), l_(b,c)*p_(b,b), l_(b,c)*l_(c,d)*p_(b,b)+l_(b,d)*p_(b,b)}, {0, l_(b,c)*p_(b,b), l_(b,c)^2*p_(b,b)+p_(c,c), l_(b,c)^2*l_(c,d)*p_(b,b)+l_(b,c)*l_(b,d)*p_(b,b)+l_(c,d)*p_(c,c)},{p_(a,d), l_(b,c)*l_(c,d)*p_(b,b)+l_(b,d)*p_(b,b),l_(b,c)^2*l_(c,d)*p_(b,b)+l_(b,c)*l_(b,d)*p_(b,b)+l_(c,d)*p_(c,c),l_(b,c)^2*l_(c,d)^2*p_(b,b)+2*l_(b,c)*l_(b,d)*l_(c,d)*p_(b,b)+l_(b,d)^2*p_(b,b)+l_(c,d)^2*p_(c,c)+p_(d,d)}})
///

TEST ///
G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
R = gaussianRing G
M = gaussianParametrization(R,G,SimpleTreks=>true)
assert(0 == M-matrix {{1, 0, 0, p_(a,d)}, {0, 1, l_(b,c), l_(b,c)*l_(c,d)+l_(b,d)}, {0, l_(b,c), 1, l_(b,c)*l_(b,d)+l_(c,d)}, {p_(a,d), l_(b,c)*l_(c,d)+l_(b,d), l_(b,c)*l_(b,d)+l_(c,d), 1}})
///

------------------------------
-- TEST identifyParameters ---
------------------------------

TEST ///
G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
R = gaussianRing G
H = identifyParameters(R,G)
assert(H === new HashTable from {p_(a,d) => ideal(s_(a,c),s_(a,b),p_(a,d)-s_(a,d)),p_(d,d) => ideal(s_(a,c),s_(a,b),p_(d,d)*s_(b,c)^2-p_(d,d)*s_(b,b)*s_(c,c)-s_(b,d)^2*s_(c,c)+2*s_(b,c)*s_(b,d)*s_(c,d)-s_(b,b)*s_(c,d)^2-s_(b,c)^2*s_(d,d)+s_(b,b)*s_(c,c)*s_(d,d)), l_(c,d) =>ideal(s_(a,c),s_(a,b),l_(c,d)*s_(b,c)^2-l_(c,d)*s_(b,b)*s_(c,c)-s_(b,c)*s_(b,d)+s_(b,b)*s_(c,d)), l_(b,d) =>ideal(s_(a,c),s_(a,b),l_(b,d)*s_(b,c)^2-l_(b,d)*s_(b,b)*s_(c,c)+s_(b,d)*s_(c,c)-s_(b,c)*s_(c,d)), l_(b,c) =>ideal(s_(a,c),s_(a,b),l_(b,c)*s_(b,b)-s_(b,c)), p_(a,a) =>ideal(s_(a,c),s_(a,b),p_(a,a)-s_(a,a)), p_(b,b) =>ideal(s_(a,c),s_(a,b),p_(b,b)-s_(b,b)), p_(c,c) =>ideal(s_(a,c),s_(a,b),p_(c,c)*s_(b,b)+s_(b,c)^2-s_(b,b)*s_(c,c))})
///

--------------------------
-- TEST trekSeparation  --
--------------------------

-- This TEST could potentially fail since each statement in L could be written
-- in a different order, that is, {A,B,C,D} is equivalent to {B,A,D,C}
-- and trekSeparation may return either one of these statements
-- So I have commented this test for the moment
-- but one can test trekSeparation by testing trekIdeal.
-- TEST ///
-- G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
-- R = gaussianRing G
-- T = trekSeparation G
-- T = apply(T,s -> {sort s#0, sort s#1, sort s#2, sort s#3})
-- L = {{{a}, {b, c}, {}, {}}, {{b, c}, {a, b}, {}, {b}}, {{a, b}, {b, c}, {}, {b}}, {{b, c}, {a, c}, {}, {c}}, {{b, c}, {a, d}, {}, {d}}}
-- assert(T === L)
-- ///

----------------------
-- TEST trekIdeal  ---
----------------------

TEST ///
G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
R = gaussianRing G
T = trekSeparation G
I = trekIdeal(R,G)
assert(I == ideal(s_(a,c),s_(a,b),s_(a,c)*s_(b,b)-s_(a,b)*s_(b,c),-s_(a,c)*s_(b,b)+s_(a,b)*s_(b,c),s_(a,c)*s_(b,c)-s_(a,b)*s_(c,c),s_(a,c)*s_(b,d)-s_(a,b)*s_(c,d)))
///


--------------------------------
-- TEST discreteVanishingIdeal
--------------------------------
TEST///
G = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
R = markovRing (2,3,4,2)
I = discreteVanishingIdeal (R,G);
assert ( numcols mingens I == 84)
///
     
--------------------------------------
--------------------------------------
end
--------------------------------------
--------------------------------------


--blank documentation node:
doc/// 
   Key
     gaussianMatrix
     (gaussianMatrix,Digraph,Matrix,List) 
   Headline
   Usage
   Inputs
   Outputs
   Description 
     Text
     Example
     Text
     Example
   SeeAlso
///


uninstallPackage "GraphicalModels"
restart
--installPackage("Graphs", UserMode=>true)
installPackage ("GraphicalModels", RemakeAllDocumentation => true, UserMode=>true)
viewHelp GraphicalModels
installPackage("GraphicalModels",UserMode=>true,DebuggingMode => true)


----------------------
-- Parameterization -- ????????????????????????????????????????????????????????????????????????
---------------------- 
---- We need this for both directed and undirected graphs:

----  parameterizations and for toric varieties the corresponding matrix. 
----  In the case of toric varieties the matrix is easy.  Here is the code, 
----  commented out to be used later when we are ready. 
---- 
----  toAMatrix = method()
----  toAMatrix List := Matrix => (M) -> (
----      if any(M,isMonomial)
----         then error "this parameterization does not correspond to a toric ideal." 
----         else (
----              Mexp := apply(M, exponents);
----              transpose matrix apply(Mexp, flatten)))
----
---- isMonomial = method()
---- isMonomial RingElement := Boolean => (m) -> (
----      termList := terms m;
----      if #termList == 1 then true else false)

---- isMonomial works well as long as m is actually a polynomial or monomial and not 
---- an element of ZZ, QQ, RR, etc.
