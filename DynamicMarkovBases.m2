-- -*- coding: utf-8 -*-
newPackage(
	"DynamicMarkovBases",
    	Version => "0.0.1", 
    	Date => "July 26, 2011",
    	Authors => {{Name => "Elizabeth Gross", 
		  Email => "egross7@uic.edu"},
	     {Name => "Vishesh Karwa", 
		  Email => "vishesh@psu.edu"}},
    	Headline => "a package for dynamic sampling of markov bases for hierarchical models",
    	DebuggingMode => true
    	)

export {lexBFS,isChordal,peo,baseSets,markovMove}
needsPackage "Graphs"
needsPackage "GraphicalModels" --decide later if you want to do GraphicalModels$markovRing
--returns a lexographic ordering of the vertices of a graph G
lexBFS = method(TypicalValue => List)
lexBFS Graph := G->(
      S:=new MutableList from apply (# vertices G, i->{});
      Size:=new MutableList from apply (# vertices G, i->0);
      alpha:=new MutableList from apply (# vertices G, i->0);
      ainverse:=new MutableList from apply (# vertices G, i->0);
      n:= # vertices G;
      Gvers:= vertices G;
      S#0 =toList (0..n-1);
      j:=0;
      for i from 0 to n-1 do
       (
	    v:=S#j#0;
	    S#j =delete(v,S#j);
	    --if S#j=={} then delete({},S);
	    alpha#v =i;
	    ainverse#i = v;
	    Size#v = -1;
       	    for u from 0 to (#(graph G)#(Gvers_v))-1 when Size#u>=0 do 
	    (
		 S#(Size#u)= delete(u,S#(Size#u));
		 Size#u = Size#u +1;
		 S#(Size#u) = append(S#(Size#u),u);
	      	 );
	    if S#j=={} then j=j+1;
     	    );  
       alpha = reverse alpha;
       alpha
       )

-- returns the position in list h of  x
pos = (h, x) -> position(h, i->i===x);

--input vertex label, out vertex index
getPos = (G,v)->pos(vertices G, v);
--input is integer locator, output neighbors
nbr = (G,v) ->((graph G)#((vertices G)#v));


--input is index of vertex and ordering, output is position of neighbors of vertex in ordering
--indNbr = method(TypicalValue => List)
indNbr = (G,v,sigma)->(apply(#(toList nbr(G,v)), i->pos(sigma,pos(vertices G,(toList nbr(G,v))#i))));
--Returns a boolean value depending on weather or not the graph is chordal. 
isChordal = method(TypicalValue => Boolean)
isChordal Graph := G ->(
     alpha := lexBFS(G);
     sigma :=  reverse alpha;
     print peek sigma;
     n:= #vertices G;
     --Start by assuming that the graph is chordal
     chordal := new Boolean from true;
     for v from 0 to n-1 do (
     	  nbrV := toList nbr(G,v);
     	  indNbrV := indNbr(G,v,toList sigma);
     	  --minus one denotes null
     	  w := -1;
	  posw := -1;
     	  if select(indNbrV,j->j<pos(toList sigma,v))!={} then 
	  (	
	       posw = max(select(indNbrV,j->j<pos(toList sigma,v)));
	       w=sigma#posw;
	       );
	  print indNbrV;
	  print posw;
     	  if w == -1 then continue;
     	  if w!=-1 then
     	  (
	    --finding the earlier neighbors of v excluding w
	    earlyNbrV := select(indNbrV,j->j< pos(toList sigma,v));
	    earlyNbrV = delete(w,earlyNbrV);
	    --finding the earlier neighbors of w
	    nbrW := toList nbr(G,w);
     	    indNbrW := indNbr(G,w,toList sigma);
	    earlyNbrW := select(indNbrW,j->j < pos(toList sigma,w));
	       -- if earlyNbrV is not a subset of earlyNbrW then the graph is not a chordal
	       print w;
	       print peek earlyNbrV;
	       print peek earlyNbrW;
	       if isSubset(earlyNbrV,earlyNbrW) == false then
		  (	
		    chordal = false;
		    break;
		   )	
	     )
	);				
chordal		
)

--if G is chordal returns a perfect elimination ordering of G
--esle returns an error message saying that the graph is not chordal
peo = method(TypicalValue => List)
peo Graph := G ->(
     alpha := lexBFS(G);
     sigma := reverse alpha;
     n:= #vertices G;
     --Start by assuming that the graph is chordal
     chordal := new Boolean from true;
     for v from 0 to n-1 do (
     	  nbrV := toList nbr(G,v);
     	  indNbrV := indNbr(G,v,toList sigma);
     	  --minuss one denotes null
     	  w := -1;
     	  if select(indNbrV,j->j<pos(toList sigma,v))!={} then 
	  (
	       posw := max(select(indNbrV,j->j<pos(toList sigma,v)));
	       w=sigma#posw;
	       );
     	  if w == -1 then continue;
     	  if w!=-1 then
     	  (
	    --finding the earlier neighbors of v excluding w
	    earlyNbrV := select(indNbrV,j->j< pos(toList sigma,v));
	    earlyNbrV = delete(w,earlyNbrV);
	    --finding the earlier neighbors of w
	    nbrW := toList nbr(G,w);
     	    indNbrW := indNbr(G,w,toList sigma);
	    earlyNbrW := select(indNbrW,j->j < pos(toList sigma,w));
	       -- if earlyNbrV is not a subset of earlyNbrW then the graph is not a chordal
	       if isSubset(earlyNbrV,earlyNbrW) == false then
		  (	
		    chordal = false;
		    break;
		   )	
	     )
	);			
   if chordal == false then 
   (
     "Graph is not chordal";
     sigma = {}; 
   );  
  toList  sigma
)     

--returns a set of base sets of the graph. This is valid only if the graph is chordal. 
--If the graph is not chordal, it returns an error

baseSets = method(TypicalValue => (List, List))
baseSets Graph :=G ->(
     --Compute the perfect elimination ordering
     sigma := peo(G);
     -- check if sigma is empty, if yes, graph is not chordal!!
     if sigma == {} then error "Graph is not chordal";
     n := # vertices G;     
     B := set {};
     N := apply(n,i->(select(indNbr(G,i,sigma),j->j>i)));
     D := new MutableList from apply(n,i->set{});
     for i in reverse toList (0..n-2) do
     (
	  if #(N#(sigma#i)) <= #(N#(sigma#(i+1))) then
      	  (
	   B = B+set {N#(sigma#i)};D#(pos(toList B,N#(sigma#i)))=D#(pos(toList B,N#(sigma#i)))+set{sigma#i})        
      );
     (toList B,toList delete(set{},D))     	   
)

--input is graph and list of number of values for each random variable
--could output zero vector, filter later
markovMove = method(TypicalValue => sequence)
markovMove (Graph,List) := (G,l) ->(
     (B,D):=baseSets(G);
     sep:=random (#B);
     --the last random integer tells us whether the subset spedified
--or its complement will be Gamma_1
     seq:=apply(#(D#sep)+1,i->random 2);
     --remove separators from graph
     v := set apply(#(B#sep),i->(vertices G)#((B#sep)#i));
     Gnew := select(pairs graph G, x -> not member(x#0,v));
     Gnew = apply(Gnew, x -> (x#0, x#1 - v));
     gwoS:=graph Gnew;
     g1:=flatten apply(#seq-1,i->if seq#i==1 then
reachable(gwoS,{(vertices G)#((toList D#sep)#i)}));
     g2:=toList ((set vertices G - set g1)-set apply(#(B#sep),i->(vertices G)#((B#sep)#i)));
     if last seq==0 then (gamma1:=g1; gamma2:=g2) else (gamma1=g2; gamma2=g1);
     R:=markovRing toSequence l;
     l1:=apply(#l,i->random (l_i));
     l2:=apply(#l,i->random(l_i));
     listofseq:=apply(# vertices G,i->{l1_i+1, if member((vertices G)_i,B#sep)==false
           then l2_i+1 else l1_1+1, if member((vertices G)_i,gamma2)==true
           then l2_i+1 else l1_i+1, if member((vertices G)_i,gamma2)==true
           then l1_i+1 else (if member((vertices G)_i,B#sep)==false
then l2_i+1 else l1_1+1)});
     print listofseq;
     m:=transpose listofseq;
     vars R;
     p:=symbol p;
     expo1:=exponents (p_(toSequence m#0)*p_(toSequence m#1));
     expo2:=exponents (p_(toSequence m#2)*p_(toSequence m#3));
     exps:=toSequence (flatten (expo1-expo2));
     exps
     )
      
end
beginDocumentation()

doc ///
     Key
     	  DynamicMarkovBases
	Headline
	A package for computing markov bases on the fly for decomposoble discrete undirected graphical models 
	Description
	Text
	Contributors: Elizabeth Gross, Vishesh Karwa
	Text
	The primary aim of this package is to generate markov bases on the fly. 
	This is useful for undirected graphical models for large n (large here means greater than 7). 
	For such models, the markov bases can have many elements. 
	The main idea is to generate a markov move randomly without enumerating all the moves of the set.
	These dynamically generated moves can be used to construct Markov chains.
	
	Caveat
	This package requires Graphs.m2.
	
 --------------------------------------
 --Documenation lexBFS---
 --------------------------------------
 
 doc ///
      Key
      lexBFS
      Headline
       Lexographic breadth first search ordering of the vertices of a graph 
      Usage
      lexBFS G 
      Inputs
      G:
      	   @ofClass {Graph}@
      Output:
      L:List
       whose entries are the lexographic BFS ordering of the vertices of the graph
       
       Description
       
       Text 
       	   A lexographic breadth first search ordering is used as an input to many other graph algorithms.
	   In this package, this ordering is used as a preliminary step to testing if a graph is chordal.
	   

TEST ///
    assert ( firstFunction 2 == "D'oh!" )
///
