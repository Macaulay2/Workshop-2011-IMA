needsPackage "SimplicialComplexes"
needsPackage "Graphs"
--needsPackage "EdgeIdeals"
needsPackage "Posets"

newPackage(
	"SimplicialComplexesPlus",
	Version => "0.1",
	Date => "March 1st, 2011",
	Authors => {
	     	{Name => "Gwyneth Whieldon", Email => "whieldon@math.cornell.edu", HomePage => "http://www.math.cornell.edu/~whieldon/Main_Details.html"},
     	        {Name => "David Cook II", Email => "dcook@ms.uky.edu", HomePage => "http://www.ms.uky.edu/~dcook/"}
	},
	Headline => "Adds operations on simplicial complexes",
	Configuration => { },
	DebuggingMode => true
)

export {
	combJoin,
	bdcrossPolytope,
	simplex,
	bdsimplex,
	sctoGap,
	sctoGapFile,
	sd,
	recoverLabels,
	sdlabel,
	originalvars,
	nerveComplex,
	IsMultigraded
}

needsPackage "Graphs"
needsPackage "SimplicialComplexes"
--needsPackage "EdgeIdeals"
needsPackage "Posets"


cartesianProduct = method();

cartesianProduct(List,List):= List => (H,J) -> (
     flatten apply(H, h-> apply(J, i-> h*i))
     )

combJoin = method();

combJoin(SimplicialComplex,SimplicialComplex):= SimplicialComplex => (A,B)->(
     f:=flatten entries facets A;
     g:=flatten entries facets B;
     simplicialComplex cartesianProduct(f,g)
)

bdcrossPolytope = method();
bdcrossPolytope(ZZ):=(n)->(
--     s:=getSymbol "x";
--     t:=getSymbol "y";
     x:=local x;
     y:=local y;
     R:=ZZ/10007[x_1..x_n,y_1..y_n];
     a:=apply(toList (0..n-1), i-> R_i*R_(n+i));
     simplicialComplex monomialIdeal a
     )

--Prewritten methods for producing the n-diml simplex and its boundary:
simplex = method();


simplex(ZZ):=SimplicialComplex=>(n)->(
     x:=local x;
     R:=QQ[x_0..x_n];
     facet:={product flatten entries vars R};
     simplicialComplex facet
     )

bdsimplex = method();


bdsimplex(ZZ):=SimplicialComplex=>(n)->(
     x:=local x;
     R:=QQ[x_0..x_n];
     simplicialComplex flatten entries faces(n-1,simplex(n))
     )

--Method to print simplicial complexes in Gap format:
sctoGap = method();


--This one you specify the name:
sctoGap(SimplicialComplex,String):=String=>(D,s)->(
     vertset:=gens ring D;
     numvert:=toList(1..#vertset);
     replacepairs:=hashTable apply(numvert, i-> vertset_(i-1) => i);
     protofacetlist:=apply(flatten entries facets D, f-> support f);
     facetlist:=toString apply(protofacetlist, f-> apply(f, i-> replacepairs#i));
     concatenate(s,":=SCFromFacets(",replace("\\}","]",replace("\\{","[",facetlist)),");")
     )

--This one has "delta" as the automatic complex name:
sctoGap(SimplicialComplex):=String=>(D)->(
     sctoGap(D,"delta")
     )

--This writes your complex to a file for Gap to read later:

sctoGapFile = method();


sctoGapFile(SimplicialComplex,String):=File=>(D,s)->(
     fn:=concatenate(s,".g");
     fn << toString sctoGap(D,s) << endl << close;
     )

sctoGapFile(SimplicialComplex):=File=>(D)->(
     fn:=concatenate(temporaryFileName(),".g");
     fn << toString sctoGap(D) << endl << close;
     )

--Internal test function used by sd:

testmax = method();


testmax(List):=Boolean=>(L)->(
     min apply(L, j->#j) > 1
     )

--facePoset=method();

--facePoset(SimplicialComplex):=Poset=>(D)->(
--     faceset:=apply(flatten apply(toList(0..dim D), i-> toList flatten entries faces(i,D)), r-> support r);
--     chainheads:=apply(flatten entries facets D, i-> support i);
--     maxchains:=apply(chainheads, i-> {i});
--     while any(maxchains, testmax) do ( 
--     	  nextstage:={};
--     	  holdover:=select(maxchains,c-> not testmax c);
--     	  for m in select(maxchains,testmax) do (
--	       minsize:=min apply(m, i-> #i);
--	       minset:=first select(m, i-> #i== minsize);
--     	       coveredfaces:=subsets(minset,minsize-1);
--	       nextstage=join(nextstage,apply(coveredfaces, c->append(m,c)))
--	       );
--      	  maxchains = join(nextstage,holdover);
--      	  );    
--     poset(faceset,unique flatten apply(maxchains, i-> apply(subsets(i,2),reverse)))
--     )

--Subdivisions method:
sd = method();


originalvars:=local originalvars;

--Relabels vertices to make them easier to work with, stores original faces as cache table:
sd(SimplicialComplex):=SimplicialComplex=>(D)->(
     x:=local x;
     kk:=coefficientRing D;
     faceset:=apply(flatten apply(toList(0..dim D), i-> toList flatten entries faces(i,D)), r-> support r);
     numfaces:=#faceset;
     varfaces:=apply(numfaces, i-> x_i);
     R:=kk[varfaces];
     toVarfaces:=hashTable(apply(toList(0..numfaces-1), i-> faceset_i=>R_i));
     toOrigFaces:=hashTable apply(apply(pairs toVarfaces, i-> reverse i), j-> first j => last j);
     chainheads:=apply(flatten entries facets D, i-> support i);
     maxchains:=apply(chainheads, i-> {i});
     while any(maxchains, testmax) do ( 
     	  nextstage:={};
     	  holdover:=select(maxchains,c-> not testmax c);
     	  for m in select(maxchains,testmax) do (
	       minsize:=min apply(m, i-> #i);
	       minset:=first select(m, i-> #i== minsize);
     	       coveredfaces:=subsets(minset,minsize-1);
	       nextstage=join(nextstage,apply(coveredfaces, c->append(m,c)))
	       );
      	  maxchains = join(nextstage,holdover);
      	  );
      K:=simplicialComplex apply(maxchains, c-> product apply(c, j-> toVarfaces#j));
      originalvars = new MutableHashTable;
      K.cache.originalvars= toOrigFaces;
      K
      )

--This prints the list of facets in sd D:
recoverLabels = method();


recoverLabels(SimplicialComplex):=List=>(D)->(
     if D.cache.?originalvars then (
	  facetlist:=apply(flatten entries facets D, i-> support i);
     	  apply(facetlist, c-> apply(c, v-> D.cache.originalvars#v))
	  )
     else (
	  error "Not a generated barycentric subdivision."
	  )
     )

--Has vertices labeled by their original face in the complex:
sdlabel = method();


sdlabel(SimplicialComplex):=SimplicialComplex=>(D)->(
     x:=local x;
     kk:=coefficientRing D;
     faceset:=apply(flatten apply(toList(0..dim D), i-> toList flatten entries faces(i,D)), r-> support r);
     numfaces:=#faceset;
     faceset2:=apply(faceset, f->replace("\\}",")",replace("\\{","(",toString(apply(f, v-> index v+1)))));
     varfaces:=apply(faceset2, i-> x_i);
     R:=kk[varfaces];
     toVarfaces:=hashTable(apply(toList(0..numfaces-1), i-> faceset_i=>R_i));
     chainheads:=apply(flatten entries facets D, i-> support i);
     maxchains:=apply(chainheads, i-> {i});
     while any(maxchains, testmax) do ( 
     	  nextstage:={};
     	  holdover:=select(maxchains,c-> not testmax c);
     	  for m in select(maxchains,testmax) do (
	       minsize:=min apply(m, i-> #i);
	       minset:=first select(m, i-> #i== minsize);
     	       coveredfaces:=subsets(minset,minsize-1);
	       nextstage=join(nextstage,apply(coveredfaces, c->append(m,c)))
	       );
      	  maxchains = join(nextstage,holdover);
      	  );
      simplicialComplex apply(maxchains, c-> product apply(c, j-> toVarfaces#j))
      )
 
 
nerveComplex = method(Options=>{symbol IsMultigraded => false});

nerveComplex(Graph):= opts -> (G) -> (
     m := # edges G;
     e :=local e;
     S := if not opts.IsMultigraded then (
	  QQ(monoid[(symbol e)_1..(symbol e)_m])
	  )
     else (
	  QQ(monoid[(symbol e)_1..(symbol e)_m, MonomialSize => 8, Degrees => apply(m, i-> apply(m, j -> if i === j then 1 else 0))])
     	  );
     I := apply(vertices G, v -> select(0..(m-1), i -> member(v, toList(edges G)#i)));
     simplicialComplex apply(I, L -> product toList apply(L, i-> S_i))
)

nerveComplex(SimplicialComplex):= opts -> (D)->(
     m := # flatten entries facets D;
     e := local e;
     kk := coefficientRing ring D;
     S := if not opts.IsMultigraded then (
	  kk(monoid[(symbol e)_1..(symbol e)_m])
	  )
     else (
	  kk(monoid[(symbol e)_1..(symbol e)_m, MonomialSize => 8, Degrees => apply(m, i-> apply(m, j -> if i === j then 1 else 0))])
     	  );
     I := apply(gens ring D, v -> select(0..(m-1), i -> member(v, support (flatten entries facets D)#i)));
     simplicialComplex apply(I, L -> product toList apply(L, i-> S_i))
)



beginDocumentation();


doc ///
	Key
		SimplicialComplexesPlus

	Description
		Text
			This package adds a number of features to the SimplicialComplexes package, including barycentric subdivision, simplex and boundary of simplex constructions, combinatorial join, construction of the cross polytope, and exportation of Macaulay 2 code for a simplicial complex into GAP format. 
		Example
			simplex 5
			D=bdsimplex 3
			C=sd D
			facetset=flatten entries facets C
			recoverLabels(C)--displays facets of sd corresponding to chains of faces in D
			sdlabel bdsimplex 2
			sctoGap bdsimplex 3
		Text
		        This package includes LaTeX and GAP format outputs.
     	SeeAlso
		     	bdsimplex
			simplex
			bdcrossPolytope
			combJoin
			sctoGap
			sctoGapFile
			sd
			recoverLabels
			sdlabel
///

doc ///
	Key
		simplex
		(simplex, ZZ)
      	Headline 
		returns the simplex as an object of type SimplicialComplex.
	Description
		Text
			inputs:  dimension n
		Text
			outputs:  simplex D of dimension n
		Example
			D3=simplex 3
			D7=simplex 7
		Text
		     	This produces the simplex on n+1 vertices of dimension n.
	SeeAlso
		bdsimplex
		sd
		sctoGap
///

doc ///
	Key
		bdsimplex
		(bdsimplex, ZZ)
	Headline 
		returns the boundary of a simplex as an object of type SimplicialComplex.
	Description
		Text
			inputs:  dimension n
		Text
			outputs:  boundary of simplex D of dimension n
		Example
			Bd3=bdsimplex 3
			Bd1=bdsimplex 1
			Bd4=bdsimplex 4
		Text
		     	This produces the (n-1)-skeleton of the n simplex.
	SeeAlso
		simplex
		sd
		sctoGap
///

doc ///
	Key
		sd
		(sd, SimplicialComplex)
	Headline 
		returns the barycentric subdivision of a simplicial complex
	Description
		Text
			inputs:  simplicial complex D
		Text
			outputs:  barycentric subdivision of D with new vertex labels
		Example
     	       	    	R=QQ[x_1..x_4]
			L={{x_1,x_2,x_3},{x_1,x_4},{x_2,x_4}}
		     	D=simplicialComplex(apply(L, product))
     	       	    	subdivD=sd D
			flatten entries facets oo
			recoverLabels subdivD
	SeeAlso
		sdlabel
		recoverLabels
///


doc ///
	Key
		bdcrossPolytope
		(bdcrossPolytope, ZZ)
	Headline 
		returns boundary of the n dimensional cross polytope
	Description
		Text
			inputs:  n
		Text
			outputs:  (n-1)-dimensional complex of boundary of n-dimensional cross polytope
		Example
     	       	    	D=bdcrossPolytope 3
			ideal D
	SeeAlso
		simplex
		bdsimplex
///

doc ///
	Key
		sctoGap
		(sctoGap, SimplicialComplex)
		(sctoGap, SimplicialComplex, String)
	Headline 
		returns a string of input to GAP
	Description
		Text
			inputs:  simplicial complex D
		Text
			outputs:  string of GAP code constructing simplicial complex D
		Example
     	       	    	D=bdsimplex 3
		     	sctoGap D
		Text
		     	This produces a simplicial complex on vertex set [1,...,n] in GAP.  Other labelings have not been implemented.
		Example
		     	R=QQ[a..d]
			L={{a,b,c},{a,d},{b,d}}
     	       	    	D=simplicialComplex(apply(L, product))
			sctoGap D
		Text
		     	As a default, this will name the new complex "delta".  To choose a different name, add a string with desired complex name as the second input.
		Example
     	       	    	R=QQ[a..d]
			L={{a,b,c},{a,d},{b,d}}
     	       	    	D=simplicialComplex(apply(L,product))
			sctoGap(D,"testcomplex")

	SeeAlso
		sctoGapFile
///

doc ///
	Key
		sctoGapFile
		(sctoGapFile, SimplicialComplex)
		(sctoGapFile, SimplicialComplex, String)
	Headline 
		outputs a file containing a string of input to GAP
	Description
		Text
			inputs:  simplicial complex D
		Text
			outputs:  file containing string of GAP code constructing simplicial complex D
		Example
     	       	    	D=bdsimplex 3
		     	sctoGapFile(D,"desiredname");
			get "desiredname.g"
		Text
		     	Note that this names the file "desiredname.g" not "desiredname".  This can be changed by user.  This file can be read directly by GAP with Read("desiredname.g"), returning a complex in GAP named "desiredname".
		Text
		     	If no name is specified, this will produce a temporaryFileName as the name and name the complex "delta".
     	        Example
		     	D=bdsimplex 3
			sctoGapFile D
	SeeAlso
		sctoGap
///

doc ///
	Key
		sdlabel
		(sdlabel, SimplicialComplex)
	Headline 
		returns the barycentric subdivision of a simplicial complex
	Description
		Text
			inputs:  simplicial complex D
		Text
			outputs:  barycentric subdivision of D with vertices labeled by face in D
		Example
     	       	    	R=QQ[x_1..x_4]
			L={{x_1,x_2,x_3},{x_1,x_4},{x_2,x_4}}
		     	D=simplicialComplex(apply(L, product))
     	       	    	sdlabel D
			flatten entries facets oo
		Text
		     	This is slightly clunkier, but easier to see chains of faces of D as facets of sd D.
	SeeAlso
		sd
		recoverLabels
///


end;

uninstallPackage"SimplicialComplexesPlus"
restart

path=append(path, "/Users/gwynethwhieldon/Dropbox/M2/packages/")
--loadPackage"SimplicialComplexesPlus"
installPackage"SimplicialComplexesPlus"
viewHelp SimplicialComplexesPlus

loadPackage"SimplicialComplexes"
loadPackage"EdgeIdeals"