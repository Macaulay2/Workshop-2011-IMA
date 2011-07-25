-- -*- coding: utf-8 -*-
newPackage(
	"ChernSegre",
    	Version => "1.0", 
    	Date => "July 25, 2011",
    	Authors => {{Name => "Christine Jost", 
		  Email => "jost@math.su.se", 
		  HomePage => "http://www.math.su.se/~jost"}},
    	Headline => "Computations of degrees of Chern and Segre classes of projective schemes",
    	DebuggingMode => true
    	)

export {segreClass}

segreClass = method(TypicalValue => List)
segreClass List := I -> (
    
     -- Obtain:
     -- the ring R 
     -- the dimension of the ambient space
     -- the dimension n of Z
     -- a list of the generators of I sorted by degree
     -- the maximal degree of the generators of I and
     -- a generator of I with minimal degree
     R = ring I;
     ambientDim = dim Proj R;
     dimension = dim Proj(R/I) ;
     gensI = flatten entries sort gens I;
     maxDeg = first max degrees I; 
     minDegGen = first gensI;
    
     -- Pick random elements in I of degree maxdeg, as many as the dimension of the ambient space, store in the list f.
     f = for i from 1 to ambientDim list sum( gensI, g -> g * random(maxDeg - first(degree(g)), R) );      
     
     -- The for loop computes the degrees of the Segre classes of Z, stores them in the list s.
     s = {};
     for d from (ambientDim - dimension) to ambientDim do (
	  
	  -- Obtain the ideal J of the intersection of d hypersurfaces containing Z, where d = comdimension of Z, ..., dimension of the ambient space.
	  J = ideal(take(f,d));
	  
	  -- Compute the residual of Z in the intersection of the d hypersurfaces, using saturation. Compute the degree of the residual. 
	  residual = saturate(J,minDegGen);
	  residualDeg = if residual != ideal vars R then degree residual else 0;
	  
     	  -- Using the degree of the residual, compute the degree of the pth Segre class, where p = d - codimension of Z.
	  p = d - (ambientDim - dimension);
	  degSegreClass = maxDeg^d - residualDeg - sum( 0..(p-1), i -> binomial(d,p-i)*maxDeg^(p-i)*s_i );
	  
	  s = append(s, degSegreClass);
	    
	  );
     
     return s;
     
     )


beginDocumentation()
document { 
	Key => ChernSegre,
	Headline => "Computations of degrees of Chern and Segre classes of projective schemes",
	EM "ChernSegre", "computes degrees of Chern and Segre classes"
	}
document {
	Key => {(segreClass,Ideal),},
	Headline => "computes degrees of the Segre classes",
	Usage => "segreClass I",
	Inputs => { "I" },
	Outputs => {{ "a list with degrees of Segre classes {deg s_0, ... , deg s_n} of the projective scheme given by the ideal", TT "I" }},
        SourceCode => {(segreClass,Ideal)},
	EXAMPLE lines ///
	   use QQ[x,y,z]
	   segreClass ideal(x)
     	///
	}

TEST ///
    R = QQ[x,y,z]
    I = (x)
    assert ( segreClass I == {1,-1} )
 ///
