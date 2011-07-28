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

export {firstFunction}

separators = method(TypicalValue => String)
separators Graph := G -> (
     S:=new MutableList from apply (# vertices G,i-> {});
     Size:=new MutableList from apply (# vertices G, i->0);
     alpha:=new MutableList from apply (# vertices G, i->0);
     ainverse:=new MutableList from apply (# vertices G, i->0);
     S#0:=vertices G;
     j:=0
     for i from 1 to n do
     	   
      

beginDocumentation()


TEST ///
    assert ( firstFunction 2 == "D'oh!" )
///
