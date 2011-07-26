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

firstFunction = method(TypicalValue => String)
firstFunction ZZ := String => n -> if n == 1 then "Hello World!" else "D'oh!"

beginDocumentation()


TEST ///
    assert ( firstFunction 2 == "D'oh!" )
///
