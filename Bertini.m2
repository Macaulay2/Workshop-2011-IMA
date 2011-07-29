needsPackage "NAGtypes"

newPackage(
  "Bertini",
  Version => "0.1", 
  Date => "25 July 2011",
  Authors => {
    {Name => "Dan Bates",
     Email => "bates@math.colostate.edu",
     HomePage => "http://www.math.colostate.edu/~bates"},
    {Name => "Contributing Author: Anton Leykin",
     HomePage => "http://www.math.gatech.edu/~leykin"}
  },
  Headline => "Interface to Bertini",
  Configuration => { 
    "path" => "",
    "BERTINIexe"=>"bertini", 
    "keep files" => true
  },
  DebuggingMode => false,
  AuxiliaryFiles => true,
  CacheExampleOutput => true
)

export { 
  "bertiniSolve",
  "bertiniZeroDimSolve",
  "bertiniParameterHomotopy",
  "bertiniPosDimSolve",
  "bertiniSample",
  "bertiniComponentMemberTest",
  "bertiniRefineSols",
  "StartSystem",  
  "StartSolutions",  
  "gamma",
  "MPTYPE",  
  "PRECISION",  
  "ODEPREDICTOR",  
  "TRACKTOLBEFOREEG",  
  "TRACKTOLDURINGEG",
  "FINALTOL",  
  "MAXNORM",  
  "MINSTEPSIZEBEFOREEG",  
  "MINSTEPSIZEDURINGEG",  
  "IMAGTHRESHOLD",
  "COEFFBOUND",  
  "DEGREEBOUND",  
  "CONDNUMTHRESHOLD",  
  "RANDOMSEED",  
  "SINGVALZEROTOL",
  "ENDGAMENUM", 
  "USEREGENERATION",  
  "SECURITYLEVEL",  
  "SCREENOUT",  
  "OUTPUTLEVEL",
  "STEPSFORINCREASE",  
  "MAXNEWTONITS",  
  "MAXSTEPSIZE",  
  "MAXNUMBERSTEPS",  
  "MAXCYCLENUM",
  "REGENSTARTLEVEL",
  "runType",
  "compnum",
  "dimen",
  "numpts",
  "digits",
  "pts"
}

needsPackage "NAGtypes"

--##########################################################################--
-- GLOBAL VARIABLES 
--##########################################################################--

 DBG = 0; -- debug level (10=keep temp files)
 path'BERTINI = (options Bertini).Configuration#"path";
 BERTINIexe=path'BERTINI|(options Bertini).Configuration#"BERTINIexe"; 
-- this is the executable string we need to make sure that calls to PHCpack actually run:    -- How shall we do this with Bertini ???
-- NOTE: the absolute path should be put into the init-PHCpack.m2 file 

-- QUESTION: do we need to prepend "rootPath" to all the file names to resolve issues with cygwin??? (question from PHCpack interface)

needsPackage "SimpleDoc"

-- Bertini interface for NAG4M2
-- used by ../NumericalAlgebraicGeometry.m2

-- need to include proper attribution each time Bertini is run...how to do???
-- (license calls for a line in the output that states which Bertini version was used)

-- The following six methods are just front ends for various Bertini functions.
-- Each just calls bertiniSolve() with the appropriate input data and toggle (corresp. to the type of run).
-- bertiniSolve then does all the work of building the input file, calling bertini, and calling the appropriate output parser. 

bertiniZeroDimSolve = method(TypicalValue => List, Options=>{MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1})
bertiniZeroDimSolve List := o -> F -> (  
--F is the list of polynomials.
         L := {runType=>0};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         ) 


bertiniParameterHomotopy = method(TypicalValue => List, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1})
bertiniParameterHomotopy List := o -> F -> (
--F is the list of polynomials
         L := {runType=>1};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         )

--  The following will NOT be funcitonal until we have (and include as output) a numerical irreducible decomposition data type. 
bertiniPosDimSolve = method(TypicalValue => List, Options=>{MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1})
bertiniPosDimSolve List := o -> F -> (  
--F is the list of polynomials
         L := {runType=>2};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         ) 

bertiniSample = method(TypicalValue => List, Options=>{MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1,dimen=>-1,compnum=>-1,numpts=>-1})
bertiniSample List := o -> F -> (  
--F is the list of polynomials
         L := {runType=>3};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         ) 

--  The following will NOT be functional until we have (and include in the arg list) a numerical irreducible decomposition data type.
bertiniComponentMemberTest = method(TypicalValue => List, Options=>{MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1,pts=>{}})
bertiniComponentMemberTest List := o -> F -> (  
--F is the list of polynomials.
         L := {runType=>4};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         ) 

bertiniRefineSols = method(TypicalValue => List, Options=>{MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1,pts=>{},digits=>-1})
bertiniRefineSols List := o -> F -> ( 
--F is the list of polynomials.
         L := {runType=>5};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         ) 


---------------------------------------------------
-- bertiniSolve: This is the main control function:
---------------------------------------------------

bertiniSolve = method(TypicalValue => List, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1,dimen=>-1,compnum=>-1,numpts=>-1,pts=>{},digits=>-1,runType=>0})

bertiniSolve List := o -> F -> (  -- F is the list of polynomials
  	  dir := makeBertiniInput(F,o);   -- creates the input file 
          if o.runType == 0 then ( -- ZeroDim 
    	    run("cd "|dir|"; "|BERTINIexe|" >bertini_session.log");  -- runs Bertini, storing screen output to bertini_session.log
	    readSolutionsBertini(dir,"finite_solutions")  -- grabs "finite_solutions" and puts all finite solutions in NAGTypes data types...Is finite_solutions the correct output file??? 
            );
          if o.runType == 1 then ( -- param homotopy
    	    run("cd "|dir|"; "|BERTINIexe|" >bertini_session.log");  -- runs Bertini, storing screen output to bertini_session.log
	    readSolutionsBertini(dir,"finite_solutions")  -- grabs "finite_solutions" and puts all finite solutions in NAGTypes data types...Is finite_solutions the correct output file??? 
            );
          if o.runType == 2 then ( -- PosDim 
    	    run("cd "|dir|"; "|BERTINIexe|" >bertini_session.log");  -- runs Bertini, storing screen output to bertini_session.log
	    --readSolutionsBertini(dir,"finite_solutions")  -- grabs "finite_solutions" and puts all finite solutions in NAGTypes data types...Is finite_solutions the correct output file??? 
            );
          if o.runType == 3 then ( -- Sample 
            stdio << "Run terminated.  Sampling will be available via this M2/Bertini interface once witness sets are handled correctly in the interface.\n"
    	    --run("cd "|dir|"; "|BERTINIexe|" < sample_script >bertini_session.log");  -- runs Bertini, storing screen output to bertini_session.log
	    --readSolutionsBertini(dir,"finite_solutions")  -- grabs "finite_solutions" and puts all finite solutions in NAGTypes data types...Is finite_solutions the correct output file??? 
            );
          if o.runType == 4 then ( -- Membership  
            stdio << "Run terminated.  Component membership will be available via this M2/Bertini interface once witness sets are handled correctly in the interface.\n"
    	    --run("cd "|dir|"; "|BERTINIexe|" >bertini_session.log");  -- runs Bertini, storing screen output to bertini_session.log
	    --readSolutionsBertini(dir,"finite_solutions")  -- grabs "finite_solutions" and puts all finite solutions in NAGTypes data types...Is finite_solutions the correct output file??? 
            );
          if o.runType == 5 then ( -- Refine/Sharpen 
    	    run("cd "|dir|"; "|BERTINIexe|" < sharpen_script >bertini_session.log");  -- runs Bertini, storing screen output to bertini_session.log
	    readSolutionsBertini(dir,"finite_solutions")  -- grabs "finite_solutions" and puts all finite solutions in NAGTypes data types...Is finite_solutions the correct output file??? 
            );
          )


-- DAN PLAN (7/26/11)
--   create files as necessary for various runs (ex.: param, sample, member)
--   build output parsers: output is read into M2 data types (still deciding on those), with each sort of run feeding into a different output file parser, since different sorts of runs yield different output files 

-------------------
-- makeBertiniInput
-------------------

makeBertiniInput = method(TypicalValue=>Nothing, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1,dimen=>-1,compnum=>-1,numpts=>-1,pts=>{},digits=>-1,runType=>0})  
makeBertiniInput List := o -> T -> ( -- T=polynomials of target system

  v := gens ring T#0; -- variables
  dir := temporaryFileName(); -- build a directory to store temporary data 
  makeDirectory dir; 
  f := openOut (dir|"/input"); -- typical (but not only possible) name for Bertini's input file 

  -- The following block is the config section of the input file 
  f << "CONFIG\n\n"; -- starting the config section of the input file 

  -- for each user-provided option, we write the appropriate config to the file IF it's not just the (meaningless) default:
  if o.MPTYPE =!= -1 then
    f << "MPTYPE: " << o.MPTYPE << ";\n";
  if o.PRECISION =!= -1 then
    f << "PRECISION: " << o.PRECISION << ";\n";
  if o.ODEPREDICTOR =!= -1 then
    f << "ODEPREDICTOR: " << o.ODEPREDICTOR << ";\n";
  if o.TRACKTOLBEFOREEG =!= -1 then
    f << "TRACKTOLBEFOREEG: " << o.TRACKTOLBEFOREEG << ";\n";
  if o.TRACKTOLDURINGEG =!= -1 then
    f << "TRACKTOLDURINGEG: " << o.TRACKTOLDURINGEG << ";\n";
  if o.FINALTOL =!= -1 then
    f << "FINALTOL: " << o.FINALTOL << ";\n";
  if o.MAXNORM =!= -1 then
    f << "MAXNORM: " << o.MAXNORM << ";\n";
  if o.MINSTEPSIZEBEFOREEG =!= -1 then
    f << "MINSTEPSIZEBEFOREEG: " << o.MINSTEPSIZEBEFOREEG << ";\n";
  if o.MINSTEPSIZEDURINGEG =!= -1 then
    f << "MINSTEPSIZEDURINGEG: " << o.MINSTEPSIZEDURINGEG << ";\n";
  if o.IMAGTHRESHOLD =!= -1 then
    f << "IMAGTHRESHOLD: " << o.IMAGTHRESHOLD << ";\n";
  if o.COEFFBOUND =!= -1 then
    f << "COEFFBOUND: " << o.COEFFBOUND << ";\n";
  if o.DEGREEBOUND =!= -1 then
    f << "DEGREEBOUND: " << o.DEGREEBOUND << ";\n";
  if o.CONDNUMTHRESHOLD =!= -1 then
    f << "CONDNUMTHRESHOLD: " << o.CONDNUMTHRESHOLD << ";\n";
  if o.RANDOMSEED =!= -1 then
    f << "RANDOMSEED: " << o.RANDOMSEED << ";\n";
  if o.SINGVALZEROTOL =!= -1 then
    f << "SINGVALZEROTOL: " << o.SINGVALZEROTOL << ";\n";
  if o.ENDGAMENUM =!= -1 then
    f << "ENDGAMENUM: " << o.ENDGAMENUM << ";\n";
  if o.USEREGENERATION =!= -1 then
    f << "USEREGENERATION: " << o.USEREGENERATION << ";\n";
  if o.SECURITYLEVEL =!= -1 then
    f << "SECURITYLEVEL: " << o.SECURITYLEVEL << ";\n";
  if o.SCREENOUT =!= -1 then
    f << "SCREENOUT: " << o.SCREENOUT << ";\n";
  if o.OUTPUTLEVEL =!= -1 then
    f << "OUTPUTLEVEL: " << o.OUTPUTLEVEL << ";\n";
  if o.STEPSFORINCREASE =!= -1 then
    f << "STEPSFORINCREASE: " << o.STEPSFORINCREASE << ";\n";
  if o.MAXNEWTONITS =!= -1 then
    f << "MAXNEWTONITS: " << o.MAXNEWTONITS << ";\n";
  if o.MAXSTEPSIZE =!= -1 then
    f << "MAXSTEPSIZE: " << o.MAXSTEPSIZE << ";\n";
  if o.MAXNUMBERSTEPS =!= -1 then
    f << "MAXNUMBERSTEPS: " << o.MAXNUMBERSTEPS << ";\n";
  if o.MAXCYCLENUM =!= -1 then
    f << "MAXCYCLENUM: " << o.MAXCYCLENUM << ";\n";
  if o.REGENSTARTLEVEL =!= -1 then
    f << "REGENSTARTLEVEL: " << o.REGENSTARTLEVEL << ";\n";

  -- now we handle the various runType options:
  if o.runType == 1 then --param run -- startSystem and startSolutions should be nonempty...add sanity check???
    f << "USERHOMOTOPY: 1;\n";
  if o.runType == 2 then --pos dim run
    f << "TRACKTYPE: 1;\n";
  if o.runType == 3 then --sample component -- need dim and compnum from user, along with witness_data file (in file or data type???), then need to create short script to handle interactive session 
    f << "TRACKTYPE: 2;\n";
  if o.runType == 4 then --membership test -- need to create file from pts (o.pts should be nonempty!)
    f << "TRACKTYPE: 3;\n";
  if o.runType == 5 then --refine solutions -- need to create file from pts (o.pts should be nonempty, and digits should be specified by user)
    f << "SHARPENONLY: 1;\n";
 
  f << endl << "END;\n\n";  -- end of config section

  -- The following block is the input section of the input file
  f << "INPUT" << endl << endl;
  if o.runType==1 then  -- if user-defined, declaration type of vars is "variable"
    f << "variable "
  else f << "variable_group "; -- if not user-defined, dec type of vars if "variable_group"
  scan(#v, i->  -- now we list the variables in a single list  ...  What about an mhom structure???
       if i<#v-1 
       then f << toString v#i << ", "
       else f << toString v#i << ";" << endl
       );
  f << "function "; -- "function" section
  scan(#T, i-> -- here are the function names
       if i<#T-1
       then f << "f" << i << ", "
       else f << "f" << i << ";" << endl << endl
      );
  bertiniNumbers := p->( L := toString p; -- bertiniNumbers is a method that takes in "p" (list of polynomials) and returns them with ii replaced with I, e replaced with E (don't know why the latter)???
       L = replace("ii", "I", L); 
       L = replace("e", "E", L);
       L
       );
  if (o.runType!=1) -- non-param runs: just write out the polynomials
    then scan(#T, i -> f << "f" << i << " = " << bertiniNumbers T#i << ";" << endl) 
  else (  -- param runs: write out polys AND other junk (see next several lines!)
       if #o.StartSystem != #T then error "expected equal number of equations in start and target systems";
       f << "pathvariable t;\n" 
         << "parameter s;\n"
         << "s = t;\n\n";  -- need to make gamma a random number here !!!???
       scan(#T, i -> f << "f" << i 
	    << " = (" << bertiniNumbers T#i << ")*(1-s)+s*("<< bertiniNumbers o.gamma << ")*(" << bertiniNumbers o.StartSystem#i << ");" << endl 
	   );
       );
  f << endl << "END;" << endl << endl;
  close f;

  --Now we build auxilary files for various sorts of runs:
  if (o.runType==1) then ( -- writing out start file in the case of a param run
       f = openOut (dir|"/start"); -- the only name for Bertini's start solutions file 
       f << #o.StartSolutions << endl << endl;
       scan(o.StartSolutions, s->(
		 scan(s, c-> f << realPart c << " " << imaginaryPart c << ";" << endl );
		 f << endl;
		 ));
       close f;
       );

  if (o.runType==4) then ( -- writing out file with points in the case of a membership run
       f = openOut (dir|"/member_points"); -- the only name for Bertini's membership points file 
       f << #o.StartSolutions << endl << endl;
       scan(o.StartSolutions, s->(
		 scan(s, c-> f << realPart c << " " << imaginaryPart c << ";" << endl );
		 f << endl;
		 ));
       close f;
       );


  if (o.runType==5) then ( -- writing out file with points in the case of a refine run
       f = openOut (dir|"/points"); -- the only name for Bertini's sharpening points file 
       f << #o.StartSolutions << endl << endl;
       scan(o.StartSolutions, s->(
		 scan(s, c-> f << realPart c << " " << imaginaryPart c << ";" << endl );
		 f << endl;
		 ));
       close f;

       f = openOut (dir|"/sharpen_script"); -- writing out file with query responses in case of a refine/sharpen run
       f << "5" << endl << o.digits << endl << "2" << endl << "points" << endl;
       close f;
       );

  if (o.runType==3) then ( -- writing out file with query responses in case of a sample run
       f = openOut(dir|"/sample_script");
       f << o.dimen << endl << o.compnum << endl << o.numpts << endl << "0" << endl << "sample_points" << endl;  -- sampled points will be written file named sample_points
       close f;
       );

  stdio << "Temporary directory for input and output files:" << dir << endl << endl;
  dir
  )

cleanupOutput = method(TypicalValue=>String)
cleanupOutput String := s -> (
-- cleanup output (Bertini and hom4ps2)
  t := replace("E", "e", s);
  t = replace("[(,)]","", t);
  t = replace("e\\+","e",t)
  )

readSolutionsBertini = method(TypicalValue=>List)
readSolutionsBertini (String,String) := (dir,f) -> (  -- dir=directory holding the output files, f=file name from which to grab solutions
  s := {};
  if f == "finite_solutions" then (
       --print "implementation unstable: Bertini output format uncertain";
       l := lines get (dir|"/"|f);
       nsols := value first separate(" ", l#0);
       l = drop(l,2);
       while #s < nsols do (	 
	    coords := {};
	    while #(first l) > 2 do ( 
	      	 coords = coords | {(
		   	   a := separate(" ",  cleanupOutput(first l));	 
		   	   (value a#0)+ii*(value a#1)
	      	   	   )};
    	      	 l = drop(l,1);
	      	 );	
	    l = drop(l,1);
            if DBG>=10 then << coords << endl;
	    s = s | {{coords}};
	    );	
       ) 
  else if f == "raw_solutions" then (
       l = lines get (dir|"/"|f);
       while #l>0 and #separate(" ", l#0) < 2 do l = drop(l,1);
       while #l>0 do (
	    if DBG>=10 then << "------------------------------" << endl;
	    coords = {};
	    while #l>0 and #separate(" ", l#0) >= 2 do ( 
	      	 coords = coords | {(
		   	   a = separate(" ",  cleanupOutput(first l));	 
		   	   (value a#0)+ii*(value a#1)
	      	   	   )};
    	      	 l = drop(l,1);
	      	 );
	    while #l>0 and #separate(" ", l#0) < 2 do l = drop(l,1);
            if DBG>=10 then << coords << endl;
	    s = s | {{coords}};
	    );     
    ) else error "unknown output file";
  s
  )

trackBertini = method(TypicalValue => List)
trackBertini (List,List,List,MutableHashTable) := List => (S,T,solsS,o) -> (
     -- tempdir := temporaryFileName() | "NumericalAlgebraicGeometry-bertini";
     -- mkdir tempdir; 	  
     dir := makeBertiniInput(T, StartSystem=>S, StartSolutions=>solsS, gamma=>o.gamma);
     compStartTime := currentTime();      
     run("cd "|dir|"; "|BERTINIexe|" >bertini_session.log");
     if DBG>0 then << "Bertini's computation time: " << currentTime()-compStartTime << endl;
     readSolutionsBertini(dir, "raw_solutions")
     )



--##########################################################################--
-- DOCUMENTATION
--##########################################################################--

beginDocumentation()

--doc ///
--  Key
--    Bertini
--  Headline
--    software for numerical algebraic geometry
--  Description
--    Text
--      Interfaces the functionality of the software {\tt Bertini}
--      to solve polynomial systems and perform calculations in
--      {\em numerical algebraic geometry}.  The software is available at
--      @HREF"http://www.nd.edu/~sommese/bertini/"@.
--      The site currently provides only executable versions named {\tt bertini} or {\tt bertini.exe} (for Cygwin).
--      The user must have the executable program {\tt phc} available,
--      preferably in the executation path.
--
--      Below is a simple example using the most popular function,
--      a basic zero-dimensional solve with no special options.
--    Example
--      R = CC[x,y]
--      F = {x^2-1,y^2-1}
--      solns = bertiniSolve(F)
--///;

--doc ///
--  Key 
--    bertiniSolve
--    (bertiniSolve,List)
--    (bertiniSolve,List,HashTable)
--  Headline
--    temporarily a method for doing a zero-dimensional Bertini run, soon to be deprecated
--  Usage
--    S = bertiniSolve F
--  Inputs
--    F:List
--      whose entries are polynomials (system need not be square) 
--  Outputs
--    S:List
--      whose entries are the solutions found by Bertini, with junk points removed if system is not square
--  Description
--    Text
--      For now, this function simply builds a Bertini style input file from F and calls Bertini on 
--      this input file.  Solutions are currently pulled from machine readable file finitesolutions
--      and returned as a list.
--    Example
--      R = CC[x,y]
--      F = {x^2-1,y^2-1}
--      S = bertiniSolve F
--///;



end
