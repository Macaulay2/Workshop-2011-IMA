newPackage(
	"NumericalTropicalVariety",
	Version => "0.7",
	Date=> "July 21, 2011",
	Authors => {
			{Name=>"Henry Duong", Email=>"henry.y.duong@gmail.com"},
			{Name=>"Anton Leykin", Email=>"leykin@math.gatech.edu"},
			{Name=>"Josephone Yu", Email=>"josephine.yu@math.gatech.edu"}						
			},
	Headline=> "Calculates the Tropical Variety of an Ideal by Numerical Methods",
	DebuggingMode=> true
	)

export{sampleAmoeba, Factor, Multiplier, Extra, Tolerance}

needsPackage "NumericalAlgebraicGeometry"

sampleAmoeba=method(Options=>{Factor=>5_RR, Multiplier=>1000_RR, Extra=>1000_CC, Tolerance=>0.00001_RR})
sampleAmoeba (Ideal) := o -> (I) -> (
     R := ring I;
     n := numgens R;
     logsols1:={};
     logsols2:={};
     for i from 0 to (2*n-1) do (
	       C:=determinecut(I, i, o#Extra, o#Tolerance);
     	       curraxis := R_(i//2);
	       sys := I_*|{curraxis+C^((-1)^i)};
     	       print sys;
     	       sols := solveSystem sys;
     	       print sols;  
               regsols :=select(sols, s->status s == Regular);
     	       ref := refine(sys,regsols);
	       print "carry";
      	       print ref;
     	       sys2 := I_*|{curraxis+((o#Factor)^((-1)^i))*C^((-1)^i)};
	       sols2 :={};
	       if #ref == 0 then sols2 = solveSystem sys2 else sols2 = track(sys, sys2, ref/coordinates);
	       print sys2;
               print "sols2";
	       print sols2;
               --print "midcount";
	       --print {#ref};
               --print {#sols2};
               regsols2 :={};
	       refadjust :={};
               for i from 0 to #sols2-1 do (
			if status(sols2#i)== Regular then (
				regsols2=regsols2 | {sols2#i};
				refadjust=refadjust | {ref#i}
			);
	       );
	--       print "reduced ref?";
	       ref=reverse(refadjust);
	       regsols2=reverse(regsols2);
     	       ref2 := refine(sys2,regsols2);
	       print ref2;
	       logsols1 = logsols1 | (ref/(s->apply(coordinates s, c->log abs c)));
     	       logsols2 = logsols2 | (ref2/(s->apply(coordinates s, c->log abs c)));
               print "count";
	       print {#logsols1};
               print {#logsols2}
     );
     print logsols1;
     print logsols2;
     print (logsols2-logsols1);	
     result :={};
     for i from 0 to ((#(logsols2-logsols1))-1) do
	(
		result=result|{ShortApproxCollinearVectorAlt((logsols2-logsols1)#(i-1), (o#Multiplier))}
	);
     result=unique(reverse(result));
     return result;
     )

ShortApproxCollinearVector = method()
ShortApproxCollinearVector (List, RR) := (p, multiplier) -> (
     print p;
     n := #p;
     if n < 2 then return p; -- check for special case
     x := local x;
     R := CC[x_1..x_n]; --RR
     pivot := max(p/abs);
     pivotloc :=0;
     for i from 0 to n-1 do (
        	if abs(p#(i))== pivot then (pivotloc = i; break;)
     ); --position
     --print pivot;
     --print pivotloc;
     M := mutableMatrix(random(R^(n-1), R^n)); --generate the upper matrix
     for i from 0 to pivotloc-1 do(
	for j from 0 to n-1 do(
		if i==j then M_(i,j)=-R_(pivotloc) else (if j==pivotloc then M_(i,j)=R_(i) else M_(i,j)=0);
	);
     ); --replace R_ with p#
     for i from pivotloc to n-2 do(
        for j from 0 to n-1 do(
		if i+1==j then M_(i,j)=-R_(pivotloc) else (if j==pivotloc then M_(i,j)=R_(i+1) else M_(i,j)=0);
	);
     );
     M = matrix(M) || map R^n; --multiplier/m
     --print M;
     m := max(p/abs); --pivot
     RtoCC := map(coefficientRing R, R, matrix{(multiplier/m)*p});
     Mp := matrix (entries RtoCC M /(r->r/floor@@realPart));
     L := LLL Mp;
     --print toString (Mp,L);
     v := flatten entries L_{0}^(toList(n-1..2*n-2));
     i := position(v, x->x!=0);
     if v#i*p#i<0 then v=-v;
     print v;
     return v; 
     ) 

ShortApproxCollinearVectorAlt = method()
ShortApproxCollinearVectorAlt (List, RR) := (p, multiplier) -> (
     print p;
     n := #p;
     if n < 2 then return p; -- check for special case
     pivot := max(p/abs);
     pivotloc :=position(p, s->abs(s)==pivot); 
     M := mutableMatrix(random(RR^(n-1), RR^n)); --generate the upper matrix
     for i from 0 to pivotloc-1 do(
	for j from 0 to n-1 do(
		if i==j then M_(i,j)=-p#(pivotloc) else (if j==pivotloc then M_(i,j)=p#(i) else M_(i,j)=0);
	);
     ); 
     for i from pivotloc to n-2 do(
        for j from 0 to n-1 do(
		if i+1==j then M_(i,j)=-p#(pivotloc) else (if j==pivotloc then M_(i,j)=p#(i+1) else M_(i,j)=0);
	);
     );
     print M;
     M = matrix(M)*(multiplier/pivot);
     Mzz := mutableMatrix(random(ZZ^(n-1),ZZ^n));
     for i from 0 to n-2 do(
	for j from 0 to n-1 do(
		Mzz_(i,j)=round(M_(i,j));
	);
     ); 
     M = matrix(Mzz) || map ZZ^n;
     L := LLL M;
     --print toString (Mp,L);
     v := flatten entries L_{0}^(toList(n-1..2*n-2));
     i := position(v, x->x!=0);
     if v#i*p#i<0 then v=-v;
     print v;
     return v; 
     ) 

ShortApproxCollinearVectorAlt2 = method()
ShortApproxCollinearVectorAlt2 (List, RR) := (p, multiplier) -> (
     print p;
     n := #p;
     if n < 2 then return p; -- check for special case
     nchoose2:= n!/((n-2)!*2!);
     pivot := max(p/abs);
     --pivotloc :=position(p, s->abs(s)==pivot); 
     M := mutableMatrix(random(RR^(nchoose2), RR^n)); --generate the upper matrix
     rownum :=0;
     for i from 0 to n-1 do(
	for j from i+1 to n-1 do(
		for k from 0 to n-1 do(
			if k==i then M_(rownum,k)=p#k else (if k==j then M_(rownum,k)=-p#k else M_(rownum,k)=0);		
		);
		rownum = rownum+1;
	);
     ); 
     print M;
     M = matrix(M)*(multiplier/pivot);
     Mzz := mutableMatrix(random(ZZ^(n-1),ZZ^n));
     for i from 0 to n-2 do(
	for j from 0 to n-1 do(
		Mzz_(i,j)=round(M_(i,j));
	);
     ); 
     M = matrix(Mzz) || map ZZ^n;
     L := LLL M;
     --print toString (Mp,L);
     v := flatten entries L_{0}^(toList(n-1..2*n-2));
     i := position(v, x->x!=0);
     if v#i*p#i<0 then v=-v;
     print v;
     return v; 
     ) 

determinecut=method()
determinecut (Ideal,ZZ, CC, RR) := (I,n, MyExtra, Tolerance) -> (
	R := ring I;
	curraxis := R_(n//2); --n//2
	Jh=det(jacobian(ideal(I_*|{curraxis})));
	sys := I_*|{Jh};
	--print sys;
	try (
		sols := solveSystem sys;
	) then (        
		print "singularities";		
		--print sols;
		regsols :=select(sols, s->status s == Regular);
		print regsols;
		print "end singularities";
		curraxisvals :={};
		for i from 0 to #regsols -1 do (
			if abs((coordinates(regsols#i))#(n//2)) > Tolerance then curraxisvals = curraxisvals | {(coordinates(regsols#i))#(n//2)};	
		);
		mymax := max(curraxisvals/abs);
		mymin := min(curraxisvals/abs);
		if mymax >= (1_CC/mymin) then return mymax+MyExtra else return (1_CC/mymin)+MyExtra;
	) else (
		return MyExtra;
	)	
     ) 

beginDocumentation()
document { 
	Key => Amoeba Sampling,
	Headline => "an example Macaulay2 package",
	EM "PackageTemplate", " is an example package which can
	be used as a template for user packages."
	}
document {
	Key => {firstFunction, (firstFunction,ZZ)},
	Headline => "a silly first function",
	Usage => "firstFunction n",
	Inputs => {
		"n" => ZZ => {}
		},
	Outputs => {
		String => {}
		},
	"This function is provided by the package ", TO PackageTemplate, ".",
	EXAMPLE {
		"firstFunction 1",
		"firstFunction 0"
		}
	}
document {
	Key => secondFunction,
	Headline => "a silly second function",
	"This function is provided by the package ", TO PackageTemplate, "."
	}
document {
	Key => (secondFunction,ZZ,ZZ),
	Headline => "a silly second function",
	Usage => "secondFunction(m,n)",
	Inputs => {
	     "m" => {},
	     "n" => {}
	     },
	Outputs => {
	     {"The sum of ", TT "m", ", and ", TT "n", 
	     ", and "}
	},
	EXAMPLE {
		"secondFunction(1,3)",
		"secondFunction(23213123,445326264, MyOption=>213)"
		}
	}
document {
     Key => MyOption,
     Headline => "optional argument specifying a level",
     TT "MyOption", " -- an optional argument used to specify a level",
     PARA{},
     "This symbol is provided by the package ", TO PackageTemplate, "."
     }
document {
     Key => [secondFunction,MyOption],
     Headline => "add level to result",
     Usage => "secondFunction(...,MyOption=>n)",
     Inputs => {
	  "n" => ZZ => "the level to use"
	  },
     Consequences => {
	  {"The value ", TT "n", " is added to the result"}
	  },
     "Any more description can go ", BOLD "here", ".",
     EXAMPLE {
	  "secondFunction(4,6,MyOption=>3)"
	  },
     SeeAlso => {
	  "firstFunction"
	  }
     }

end;

