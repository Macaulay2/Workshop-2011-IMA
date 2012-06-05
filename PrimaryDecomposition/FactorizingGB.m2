variables = {3283=>"DAGE", 3096=>"PtP2", 2909=>"Akt", 1952=>"KdStarPgStar",
319=>"G", 1683=>"KdStarPg", 2321=>"KdStarPgStarP2", 2921=>"AktP3", 2855=>"P3",
1370=>"KdStarGStarP3kP3", 622=>"KdStarGStar", 331=>"GP3",
1904=>"KdStarGStarP3kStar", 2933=>"AktStar", 2867=>"DAG", 1382=>"GStarP3kP3",
2273=>"KdStarGStarP3kStarP2", 634=>"KdStarGStarP3", 343=>"Pg",
1916=>"KdStarGStarP3kStarP3", 3319=>"E", 1647=>"GStarPgP3",
1394=>"KdStarGStarP3k", 2285=>"KdStarGStarP3kStarP3P2", 646=>"GStarP3",
421=>"KdStarG", 1928=>"KdStarGStarPgStarP3", 3331=>"Pt", 3188=>"PtP3P2",
1659=>"KdStarGStarPgP3", 2297=>"KdStarGStarPgStarP3P2", 295=>"KdStar",
433=>"KdStarGP3", 3271=>"PtP3", 1940=>"KdStarGStarPgStar",
2309=>"KdStarGStarPgStarP2", 1671=>"KdStarGStarPg", 2254=>"P2", 307=>"P3k"}

reactions = [[["1370"], ["307", "634"]], [["634", "307"], ["1370"]], [["1659"], ["295",
"1647"]], [["1647", "295"], ["1659"]], [["1647"], ["646", "343"]], [["343",
"646"], ["1647"]], [["1382"], ["307", "646"]], [["307", "646"], ["1382"]],
[["3283"], ["3319", "2867"]], [["2867", "3319"], ["3283"]], [["3271"],
["2855", "3331"]], [["2855", "3331"], ["3271"]], [["2297"], ["1659", "2867"]],
[["2309"], ["1671", "2867"]], [["2321"], ["2867", "1683"]], [["2285"],
["1370", "2855"]], [["2273"], ["2855", "1394"]], [["646", "295"], ["634"]],
[["634"], ["646", "295"]], [["433"], ["634"]], [["421"], ["622"]], [["1370"],
["1382", "295"]], [["295", "1382"], ["1370"]], [["634"], ["622", "2855"]],
[["622", "2855"], ["634"]], [["3188"], ["3096", "2254"]], [["3096"], ["3331",
"2254"]], [["3331", "2254"], ["3096"]], [["1659"], ["1928"]], [["1671"],
["1940"]], [["1683"], ["1952"]], [["1370"], ["1916"]], [["1394"], ["1904"]],
[["343", "295"], ["1683"]], [["3283"], ["3319", "2254"]], [["433"], ["331",
"295"]], [["3271"], ["2254", "3331"]], [["331", "295"], ["433"]], [["331"],
["2855", "319"]], [["2921"], ["2933", "2855"]], [["2855", "319"], ["331"]],
[["2921"], ["2855", "2909"]], [["2909", "2855"], ["2921"]], [["421"], ["295",
"319"]], [["295", "319"], ["421"]], [["3188"], ["3096", "2855"]], [["2855",
"3096"], ["3188"]], [["2297"], ["1928", "2254"]], [["2254", "1928"],
["2297"]], [["2309"], ["1940", "2254"]], [["1940", "2254"], ["2309"]],
[["2321"], ["1952", "2254"]], [["2254", "1952"], ["2321"]], [["2285"],
["1916", "2254"]], [["1916", "2254"], ["2285"]], [["2273"], ["1904", "2254"]],
[["2254", "1904"], ["2273"]], [["1659"], ["343", "634"]], [["343", "634"],
["1659"]], [["1671"], ["343", "622"]], [["622", "343"], ["1671"]], [["1683"],
["343", "295"]], [["1394"], ["307", "622"]], [["307", "622"], ["1394"]]]


makeRing = method()
makeRing List := variables -> (
  v := apply(variables, pair -> "x" | (toString first pair) );
  --ZZ/30011[v]
  QQ[v]
)

makeIdeal = method()
makeIdeal Array := reactions -> (
  transitions := apply( toList reactions, pair -> (
    input := product(first pair, v -> value ("x" | (toString v)));
    output := product(last pair, v -> value ("x" | (toString v)));
    {input, output }
    ));
  --ideal apply(transitions, t -> (
  --  source := first t;
  --  target := last t;
  --  source * ( target - source )
  --  )
  --)
  LL := sort apply(transitions, l -> sort l); -- sort all reactions to find reversible reactions 
  i = 0;
  ideal flatten while( i < #LL) list (
    a := LL#i;
    b := LL#((i+1)%#LL);
    source := first LL#i;
    target := last LL#i;
    if a == b then  (  -- reversible interaction
      --print "reversible";
      i = i + 2;
      {source - target}
    )
    else (
      i = i + 1;
      -- keep the order from original list
      if member( {source, target}, transitions ) then (
        --print "member";
        --print {source,target};
        {source * ( target - source )} 
      )
      else (
        --print "not member";
        --print {source,target};
        {target*(source - target) }
      )
    )
  )
)

makeNaiveIdeal = method()
makeNaiveIdeal Array := reactions -> (
  transitions := apply( toList reactions, pair -> (
    input := product(first pair, v -> value ("x" | (toString v)));
    output := product(last pair, v -> value ("x" | (toString v)));
    {input, output }
    ));
  ideal apply(transitions, t -> (
    source := first t;
    target := last t;
    source * ( target - source )
    )
  ))

-- returns true if larger is not a superset of smaller
notSuperset = method()
notSuperset(Set, Set) := (smaller, larger) -> (
  assert( #smaller <= #larger);
  if (#smaller == #larger) then return smaller =!= larger;
  return not all(toList smaller, e -> member(e, larger) )
  )

getInclusionMinimalSets = method()
getInclusionMinimalSets List := D -> (
  siphons := apply(D, P -> (
    --set sort select( gens R, x -> x % P == 0 )
    set sort select( flatten entries gens gb P, f -> size f == 1 )
    )
  );
  siphons = (sort apply(siphons, s -> {#s, s} )) / last;

  -- get the inclusion minimal subsets
  -- sets with smallest number of elements first
  -- the first element is certainly minimal, remove it and all supersets from sihpons, add the first element to minimalSiphons
  -- then continue on smaller siphon list
  minimalSiphons := {};
  while ( #siphons > 0 ) do (
    P := first siphons;
    minimalSiphons = minimalSiphons | {toList P};
    siphons = select( siphons, s -> notSuperset(P,s));
  );
  minimalSiphons
)  

translateVarsToNames = method()
translateVarsToNames (List, List) := (variables,Siphons) -> (
  v := apply(variables, pair -> value ("x" | (toString first pair) ) => last pair );
  H := new HashTable from v ;
  apply(minimalSiphons, S -> (
    apply( S, s->  H#s ) 
  ) )
)

factors = (F) -> (
     facs := factor F;
     facs = apply(#facs, i -> (facs#i#1, (1/leadCoefficient facs#i#0) * facs#i#0 ));
     select(facs, (n,f) -> # support f =!= 0))

findElementThatFactors = method()
findElementThatFactors(Ideal, Set) := (I, nonzeros) -> (
     for f in I_* do (
	  facs := factors f;
	  if #facs > 1 or (#facs == 1 and facs#0#0 > 1) then return (f,facs/last);
	  );
     (f, {})
     )

facGB0 = method()
facGB0(Ideal, Set) := (I, nonzeros) -> (
     -- returns a pair (P:List, L:List)
     --  where : P is a list of ideals, that have no factorization left.
     --  and     L is a list of (J:ideal, nonz: nonzeros), 
     --    where J is an ideal containing I, and nonz is a set of monic polynomials, which are not in the resulting min primes
     (f, facs) := findElementThatFactors(I, nonzeros); -- chooses a generator of I that factors
     if #facs == 0 then ( 
	  --<< "no elements found that factor" << endl; << "ideal is " << toString I << endl; 
	  return ((I, nonzeros), {})
	  );
     prev := set{};
     ({}, for g in toList(set facs - nonzeros) list (
	  if member(g, nonzeros) then continue;
	  J := trim(ideal(g) + I);
	  J = trim ideal apply(J_*, f -> (
		    product toList (set ((factors f)/last) - nonzeros)
	       ));
          if numgens J === 1 and J_0 == 1 then continue;
	  result := (J, nonzeros + prev);
	  prev = prev + set{g};
	  result
	  ))
     )

facGB = method(Options=>{Limit=>infinity})
facGB Ideal := opts -> (J) -> (
     C = {};
     L = {(J,set{})};
     i := 0;
     while i < opts.Limit and #L > 0 do (
     	  L2 := flatten for j in L list (
     	       (C1,L1) = facGB0 j;
	       if C1 =!= {} then C = append(C, C1);
	       L1
	       );
     	  L = L2;
     	  << "number: " << (i, #C, #L) << endl;
     	  --<< "C = " << netList C << endl;
     	  --<< "L = " << netList L << endl;
	  i = i+1;
     	  );
     (C, L)     
     )

end


restart
load "siphons.m2"
load "newGTZ.m2"
reactions
variables 
R = makeRing variables
I = makeIdeal reactions + ideal product gens R;

-- try myPD:
gbTrace=3
gens gb I;
myPD(I, Strategy=>{GeneralPosition}, Verbosity=>2)

J = minimalPresentation(I)
L = ideal(J_*/(f -> (factorize f)/last//product))
myPD(L, Strategy=>{GeneralPosition}, Verbosity=>2)

-- try Singular PD:
D = singularPD I;
minimalSiphons = getInclusionMinimalSets D;
myRes = translateVarsToNames( variables, minimalSiphons)
scan(myRes, S -> print toString S )

load "results.tmp"
sort apply(myRes, S -> sort S )
sort apply(result, S -> sort S )
oo === ooo
--time D = decompose (I + ideal product gens R)



restart
R = QQ[R1,R2,GL1,GL2,GR1,GR2,E1,E2,F1,F2]
transitions = { {R1*F1, GL1},
{GL1*F2, GR1},
{GR1, E1},
{E1, R1*F1*F2},
{R2*F2, GL2},
{GL2*F1, GR2},
{GR2, E2},
{E2, R2*F1*F2}}



II = last select(D, P-> (
  #set sort select( flatten entries gens P, f -> size f == 1 ) == 1 ) )

select(gens R, x -> x%II == 0 ) 


--time D = decompose (I + ideal product gens R)
siphons = apply(D, P -> (
  --set sort select( gens R, x -> x % P == 0 )
  set sort select( flatten entries gens gb P, f -> size f == 1 )
  )
)
siphons = (sort apply(siphons, s -> {#s, s} )) / last

-- get the inclusion minimal subsets
-- sets with smallest number of elements first
-- the first element is certainly minimal, remove it and all supersets from sihpons, add the first element to minimalSiphons
-- then continue on smaller siphon list
minimalSiphons = {}
while ( #siphons > 0 ) do (
  P := first siphons;
  minimalSiphons = minimalSiphons | {toList P};
  siphons = select( siphons, s -> notSuperset(P,s));
)

select(variables, v-> last v == "KdStar")

end

notSuperset({1,2}, {1,3})
notSuperset({1,2}, {1,2,3})
notSuperset({1,2}, {1,2,3,4})
notSuperset({1,2}, {1,3,4})

I := (0..20)
j := 0;
while( member (18, I) ) do (
  j = j + 1;
  I = (0..(20 - j));
  print j
  )


{{x1370, x634*x307}, {x634*x307, x1370}, {x1659, x1647*x295}, {x1647*x295, x1659}, {x1647, x343*x646}, {x343*x646, x1647}, {x1382, x646*x307}, {x646*x307, x1382}, {x3283, x2867*x3319}, {x2867*x3319, x3283}, {x3271, x2855*x3331}, {x2855*x3331, x3271}, {x2297, x2867*x1659}, {x2309, x2867*x1671}, {x2321, x1683*x2867}, {x2285, x2855*x1370}, {x2273, x2855*x1394}, {x646*x295, x634}, {x634, x646*x295}, {x433, x634}, {x421, x622}, {x1370, x1382*x295}, {x1382*x295, x1370}, {x634, x2855*x622}, {x2855*x622, x634}, {x3188, x3096*x2254}, {x3096, x3331*x2254}, {x3331*x2254, x3096}, {x1659, x1928}, {x1671, x1940}, {x1683, x1952}, {x1370, x1916}, {x1394, x1904}, {x343*x295, x1683}, {x3283, x3319*x2254}, {x433, x331*x295}, {x3271, x3331*x2254}, {x331*x295, x433}, {x331, x319*x2855}, {x2921, x2855*x2933}, {x319*x2855, x331}, {x2921, x2909*x2855}, {x2909*x2855, x2921}, {x421, x319*x295}, {x319*x295, x421}, {x3188, x3096*x2855}, {x3096*x2855, x3188}, {x2297, x1928*x2254}, {x1928*x2254, x2297}, {x2309, x1940*x2254}, {x1940*x2254, x2309}, {x2321, x1952*x2254}, {x1952*x2254, x2321}, {x2285, x1916*x2254}, {x1916*x2254, x2285}, {x2273, x1904*x2254}, {x1904*x2254, x2273}, {x1659, x634*x343}, {x634*x343, x1659}, {x1671, x622*x343}, {x622*x343, x1671}, {x1683, x343*x295}, {x1394, x622*x307}, {x622*x307, x1394}}

                                                                ideal(x1940*x1671-x1671^2,-x622*x343+x1671,-x1940*x2254+x2309,x2867*x2309*x1671- x2309^2,x3331*x3271*x2254-x3271^2,-x2855*x3331+x3271,x634*x433-x433^2,-x331*x295+ x433,-x1928*x2254+x2297,x2867*x1659*x2297-x2297^2,x1928*x1659-x1659^2,-x1647*x295+ x1659,-x634*x343+x1659,x3096*x3188*x2254-x3188^2,-x3096*x2855+x3188,x622*x421-x421 ^2,-x319*x295+x421,-x1916*x2254+x2285,x2855*x1370*x2285-x2285^2,x1904*x1394-x1394^ 2,-x622*x307+x1394,-x343*x646+x1647,-x1370^2+x1370*x1916,-x646*x295+x634,-x2855* x622+x634,-x1904*x2254+x2273,x2855*x2273*x1394-x2273^2,-x646*x307+x1382,-x319* x2855+x331,-x634*x307+x1370,-x1382*x295+x1370,x2921*x2855*x2933-x2921^2,-x2909* x2855+x2921,-x1952*x2254+x2321,x1683*x2321*x2867-x2321^2,x1952*x1683-x1683^2,-x343 *x295+x1683,-x3331*x2254+x3096,x3283*x3319*x2254-x3283^2,-x2867*x3319+x3283,x3283* x3096*x2909*x1952*x319*x1683*x2321*x2921*x2855*x1370*x622*x331*x1904*x2933*x2867* x1382*x2273*x634*x343*x1916*x3319*x1647*x1394*x2285*x646*x421*x1928*x3331*x3188* x1659*x2297*x295*x433*x3271*x1940*x2309*x1671*x2254*x307)

{3283 => DAGE, 3096 => PtP2, 2909 => Akt, 1952 => KdStarPgStar, 319 => G, 1683 => KdStarPg, 2321 => KdStarPgStarP2, 2921 => AktP3, 2855 => P3, 1370 => KdStarGStarP3kP3, 622 => KdStarGStar, 331 => GP3, 1904 => KdStarGStarP3kStar, 2933 => AktStar, 2867 => DAG, 1382 => GStarP3kP3, 2273 => KdStarGStarP3kStarP2, 634 => KdStarGStarP3, 343 => Pg, 1916 => KdStarGStarP3kStarP3, 3319 => E, 1647 => GStarPgP3, 1394 => KdStarGStarP3k, 2285 => KdStarGStarP3kStarP3P2, 646 => GStarP3, 421 => KdStarG, 1928 => KdStarGStarPgStarP3, 3331 => Pt, 3188 => PtP3P2, 1659 => KdStarGStarPgP3, 2297 => KdStarGStarPgStarP3P2, 295 => KdStar, 433 => KdStarGP3, 3271 => PtP3, 1940 => KdStarGStarPgStar, 2309 => KdStarGStarPgStarP2, 1671 => KdStarGStarPg, 2254 => P2, 307 => P3k}

-------------------------------
-- Mike+Franzi working together
restart
load "siphons.m2"
load "newGTZ.m2"
--reactions
--variables 
R = makeRing variables
I = makeNaiveIdeal reactions --  + ideal product gens R;
J = trim I

findElementThatFactors(I, {})
factor I_0

-- facGB(ideal I) --> return a set of GB's s.t. the radical of I is the intersection of 
--                    the radicals of all the GB ideals.

facGB0(I, nonzeroElems)
factor J_0

L1 = facGB0(J, set{})
L2 = flatten apply(L1, facGB0)
L3 = flatten apply(L2, facGB0)
L8/last
L5/(x -> numgens x#0)
L4 = flatten apply(L3, facGB0);
L5 = flatten apply(L4, facGB0);
#L5
L6 = flatten apply(L5, facGB0);
L7 = flatten apply(L6, facGB0);
L8 = flatten apply(L7, facGB0);
L9 = flatten apply(L8, facGB0);
L10 = flatten apply(L9, facGB0);
L11 = flatten apply(L10, facGB0);


(C1,L1) = facGB0(J, set{}, {})
L2 = flatten apply(L1, facGB0)
L3 = flatten apply(L2, facGB0)
L8/last
L5/(x -> numgens x#0)
L4 = flatten apply(L3, facGB0);
L5 = flatten apply(L4, facGB0);
#L5
L6 = flatten apply(L5, facGB0);
L7 = flatten apply(L6, facGB0);
L8 = flatten apply(L7, facGB0);
L9 = flatten apply(L8, facGB0);
L10 = flatten apply(L9, facGB0);
L11 = flatten apply(L10, facGB0);

time facGB J;
C = oo#0;
#C
C1 = C/(f -> (
	  s := product f#1;
	  if s == 1 then f#0 else saturate(f#0, s)
	  )
     )

C1 = C/(f -> (decompose f#0, f#1))

	  s := product f#1;
	  if s == 1 then f#0 else(f#0, s)
	  )
     )
-- try myPD:
gbTrace=3
gens gb I;
myPD(I, Strategy=>{GeneralPosition}, Verbosity=>2)

J = minimalPresentation(I)
L = ideal(J_*/(f -> (factorize f)/last//product))
myPD(L, Strategy=>{GeneralPosition}, Verbosity=>2)

-- Create a ring in variables a..zA--Z
J1 = J
R1 = (coefficientRing R)[vars(0..numgens R - 1), MonomialSize=>8]
J1 = sub(J1,vars R1)
needsPackage "ExampleIdeals"
"siphon-example.sing" <<  toSingular R1 << endl << toSingular J1 << endl << close
