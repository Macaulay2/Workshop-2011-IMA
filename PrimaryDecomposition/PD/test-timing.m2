-- Code to check the timing of a list of examples, and save the times
-- Then, we can compare different algorithms on these examples

-- the following package is not in the M2 binary distribution (as it is very rough still)
restart
needsPackage "ExampleIdeals"
debug needsPackage "PD"

--ETable = getExampleFile("minprimes-examples.m2")

-- need the following functions:
-- (1) get table
-- (2) run the examples, get timings, save to a file
-- (3) display several different timings next to each other
-- (4) boldface the best?

wallTime = Command (() -> value get ///!date +%s///)
wallTiming = f -> (
    a := wallTime(); 
    r := f(); 
    b := wallTime();  
    << "wall time : " << b-a << " seconds" << endl;
    r);

runExamples = (ETable, Keys, filename, beginString, fcn) -> (
    K := if Keys === null then sort keys ETable else Keys;
    if not fileExists filename then (
         F := openOut filename;
         F << beginString << endl;
         close F;
         );
    doAllExamples := () -> (for k in K do (
        -- run example, with timing
        -- append info to file
        I := value (ETable#k#1);  -- evaluates to an ideal, at least we expect that
        if not instance(I, Ideal) then error "expected an ideal";
        << "running: " << k << ": " << ETable#k#0 << flush;
        t := timing (fcn I);
        << "  " << t#0 << endl;
        F = openOutAppend filename;
        F << "\"" << ETable#k#0 << "\" => " << t#0 << endl;
        close F;
        ));
     wallTiming doAllExamples
    )

readResults = method()
readResults String := (filename) -> (
    L := lines get filename;
    LV := L/value;
    header := substring(L#0, 2, #L#0-2);
    (header, hashTable select(LV, f -> f =!= null)))

num2str = (n) -> (
    -- n should be a non-negative real number.  Returns a string rep of the number
    -- where there are exactly 3 digits after the .
    -- 
    m := round(n * 1000.);
    s := toString m;
    if m < 0 then error("expected non-negative number, but received "|s);
    if #s < 3 then (
        "." | concatenate((3-#s):"0")  | s)
    else (
        substring(s, 0, #s-3) | "." | substring(s, #s-3, 3)
    ))

combineResults = method()
combineResults List := (L) -> (
    -- L is a list of filenames (later, could be hash tables of results?)
    R := L/readResults;
    k := R/last/keys//join//flatten//unique//sort;
    firstrow := prepend("", R/first);
    prepend(firstrow, for k1 in k list (
        prepend(toString k1, 
        for i from 0 to #L-1 list (
            if R#i#1#?k1 then num2str(R#i#1#k1) else ""
            ))
        ))
    )
view = method()
view List := (L) -> (
    -- L is a list of lists, as output by combineResults
    netList(L, Alignment=>Right)
    )

viewCSV = method()
viewCSV List := (L) -> (
    -- L is a list, as output by combineResults
    --
    for a in L do (
         a1 := between(",",a);
         line := a1/toString//concatenate;
         << line << endl;
         )
    )

strat1 = ({Linear,DecomposeMonomials,(Factorization,3)},infinity)
strat2 = ({strat1, (Birational, infinity)}, infinity)
stratEnd = ({IndependentSet,SplitTower},infinity)
stratA = {strat1,(Birational,infinity)}
stratB = {
    ({strat1, (Birational, infinity)}, infinity)
    }
stratC = strat1
fcnA = (I) -> minprimes(I, Strategy=>stratA) 
fcnB = (I) -> minprimes(I, Strategy=>stratB) 
fcnC = (I) -> minprimes(I, Strategy=>strat1) 

end

restart
load "PD/test-timing.m2"
ETable = getExampleFile("PD/minprimes-examples.m2")

runExamples(ETable, null, "foo-minprimes", "--minprimes", minprimes)
runExamples(ETable, null, "foo-stratA", "-- " | toString stratA, fcnA)
runExamples(ETable, null, "foo-stratB", "-- " | toString stratB, fcnB)
runExamples(ETable, null, "foo-stratC", "-- " | toString stratC, fcnC)
runExamples(ETable, null, "foo-decompose", "--decompose", decompose)
combineResults{"foo-decompose", "foo-minprimes", "foo-stratA", "foo-stratB", "foo-stratC"}
view oo
view transpose ooo
viewCSV oo

fcnD = (I) -> minprimesWithStrategy(I, Strategy=>stratD)
time runExamples(ETable, null, "foo-stratD-DGP", "--testing only", fcnD)
runExamples(ETable, splice{10..36}, "foo-stratD-DGP", "--testing only", fcnD)
runExamples(ETable, splice{16..36}, "foo-stratD-DGP", "--testing only", fcnD)
-- 9, 12, 13, 15

restart
load "PD/test-timing.m2"
ETable = getExampleFile("PD/DGP.m2");
kk = ZZ/32003
I = value ETable#9#1
splitIdeal(I, Strategy=>stratD, Verbosity=>0);

runExamples(ETable, null, "DGP-decompose", "--decompose", decompose)
runExamples(ETable, splice{14..36}, "DGP-decompose", "--decompose", decompose)
runExamples(ETable, splice{27..36}, "DGP-decompose", "--decompose", decompose)

runExamples(ETable, null, "DGP-minprimes", "--minprimes", minprimes)
runExamples(ETable, null, "DGP-stratA", "--stratA", fcnA)
runExamples(ETable, null, "DGP-stratB", "--stratB", fcnB)
runExamples(ETable, null, "DGP-stratC", "--stratC", fcnC)
combineResults{"DGP-decompose", "DGP-minprimes", "DGP-stratA", "DGP-stratB", "DGP-stratC"}

view oo
view transpose ooo
viewCSV oo








-----------------------------
-- harder tests
restart
load "PD/test-timing.m2"
ETable = getExampleFile("PD/minprimes2-examples.m2");
ETable

runExamples(ETable, null, "primes2-minprimes", "--minprimes", minprimes)
runExamples(ETable, null, "primes2-stratA", "--stratA", fcnA)
runExamples(ETable, null, "primes2-stratB", "--stratB", fcnB)
runExamples(ETable, null, "primes2-stratC", "--stratC", fcnC)

I = value ETable#3#1
time minprimes(I, Verbosity=>2);
oo/codim
time splitIdeal(I, Strategy=>{defaultStrat, (IndependentSet,infinity), SplitTower}, Verbosity=>2);
oo/codim
numgens I
ETable = getExampleFile("PD/bayes-examples.m2");

gens ring I
for x in reverse gens ring I do (
    I1 := sub(I, x=>0);
    g := gens gb(I1, Algorithm=>LinearAlgebra);
    lt := ideal leadTerm g;
    if codim lt < 7 then (<< "####element " << x << " is a zero-divisor" << endl)
    else (<< "#### " << x << " is ok" << endl;);
    )

J = sub(I, {b_2=>1})
J1 = time mikeSplit(J, Strategy=>(Linear,infinity), Verbosity=>2);
J1 = (first J1).Ideal
J1 = sub(J1, c_12=>1)

Ja = J1 + ideal(b_4*b_5-1)
gens gb Ja;
independentSets J1
support first oo
makeFiberRings(oo, R)
sub(J1, last oo)
see J1  -- 3 gens, codim3
diff(c_5,J1_0) == 1 - b_4*b_5
g1 = diff(c_5, J1_1) * J1_0 - (1-b_4*b_5) * J1_1
g2 = diff(c_5, J1_2) * J1_0 - (1-b_4*b_5) * J1_2

J2 = ideal(g1,g2)
codim J2
independentSets J2
-- time minprimes J2; -- doesn't seem to work well

M = contract(transpose matrix{{c_1..c_12}}, gens I)
submatrix(M, {0,1,2,3,4,7,8}, )
det oo

use ring R
M1 = contract(transpose matrix{{b_1..b_10}}, gens I)
gbTrace=1
detC = minors(7,M1);
M2 = contract(transpose matrix{{c_1..c_12}}, gens I)

--------------------------------
----
I = value ETable#10#1
time mikeSplit(I, Strategy=>IndependentSet, Verbosity=>2);
I = ideal gens gb I;
-- b_(3,3) is a nzd
I1 = eliminate({a_(1,3)}, I);
time mikeSplit(I, Strategy=>strat1, Verbosity=>2);
#oo

time mikeSplit(I, Strategy=>Birational, Verbosity=>2);
