
newPackage(
        "UnitTestsPD",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "Short tests for basic correctness of PD.m2",
        DebuggingMode => true
        )

export {checkMinimalPrimes}

debug needsPackage "PD"

checkMinimalPrimes = method(Options => {"Answer" => null, "CheckPrimality" => false})
checkMinimalPrimes(Ideal, List) := opts -> (I, C1) -> (
    -- check that the intersection of the components in C1
    --   is contained in the radical of I
    -- check that each comp contains I
    for c in C1 do assert isSubset(I, c);
    J := intersect C1;
    assert (radicalContainment(J, I) === null);
    if opts#"CheckPrimality" then assert all(C1, isPrime);
    if opts#"Answer" =!= null then (
        C2 := if opts#"Answer" === decompose then decompose I else opts#"Answer";
        set1 := C1/(i -> set flatten entries gens gb i)//set;
        set2 := C2/(i -> set flatten entries gens gb i)//set;
        assert(set1 === set2);
        );
    )

-- SIMPLETEST checks the results with the original decompose function
-- but this should only be run on examples that 'decompose' can do quickly  
SIMPLETEST = (str) -> TEST str  

-- These are slower tests, that we will eventually run explicitly
BENCHMARK = (str) -> TEST str

-- radicalContainment
TEST ///
    debug needsPackage "PD"
    R = ZZ/32003[a..f]
    F = map(R,R,symmetricPower(2,matrix{{a,b,c}}))
    I = ker F
    J = I^2
    G = I_0
    assert radicalContainment(G,J)
    assert not radicalContainment(G-a^2,J)
    assert (radicalContainment(I, I^2) === null)
///

TEST ///
    debug needsPackage "PD"
    R = (frac(QQ[a,b]))[x,y,z]
    F = 15 * a * (a*x-y-1/a)^2 * (1/b * x * z - a * y)^2
    assert(set factors F === set {(2, a^2*x-a*y-1), (2, x*z - a*b*y)})
    assert ( vars coefficientRing ring numerator F == 0 ) 

    G = a * (a*x-y-1/a)^2 * (1/b * x * z - a * y)^2
    assert( set factors F === set factors G)
///

TEST ///
    debug needsPackage "PD"
    R = QQ[a,b,x,y,z]
    F = 15 * a * (a*x-y-a^2)^2 * (b^2 * x * z - a * y)^2
    assert(set factors F === set {(1,a), (2, -a*x+y+a^2), (2, b^2*x*z - a*y)})
    --assert(numerator F == F) -- this would fail at the moment.  Should it be made to work?
///

TEST ///
    debug needsPackage "PD"
    R = ZZ/32003[a..d]
    I = monomialCurveIdeal(R,{1,3,4})
    J = I + ideal(a^5-b^5)
    assert(findNonMemberIndex(I,J) == -1)-- which (index of)  element of I is not in J
    assert(findNonMemberIndex(J,I) == 4) -- J_4 is not in I
    assert(selectMinimalIdeals {I,J} === {I})
    assert(selectMinimalIdeals {J,I} === {I})
///

TEST ///
  debug needsPackage "PD"
  R = ZZ/32003[a,b,c,d,e,f,g,h]
  (S,SF) = makeFiberRings {c}
  -- TODO NOTE: S whould contain ringmaps S-->R, R-->S, S-->SF,
  --  note: SF-->S we have numerator, denominator
  assert ( first sort gens S == c ) 
  assert ( not member(c, gens SF) ) 
  use SF
  use coefficientRing SF
  F = (1/c) * a
  assert ( F*c == a ) 
  assert(ring F === SF)
  assert(ring numerator F === S)
///

TEST ///
  debug needsPackage "PD"
  R = ZZ/32003[a,x]
  I = ideal( a*x + a^2 )
  (S,SF) = makeFiberRings {a}
  IS = sub(I,S)
  use SF
  use coefficientRing SF
  (L, M) = minimalizeOverFrac(IS, SF)
  assert( ring ideal L === SF )
  assert( ring ideal M === S )
  assert( ( ideal(x+a)  === ideal first minimalizeOverFrac(IS, SF) ) )
  assert( ( ideal(sub(a,S))  === ideal last minimalizeOverFrac(IS, SF) ) )
///

TEST ///
  debug needsPackage "PD"
  R = ZZ/32003[a,x]
  I = ideal( a*x + a^2 )
  (S,SF) = makeFiberRings {a,x}
  IS = sub(I,S)
  assert( ( ideal 1_SF === ideal first minimalizeOverFrac(IS, SF) ) )
  assert( ( IS  ===  ideal last minimalizeOverFrac(IS, SF) ) )
///

TEST ///
  debug needsPackage "PD"
  R = ZZ/32003[a,x]
  I = ideal( a*x + a^2 )
  assert try (S,SF) = makeFiberRings {} else true
///

TEST ///
  debug needsPackage "PD"
  R = QQ[a,b,c,d,e,h]
  (S,SF) = makeFiberRings {c}
  use SF
  use coefficientRing SF
  I = ideal(h^4+c*h^3+6*c^2*h^2-4*c^3*h+c^4,e+(1/(11*c^2))*h^3+((-2)/(11*c))*h^2+(1/11)*h+(4*c)/11,d+((-3)/(11*c^2))*h^3+(6/(11*c))*h^2+((-3)/11)*h+(-c)/11,b+(1/(11*c^2))*h^3+((-2)/(11*c))*h^2+(1/11)*h+(4*c)/11,a+(1/(11*c^2))*h^3+((-2)/(11*c))*h^2+(1/11)*h+(4*c)/11)
  use S
  J = ideal(d+3*e+c,b-e,a-e,e*h+3*e*c-h^2+h*c+c^2,e^2+3*e*c+c^2)
  assert( J == contractToPolynomialRing I )
///

TEST ///
  debug needsPackage "PD"
  R = QQ[a,b,c,d,e,h]
  J = ideal(d+3*e+c,b-e,a-e,e*h+3*e*c-h^2+h*c+c^2,e^2+3*e*c+c^2)
  assert( independentSets J == {h}) 
  Je = extendIdeal J
  use ring Je
  use coefficientRing ring Je
  assert( Je == ideal(e^4+h*e^3+h^2*e^2+h^3*e+h^4,d+(1/(h))*e^2+2*e+h,c+((-1)/(h))*e^2+e-h,b-e,a-e))
///

BENCHMARK ///
  debug needsPackage "PD"
  Q = ZZ/32003[a,b,c,d]
  -- 3 random cubics in R
  I = ideal(-840*a^3-7687*a^2*b+9625*a*b^2-3820*b^3-10392*a^2*c-13100*a*b*c-11362*b^2*c-7463*a*c^2-11288*b*c^2+1417*c^3-14802*a^2*d-7804*a*b*d+5834*b^2*d-10186*a*c*d-11900*b*c*
     d+5062*c^2*d+14848*a*d^2+1270*b*d^2+4670*c*d^2+14589*d^3,6046*a^3-1565*a^2*b-10455*a*b^2+13719*b^3+9618*a^2*c+4969*a*b*c+14049*b^2*c+7621*a*c^2-15861*b*c^2-11905*c^3-
     13456*a^2*d+2029*a*b*d+8067*b^2*d-10420*a*c*d-14441*b*c*d-13965*c^2*d-3634*a*d^2-4035*b*d^2+350*c*d^2-8942*d^3,-12512*a^3-11973*a^2*b-8963*a*b^2-12001*b^3-10663*a^2*c-
     7202*a*b*c+9856*b^2*c-7955*a*c^2-8818*b*c^2+398*c^3+4259*a^2*d+13332*a*b*d+1576*b^2*d+3008*a*c*d+2588*b*c*d-6135*c^2*d-5311*a*d^2+6731*b*d^2-13991*c*d^2-9315*d^3)
  C1 = minprimes I;
  singularList = {ideal " c25+13767c24d+333c23d2+2478c22d3-7440c21d4-15655c20d5-4815c19d6+2905c18d7-9657c17d8+6596c16d9-259c15d10+15292c14d11+8119c13d12-1206c12d13-11455c11d14+11807c10d15-2026c9d16+8307c8d17+14982c7d18+3497c6d19+12142c5d20+11624c4d21-54c3d22-9394c2d23+1916cd24+15319d25 , -4407c24-15196c23d+5428c22d2-15255c21d3-5669c20d4+2730c19d5-14633c18d6-278c17d7-7870c16d8+4996c15d9+5806c14d10-7410c13d11-6200c12d12+13830c11d13+2838c10d14+1136c9d15-14230c8d16-6507c7d17+545c6d18+2167c5d19+8969c4d20-3248c3d21-13200c2d22+bd23-3900cd23-8607d24 , 11176c23-10521c22d+13102c21d2-11217c20d3+15230c19d4+8358c18d5+6861c17d6+3523c16d7+3510c15d8-15747c14d9-8542c13d10-4549c12d11-13819c11d12+15835c10d13+6926c9d14-14048c8d15+6377c7d16+14057c6d17+12177c5d18-12108c4d19+15854c3d20+bcd21-7965c2d21-6940bd22+9878cd22-515d23 , 12762c22-14850c21d-3995c20d2-6922c19d3+5412c18d4-13776c17d5+9593c16d6+10827c15d7+12336c14d8+2025c13d9-9274c12d10+4644c11d11+12458c10d12-14403c9d13-10400c8d14+7511c7d15+6520c6d16-5229c5d17-12005c4d18+bc2d19+7674c3d19+13347bcd20+11720c2d20-8765bd21+6151cd21-12886d22 , -3c21-5557c20d+14789c19d2+9824c18d3+13399c17d4+12204c16d5-398c15d6+13708c14d7+14057c13d8-6450c12d9+3768c11d10-13048c10d11-1393c9d12+2881c8d13+1748c7d14-4528c6d15+10831c5d16+bc3d17-14929c4d17+9796bc2d18-293c3d18-6243bcd19+5945c2d19-5013bd20-1892cd20+8819d21 , 2821c20+5738c19d-11541c18d2+13088c17d3-3838c16d4-9756c15d5-2493c14d6+5899c13d7-12949c12d8-7505c11d9-12554c10d10-11153c9d11-5715c8d12+2361c7d13+1799c6d14+bc4d15+13649c5d15+1247bc3d16-7318c4d16-11989bc2d17-13777c3d17-11876bcd18+9845c2d18+7240bd19-15850cd19+2831d20 , 7358c19+11639c18d+11372c17d2+3964c16d3+1643c15d4-11934c14d5-6581c13d6+9659c12d7-10325c11d8-4362c10d9+8934c9d10-14444c8d11+1325c7d12+bc5d13+15401c6d13+9420bc4d14+1965c5d14+14396bc3d15-9771c4d15+522bc2d16-11848c3d16-4161bcd17+2885c2d17-10477bd18+647cd18-7051d19 , -7124c18+8514c17d-11062c16d2-14927c15d3-11438c14d4-3688c13d5+1130c12d6+10158c11d7+11503c10d8-15922c9d9-11612c8d10+bc6d11+10775c7d11-2845bc5d12+1199c6d12+15265bc4d13+4665c5d13-5875bc3d14-6220c4d14+2963bc2d15-3234c3d15+498bcd16+13045c2d16+10418bd17+10508cd17+435d18 , -15842c17+12c16d-8632c15d2-3285c14d3-9228c13d4+5962c12d5+8775c11d6-14144c10d7+2970c9d8+bc7d9+12503c8d9+8063bc6d10-6653c7d10-11045bc5d11-13915c6d11+1691bc4d12-3946c5d12-11163bc3d13-411c4d13+12513bc2d14+2020c3d14-14376bcd15-2847c2d15+10495bd16-12986cd16+2727d17 , 12398c16-4c15d+99c14d2-11259c13d3-3766c12d4+10250c11d5-4076c10d6+bc8d7-2896c9d7+6644bc7d8-3869c8d8-6556bc6d9-9592c7d9+11954bc5d10-9567c6d10+4724bc4d11+3311c5d11+6663bc3d12-7990c4d12-3594bc2d13-2358c3d13-10977bcd14+12752c2d14-12668bd15+11651cd15+426d16 , 12213c15+15877c14d-6153c13d2-6868c12d3-1790c11d4+bc9d5+11490c10d5-2552bc8d6+1034c9d6-14943bc7d7-9714c8d7+5148bc6d8-12060c7d8-8934bc5d9-14530c6d9+7458bc4d10-590c5d10+5202bc3d11-6566c4d11+13344bc2d12+13824c3d12+7761bcd13+5043c2d13+14286bd14-13323cd14+3836d15 , 11678c14-13583c13d+2407c12d2+bc10d3-15722c11d3-5151bc9d4-6700c10d4+14402bc8d5-11969c9d5+13880bc7d6+8651c8d6-15039bc6d7+15387c7d7-11771bc5d8+5153c6d8+8469bc4d9+7983c5d9+11132bc3d10+10405c4d10-15756bc2d11-7298c3d11+3587bcd12+14804c2d12+11059bd13+3802cd13+7788d14 , 12599c13+bc11d-6271c12d+4415bc10d2+749c11d2+3411bc9d3+8566c10d3+15479bc8d4+14050c9d4-15290bc7d5-13632c8d5-1614bc6d6-7809c7d6-10642bc5d7-6992c6d7+5364bc4d8+11005c5d8-3004bc3d9+6658c4d9-4611bc2d10+7601c3d10-9879bcd11+5352c2d11-12677bd12+14738cd12+12409d13 , bc12-1783c13-2779bc11d-4921c12d-5191bc10d2-9398c11d2-1824bc9d3-653c10d3+15881bc8d4-9309c9d4-7224bc7d5-11473c8d5-3599bc6d6+8817c7d6-14293bc5d7+7468c6d7-2604bc4d8+2826c5d8-15028bc3d9+7113c4d9-9285bc2d10-6795c3d10+6278bcd11+13155c2d11-14374bd12+4525cd12+4108d13 , -8063bc11+6982c12+15948bc10d+3019c11d+12859bc9d2+6658c10d2-11198bc8d3+3114c9d3+10748bc7d4-8873c8d4-9095bc6d5-10668c7d5-34bc5d6+10137c6d6+217bc4d7-5639c5d7-12232bc3d8+5279c4d8-8861bc2d9+7281c3d9+b2d10-4820bcd10+8956c2d10+15395bd11-15832cd11+10572d12 , -759bc11-6656c12+11139bc10d-10450c11d+11848bc9d2+3738c10d2+7340bc8d3+1991c9d3-5506bc7d4-6924c8d4+4185bc6d5+9644c7d5-14015bc5d6-10007c6d6+3825bc4d7+5257c5d7-7bc3d8+14215c4d8+b2cd9+5906bc2d9-11487c3d9+7900b2d10+11733bcd10-11242c2d10-5599bd11+7151cd11-9331d12 , 13840bc10+10265c11+8348bc9d+2785c10d-12257bc8d2+8756c9d2-11526bc7d3-333c8d3-917bc6d4+14143c7d4+528bc5d5-9301c6d5+7464bc4d6+15650c5d6+b2c2d7+5815bc3d7+8149c4d7-6216b2cd8+6664bc2d8+12003c3d8-15776b2d9-10851bcd9+2784c2d9-4028bd10+5819cd10-9414d11 , -6875bc10+1430c11-669bc9d-7483c10d-11968bc8d2+12749c9d2+14711bc7d3+2131c8d3-15501bc6d4-15444c7d4+14333bc5d5-12257c6d5+b2c3d6-6407bc4d6-13646c5d6+10752b2c2d7-7038bc3d7-11294c4d7-9066b2cd8+6920bc2d8+8176c3d8-11528b2d9+13794bcd9+13881c2d9+116bd10-2066cd10+2184d11 , 13201bc9-4794c10-9881bc8d+2542c9d+3325bc7d2-2605c8d2+6064bc6d3+12261c7d3+b2c4d4-5607bc5d4+13905c6d4+4173b2c3d5-6507bc4d5-2069c5d5-11020b2c2d6+6061bc3d6+3749c4d6+15069b2cd7+4248bc2d7+10721c3d7+1625b2d8-5923bcd8+5895c2d8-1833bd9-7558cd9+8134d10 , 9428bc9-4844c10-8680bc8d+7085c9d-6186bc7d2-742c8d2+b2c5d3-12613bc6d3-7187c7d3+13678b2c4d4+8863bc5d4-6093c6d4+10628b2c3d5-6772bc4d5+1260c5d5+6716b2c2d6+590bc3d6-10848c4d6+692b2cd7-14307bc2d7-11452c3d7-10098b2d8-308bcd8+8455c2d8+6871bd9+15822cd9+580d10 , -13641bc8+8475c9+b2c6d-15247bc7d+10622c8d-2186b2c5d2+10248bc6d2-9506c7d2-2224b2c4d3+2677bc5d3+14460c6d3+3782b2c3d4-7486bc4d4+3038c5d4+10597b2c2d5-8768bc3d5+7192c4d5+13050b2cd6-4907bc2d6-5311c3d6+13458b2d7+14811bcd7+15190c2d7-4097bd8+13173cd8-783d9 , b2c7-5332bc8-7730c9+5413b2c6d+6342bc7d-890c8d+486b2c5d2+15759bc6d2-10817c7d2-1240b2c4d3+6658bc5d3+2155c6d3+846b2c3d4-6374bc4d4+12671c5d4+1200b2c2d5+3585bc3d5+15404c4d5-4822b2cd6-11933bc2d6+4302c3d6-15489b2d7-8363bcd7-6474c2d7-9270bd8-8240cd8-4848d9 , -15836b2c7-7692bc8-3537c9+6042b2c6d+8057bc7d-8001c8d-6288b2c5d2-7658bc6d2-9691c7d2-8285b2c4d3+7737bc5d3-12242c6d3+8392b2c3d4-585bc4d4+10393c5d4+13254b2c2d5+10230bc3d5+5736c4d5+b3d6+10644b2cd6+7319bc2d6+14380c3d6-9797b2d7+11257bcd7+8768c2d7-3264bd8+5784cd8+10493d9 , 4303b2c6-7974bc7+4047c8+4370b2c5d-12258bc6d-219c7d+8704b2c4d2+10815bc5d2+11209c6d2+2542b2c3d3-1795bc4d3-567c5d3+b3cd4-566b2c2d4+3985bc3d4+8850c4d4-8500b3d5-9285b2cd5+7088bc2d5-6584c3d5+10190b2d6+1305bcd6-6518c2d6+6248bd7-13047cd7-1266d8 , 9824b2c6-10159bc7+3079c8+9571b2c5d+12941bc6d-3762c7d+77b2c4d2-14752bc5d2-2413c6d2+b3c2d3+3337b2c3d3-6538bc4d3-2472c5d3+7186b3cd4-15301b2c2d4+3983bc3d4-3619c4d4-6528b3d5-9387b2cd5+6975bc2d5+695c3d5-15947b2d6-10097bcd6-8757c2d6+1797bd7+12308cd7-1407d8 , -6107b2c6+11084bc7-7632c8-10515b2c5d+10400bc6d+11870c7d+b3c3d2+15058b2c4d2-8008bc5d2-9287c6d2+12019b3c2d3-4272b2c3d3-692bc4d3+9871c5d3+9815b3cd4-1980b2c2d4-10385bc3d4-12211c4d4-9889b3d5-12727b2cd5-11234bc2d5-6784c3d5-8087b2d6+5159bcd6+6580c2d6+15733bd7+14821cd7+14654d8 , b3c4+12680b2c5-4340bc6-14271c7+8739b3c3d+5964b2c4d-11726bc5d-1888c6d-12154b3c2d2+2878b2c3d2+5938bc4d2+15617c5d2+9862b3cd3-11606b2c2d3+11522bc3d3-6281c4d3-3955b3d4-3908b2cd4-148bc2d4+5224c3d4+2825b2d5-13446bcd5-9706c2d5+9862bd6-12969cd6-1314d7 , 7019b3c4-12024b2c5+14134bc6+12518c7+15045b3c3d+2b2c4d+15934bc5d+1841c6d+2941b3c2d2+14657b2c3d2+813bc4d2+13802c5d2+b4d3+9667b3cd3-9429b2c2d3-3134bc3d3+10880c4d3-368b3d4+13747b2cd4+1781bc2d4-6873c3d4-8995b2d5+14503bcd5-8468c2d5-980bd6-15649cd6-5875d7 , -11348b3c4-9681b2c5+15578bc6+1433c7-9084b3c3d-12302b2c4d+9596bc5d-12435c6d+b4cd2+14317b3c2d2+1722b2c3d2-10760bc4d2+12485c5d2+15690b4d3+14141b3cd3-4228b2c2d3+2141bc3d3+1642c4d3+1418b3d4+2118b2cd4-5678bc2d4+13921c3d4+8199b2d5-8063bcd5-10613c2d5-628bd6-11667cd6+15871d7 , -6370b3c4+13642b2c5-9393bc6-912c7+b4c2d-11532b3c3d+1609b2c4d-11102bc5d+9685c6d+8280b4cd2-5438b3c2d2-2917b2c3d2+13811bc4d2-2116c5d2-13058b4d3+9391b3cd3-2656b2c2d3+13352bc3d3-13058c4d3-1572b3d4+6698b2cd4-10835bc2d4-13293c3d4+1279b2d5+6480bcd5-7012c2d5-7727bd6+2233cd6-14375d7 , b4c3+3368b3c4-3093b2c5-3373bc6-12956c7-232b4c2d+2143b3c3d-10021b2c4d-12172bc5d-1806c6d-15204b4cd2-3636b3c2d2-1878b2c3d2-13586bc4d2+12160c5d2+11382b4d3-7427b3cd3-9673b2c2d3-15729bc3d3-4712c4d3-14140b3d4+11375b2cd4-11217bc2d4+2269c3d4+12084b2d5+3013bcd5-8740c2d5-3445bd6-13123cd6-9468d7 , 7707b4c2+2743b3c3+4484b2c4-9275bc5-2532c6+b5d-8456b4cd-9673b3c2d-2357b2c3d-10820bc4d-1967c5d+14491b4d2+3621b3cd2+771b2c2d2+12995bc3d2+11676c4d2+6692b3d3-2058b2cd3+13237bc2d3-13172c3d3+3183b2d4-1914bcd4+3853c2d4+5127bd5-9291cd5+2634d6 , b5c+6800b4c2+8851b3c3+7676b2c4+7926bc5+732c6+15595b5d+9776b4cd+3352b3c2d-8810b2c3d-11603bc4d+14852c5d+13111b4d2+9417b3cd2+3383b2c2d2-8698bc3d2+960c4d2+6722b3d3-3226b2cd3-12936bc2d3+225c3d3-426b2d4-3920bcd4+1478c2d4+196bd5-3449cd5-11586d6 , b6+14674b5c-14313b4c2+11016b3c3-1567b2c4-2950bc5-10445c6+15536b5d-1070b4cd+12258b3c2d-7872b2c3d+698bc4d+14476c5d-3527b4d2-8257b3cd2-5918b2c2d2-1750bc3d2+7444c4d2+12615b3d3-3244b2cd3-137bc2d3-5806c3d3-13426b2d4+8355bcd4+1840c2d4+7683bd5-12123cd5-11127d6 , -14683b6-13195b5c-2546b4c2+12217b3c3-3087b2c4+10642bc5-5016c6-7551b5d+11525b4cd-13016b3c2d-10580b2c3d-5944bc4d-4013c5d-5925b4d2-6997b3cd2+8436b2c2d2+8876bc3d2-286c4d2+14166b3d3+6683b2cd3+2439bc2d3-7200c3d3-5948b2d4+2351bcd4+15129c2d4+ad5-4587bd5+5850cd5+782d6 , 4732b5c-3072b4c2-11024b3c3+11579b2c4-7724bc5+14788c6+14082b5d+9238b4cd-13773b3c2d+656b2c3d+5569bc4d-2338c5d+2222b4d2+700b3cd2-2299b2c2d2+5353bc3d2-1992c4d2+13180b3d3-14349b2cd3-13394bc2d3-14983c3d3-11396b2d4+acd4-10312bcd4-2154c2d4-3601ad5-6017bd5-3935cd5+14654d6 , 11666b5c-15257b4c2-203b3c3-8567b2c4-5018bc5+12844c6+5223b5d-12830b4cd+65b3c2d+11658b2c3d+3921bc4d-12964c5d+14515b4d2-476b3cd2-6970b2c2d2+12291bc3d2-9883c4d2+7169b3d3+9756b2cd3+ac2d3-10588bc2d3+4483c3d3+1117b2d4+14125acd4+14069bcd4-5411c2d4-5924ad5+2164bd5-13444cd5+8675d6 , 13960b5c-9641b4c2-12253b3c3-7813b2c4-11879bc5-7597c6-11324b5d-11361b4cd+2703b3c2d-14020b2c3d+12884bc4d+15745c5d-9592b4d2+6086b3cd2-2265b2c2d2+ac3d2+2073bc3d2-1271c4d2-7229b3d3-15840b2cd3-962ac2d3+15187bc2d3-13511c3d3+9652b2d4+83acd4-14290bcd4+12037c2d4-10333ad5-11430bd5+9855cd5-11556d6 , 11269b5-14165b4c+125b3c2-3963b2c3+ac4+14404bc4+6323c5-3066b4d-8975b3cd+2933b2c2d-11491ac3d+5832bc3d-6306c4d+881b3d2+12711b2cd2-9498ac2d2+580bc2d2-6540c3d2-7933b2d3-8437acd3+1024bcd3+9127c2d3+1117ad4+6202bd4-6310cd4-5793d5 , 11069b5+7277b4c+10225b3c2-2527b2c3+11708ac4-1451bc4-9039c5+10277b4d-5290b3cd+1617b2c2d+7618ac3d+10862bc3d+8083c4d-8817b3d2+2614b2cd2+13113ac2d2-2647bc2d2-12583c3d2+abd3+14772b2d3+2159acd3+10258bcd3-7201c2d3+14532ad4+8861bd4-11544cd4+10827d5 , -14951b5+5071b4c-2048b3c2+6623b2c3-7812ac4+1476bc4+15185c5+11004b4d+7056b3cd+3940b2c2d+15163ac3d+12741bc3d+10224c4d-1114b3d2+abcd2-7434b2cd2-8246ac2d2+5953bc2d2+11198c3d2+15012abd3+12412b2d3+9735acd3-2790bcd3-13489c2d3+8399ad4+10062bd4+6089cd4-4501d5 , -11512b5-1130b4c+1215b3c2-7078b2c3-4312ac4-9824bc4+12811c5+4534b4d+6024b3cd+abc2d+6920b2c2d-8141ac3d+13005bc3d+8526c4d+1412b3d2-15512abcd2-14940b2cd2+8735ac2d2+11988bc2d2+4704c3d2-3495abd3+1975b2d3+13586acd3-4532bcd3+7769c2d3-15951ad4-4713bd4+13541cd4+8580d5 , -8165b5+3347b4c-657b3c2+abc3+13057b2c3-650ac4-8260bc4-5669c5-7036b4d+4503b3cd+3581abc2d-13288b2c2d-15193ac3d+1236bc3d+1414c4d+6058b3d2-862abcd2+6870b2cd2-8409ac2d2+3977bc2d2+2362c3d2-11087abd3-8834b2d3-10289acd3+9404bcd3-1755c2d3+11691ad4+8169bd4-13754cd4-10987d5 , -12135b5+10882b4c+7998b3c2-9553abc3-14273b2c3+13697ac4-513bc4-10249c5+1115b4d+2518b3cd-6775abc2d-4249b2c2d-12272ac3d-5519bc3d+11912c4d+ab2d2+15502b3d2-6208abcd2-5884b2cd2+11557ac2d2+6896bc2d2+13231c3d2+5762abd3+13391b2d3-4360acd3+1763bcd3-4498c2d3+2699ad4-4335bd4+9356cd4+11447d5 , 8918b4+ab2c+3324b3c-5938abc2-1269b2c2-714ac3+4194bc3-3909c4+3426ab2d-2298b3d+3692abcd+8740b2cd-11336ac2d+5577bc2d-6747c3d+521abd2-5619b2d2-1315acd2+9854bcd2+3835c2d2+13754ad3-5456bd3+10640cd3+15586d4 , ab3+8614b4-11880ab2c-5345b3c+8392abc2-7389b2c2+3568ac3+14805bc3+10461c4-5786ab2d+15610b3d-12600abcd-15254b2cd+14412ac2d+13915bc2d+4969c3d-7535abd2-12322b2d2+959acd2-6599bcd2+173c2d2-10365ad3-8028bd3-7230cd3-12147d4 , -11347ab3+14644b4+13884ab2c+11384b3c-589abc2+7910b2c2-5304ac3+11727bc3-3264c4+3546ab2d+73b3d-6143abcd+7395b2cd+4247ac2d-2073bc2d-11045c3d+a2d2-5394abd2-15764b2d2+2926acd2+15866bcd2+1841c2d2-9946ad3+1624bd3+209cd3+9366d4 , -4550ab2+9975b3+a2c-8765abc-11257b2c+12705ac2-9665bc2+5132c3-9825a2d+15512abd-8580b2d+11687acd-1066bcd+8006c2d+6810ad2-12535bd2+9630cd2+6727d3 , a2b+2015b3-1648a2c-3910abc-4666b2c+1001ac2-8007bc2+345c3-4404a2d-1027abd-9718b2d+4411acd+11194bcd-3723c2d-13499ad2-4299bd2+159cd2+9012d3 , a3-312b3+1186a2c-14772abc-7b2c-4827ac2+6171bc2+12015c3+11880a2d-4942abd+9929b2d-589acd+10389bcd+6044c2d+5889ad2+7982bd2-14415cd2-8240d3 ",
                  ideal " c2-13428cd+10884d2 , b-12327c+2244d , a-5947c+15464d "}
  checkMinimalPrimes(I, C1, "Answer"=>singularList)
  --set1 := C1/(i -> set flatten entries gens gb i)//set;
  --C2 := singularList;
  --set2 := C2/(i -> set flatten entries gens gb i)//set;
  --assert(set1 === set2)
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = ZZ/32003[a,b,c,h]
  I = ideal(a+b+c,a*b+b*c+a*c,a*b*c-h^3)
  C = minprimes I;
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = ZZ/32003[a,b,c,d,h]
  I = ideal(a+b+c+d,a*b+b*c+c*d+d*a,a*b*c+b*c*d+c*d*a+d*a*b,a*b*c*d-h^4)
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = QQ[a,b,c,d,h]
  I = ideal(a+b+c+d,a*b+b*c+c*d+d*a,a*b*c+b*c*d+c*d*a+d*a*b,a*b*c*d-h^4)
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = QQ[a,b,c,d]
  I = ideal(a^2-b^2,a*b*c-d^3,b*d^2-a*c^2)
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = ZZ/32003[x,y,z,MonomialOrder=>Lex]
  p = z^2+1
  q = z^4+2
  I = ideal(p^2*q^3, (y-z^3)^3, (x-y*z+z^4)^4)
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  debug needsPackage "PD"
  -- ST_S/Y x, except that one is ZZ/32003
  R = QQ[b,s,t,u,v,w,x,y,z];
  I = ideal"su - bv, tv - sw, vx - uy, wy - vz"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = QQ[vars(0..8)];
  I = ideal(b*d+a*e,c*d+a*f,c*e+b*f,b*g+a*h,c*g+a*i,c*h+b*i,e*g+d*h,f*g+d*i,f*h+e*i)
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = QQ[vars(0..8),MonomialOrder=>Lex];
  I = ideal(b*d+a*e,c*d+a*f,c*e+b*f,b*g+a*h,c*g+a*i,c*h+b*i,e*g+d*h,f*g+d*i,f*h+e*i)
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = ZZ/32003[x,y,z];
  I = ideal"
    x2yz + xy2z + xyz2 + xyz + xy + xz + yz,
    x2y2z + xy2z2 + x2yz + xyz + yz + x + z,
    x2y2z2 + x2y2z + xy2z + xyz + xz + z + 1";
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = ZZ/32003[x,y,z,t]
  I = ideal(
    t^10-x,
    t^31-t^6-t-y,
    t^8-z)
  C = minprimes I
  -- decompose fails miserably here.
  checkMinimalPrimes(I, C, "CheckPrimality" => true)
  -- singular says I is prime, so we check that here
  assert (I == first C)
  -- it's a bit strange though, since minprimes returns a seemingly
  -- different ideal, but if you check I == first C, you get true
  -- even though they look very different.
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --chemistry: a chemical process in glass melting (DGP set) 9 variables
  debug needsPackage "PD"
  kk = ZZ/32003
  R = kk[a,b,c,d,e,f,g,h,j];
  I = ideal"
    a+2b+c-d+g,
    f2gh - a,
    efg - c,
    fg2j - b,
    a + b + c + f + g - 1,
    3ad + 3bd + 2cd + df + dg - a - 2b - c - g"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --horrocks (DGP) related to the Horrock bundle on P5 x
  debug needsPackage "PD"
  kk = ZZ/32003
  R = kk[a,b,c,d,e,f];
  I = ideal"2adef + 3be2f - cef2,         4ad2f + 5bdef + cdf2,         2abdf + 3b2ef - bcf2,                     4a2df + 5abef + acf2,
            4ad2e + 3bde2 + 7cdef,        2acde + 3bce2 - c2ef,         4abde + 3b2e2 - 4acdf + 2bcef - c2f2,     4a2de + 3abe2 + 7acef,
            4acd2 + 5bcde + c2df,         4abd2 + 3b2de + 7bcdf,        16a2d2 - 9b2e2 + 32acdf - 18bcef + 7c2f2, 2abcd + 3b2ce - bc2f,
            4a2cd + 5abce + ac2f,         4a2bd + 3ab2e + 7abcf,        abc2f - cdef2,                            ab2cf - bdef2,
            2a2bcf + 3be2f2 - cef3,       ab3f - 3bdf3,                 2a2b2f - 4adf3 + 3bef3 - cf4,             a3bf + 4aef3,
            3ac3e - cde3,                 3b2c2e - bc3f + 2cd2ef,       abc2e - cde2f,                            6a2c2e - 4ade3 - 3be4 + ce3f,
            3b3ce - b2c2f + 2bd2ef,       2a2bce + 3be3f - ce2f2,       3a3ce + 4ae3f,                            4bc3d + cd3e,
            4ac3d - 3bc3e - 2cd2e2 + c4f, 8b2c2d - 4ad4 - 3bd3e - cd3f, 4b3cd + 3bd3f,                            4ab3d + 3b4e - b3cf - 6bd2f2,
            4a4d + 3a3be + a3cf - 8ae2f2"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --square of a generic 3x3 matrix (DGP, from POSSO)
  debug needsPackage "PD"
  kk = ZZ/32003
  R = kk[vars(0..8)]
  I = ideal (genericMatrix(R,3,3))^2
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --shimoyama-yokoyama example I8 (DGP)
  debug needsPackage "PD"
  kk = QQ
  R = kk[b,c,d,e,f,g,h,j,k,l];
  I = ideal( 
    (l-k)^9,
    (l-k)^8*(l-b),
    (l-k)^7*(l-c),
    (l-k)^6*(l-d),
    (l-k)^5*(l-e),
    (l-k)^4*(l-f),
    (l-k)^3*(l-g),
    (l-k)^2*(l-h),
    (l-k)*(l-j))
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --riemenschneider (DGP) related to deformations of quotient singularities
  debug needsPackage "PD"
  kk = QQ
  R = kk[p,q,s,t,u,v,w,x,y,z];
  I = ideal"
    su,
    vx,
    qu,
    xz,
    stx + ux,
    uv3 - uvw + ux,
    -pu2v2 + pu2w + qtx,
    tx2y - uv2z + uwz"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2 x
  --sy-j: shimoyama-yokoyama example J (DGP) 3 variables (J_S/Y) x
  debug needsPackage "PD"
  kk = ZZ/32003
  R = kk[x,y,z];
  I = ideal"
    xy2z2 - xy2z + xyz2 - xyz,
    xy3z + xy2z,
    xy4 - xy2,
    x2yz2 - x2yz,
    x2y3 - x2y2,
    x4z3 - x4z2 + 2x3z3 - 2x3z2 + x2z3 - x2z2,
    x2y2z,
    x4yz + x3yz,
    2x4y2 + 6x3y2 + 6x2y2 + xy3 + xy2,
    x5z + x4z2 + x4z + 2x3z2 - x3z + x2z2 - x2z,
    x6y + 3x5y + 3x4y + x3y"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --roczen (DGP) related to classification of singularities (Marko) x
  debug needsPackage "PD"
  kk = ZZ/32003
  R = kk[a,b,c,d,e,f,g,h,k,o];
  I = ideal "o+1,k4+k,hk,h4+h,gk,gh,g3+h3+k3+1,fk,f4+f,eh,ef,f3h3+e3k3+e3+f3+h3+k3+1,e3g+f3g+g,e4+e,dh3+dk3+d,dg,df,de,
             d3+e3+f3+1,e2g2+d2h2+c,f2g2+d2k2+b,f2h2+e2k2+a"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --macaulay (DGP, from an older M2 tutorial)
  debug needsPackage "PD"
  kk = QQ
  R = kk[a,b,c,d]
  I = ideal"
  b4 - a3d,
  ab3 - a3c,
  bc4 - ac3d - bcd3 + ad4,
  c6 - bc3d2 - c3d3 + bd5,
  ac5 - b2c3d - ac2d3 + b2d4,
  a2c4 - a3d3 + b3d3 - a2cd3,
  b3c3 - a3d3,
  ab2c3 - a3cd2 + b3cd2 - ab2d3,
  a2bc3 - a3c2d + b3c2d - a2bd3,
  a3c3 - a3bd2,
  a4c2 - a3b2d"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --becker-niermann (DGP)
  debug needsPackage "PD"
  kk = ZZ/32003
  R = kk[x,y,z];
  I = ideal"
    x2+xy2z-2xy+y4+y2+z2,
    -x3y2+xy2z+xyz3-2xy+y4,
    -2x2y+xy4+yz4-3"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
--from ExampleIdeals/DGP.m2
--caprasse4 (DGP, from POSSO)
  debug needsPackage "PD"
  kk = QQ
  R = kk[x,y,z,t];
  I = ideal"
    y2z+2xyt-2x-z,
    -x3z+4xy2z+4x2yt+2y3t+4x2-10y2+4xz-10yt+2,
    2yzt+xt2-x-2z,
    -xz3+4yz2t+4xzt2+2yt3+4xz+4z2-10yt-10t2+2"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  debug needsPackage "PD"
  kk = ZZ/32003
  -- decompose DNF over QQ.  Coeffs probably too nasty
  R = kk[b,c,d,e]
  I = ideal"
    6b4c3 + 21b4c2d + 15b4cd2 + 9b4d3 - 8b2c2e - 28b2cde + 36b2d2e - 144b2c
      - 648b2d - 120,
    9b4c4 + 30b4c3d + 39b4c2d2 + 18b4cd3 - 24b2c3e - 16b2c2de
      + 16b2cd2e + 24b2d3e
      - 432b2c2 - 720b2cd - 432b2d2 + 16c2e2 - 32cde2 + 16d2e2 + 576ce - 576de
      - 240c + 5184,
    -15b2c3e + 15b2c2de - 81b2c2 + 216b2cd - 162b2d2 + 40c2e2 - 80cde2
      + 40d2e2 + 1008ce - 1008de + 5184,
    -4b2c2 + 4b2cd - 3b2d2 + 22ce - 22de + 261"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --moeller (DGP)
  debug needsPackage "PD"
  kk = QQ
  R = kk[a,b,c,d,u,v,w,x];
  I = ideal"
    a + b + c + d,
    u + v + w + x,
    3ab + 3ac + 3bc + 3ad + 3bd + 3cd + 2,
    bu + cu + du + av + cv + dv + aw + bw + dw + ax + bx + cx,
    bcu + bdu + cdu + acv + adv + cdv + abw + adw + bdw + abx + acx + bcx,
    abc + abd + acd + bcd,
    bcdu + acdv + abdw + abcx"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --buchberger (DGP, from POSSO)
  debug needsPackage "PD"
  kk = ZZ/32003
  R = kk[a,b,c,d,x,y,z,t];
  I = ideal"
  t - b - d,
  x + y + z + t - a - c - d,
  xz + yz + xt + zt - ac - ad - cd,
  xzt - acd"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --lanconelli (DGP, from POSSO)
  debug needsPackage "PD"
  kk = ZZ/32003
  R = kk[a,b,c,d,e,f,g,h,j,k,l];
  I = ideal"
    a + c + d + e + f + g + h + j - 1,
    -c2k - 2cdk - d2k - cek - dek - cfk - dfk - cgk - 
      dgk - egk - fgk - chk - dhk - ehk - fhk + c + d,
    -c2l-cdl-cel-cfl-cgl-dgl-egl-fgl+c2+2cd+d2+cg+dg+ch+dh,
    -b + c + e + g + j"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  --from ExampleIdeals/DGP.m2
  --wang2 (DGP)
  debug needsPackage "PD"
  kk = QQ
  R = kk[t,x,y,z];
  I = ideal"
  x2 + y2 + z2 - t2,
  xy + z2 - 1,
  xyz - x2 - y2 - z + 1"
  C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

--------------------------
-- from slower-tests.m2 --
--------------------------
SIMPLETEST ///
  debug needsPackage "PD"
  R = QQ[a,b,c,d,e,h]
  I = ideal(
     a+b+c+d+e,
	 d*e+c*d+b*c+a*e+a*b,
	 c*d*e+b*c*d+a*d*e+a*b*e+a*b*c,
	 b*c*d*e+a*c*d*e+a*b*d*e+a*b*c*e+a*b*c*d,
	 a*b*c*d*e-h^5)
   time C = minprimes I
   checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = ZZ/32003[a,b,c,d,e,h]
  I = ideal(
     a+b+c+d+e,
	 d*e+c*d+b*c+a*e+a*b,
	 c*d*e+b*c*d+a*d*e+a*b*e+a*b*c,
	 b*c*d*e+a*c*d*e+a*b*d*e+a*b*c*e+a*b*c*d,
	 a*b*c*d*e-h^5)
   time C = minprimes I
   checkMinimalPrimes(I, C, "Answer" => decompose)
///

SIMPLETEST ///
  -- UNKNOWN - Runs for a very long time on built in version, as well as the 'decompose' version.
  -- The GeneralPosition one does indeed run a lot faster though
  debug needsPackage "PD"
  R = ZZ/32003[a,b,c,d,e,f,g,h,j,k,l,MonomialOrder=>Lex]
    R = ZZ/32003[a,b,c,d,e,f,g,h,j,k,l]
  I = ideal "-2hjk + 4ef + bj + ak,
           -2hjl + 4eg + cj + al,
           -4fhj - 4ehk - djk + 2be + 2af,
           -4ghj - 4ehl - djl + 2ce + 2ag,
           -2dfj - 2dek + ab,
           -2dgj - 2del + ac"
   time C = minprimes I
   assert(intersect C == I)
   --checkMinimalPrimes(I, C, "CheckPrimality" => true) -- takes WAY too long to use as a test
   --checkMinimalPrimes(I, C, "Answer" => decompose) -- takes too long to use as a test
   assert false -- need to put some actual tests in here
///

SIMPLETEST ///
  debug needsPackage "PD"
  R = ZZ/32003[x,y,z,t,MonomialOrder=>Lex]
  I = ideal(
     y^2*z+2*x*y*t-2*x-z,
     -x^3*z+4*x*y^2*z+4*x^2*y*t+2*y^3*t+4*x^2-10*y^2+4*x*z-10*y*t+2,
     2*y*z*t+x*t^2-x-2*z,
     -x*z^3+4*y*z^2*t+4*x*z*t^2+2*y*t^3+4*x*z+4*z^2-10*y*t-10*t^2+2)
  time C = minprimes I
  checkMinimalPrimes(I, C, "Answer" => decompose)
///

BENCHMARK ///
  debug needsPackage "PD"
  --- UNKNOWN - Takes a very long time.
  R = ZZ/32003[a,b,c,d,e,f,h,MonomialOrder=>Lex]
  R = ZZ/32003[a,b,c,d,e,f,h]
  I = ideal(
         a+b+c+d+e+f,
	 a*b+b*c+c*d+d*e+e*f+a*f,
	 a*b*c+b*c*d+c*d*e+d*e*f+e*f*a+f*a*b,
	 a*b*c*d+b*c*d*e+c*d*e*f+d*e*f*a+e*f*a*b+f*a*b*c,
	 a*b*c*d*e+b*c*d*e*f+c*d*e*f*a+d*e*f*a*b+e*f*a*b*c+f*a*b*c*d,
	 a*b*c*d*e*f-h^6)
  time C = minprimes I -- STILL SLOW
///

BENCHMARK ///
  debug needsPackage "PD"
  R = ZZ/32003[a,b,c,d,e,f,g,h,j,k,l]
  I = ideal(h*j*l-2*e*g+16001*c*j+16001*a*l,h*j*k-2*e*f+16001*b*j+16001*a*k,h*j^2+2*e^2+16001*a*j,d*j^2+2*a*e,g*h*j+e*h*l+8001*d*j*l+16001*c*e+16001*a*g,f*h*j+e*h*k+8001*d*j*k+16001*b*e+16001*a*f
          ,e*g*j+8001*c*j^2+e^2*l,d*g*j+d*e*l+16001*a*c,e*f*j+8001*b*j^2+e^2*k,d*f*j+d*e*k+16001*a*b,d*e*j-a*h*j-16001*a^2,d*e^2-a*e*h-8001*a*d*j,d*g*k*l-c*h*k*l-d*f*l^2+b*h*l^2-2*c*f*g+2*b*g^2-16001
       	  *c^2*k+16001*b*c*l,d*g*k^2-c*h*k^2-d*f*k*l+b*h*k*l-2*c*f^2+2*b*f*g-16001*b*c*k+16001*b^2*l,d*g^2*k-c*g*h*k-d*f*g*l+c*f*h*l-8001*c*d*k*l+8001*b*d*l^2+16001*c^2*f-16001*b*c*g,d*f*g*k-b*g*h*k-
       	  8001*c*d*k^2-d*f^2*l+b*f*h*l+8001*b*d*k*l+16001*b*c*f-16001*b^2*g,c*f*g*k-b*g^2*k-8001*c^2*k^2-c*f^2*l+b*f*g*l-16001*b*c*k*l-8001*b^2*l^2,e^2*g*k+8001*c*e*j*k-e^2*f*l-8001*b*e*j*l,d*g*h*l^2
       	  -c*h^2*l^2-8001*d^2*l^3+2*d*g^3-2*c*g^2*h+16000*c*d*g*l+c^2*h*l-8001*c^3,d*f*h*l^2-b*h^2*l^2-8001*d^2*k*l^2+2*d*f*g^2-2*b*g^2*h+16001*c*d*g*k+16001*c*d*f*l+16001*b*d*g*l+b*c*h*l-8001*b*c^2,
       	  d*f*h*k*l-b*h^2*k*l-8001*d^2*k^2*l+2*d*f^2*g-2*b*f*g*h+16001*c*d*f*k+16001*b*d*g*k-16001*b*c*h*k+16001*b*d*f*l-16001*b^2*h*l-8001*b^2*c,d*f*h*k^2-b*h^2*k^2-8001*d^2*k^3+2*d*f^3-2*b*f^2*h+
       	  16000*b*d*f*k+b^2*h*k-8001*b^3)
  time C = minprimes I
  assert(#C == 1)
  assert(C#0 == I)
  -- TODO: check that I is really prime here
  
  -- here is an independent check that I is prime:
  I : (j*l) == I
  I1 = eliminate(I, h)
  codim I1
  I1_0
  I : e == I
  I1 = eliminate(I, {h,b,j})
  codim I1
  -- this I1 is irreducible over the field, of codim 1, and is birational to I, therefore I is prime    
///


-- above are from slower-tests.m2 --
end

-- 

restart
loadPackage "UnitTestsPD"
check "UnitTestsPD"


