-------------------------------------------
-- wang1
  restart
  debug needsPackage "PD"
  R = QQ[y,a,b]
  T = ideal {a + b^2, a^2-b*a+1}
  flatten entries gens gb T
  F = (y+a)*(y-2*b)*(y^2+a+b)
  F = F % T
  (S,SF) = makeFiberRings({}, R)
  TS = flatten entries gens gb sub(T, S)
  FS = sub(F, S) % (ideal TS)
  towerFac = factorOverTower(TS, FS)
  assert((product(towerFac/last)) % (ideal TS) == FS)

-- wang2
  restart
  debug needsPackage "PD"
  R = QQ[y,a,b,c]
  T = ideal {a^2-a*b+a*c-a-b,
             a^2-a*c+a-b^2-b*c-b+c^2,
             -1+a^2+a*c+a-b^2-b+c^2-c}
  flatten entries gens gb T
  F = (y+a*c+b+a)*(y-2*b^2+c^2+1)*(y^2+a*b+c)
  F = F % T
  (S,SF) = makeFiberRings({}, R)
  TS = flatten entries gens gb sub(T, S)
  FS = sub(F, S) % (ideal TS)
  towerFac = factorOverTower(TS, FS)
  prodTowerFac = (product(towerFac/last)) % (ideal TS);
  prodTowerFac = (1/(leadCoefficient prodTowerFac))*prodTowerFac;
  assert(prodTowerFac == FS)

-- wang3
  restart
  debug needsPackage "PD"
  debug needsPackage "UnitTestsPD"
  R = ZZ/32003[y,a,b,c,d, MonomialOrder=>Lex]
  T = ideal {a^2+a*c-a*d+b^2-b+c*d-d^2-d,
             a^2+a*b-a*d+b^2+b*c+b+d^2-d,
             1+a*b-a*c+a*d+a+b^2-b*c+b*d-b+c^2+c*d-d^2,
             a^2+a*b+a*c+a*d-b^2+b*c-b+c^2-c*d-d^2+d}
  -- not a tower?
  Tgb = flatten entries gens gb T
  factor first Tgb
  C = minprimes(T,Verbosity=>2); -- looks correct here.
  checkMinimalPrimes(T,C,"CheckPrimality"=>true)    -- checks out.  WAY faster than decompose.
  F = (y+a)*(y-2*d)*(y+b+c)
  F = F % T
  (S,SF) = makeFiberRings({}, R)
  TS = flatten entries gens gb sub(T, S)
  FS = sub(F, S) % (ideal TS)
  time towerFac = factorOverTower(TS, FS)  --- bug here!  Why are we getting things
                                           --- of higher degree?  Ans: Not a tower in the
                                           --- first place!
  prodTowerFac = (product(towerFac/last)) % (ideal TS);
  prodTowerFac = (1/(leadCoefficient prodTowerFac))*prodTowerFac;
  assert(prodTowerFac == FS)


