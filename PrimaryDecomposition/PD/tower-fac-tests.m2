-------------------------------------------
-- wang1
  restart
  debug needsPackage "PD"
  R = QQ[y,a,b, MonomialOrder=>Lex]
  R = QQ[y,a,b]
  R = QQ[a,b,y]
  T = ideal {a + b^2, a^2-b*a+1}
  flatten entries gens gb T
  F = (y+a)*(y-2*b)*(y^2+a+b)
  F = F % T
  I = T + ideal F
  time minprimes(I, Verbosity=>2)
  (S,SF) = makeFiberRings({}, R)
  TS = flatten entries gens gb sub(T, S)
  FS = sub(F, S) % (ideal TS)
  factorOverTower(TS, FS)
  assert((product(oo/last)) % (ideal TS) == FS)

