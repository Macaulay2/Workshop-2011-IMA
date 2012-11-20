R = ZZ/32003[vars(0..15)]
M = genericMatrix(R,a,4,4)
I = permanents(3,M)


end

  restart
  debug needsPackage "PD"
  debug needsPackage "SingularInterface"

  load "PD/example-permanents.m2"
  time minprimes I
