-- Copyright 1996 Michael E. Stillman
-- Based on the Macaulay script written by David Eisenbud

monomialCurveIdeal = { Affine => false } -> (S, a) -> (
    -- check that S is a polynomial ring over a field
    n := # a;
    if not all(a, i -> instance(i,ZZ) and i >= 1)
      then error "expected positive integers";
    s := symbol s;
    t := symbol t;
    k := coefficientRing S;
    local M1;
    local M2;
    local R1;
    local R2;
    local mm;
    if o.Affine then (
      M1 = monoid [t];
      M2 = monoid [Variables=>n];
      R1 = k M1;
      R2 = k M2;
      t = R1_0;
      mm = matrix table(1, n, (j,i) -> t^(a#i));
    ) else (
      topa := max a;
      a = prepend(0,a);
      M1 = monoid [s,t];
      M2 = monoid [Variables=>n+1];
      R1 = k M1;
      R2 = k M2;
      s = R1_0;
      t = R1_1;
      mm = matrix table(1, n+1, (j,i) -> s^(a#i) * t^(topa - a#i));
    )
    j := generators kernel map(R1, R2, mm);
    ideal substitute(j, submatrix(vars S, {0..n}))
    )

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/m2 "
-- End:
