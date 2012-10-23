BENCH ///
  R = ZZ/32003[a,b,c,d,e,f,g,h,j,k,l]
  I = ideal(h*j*l-2*e*g+16001*c*j+16001*a*l,h*j*k-2*e*f+16001*b*j+16001*a*k,h*j^2+2*e^2+16001*a*j,d*j^2+2*a*e,g*h*j+e*h*l+8001*d*j*l+16001*c*e+16001*a*g,f*h*j+e*h*k+8001*d*j*k+16001*b*e+16001*a*f
          ,e*g*j+8001*c*j^2+e^2*l,d*g*j+d*e*l+16001*a*c,e*f*j+8001*b*j^2+e^2*k,d*f*j+d*e*k+16001*a*b,d*e*j-a*h*j-16001*a^2,d*e^2-a*e*h-8001*a*d*j,d*g*k*l-c*h*k*l-d*f*l^2+b*h*l^2-2*c*f*g+2*b*g^2-16001
       	  *c^2*k+16001*b*c*l,d*g*k^2-c*h*k^2-d*f*k*l+b*h*k*l-2*c*f^2+2*b*f*g-16001*b*c*k+16001*b^2*l,d*g^2*k-c*g*h*k-d*f*g*l+c*f*h*l-8001*c*d*k*l+8001*b*d*l^2+16001*c^2*f-16001*b*c*g,d*f*g*k-b*g*h*k-
       	  8001*c*d*k^2-d*f^2*l+b*f*h*l+8001*b*d*k*l+16001*b*c*f-16001*b^2*g,c*f*g*k-b*g^2*k-8001*c^2*k^2-c*f^2*l+b*f*g*l-16001*b*c*k*l-8001*b^2*l^2,e^2*g*k+8001*c*e*j*k-e^2*f*l-8001*b*e*j*l,d*g*h*l^2
       	  -c*h^2*l^2-8001*d^2*l^3+2*d*g^3-2*c*g^2*h+16000*c*d*g*l+c^2*h*l-8001*c^3,d*f*h*l^2-b*h^2*l^2-8001*d^2*k*l^2+2*d*f*g^2-2*b*g^2*h+16001*c*d*g*k+16001*c*d*f*l+16001*b*d*g*l+b*c*h*l-8001*b*c^2,
       	  d*f*h*k*l-b*h^2*k*l-8001*d^2*k^2*l+2*d*f^2*g-2*b*f*g*h+16001*c*d*f*k+16001*b*d*g*k-16001*b*c*h*k+16001*b*d*f*l-16001*b^2*h*l-8001*b^2*c,d*f*h*k^2-b*h^2*k^2-8001*d^2*k^3+2*d*f^3-2*b*f^2*h+
       	  16000*b*d*f*k+b^2*h*k-8001*b^3)
///


BENCH ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/32003
  --butcher (DGP) (up to a change of coordinates, this appears to be Bu_S/Y (Wang2)) x
  R = kk[a,b,c,d,e,f,g,h];
  I = ideal"
    a + c + d - e - h,
    2df + 2cg + 2eh - 2h2 - h - 1,
    3df2 + 3cg2 - 3eh2 + 3h3 + 3h2 - e + 4h,
    6bdg - 6eh2 + 6h3 - 3eh + 6h2 - e + 4h,
    4df3 + 4cg3 + 4eh3 - 4h4 - 6h3 + 4eh - 10h2 - h - 1,
    8bdfg + 8eh3 - 8h4 + 4eh2 - 12h3 + 4eh - 14h2 - 3h - 1,
    12bdg2 + 12eh3 - 12h4 + 12eh2 - 18h3 + 8eh - 14h2 - h - 1,
    -24eh3 + 24h4 - 24eh2 + 36h3 - 8eh + 26h2 + 7h + 1"
  testPD I
///

BENCH  ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --gonnet (DGP) (I think this is: Go_S/Y, with change of coordinates) x
  R = kk[a,b,c,d,e,f,g,h,j,k,l,m,n,o,p,q,s];
  I = ideal "
    ag,
    gj + am + np + q,
    bl,
    nq,
    bg + bk + al + lo + lp + b + c,
    ag + ak + jl + bm + bn + go + ko + gp + kp + lq + a + d + f + h + o + p,
    gj + jk + am + an + mo + no + mp + np + gq + kq + e + j + q + s - 1,
    jm + jn + mq + nq,
    jn + mq + 2nq,
    gj + am + 2an + no + np + 2gq + kq + q + s,
    2ag + ak + bn + go + gp + lq + a + d,
    bg + al,
    an + gq,
    2jm + jn + mq,
    gj + jk + am + mo + 2mp + np + e + 2j + q,
    jl + bm + gp + kp + a + f + o + 2p,
    lp + b,
    jn + mq,
    gp + a
    "
  testPD I
///


BENCH ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --schwarz (DGP) constructing idempotents in group theory x
  R = kk[a,b,c,d,e,h];
  I = ideal"
    -ab - b2 - 2de - 2ch,
    -ac - 2bc - e2 - 2dh,
    -c2 - ad - 2bd - 2eh,
    -2cd - ae - 2be - h2,
    -d2 - 2ce - ah - 2bh
    "
///

BENCH ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
--dejong (DGP) related to the base space of a semi-universal deformation
-- of a rational quadruple point (same as Theo1, after change of coord) x
R = kk[a,b,c,d,e,f,g,h,j,k,l]
I = ideal"-2hjk + 4ef + bj + ak,
  -2hjl + 4eg + cj + al,
  -4fhj - 4ehk - djk + 2be + 2af,
  -4ghj - 4ehl - djl + 2ce + 2ag,
  -2dfj - 2dek + ab,
  -2dgj - 2del + ac"
///

BENCH ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
--gerdt (DGP, from POSSO)
R = kk[t,u,v,w,x,y,z];
I = ideal"2tw + 2wy - wz,
  2uw2 - 10vw2 + 20w3 - 7tu + 35tv - 70tw,
  6tw2 + 2w2y - 2w2z - 21t2 - 7ty + 7tz,
  2v3 - 4uvw - 5v2w + 6uw2 + 7vw2 - 15w3 - 42vy,
  6tw + 9wy + 2vz - 3wz - 21x,
  9uw3-45vw3+135w4+14tv2-70tuw+196tvw-602tw2-14v2z+28uwz+
    14vwz - 28w2z + 147ux - 735vx + 2205wx - 294ty + 98tz + 294yz - 98z2,
  36tw3+6w3y-9w3z-168t2w-14v2x+28uwx+14vwx-28w2x-28twy+
    42twz + 588tx + 392xy - 245xz,
  2uvw - 6v2w - uw2 + 13vw2 - 5w3 - 28tw + 14wy,
  u2w - 3uvw + 5uw2 - 28tw + 14wy,
  tuw + tvw - 11tw2 - 2vwy + 8w2y + uwz - 3vwz + 5w2z - 21wx,
  5tuw-17tvw+33tw2-7uwy+22vwy-39w2y-2uwz+6vwz-10w2z+63wx,
  20t2w - 12uwx + 30vwx - 15w2x - 10twy - 8twz + 4wyz,
  4t2w - 6uwx + 12vwx - 6w2x + 2twy - 2wy2 - 2twz + wyz,
  8twx + 8wxy - 4wxz"
///

SLOW  ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --mikro (DGP) from analyzing analog circuits
  R = kk[a,b,c,d,e,f,g,h]
  I = ideal"
  59ad + 59ah + 59dh - 705d - 1199h,
  330acde + 330aceh + 330cdeh - 407acd - 1642ade - 1410cde 
    - 407ach - 407cdh - 1642aeh - 2398ceh - 1642deh,
  -483acd - 483ach - 483cdh + 821ad + 705cd + 821ah + 1199ch + 821dh,
  13926abcde + 13926abceh + 13926bcdeh - 9404abcd - 9239abde 
    - 4968acde - 13157bcde - 9404abch - 9404bcdh - 9239abeh 
    - 4968aceh - 13025bceh - 9239bdeh - 4968cdeh,
  -cde - 377cdh - ceh - deh,
  -54acf - 54adf + a + d,
  adfg + a + d"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --amrhein (DGP)
  R = kk[a,b,c,d,e,f];
  I = ideal"
  a2 + d2 + 2ce + 2bf + a,
  2ab + 2de + 2cf + b,
  b2 + 2ac + e2 + 2df + c,
  2bc + 2ad + 2ef + d,
  c2 + 2bd + 2ae + f2 + e,
  2cd + 2be + 2af + f"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/5
  --huneke (DGP)
  R = kk[s,t,u,x,y]
  I = ideal"
  s15,
  t15,
  u15,
  u5 - s3tx + s2t2x + s2t2y - st3y"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --wang1 (DGP)
  R = kk[a,b,c,d,e,f,g,h,k,l];
  I = ideal"
  f2h-1,
  ek2 - 1,
  g2l - 1,
  2ef2g2hk2 + f2g2h2k2 + 2ef2g2k2l + 2f2g2hk2l + f2g2k2l2 + ck2,
  2e2fg2hk2 +2efg2h2k2 +2e2fg2k2l+4efg2hk2l+2fg2h2k2l+2efg2k2l2
    + 2fg2hk2l2 + 2bfh,
  2e2f2ghk2 +2ef2gh2k2 +2e2f2gk2l+4ef2ghk2l+2f2gh2k2l+2ef2gk2l2
    + 2f2ghk2l2 + 2dgl,
  e2f2g2k2 + 2ef2g2hk2 + 2ef2g2k2l + 2f2g2hk2l + f2g2k2l2 + bf2,
  2e2f2g2hk +2ef2g2h2k +2e2f2g2kl+4ef2g2hkl+2f2g2h2kl+2ef2g2kl2
    + 2f2g2hkl2 + 2cek,
  e2f2g2k2 + 2ef2g2hk2 + f2g2h2k2 + 2ef2g2k2l + 2f2g2hk2l + dg2,
  -e2f2g2hk2-ef2g2h2k2-e2f2g2k2l-2ef2g2hk2l-f2g2h2k2l-ef2g2k2l2
    - f2g2hk2l2 + a2"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --siebert (DGP)
  R = kk[t,w,x,y,z];
  I = ideal"
  w2xy + w2xz + w2z2,
  tx2y + x2yz + x2z2,
  twy2 + ty2z + y2z2,
  t2wx + t2wz + t2z2"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --amrheim2 (DGP)
  R = kk[a,b,c,d,e,f,g];
  I = ideal"
  a2 + 2de + 2cf + 2bg + a,
  2ab + e2 + 2df + 2cg + b,
  b2 + 2ac + 2ef + 2dg + c,
  2bc + 2ad + f2 + 2eg + d,
  c2 + 2bd + 2ae + 2fg + e,
  2cd + 2be + 2af + g2 + f,
  d2 + 2ce + 2bf + 2ag + g"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/3
  --huneke2 (not in published DGP) -- over ZZ/3 is real test
  R = kk[x,y,u,s,t];
  I = ideal"
  x27,
  y27,
  u27,
  u5-xy(x-y)(sx-ty)"
///


SLOW ///
  -- DGP Wang
  R = ZZ/32003[a,b,c,d,f,g,h,k,l,s,t,u,v,w,x,y,z]
  I = ideal"
    -ab-ad+2ah,
    ad-bd-cf-2ah+2bh+2ck,
    ab-ad-2bh+2dh-2ck+2fk+2gl,
    ac-2cs-at+2bt,
    ac-cs-2at+bt,
    -d-3s+4u,
    -f-3t+4v,
    -g+4w,
    -a+2x,
    -b2-c2+2bx+2cy,
    -d2-f2-g2+2dx+2fy+2gz"
  testPD I
///
