--------------------------------------------------------
--3randomcubics-4vars-32003
  Q = ZZ/32003[a,b,c,d]
  -- 3 random cubics in R
  ideal(-840*a^3-7687*a^2*b+9625*a*b^2-3820*b^3-10392*a^2*c-13100*a*b*c-11362*b^2*c-7463*a*c^2-11288*b*c^2+1417*c^3-14802*a^2*d-7804*a*b*d+5834*b^2*d-10186*a*c*d-11900*b*c*
     d+5062*c^2*d+14848*a*d^2+1270*b*d^2+4670*c*d^2+14589*d^3,6046*a^3-1565*a^2*b-10455*a*b^2+13719*b^3+9618*a^2*c+4969*a*b*c+14049*b^2*c+7621*a*c^2-15861*b*c^2-11905*c^3-
     13456*a^2*d+2029*a*b*d+8067*b^2*d-10420*a*c*d-14441*b*c*d-13965*c^2*d-3634*a*d^2-4035*b*d^2+350*c*d^2-8942*d^3,-12512*a^3-11973*a^2*b-8963*a*b^2-12001*b^3-10663*a^2*c-
     7202*a*b*c+9856*b^2*c-7955*a*c^2-8818*b*c^2+398*c^3+4259*a^2*d+13332*a*b*d+1576*b^2*d+3008*a*c*d+2588*b*c*d-6135*c^2*d-5311*a*d^2+6731*b*d^2-13991*c*d^2-9315*d^3)
--------------------------------------------------------
--hcyclic3-32003
  R = ZZ/32003[a,b,c,h]
  ideal(a+b+c,a*b+b*c+a*c,a*b*c-h^3)
--------------------------------------------------------
--hcyclic4-32003
  R = ZZ/32003[a,b,c,d,h]
  ideal(a+b+c+d,a*b+b*c+c*d+d*a,a*b*c+b*c*d+c*d*a+d*a*b,a*b*c*d-h^4)
--------------------------------------------------------
--hcyclic4-0
  R = QQ[a,b,c,d,h]
  ideal(a+b+c+d,a*b+b*c+c*d+d*a,a*b*c+b*c*d+c*d*a+d*a*b,a*b*c*d-h^4)
--------------------------------------------------------
--binom1-0
  R = QQ[a,b,c,d]
  ideal(a^2-b^2,a*b*c-d^3,b*d^2-a*c^2)
--------------------------------------------------------
--binom1-32003
  R = ZZ/32003[a,b,c,d]
  ideal(a^2-b^2,a*b*c-d^3,b*d^2-a*c^2)
--------------------------------------------------------
--huh1-32003
  R = ZZ/32003[x,y,z,MonomialOrder=>Lex]
  p = z^2+1
  q = z^4+2
  ideal(p^2*q^3, (y-z^3)^3, (x-y*z+z^4)^4)
--------------------------------------------------------
--ST_S/Y-0
  R = QQ[b,s,t,u,v,w,x,y,z];
  I = ideal"su - bv, tv - sw, vx - uy, wy - vz"
--------------------------------------------------------
--huh2-0
  R = QQ[vars(0..8)];
  I = ideal(b*d+a*e,c*d+a*f,c*e+b*f,b*g+a*h,c*g+a*i,c*h+b*i,e*g+d*h,f*g+d*i,f*h+e*i)
--------------------------------------------------------
--huh2-lex-0
  R = QQ[vars(0..8),MonomialOrder=>Lex];
  I = ideal(b*d+a*e,c*d+a*f,c*e+b*f,b*g+a*h,c*g+a*i,c*h+b*i,e*g+d*h,f*g+d*i,f*h+e*i)
--------------------------------------------------------
--replaceme
  R = ZZ/32003[x,y,z];
  I = ideal"
    x2yz + xy2z + xyz2 + xyz + xy + xz + yz,
    x2y2z + xy2z2 + x2yz + xyz + yz + x + z,
    x2y2z2 + x2y2z + xy2z + xyz + xz + z + 1";
--------------------------------------------------------
--
  R = ZZ/32003[x,y,z,t]
  I = ideal(
    t^10-x,
    t^31-t^6-t-y,
    t^8-z)
--------------------------------------------------------
--chemistry-32003
  kk = ZZ/32003
  R = kk[a,b,c,d,e,f,g,h,j];
  I = ideal"
    a+2b+c-d+g,
    f2gh - a,
    efg - c,
    fg2j - b,
    a + b + c + f + g - 1,
    3ad + 3bd + 2cd + df + dg - a - 2b - c - g"
--------------------------------------------------------
--horrocks-32003
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
--------------------------------------------------------
-- square3x3-32003
  kk = ZZ/32003
  R = kk[vars(0..8)]
  I = ideal (genericMatrix(R,3,3))^2
--------------------------------------------------------
-- SY-I8-0
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
