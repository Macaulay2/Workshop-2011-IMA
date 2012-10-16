PDTEST ///
  R = QQ[a,b,c]
  I = ideal apply(1 .. 3, i -> random(3,R))
///

PDTEST ///
  -- 2x2 permanents of generic 3x3 matrix
  R = ZZ/32003[vars(0..8)];
  I = ideal(b*d+a*e,c*d+a*f,c*e+b*f,b*g+a*h,c*g+a*i,c*h+b*i,e*g+d*h,f*g+d*i,f*h+e*i)
///

PDTEST ///
  -- 2x2 permanents of generic 3x3 matrix
  R = ZZ/32003[vars(0..8), MonomialOrder=>Lex];
  I = ideal(b*d+a*e,c*d+a*f,c*e+b*f,b*g+a*h,c*g+a*i,c*h+b*i,e*g+d*h,f*g+d*i,f*h+e*i)
///

PDTEST ///
  -- 2x2 permanents of generic 3x3 matrix
  R = QQ[vars(0..8)];
  I = ideal(b*d+a*e,c*d+a*f,c*e+b*f,b*g+a*h,c*g+a*i,c*h+b*i,e*g+d*h,f*g+d*i,f*h+e*i)
///

PDTEST ///
  R = ZZ/32003[x,y,z];
  I = ideal"
    x2yz + xy2z + xyz2 + xyz + xy + xz + yz,
    x2y2z + xy2z2 + x2yz + xyz + yz + x + z,
    x2y2z2 + x2y2z + xy2z + xyz + xz + z + 1";
///

PDTEST ///
  R = ZZ/32003[x,y,z,t]
  I = ideal(
    t^10-x,
    t^31-t^6-t-y,
    t^8-z)
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  --chemistry: a chemical process in glass melting (DGP set) 9 variables
  kk = ZZ/101
  R = kk[a,b,c,d,e,f,g,h,j];
  I = ideal"
    a+2b+c-d+g,
    f2gh - a,
    efg - c,
    fg2j - b,
    a + b + c + f + g - 1,
    3ad + 3bd + 2cd + df + dg - a - 2b - c - g"
///

PDTEST ///
  --from ExampleIdeals/DGP.m2 x
  kk = ZZ/32003
  --sy-j: shimoyama-yokoyama example J (DGP) 3 variables (J_S/Y) x
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
///

PDTEST ///
  --from ExampleIdeals/DGP.m2 x
  kk = ZZ/32003
  --sy-st: shimoyama-yokoyama example St (DGP) 9 variables (ST_S/Y) x
  R = kk[b,s,t,u,v,w,x,y,z];
  I = ideal"su - bv, tv - sw, vx - uy, wy - vz"
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/32003
  --horrocks (DGP) related to the Horrock bundle on P5 x
  R = kk[a,b,c,d,e,f];
  I = ideal"
    2adef + 3be2f - cef2,
    4ad2f + 5bdef + cdf2,
    2abdf + 3b2ef - bcf2,
    4a2df + 5abef + acf2,
    4ad2e + 3bde2 + 7cdef,
    2acde + 3bce2 - c2ef,
    4abde + 3b2e2 - 4acdf + 2bcef - c2f2,
    4a2de + 3abe2 + 7acef,
    4acd2 + 5bcde + c2df,
    4abd2 + 3b2de + 7bcdf,
    16a2d2 - 9b2e2 + 32acdf - 18bcef + 7c2f2,
    2abcd + 3b2ce - bc2f,
    4a2cd + 5abce + ac2f,
    4a2bd + 3ab2e + 7abcf,
    abc2f - cdef2,
    ab2cf - bdef2,
    2a2bcf + 3be2f2 - cef3,
    ab3f - 3bdf3,
    2a2b2f - 4adf3 + 3bef3 - cf4,
    a3bf + 4aef3,
    3ac3e - cde3,
    3b2c2e - bc3f + 2cd2ef,
    abc2e - cde2f,
    6a2c2e - 4ade3 - 3be4 + ce3f,
    3b3ce - b2c2f + 2bd2ef,
    2a2bce + 3be3f - ce2f2,
    3a3ce + 4ae3f,
    4bc3d + cd3e,
    4ac3d - 3bc3e - 2cd2e2 + c4f,
    8b2c2d - 4ad4 - 3bd3e - cd3f,
    4b3cd + 3bd3f,
    4ab3d + 3b4e - b3cf - 6bd2f2,
    4a4d + 3a3be + a3cf - 8ae2f2
    "
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/32003
  --arnborg-lazard (DGP, from POSSO) x
  R = kk[x,y,z];
  I = ideal"
    x2yz + xy2z + xyz2 + xyz + xy + xz + yz,
    x2y2z + xy2z2 + x2yz + xyz + yz + x + z,
    x2y2z2 + x2y2z + xy2z + xyz + xz + z + 1"
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/32003
  --roczen (DGP) related to classification of singularities (Marko) x
  R = kk[a,b,c,d,e,f,g,h,k,o];
  I = ideal"
    o+1,
    k4+k,
    hk,
    h4+h,
    gk,
    gh,
    g3+h3+k3+1,
    fk,
    f4+f,
    eh,
    ef,
    f3h3+e3k3+e3+f3+h3+k3+1,
    e3g+f3g+g,
    e4+e,
    dh3+dk3+d,
    dg,
    df,
    de,
    d3+e3+f3+1,
    e2g2+d2h2+c,
    f2g2+d2k2+b,
    f2h2+e2k2+a"
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --becker-niermann (DGP)
  R = kk[x,y,z];
  I = ideal"
    x2+xy2z-2xy+y4+y2+z2,
    -x3y2+xy2z+xyz3-2xy+y4,
    -2x2y+xy4+yz4-3"
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
--caprasse4 (DGP, from POSSO)
R = kk[x,y,z,t];
I = ideal"
  y2z+2xyt-2x-z,
  -x3z+4xy2z+4x2yt+2y3t+4x2-10y2+4xz-10yt+2,
  2yzt+xt2-x-2z,
  -xz3+4yz2t+4xzt2+2yt3+4xz+4z2-10yt-10t2+2"
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
--cassou (DGP, from POSSO)
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
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --square of a generic 3x3 matrix (DGP, from POSSO)
  R = kk[vars(0..8)]
  I = ideal (genericMatrix(R,3,3))^2
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --shimoyama-yokoyama example I8 (DGP)
  R = ZZ/32003[b,c,d,e,f,g,h,j,k,l];
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
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --moeller (DGP)
  R = kk[a,b,c,d,u,v,w,x];
  I = ideal"
    a + b + c + d,
    u + v + w + x,
    3ab + 3ac + 3bc + 3ad + 3bd + 3cd + 2,
    bu + cu + du + av + cv + dv + aw + bw + dw + ax + bx + cx,
    bcu + bdu + cdu + acv + adv + cdv + abw + adw + bdw + abx + acx + bcx,
    abc + abd + acd + bcd,
    bcdu + acdv + abdw + abcx"
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --riemenschneider (DGP) related to deformations of quotient singularities
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
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --buchberger (DGP, from POSSO)
  R = kk[a,b,c,d,x,y,z,t];
  I = ideal"
  t - b - d,
  x + y + z + t - a - c - d,
  xz + yz + xt + zt - ac - ad - cd,
  xzt - acd"
///


PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --lanconelli (DGP, from POSSO)
  R = kk[a,b,c,d,e,f,g,h,j,k,l];
  I = ideal"
  a + c + d + e + f + g + h + j - 1,
  -c2k - 2cdk - d2k - cek - dek - cfk - dfk - cgk - 
    dgk - egk - fgk - chk - dhk - ehk - fhk + c + d,
  -c2l-cdl-cel-cfl-cgl-dgl-egl-fgl+c2+2cd+d2+cg+dg+ch+dh,
  -b + c + e + g + j"
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --wang2 (DGP)
  R = kk[t,x,y,z];
  I = ideal"
  x2 + y2 + z2 - t2,
  xy + z2 - 1,
  xyz - x2 - y2 - z + 1"
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --macaulay (DGP, from an older M2 tutorial)
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
///

PDTEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --parametric curve (not in published DGP)
  R = ZZ/32003[x,y,z,t]
  I = ideal(
    t^10-x,
    t^31-t^6-t-y,
    t^8-z)
///

