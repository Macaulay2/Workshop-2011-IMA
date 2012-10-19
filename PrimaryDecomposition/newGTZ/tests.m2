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



