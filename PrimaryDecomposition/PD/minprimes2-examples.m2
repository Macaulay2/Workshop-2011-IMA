--------------------------------------------------------
--3x3perms4x4
  R = ZZ/32003[vars(0..15)]
  M = genericMatrix(R,a,4,4)
  permanents(3,M)
--------------------------------------------------------
--stewart-gough-nonreduced
  -- minprimes time, 13 Mar 2013, Mike rMBP:  stratA: 8.1 sec
  -- #minprimes: 17, one codim 6, rest codim 7.
  R = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  ideal(r^2-3,
        e_1*g_1+e_2*g_2+e_3*g_3+e_4*g_4, 
        (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2-r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2+r*e_2*g_4-g_4^2,
        (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, 
        (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2,
        (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2+r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2-r*e_2*g_4-g_4^2, 
        (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2, 
        (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2)
--------------------------------------------------------
--conca
  -- minprimes time, 13 Mar 2013, Mike rMBP: 59.5 sec, stratA: 1.78 sec, decompose: 14.4 sec
  -- #minprimes: 8, codims: all codim 4
  R = ZZ/31991[x_11, x_12, x_13, x_14, x_15, x_16, x_21, x_22, x_23, x_24, x_25, x_26, x_31, x_32, x_33, x_34, x_35, x_36]
  ideal(
    -x_13*x_22*x_31 + x_12*x_23*x_31 + x_13*x_21*x_32 - x_11*x_23*x_32 - x_12*x_21*x_33 + x_11*x_22*x_33,
    -x_14*x_22*x_31 + x_12*x_24*x_31 + x_14*x_21*x_32 - x_11*x_24*x_32 - x_12*x_21*x_34 + x_11*x_22*x_34,
    -x_15*x_23*x_31 + x_13*x_25*x_31 + x_15*x_21*x_33 - x_11*x_25*x_33 - x_13*x_21*x_35 + x_11*x_23*x_35,
    -x_16*x_23*x_32 + x_13*x_26*x_32 + x_16*x_22*x_33 - x_12*x_26*x_33 - x_13*x_22*x_36 + x_12*x_23*x_36
    )
--------------------------------------------------------
--franzi-siphon-naive
  -- has 131 components, same as franzi-siphon-nonnaive
  R1 = QQ[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,A,B,C,D,E,F,G,H,I,J,K,L,M,MonomialSize => 8]
  ideal ( I*K-K^2, r*G-G^2, A*D-D^2, k*z-z^2, m*w-w^2, j^2-j*t, d*f-f^2, p*y*M-p^2, k*w*M-w^2, j*r*M-j*t, 
      I*J*L-J^2, B*H*L-H^2, A*E*L-E^2, b*C*L-C^2, b*B*L-b^2, t*x*L-x^2, a*u*L-a^2, m*q*L-q^2, d*g*L-g^2, 
      o*J*K-J^2, k*s*K-K^2, i*B*H-H^2, l*F*G-G^2, v*D*F-D^2, e*z*F-z^2, r*y*F-r^2, f*s*F-f^2, j*p*F-j*t, 
      o*D*E-E^2, r*s*D-D^2, b*i*C-C^2, s*v*y-v^2, i*j*x-x^2, i*q*w-q^2, a*o*u-a^2, i*k*r-r^2, f*g*o-g^2, 
      h*i*n-h^2, e*i*l-l^2, c*h*i-h^2, y^2*M^2-p^2, r^2*M^2-j*t, k^2*M^2-w^2, I^2*L^2-J^2, B^2*L^2-b^2, 
      A^2*L^2-E^2, t^2*L^2-x^2, m^2*L^2-q^2, d^2*L^2-g^2, y^2*F^2-r^2, v^2*F^2-D^2, s^2*F^2-f^2, 
      p^2*F^2-j*t, l^2*F^2-G^2, e^2*F^2-z^2, i^2*B^2-H^2, s^2*y^2-v^2, o^2*u^2-a^2, r^2*s^2-D^2, 
      k^2*s^2-K^2, i^2*k^2-r^2, e^2*i^2-l^2, c^2*i^2-h^2, b^2*i^2-C^2)
--------------------------------------------------------
--franzi-siphon-nonnaive1
  -- 131 components, codims: 2:26, 12:27, 12:28, 24:29, 12:30, 29:31, 28:32, 12:33
  R1 = QQ[x3283, x3096, x2909, x1952, x319, x1683, x2321, x2921, x2855, x1370, x622, x331, x1904, x2933, 
      x2867, x1382, x2273, x634, x343, x1916, x3319, x1647, x1394, x2285, x646, x421, x1928, x3331,
       x3188, x1659, x2297, x295, x433, x3271, x1940, x2309, x1671, x2254, x307];
  I1 = ideal(x1940*x1671-x1671^2,-x622*x343+x1671,-x1940*x2254+x2309,x2867*x2309*x1671-x2309^2,x3331*x3271*x2254-x3271^2,
      -x2855*x3331+x3271,x634*x433-x433^2,-x331*x295+x433,-x1928*x2254+x2297,x2867*x1659*x2297-x2297^2,
      x1928*x1659-x1659 ^2,-x1647*x295+x1659,-x634*x343+x1659,x3096*x3188*x2254-x3188^2,
      -x3096*x2855+x3188,x622*x421-x421^2,-x319*x295+x421,-x1916*x2254+x2285,x2855*x1370*x2285-x2285^2,
      x1904*x1394-x1394^2,-x622*x307+x1394,-x343*x646+x1647,-x1370^2+ x1370*x1916,-x646*x295+x634,
      -x2855*x622+x634,-x1904*x2254+x2273,x2855*x2273*x1394-x2273^2,-x646*x307+x1382,-x319*x2855+x331,
      -x634*x307+x1370,-x1382*x295+x1370,x2921*x2855*x2933-x2921^2,-x2909*x2855+x2921,-x1952*x2254+x2321,
      x1683*x2321*x2867-x2321^2,x1952*x1683-x1683^2,-x343*x295+x1683,-x3331*x2254+x3096,
      x3283*x3319*x2254-x3283^2,-x2867*x3319+x3283)
--------------------------------------------------------
--franzi-siphon-nonnaive2
  -- 131 components, codims: 2:26, 12:27, 12:28, 24:29, 12:30, 29:31, 28:32, 12:33
  R1 = QQ[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,A,B,C,D,E,F,G,H,I,J,K,L,M,MonomialSize => 8]
  ideal(I*K-K^2,-k*s+K,-I*L+J,o*J*K-J^2,B*H*L-H^2,-i*B+H,r*G-G^2,-l*F+G,-A*L+E,o*D*E-E^2,A*D-D^2,
      -v*F+D,-r*s+D,b*C*L-C^2,-b*i+C,k*z-z^2,-e*F+z,-t*L+x,i*j*x-x^2,m*w-w^2,-k*M+w,-s*y+v,-j^2+j*t,
      -y*F+r,-i*k+r,-m*L+q,i*q*w-q^2,-y*M+p,-e*i+l,-r*M+j,-p*F+j,h*i*n-h^2,-c*i+h,-d*L+g,f*g*o-g^2,
      d*f-f^2,-s*F+f,-B*L+b,a*u*L-a^2,-o*u+a)  
--------------------------------------------------------
--adjminors2-3-8
  -- 2 by 2 adjacent minors of generic 3 by 8 matrix
  -- #minprimes = 57.  stratA time: 20.6 sec [mike mMBP, 13 Mar 2013]
  -- I = adjacentMinorsIdeal(2,3,8,CoefficientRing=>ZZ/32003)
  R1 = ZZ/32003[vars(0..23)]
  ideal(-b*d+a*e,-e*g+d*h,-h*j+g*k,-k*m+j*n,-n*p+m*q,-q*s+p*t,-t*v+s*w,-c*e+b*f,-f*h+e*i,
      -i*k+h*l,-l*n+k*o,-o*q+n*r,-r*t+q*u,-u*w+t*x)
----------------------------------------------
--adjminors2-3-9
  -- I = adjacentMinorsIdeal(2,3,9,CoefficientRing=>ZZ/32003)
  -- out or reach so far?
  R1 = ZZ/32003[vars(0..26)]
  ideal(-b*d+a*e,-e*g+d*h,-h*j+g*k,-k*m+j*n,-n*p+m*q,-q*s+p*t,-t*v+s*w,-w*y+v*z,-c*e+b*f,
      -f*h+e*i,-i*k+h*l,-l*n+k*o,-o*q+n*r,-r*t+q*u,-u*w+t*x,-x*z+w*A)
----------------------------------------------
--adjminors3-5-5
  -- I = adjacentMinorsIdeal(3,5,5,CoefficientRing=>ZZ/32003)
  -- out or reach so far?
  R1 = ZZ/32003[vars(0..24)]
  ideal"-cgk+bhk+cfl-ahl-bfm+agm,-hlp+gmp+hkq-fmq-gkr+flr,
      -mqu+lru+mpv-krv-lpw+kqw,-dhl+cil+dgm-bim-cgn+bhn,
      -imq+hnq+ilr-gnr-hls+gms,-nrv+msv+nqw-lsw-mqx+lrx,
      -eim+djm+ehn-cjn-dho+cio,-jnr+ior+jms-hos-imt+hnt,
      -osw+ntw+orx-mtx-nry+msy"
----------------------------------------------
--rajchgot1-commutingscheme
  -- also want to compute the components of the intersection of components of I.
  s=3;
  R = ZZ/101[a_(1,1)..a_(s,s),b_(1,1)..b_(s,s)];
  A = transpose genericMatrix(R, a_(1,1),s,s);
  B = transpose genericMatrix(R, b_(1,1), s,s);
  I1 = ideal(A*B-B*A);
  I = I1 + ideal(det A)+ideal(det B)
----------------------------------------------
----------------------------------------------
----------------------------------------------
