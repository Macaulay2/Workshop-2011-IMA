restart
loadPackage "FactorizingGB"
R1 = QQ[a..M, MonomialSize => 8]
I1 = ideal(K,J,I,E,D,A,v,s,r-G,q-t,o,m-w,l-y,k-z,j-t,i-L,g,f,d,c-n,b-H,a,G*M-t,z*M-w,y*M-p, H*L-C,B*L-H,z*L-G,w*L-t,t*L-x,n*L-h,e*L-y,B*G-z*H,y*F-G,p*F-t,e*F-z,B*C-H^2,z*C-G*H,w* C-t*H,t*C-x*H,n*C-h*H,e*C-y*H,y*B-e*H,x*B-t*H,t*B-w*H,h*B-n*H,y*z-e*G,x*z-t*G,t*z-w*G, h*z-n*G,w*y-p*z,t*y-p*G,e*x-p*G,t^2-w*x,n*t-h*w,h*t-n*x,e*t-p*z,e*h-n*y,e*H*M-p*B,p*G* L-x*y,p*C*G-x*y*H,p*z*B-e*w*H,p*z^2-e*w*G,n*x*y-h*p*G,h^2*w-n^2*x)
simplifyIdeal I1

Rlex = QQ[a..M, MonomialSize => 8]
Ilex = sub(I1, vars Rlex)
time gens gb Ilex;
--result from minAssGTZ
--ideal(K,J,I,-B*L+H,-e*F*L+G,E,D,-H*L+C,A,-e*F+z,-e*L+y,-G*L*M+x,-z*M+w,v,-G*M+t,s,r-G,q-
--     t,-y*M+p,o,m-w,l-y,k-z,j-t,i-L,-n*L+h,g,f,d,c-n,b-H,a)

loadPackage "newGTZ"
time myPD(I1, Strategy=>{GeneralPosition});


ring R1=0,(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,A,B,C,D,E,F,G,H,I,J,K,L,M),dp;
ideal I1 = K,J,I,E,D,A,v,s,r-G,q-t,o,m-w,l-y,k-z,j-t,i-L,g,f,d,c-n,b-H,a,G*M-t,z*M-w,y*M-p, H*L-C,B*L-H,z*L-G,w*L-t,t*L-x,n*L-h,e*L-y,B*G-z*H,y*F-G,p*F-t,e*F-z,B*C-H^2,z*C-G*H,w* C-t*H,t*C-x*H,n*C-h*H,e*C-y*H,y*B-e*H,x*B-t*H,t*B-w*H,h*B-n*H,y*z-e*G,x*z-t*G,t*z-w*G, h*z-n*G,w*y-p*z,t*y-p*G,e*x-p*G,t^2-w*x,n*t-h*w,h*t-n*x,e*t-p*z,e*h-n*y,e*H*M-p*B,p*G* L-x*y,p*C*G-x*y*H,p*z*B-e*w*H,p*z^2-e*w*G,n*x*y-h*p*G,h^2*w-n^2*x;
I1;
list L1=facstd(I1);
LIB "primdec.lib";
list PQ = minAssGTZ(I1);
printlevel;
list PQ = minAss(I1. "SL");

