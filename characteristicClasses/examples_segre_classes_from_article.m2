ratnormalcurve = () -> (use (ZZ/32749)[x0,x1,x2,x3,x4,x5,x6]; 
M=matrix{{x0,x1,x2,x3,x4,x5},{x1,x2,x3,x4,x5,x6}};
I=minors(2,M);
return I)

ratnormalcurve2 = () -> (use (ZZ/32749)[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10]; 
M=matrix{{x0,x1,x2,x3,x4,x5,x6,x7,x8,x9},{x1,x2,x3,x4,x5,x6,x7,x8,x9,x10}};
I=minors(2,M);
return I)

grassmann = () -> (use ring Grassmannian(1,5,CoefficientRing => QQ); 
return Grassmannian(1,5,CoefficientRing => QQ))

surf = () -> (use (ZZ/32749)[x_0..x_(8)]; 
R=(ZZ/32749)[x_0..x_(8)];
r1={random(1,R),random(1,R),random(1,R)};
r2={random(1,R),random(1,R),random(1,R)};
r3={random(1,R),random(1,R),random(1,R)};
r4={random(1,R),random(1,R),random(1,R)};
M=matrix{r1,r2,r3,r4};
I=minors(2,M);
return I)

abeliansurf = () -> (use (ZZ/32749)[x0,x1,x2,x3,x4]; 
g1=x0*x1^3*x2+x1*x2^3*x3+x0^3*x1*x4+x2*x3^3*x4+x0*x3*x4^3;
g2=x0^2*x1^2*x3+x0*x2^2*x3^2+x1^2*x2^2*x4+x0^2*x2*x4^2+x1*x3^2*x4^2;
g3=x0^5+x1^5+x2^5+x3^5-5*x0*x1*x2*x3*x4+x4^5;
g4=x0^3*x1^2*x2+x0^2*x2^3*x3+x0*x1^3*x3^2+x1*x2^2*x3^3-x1^5*x4-x2^5*x4+4*x0*x1*x2*x3*x4^2-x4^6;
g5=x0*x1^2*x2*x3^2+x2^3*x3^3-x1^4*x2*x4-x0^2*x1^2*x4^2+x0*x2^2*x3*x4^2-x1*x3*x4^4;
g6=x0*x1^2*x3^3+x2^2*x3^4-x1^4*x3*x4+2*x0*x2*x3^2*x4^2+x1^2*x2*x4^3+x0^2*x4^4;
g7=x1^5*x2+x0^3*x1*x3^2+x2*x3^5+x0^2*x1^3*x4-x0*x1*x2^2*x3*x4+x0*x3^3*x4^2+x1^2*x3*x4^3;
g8=x1^4*x2^2+x0^3*x2*x3^2-x0*x1*x3^4+2*x0^2*x1^2*x2*x4+x1^3*x3^2*x4+x0^4*x4^2;
g9=x0^2*x1^4+2*x0*x1^2*x2^2*x3+x2^4*x3^2+x0*x2^3*x4^2+x1^3*x3*x4^2-x1*x2*x4^4;
g10=x0*x1^5+x1^3*x2^2*x3-x0^2*x1*x2*x3*x4+x1^2*x3^3*x4+x1*x2^3*x4^2+x2*x3^2*x4^3+x0*x4^5;
g11=x0*x1^4*x3+x1^2*x2^2*x3^2-x0^2*x2*x3^2*x4+x1*x3^4*x4-x0*x1^2*x2*x4^2-x0^3*x4^3;
g12=x0^3*x1^3+x0^2*x1*x2^2*x3-x1*x2^4*x4+x0*x1^2*x3*x4^2-x2^2*x3^2*x4^2-x0*x2*x4^4;
g13=x0^4*x1^2+x0^3*x2^2*x3-x0*x2^4*x4+2*x0^2*x1*x3*x4^2+x1*x2^2*x4^3+x3^2*x4^4;
g14=x0^2*x1^2*x2^2+x0*x2^4*x3+x0^4*x2*x4-x0^2*x1*x3^2*x4-x1*x2^2*x3*x4^2-x3^3*x4^3;
g15=x0*x1^2*x2^3+x2^5*x3+x0^3*x2^2*x4-x0*x1*x2*x3^2*x4+x1^3*x2*x4^2+x0^2*x1*x4^3+x3*x4^5;
g16=x1^3*x2^3-x0^4*x1*x3-x0*x2*x3^4+x0^2*x1*x2^2*x4+x1^2*x2*x3^2*x4-x0^2*x3^2*x4^2;
g17=x1^2*x2^4-x0^4*x2*x3+x0^2*x1*x3^3+x0^2*x2^3*x4+2*x1*x2^2*x3^2*x4+x3^4*x4^2;
g18=x1^6-x0^2*x2*x3^3+x1*x3^5-4*x0*x1^2*x2*x3*x4-x2^3*x3^2*x4-x0^3*x3*x4^2-x0*x2^2*x4^3+x1*x4^5;
I=ideal(g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18);
return I)

segreproduct = () -> (
     R = QQ[x_1..x_(12)];
     M = genericMatrix(R,3,4);
     return  minors(2,M))

