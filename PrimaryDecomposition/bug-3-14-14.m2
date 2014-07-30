restart
debug loadPackage "PD"
R = ZZ/32003[a,b,c,d,f,g,h,k,l,s,t,u,v,w,x,y,z, MonomialSize=>8]
I = ideal(
    -a*b-a*d+2*a*h,
    a*d-b*d-c*f-2*a*h+2*b*h+2*c*k,
    a*b-a*d-2*b*h+2*d*h-2*c*k+2*f*k+2*g*l,
    a*c-2*c*s-a*t+2*b*t,
    a*c-c*s-2*a*t+b*t,
    -d-3*s+4*u,
    -f-3*t+4*v,
    -g+4*w,
    -a+2*x,
    -b^2-c^2+2*b*x+2*c*y,
    -d^2-f^2-g^2+2*d*x+2*f*y+2*g*z)

time C = minprimes I;
assert(#C == 6)
assert(intersect C == I)

C1 = doSplitIdeal(I, Verbosity=>2)
getPrimesInPDState first C1
netList oo

restart
needsPackage "MGBInterface"
R = ZZ/32003[a, b, c, d, f, g, h, k, l, s, t, u, v, w, x, y, z]
J = ideal(4*h^2+2*c*k+12*h*s+9*s^2+3*c*t-16*h*u-24*s*u+16*u^2-4*c*v-4*h*x-6*s*x+8*u*x,
    -4*h^2-2*c*k-12*h*s-6*k*t+16*h*u+8*k*v+8*l*w+4*h*x+12*s*x-16*u*x,
    -2*c*s+4*h*t+6*s*t-8*t*u+2*c*x-2*t*x,
    -c*s+2*h*t+3*s*t-4*t*u+2*c*x-4*t*x,
    -c^2-4*h^2-12*h*s-9*s^2+16*h*u+24*s*u-16*u^2+4*h*x+6*s*x-8*u*x+2*c*y,
    -9*s^2-9*t^2+24*s*u-16*u^2+24*t*v-16*v^2-16*w^2-6*s*x+8*u*x-6*t*y+8*v*y+8*w*z)
MGB J

J1 = saturate(J,w)
J2 = mySat0(J,w)
J1 == J2



R = ZZ/101[a,b,c,d,e,f]
m = matrix{{a,b},{c,d},{e,f}}
MGB m

--- crash in mgb -------------
R = ZZ/101[a,b,c,d,e,f]
m = matrix{{a^2-b*c,1,0}, {a*b,0,1}}
MGB m
-----------------------------
R = ZZ/101[a,b,c,d,e,f]
m = transpose matrix{reverse{a^2-b*c,1,0}, reverse{a*b,0,1}}
MGB m

