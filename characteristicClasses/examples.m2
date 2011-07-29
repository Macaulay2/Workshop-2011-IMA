----------------------------------------------------
-- Segre varieties P^(m-1) x P^(n-1) -> P^(mn-1)
----------------------------------------------------
-- (Segre classes of Segre varieties, yeah)

-- Unfortunately, our algorithm is slower than Aluffi's, fails for (3,4)

segreVar = (m,n) -> (
     R = QQ[x_1..x_(m*n)];
     M = genericMatrix(R,m,n);
     return  minors(2,M))



----------------------------------------------------
-- Grassmannians
----------------------------------------------------

-- use Grassmannian(n,k,CoefficientRing=>QQ)

-- both ours and Aluffi's are slow for G(2,5)
     
     



---------------------------------------------------
-- curves in P2
---------------------------------------------------
quadricP2 = () -> (use QQ[x,y,z]; return ideal(x^2+y^2+z^2))



---------------------------------------------------
-- curves in P3
---------------------------------------------------

-- three lines
threelines = () -> (use QQ[x,y,z,w]; return ideal(x*y,x*z,y*z))
-- three coplanar lines
threelinescoplanar =  () -> (use QQ[x,y,z,w]; return ideal(z,x*y*(x+y))) -- out of memory


-- twisted cubic
twistedcubic = () -> (use QQ[x,y,z,w]; return ideal(x*z-y^2,y*w-z^2, x*w-y*z ))

-- from Aluffi [reference!] example 4.1
aluffiex41 = () -> (use QQ[x,y,z,w]; return ideal(x^2*z,y^2*z,z^3,z*w^2,x*y*(x+y)) )


-- Viviani's curve
viviani = () -> (use QQ[x,y,z,w]; return ideal(x^2 + y^2 + z^2 - 4*w^2, (x-w)^2+y^2 - w^2) )

-- tennis ball curve
tennisball = () -> (use QQ[x,y,z,w]; return ideal(x^2 + y^2 + z^2 - w^2, z*w - x^2 + y^2) )

-- horopter curve
horopter = () -> (use QQ[x,y,z,w]; return ideal(x^2 + z^2 - 2*w*x, w*z - x*y) )

-- archytas curve
archytas = () -> (use QQ[x,y,z,w]; return  ideal( (x^2 + y^2 + z^2)^2 - w^2 * (x^2 + y^2), x^2 + y^2 - w*x) )


-- curves with embedded point
embcurve1 = () -> (use QQ[x,y,z,w]; return ideal(z*w^2, x^2*z, x*y^2) )
embcurve2 = () -> (use QQ[x,y,z,w]; return ideal(z^2, x*z, y*z, x*y) )
embsurface1 = () -> (use QQ[x,y,z,w,ww]; return ideal(z^2, x*z, y*z, x*y) )
embsurface2 = () -> (use QQ[x,y,z,w]; return intersect( ideal(x^2,y^2,z^2), ideal(z) ) ) 
embsurface3 = () -> (use QQ[x,y,z,w]; return intersect( ideal(x^2,y^2), ideal(x) ))



-- elliptic curve in P3
ellipticP3 = () -> (use QQ[x,y,z,w]; return ideal(x^2 - y^2 + w^2, z^2 - y^2 - w^2) )


-- other curves in P3
curve1P3 = () -> (use QQ[x,y,z,w]; return ideal(x^3 + y^3 - z^3 - w^3, x^5 - y*z^4))
curve2P3 = () -> (use QQ[x,y,z,w]; return ideal(x^3 + y^3 - z^3 - w^3, z*w^3) )
curve3P3 = () -> (use QQ[x,y,z,w]; return ideal(x*w - z^2, y^2*w - z^3)) 


-- from Aluffi's Example 4.1, with misprint
misprint = () -> (use QQ[x,y,z,w]; return ideal(x^2*z,y^2*z,z^3,z^2*w,x*y*(x+y)) )


---------------------------------------------------
-- surfaces in P3
---------------------------------------------------


threeplanes = () -> (use QQ[x,y,z,w]; return ideal(x*y*(x+y)))

--cubics
fermatcubic = () -> (use QQ[x,y,z,w]; return ideal(x^3+y^3+z^3+w^3) )
clebschsurface = () -> (use QQ[x,y,z,w]; return ideal(x^3 + y^3 + z^3 + w^3 - (x+y+z+w)^3))
cayleynodalcurve = () -> (use QQ[x,y,z,w]; return ideal(x*y*z + x*y*w + x*z*w + y*z*w) )


-- quadrics
quadric1 = () -> (use QQ[x,y,z,w]; return ideal(x^2 + y^2 + z^2 + w^2))
quadric2 = () -> (use QQ[x,y,z,w]; return ideal(x^2 + y^2 + z^2 - w^2))
quadric3 = () -> (use QQ[x,y,z,w]; return ideal(x^2 + y^2 - z^2 - w^2))
conecylinder = () -> (use QQ[x,y,z,w]; return ideal(x^2 - y^2 - z^2))


-- Whitney umbrella
whitney = () -> (use QQ[x,y,z,w]; return ideal(x^2*w - y^2 *z))

-- Cayley cubic
cayley = () -> (use QQ[x,y,z,w]; return ideal(4*w*(x^2 + y^2 + z^2) + 16*x*y*z - w^3))


---------------------------------------------------
-- surfaces in P5
---------------------------------------------------

-- Veronese surface
veroneseP5 = () -> (use QQ[x0,x1,x2,x3,x4,x5]; M := matrix{{x0,x3,x4},{x3,x1,x5},{x4,x5,x2}}; return  minors(2,M) )

