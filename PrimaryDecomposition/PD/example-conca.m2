restart
S = ZZ/1999[x_(1)..x_(36)]

I = ideal{ 
    -x_(13)*x_(22)*x_(31) + x_(12)*x_(23)*x_(31) + x_(13)*x_(21)*x_(32) - x_(11)*x_(23)*x_(32) - x_(12)*x_(21)*x_(33) + x_(11)*x_(22)*x_(33),
    -x_(14)*x_(22)*x_(31) + x_(12)*x_(24)*x_(31) + x_(14)*x_(21)*x_(32) - x_(11)*x_(24)*x_(32) - x_(12)*x_(21)*x_(34) + x_(11)*x_(22)*x_(34),
    -x_(15)*x_(23)*x_(31) + x_(13)*x_(25)*x_(31) + x_(15)*x_(21)*x_(33) - x_(11)*x_(25)*x_(33) - x_(13)*x_(21)*x_(35) + x_(11)*x_(23)*x_(35),
    -x_(16)*x_(23)*x_(32) + x_(13)*x_(26)*x_(32) + x_(16)*x_(22)*x_(33) - x_(12)*x_(26)*x_(33) - x_(13)*x_(22)*x_(36) + x_(12)*x_(23)*x_(36)
    }

H=primaryDecomposition I

J=radical(I)

HH=primaryDecomposition J

end
time decompose I
time primaryDecomposition I
time J = radical I

debug needsPackage "PD"
I = ideal I_*
time minprimes I

I == intersect H -- true
time birationalSplit I

C = oo
C_2
time C/(c0 -> saturate((ideal (c0#1/last)) + c0#0, product c0#2))
selectMinimalIdeals oo
time C/(c0 -> trim saturate((ideal c0#1) + c0#0))
C_1
time C/(c0 -> product c0#2)

minprimesViaBirationalSplit = method()
minprimesViaBirationalSplit Ideal := (I) -> (
    C := birationalSplit I;
    L := for c0 in C list (
            f := product c0#2; -- the flattener to consider
            B := ideal(c0#1/last); -- the "fractions"
            -- now we need to split co#0 up first, if possible:
            C1 := if co#0 == 0 then {c0#0}
            C1 := minprimes c0#0
        );
    L
    )
