// Magma code related to "Fast Jacobian arithmetic for hyperelliptic curves of genus 3"
// by Andrew V. Sutherland, see http://arxiv.org/abs/1607.08602 for details.
// Copyright 2016, Andrew V. Sutherland, 2016.  Licensed under GPL version 3.
// Modified 2021 by Juanita Duque-Rosero, Sachi Hashimoto, and Pim Spelier for odd degree f

g:=2;

Compose := function(D1,D2,f)
    u1:=D1[1]; v1:=D1[2]; u2:=D2[1]; v2:=D2[2];
    w,c := XGCD([u1,u2,v1+v2]);
    u3 := (u1*u2) div w^2;
    v3 := ((c[1]*u1*v2+c[2]*u2*v1+c[3]*(v1*v2+f)) div w) mod u3;
    return <u3,v3>;
end function;

Reduce := function(D1,f,g)
    u1:=D1[1]; v1:=D1[2];
    u2 := (f-v1^2) div u1;  

    u2 := u2 / LeadingCoefficient(u2);
    v2 := (-v1) mod u2;
    if Degree(v1) eq g+1 and LeadingCoefficient(v1) eq 1 then
        delta := Degree(u1)-(g+1);
    elif Degree(v1) eq g+1 and LeadingCoefficient(v1) eq -1 then
        delta := g+1-Degree(u2);
    else
        delta := (Degree(u1)-Degree(u2)) div 2;
    end if;
    return <u2,v2>;
end function;

createMumford := function(pt1, pt2)
    L := Parent(pt1[1]);
    R<u>:=PolynomialRing(L);
    xcoord := (u - pt1[1]) * ( u - pt2[1]);
    ycoord := pt2[2] * ( u -pt1[1]) / (pt2[1] - pt1[1]) + pt1[2] * (u - pt2[1]) / (pt1[1] - pt2[1]);
    return xcoord, ycoord;
end function;
