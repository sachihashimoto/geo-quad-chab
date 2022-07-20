//The following intrinsic is the Magma source file for Jacobian point with a small bug fixed on line 33
//This code does not belong to us, it is only provided here to help Magma users fix the bug in the intrinsic


intrinsic JacobianPoint(J::JacHyp, D::DivCrvElt) -> JacHypPt
{The point on the Jacobian J (of a hyperelliptic curve C)
associated to the divisor D on C. If D does not have degree 0,
then a suitable multiple of the divisor at infinity is subtracted.
When the divisor at infinity on C has even degree, D is required to have even degree.}

// The intrinsic works for any divisor such that the corresponding point
// is definable in Magma, and otherwise an error results.
// Not implemented in characteristic 2.

   debug := false;
   C := Curve(D);
   F := BaseField(C);
   require J eq Jacobian(C): "The first argument should be the Jacobian
          of a curve C and the second argument should be a divisor on C";
   require Characteristic(BaseField(C)) ne 2:
      "Not implemented in characteristic 2.
       If this is needed, please email Magma.";
   P<X,Y,Z> := CoordinateRing(Ambient(C));
   g := Genus(C);
   f, h := HyperellipticPolynomials(C);

   // Reduce to the case where C has the form y^2 = f(x)
   if h ne 0 then
      Csim :=  HyperellipticCurve(f+h^2/4);
      CtoCsim := map< C -> Csim | [X, Y+Z^(g+1)*Evaluate(h,X/Z)/2, Z] >;
      D := Pullback( Inverse(CtoCsim), D);
      pt := Jacobian(Csim)!D;
      return elt< J | pt[1], pt[2]-h/2, pt[3] >;
   end if;

   PAI := PointsAtInfinity(C);
   if #PAI eq 2 then
      TwoPtsAtInf := true;
      _, s := IsSquare(LeadingCoefficient(f));
      Pinf1 := C![1,s,0];
      Pinf2 := C![1,-s,0];
      DivAtInfty := Divisor(C, ideal < P | Z >);
      assert PAI eq {@ Pinf1, Pinf2 @};
   elif #PAI eq 1 then
      DivAtInfty := Divisor(PAI[1]);
      PlaceAtInf := Support(DivAtInfty)[1];
      TwoPtsAtInf := false;
   else
      DivAtInfty := Divisor(C, ideal < P | Z >);
      PlaceAtInf := Support(DivAtInfty)[1];
      TwoPtsAtInf := false;
   end if;
   if Degree(DivAtInfty) eq 2 then
      require IsEven(Degree(D)):
         "D must have even degree when the divisor at infinity has degree 2";
   end if;

   // Get the zeros and poles of D, and separate off the infinite and Weierstrass parts too.
   // For the Weierstrass places, we may reduce the multiplicities mod 2.
   TupUniv := CartesianProduct(Places(C),Integers());
   DivWeierstrass := Divisor(C, ideal<P | Y, Z^Degree(f)*Evaluate(f, X/Z)>);
   InfW := Support(DivAtInfty) cat Support(DivWeierstrass);
   Dnum := Divisor(C, [ TupUniv | d : d in Decomposition(D)
                      |  d[1] notin InfW and  d[2] gt 0] );
   Dden := -Divisor(C, [ TupUniv | d : d in Decomposition(D)
                      |  d[1] notin InfW and  d[2] lt 0] );
   Dinf := Divisor(C, [ TupUniv | d : d in Decomposition(D)
                      |  d[1] in Support(DivAtInfty) ] );
   DW   := Divisor(C, [ TupUniv | <d[1], d[2] mod 2> : d in Decomposition(D)
                      |  d[1] in Support(DivWeierstrass) ] );
   assert Support(D - (Dnum-Dden+Dinf)) subset Support(DivWeierstrass);
   // Replace the pole divisor by its reflection (with positive multiplicity).
   // Doing this doesn't change the parity of deg D,
   // and it doesn't change the divisor class that is being represented.
   DdenReflected := Pullback( HyperellipticInvolution(C), Dden );
   Dnoninf := Dnum + DW + DdenReflected;   // Effective divisor such that
                                           // Dnoninf + Dinf gives what we want
   I := Ideal(Dnoninf);
   if debug then
      print "Dnum, Dden, Dinf, DW are\n ", Support(Dnum), Support(Dden), Support(Dinf), Support(DW);
   end if;

   // Keep track of the infinite contributions, only in the case TwoPtsAtInf.
   // (In other cases, divisors at infinity are trivial anyway).
   // The imbalance between Pinf1 and Pinf2 in D is recorded in v,
   // and this will be added at the end.
   if TwoPtsAtInf then
      v := Valuation(Dinf, Pinf1) - Valuation(Dinf, Pinf2);
      if debug then print "v is ",v; end if;
   end if;

   // Now we want an equation of the form c(x)*y = b(x).
   // We get this from a Groebner basis for I using lex order, with x smaller than y
   Pxy<y,x> := PolynomialRing(BaseRing(P),2, "lex");
   f := Evaluate(f, x);
   I := ideal< Pxy | [Evaluate(pol, [x,y,1]) : pol in Basis(I)] >;
   Ix := EliminationIdeal(I,{x});
   a := Basis(Ix)[1];
   // remove factors from the ideal corresponding to "vertical" divisors
   // (since they are trivial).
   for fa in Factorisation(a) do
      Ifa := ideal< Pxy | fa[1], y^2-f >;  // "vertical" divisor supported at the roots of fa
      while I subset Ifa do
         Inew := ColonIdeal(I, Ifa);  // should be able to take exact ideal quotients here
         assert Inew*Ifa+ideal<Pxy | y^2-f>  eq I;   // really working in Pxy/(y^2-f)
         I := Inew;
      end while;
   end for;
   if I eq Pxy then   // ideal is now trivial, so return the infinite contribution, if any.
      if TwoPtsAtInf then
         return (v div 2)*(Pinf1-Pinf2);
      else
         return J!0;
      end if;
   end if;
   Ix := EliminationIdeal(I,{x});
   a := Basis(Ix)[1];
   // Now get an equation of the form c(x)*y = b(x).
   // Remember that I has lex order, with x smaller than y
   GB := GroebnerBasis(I);
   assert #GB eq 2;
   assert a eq GroebnerBasis(I)[2];
   CyeqB := GroebnerBasis(I)[1];
   assert Degree(CyeqB, y) eq 1;
   b := -Evaluate(CyeqB, [0,x]);    // Beware: the variables are in the order y, x
   c := Evaluate(CyeqB + b, [1,x]);
   assert CyeqB eq c*y-b;
   assert GCD(a,c) eq 1;   // common factors should have been removed as "vertical" divisors

   // Reduce b(x)/c(x) mod a(x), so we obtain y-b(x) with deg b < deg a.
   Pu := PolynomialRing(BaseRing(P)); u := Pu.1;   // Univ poly ring, for div or quo.
   au, bu, cu, fu := Explode([ Evaluate(pol,[0,u]) : pol in [a,b,c,f] ]);
      // Recall a,b,c,f are polys in variables y, x, in that order.
   gcd, M, N := XGCD(au, cu);   // N should equal 1/c mod a
   assert gcd eq 1;
   bu := bu*N mod au;
   // Reduction: Replace a by (b^2-f)/a and reduce b mod a ... until deg a <= g+1.
   while Degree(au) gt Degree(fu)/2 do    // it goes down to g or g+1
      // Replace (a,y-b) by a linear equivalent divisor,
      // using the fact that the divisor given by y-b is trivial.
      // More precisely, the homogenisation z^k*y-b(x,z),
      // where k = deg(b(x)) - (g+1) when this is positive.
      // Contribution at infinity in z^k*y-b(x,z):
      //    * We only care if TwoPtsAtInf.
      //    * Only possible when k = 0 and deg(b(x)) = g+1.
      //    * In this case, the point (1:s:0) appears (for s = 1 or -1)
      //      iff s is the leading coeff of b(x),
      //      and the multiplicity is 2g+2 - deg( b(x)^2-f ).
      if TwoPtsAtInf and Degree(bu) eq g+1 then   // maybe a contribution at infinity
         multinf :=  2*g+2 - Degree(bu^2-fu);
         if multinf gt 0 then
            blc := LeadingCoefficient(bu);
            assert blc eq s or blc eq -s;    // s^2 = LeadingCoeff(fu)
            sInt := blc eq s select 1 else -1;   // looks silly, but needed if s is in GF(p).
            v +:= - sInt*multinf;   // add Pinf1 this many times to the running total
               // Recall v is the amount multiplicity(Pinf1) exceeds multiplicity(Pinf2).
               // The minus sign is because we need the reflection of the point.
            if debug then print "v is now ",v; end if;
         end if;
      end if;
      au := ExactQuotient(bu^2-fu,au);
      au := au/LeadingCoefficient(au);   // keep au monic (why not?)
      bu := - bu mod au;   // reflect the points, to get the inverse in Pic^0(C)
   end while;
   if debug then print "au is and bu are now",au, bu; end if;

   if IsOdd(Degree(au)) then  // this should only happen when there's
                              // at least one rational point at infinity,
      if TwoPtsAtInf then   // this should only have happenned if Pinf1
         assert IsOdd(v);   // appears an odd number of times in the running total.
                            // We will now absorb one Pinf1 into (a,y-b).
         v -:= 1;
         if debug then print "absorbing Pinf1, v is now ",v; end if;
         if Degree(au) lt g+1 then
            // simply put Pinf1 = (1:s:0) in the divisor.
            // Homogeneously, replace a(x,z) and b(x,z) by
            //     z*a(x,z) and b(x,z) + s*x^k*a(x,z),
            // (the second of these equals b(x) when a=0 and z=1,
            // and equals s when z=0, since a is monic).
            k := g+1 - Degree(au);
            bu := bu + s*u^k*au;
            d := Degree(au) + 1;
            abJ := elt< J | [au,bu], d >;
         else
            if debug then print "Awkward case, deg(au) = g+1"; end if;
            // deg(au) = g+1, and we find an equivalent divisor
            // of degree (g+1) containing Pinf1 = (1:s:0).
            // Since deg b < g+1 and a is monic of deg g+1,
            // the trivial divisor of degree 2g+2 cut by
            //     y + z^l*b(x,z) + s*a(x,z)
            // contains (1:-s:0) and the divisor (a,y+b),
            // i.e. the reflection of (1:s:0) + (a,y-b).
            // Therefore the remaining part of it, which has degree g,
            // will be linearly equivalent to (1:s:0) + (a,y-b).
            DD := Divisor(C, ideal<P | Y + Z^(g+1)*(Evaluate(bu,X/Z)+s*Evaluate(au,X/Z)) >);
            DD := DD - Divisor(Pinf2)
                     - Divisor(C, ideal< P |  Z^(g+1)*Evaluate(au,X/Z),
                                            Y+Z^(g+1)*Evaluate(bu,X/Z)> );
            if debug then print "    ... DD is ", Support(DD); end if;
            assert IsEffective(DD);
            abJ := JacobianPoint(J, DD);
                // Recursive call should work with no reduction required.
         end if;
      else
         require Degree(DivAtInfty) eq 1:
            "Error: degree became odd while finding the reduced representation";
         abJ := J![au,bu];
      end if;
   else
      abJ := J![au,bu];
   end if;
   if debug then print "ready to return ", au, bu, abJ; end if;

   if TwoPtsAtInf then    // Put in the infinite bit using addition on J.
      return abJ + (v div 2)*(Pinf1-Pinf2);
   else
      return abJ;
   end if;
end intrinsic;
