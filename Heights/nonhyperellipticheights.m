//AttachSpec("periodmatrices/RieSrf/RieSrf.spec");
AddAttribute(Crv, "RiemannSurface");
Attach("Heights/RS_attr.m");

function MyDivGen(D)
	X := New(MyDivCrvElt);
	X`Div := D;
	X`I := AssociativeArray();
	X`IZ3 := AssociativeArray();
	X`IZ12 := AssociativeArray();
	X`Rp := AssociativeArray();
	return X;
end function;

//import "/usr/local/magma/package/Geometry/Crv/RegModel/main.m" : ancestors, lift_ideal;
//import "/usr/local/magma/package/Geometry/Crv/RegModel/interface.m" : regular_fibres_indices;

import "/Applications/magma/package/Geometry/Crv/RegModel/main.m" : ancestors, lift_ideal;
import "/Applications/magma/package/Geometry/Crv/RegModel/interface.m" : regular_fibres_indices;
import "periodmatrices/RieSrf/abeljacobi.m" : StrongApproximationSimple;
//import "/usr/local/magma/package/Geometry/Crv/RegModel/main.m" : ancestors, lift_ideal;
//import "periodmatrices/RieSrf/abeljacobi.m" : StrongApproximationSimple;
//import "/usr/local/magma/package/Geometry/Crv/RegModel/interface.m" : regular_fibres_indices;
load "Heights/lml.m";
load "Heights/corr_term.m";

function B2I(b)
	if b then
		return 1;
	else
		return 0;
	end if;
end function;

function ImMatrix(M)
	return Matrix( [ [ Im(M[i][j]) : j in [1..NumberOfColumns(M)]] : i in [1..NumberOfRows(M)]]);
end function;

function MyLocalisation(R,I,f) // R : polynomial ring, I : ideal of R, f : element of R
    Ru := PolynomialRing(BaseRing(R), Rank(R)+1);
    phi := hom<R -> Ru | [Ru.i : i in [1..Rank(R)]]>;
    Iu := ideal<Ru|[phi(r) : r in Generators(I)] cat [Ru.Rank(Ru)*phi(f)-1]>;
    return Ru, Iu, phi;
end function;

function MyLength(I)
	vprint User3: "MyLength:", I, GroebnerBasis(I);
	ret := local_module_length(GroebnerBasis(I));
	vprint User3: "MyLength finished";
    return ret;
end function;

// Computes a superset of the bad primes of C.
function MyBadPrimes(C)
	f := Equation(C);
	RZ<xZ,yZ,zZ> := PolynomialRing(Integers(),3);
	den := LCM([Denominator(c) : c in Coefficients(f)]);
	f := RZ!(den*f);
	fx := Derivative(f, xZ);
	fy := Derivative(f, yZ);
	fz := Derivative(f, zZ);
	
	NaiveDiscriminant := 1;
	for P in [ [xZ, yZ, 1], [xZ, 1, zZ], [1, yZ, zZ] ] do
		I := Ideal([ Evaluate(g, P) : g in [f, fx, fy, fz]]);
		G := GroebnerBasis(I);
		PotentialDiscriminant := G[#G];
		assert(PotentialDiscriminant in Integers());
		NaiveDiscriminant := LCM(NaiveDiscriminant, PotentialDiscriminant);
	end for;
	
	return Set(PrimeFactors(Integers()!NaiveDiscriminant));
end function;

// Lift ideal over Q to Z
function LiftIdealToZ(I,RZ)
	G := Generators(I);
	for i in [1..#G] do
		a := LCM([Denominator(c) : c in Coefficients(G[i])]);
		G[i] *:= a;
	end for;
	return ideal<RZ | G>;
end function;


// Given two horizontal divisors, find where they meet
function MeetingLocus(D,E)
	C := Curve(D);
	
	// Assume D, E effective, and of disjoint support
	assert(IsEffective(D));
	assert(IsEffective(E));
	assert(GCD(D,E) eq DivisorGroup(C)!0);
	
	// Groebner basis calculation
	f := Equation(C);
	RZ<xZ,yZ,zZ> := PolynomialRing(Integers(),3);
	den := LCM([Denominator(c) : c in Coefficients(f)]);
	f := RZ!(den*f);
	I := LiftIdealToZ(Ideal(D), RZ);
	J := LiftIdealToZ(Ideal(E), RZ);
	
	NaiveLocus := 1;
	for P in [ [xZ, yZ, 1], [xZ, 1, zZ], [1, yZ, zZ] ] do
		K := Ideal([ Evaluate(g, P) : g in [f] cat Generators(I) cat Generators(J)]);
		G := GroebnerBasis(K);
		vprint User3: "MeetingLocus: GroebnerBasis computed";
		PotentialLocus := G[#G];
		assert(PotentialLocus in Integers());
		NaiveLocus := LCM(NaiveLocus, PotentialLocus);
		vprint User3: "MeetingLocus: NaiveLocus updated:", NaiveLocus;
	end for;
	
	return Set(PrimeFactors(Integers()!NaiveLocus));
end function;

function MeetingLoci(D,E)
	return MeetingLocus(Numerator(D), Numerator(E)), MeetingLocus(Numerator(D), Denominator(E)), MeetingLocus(Denominator(D), Numerator(E)), MeetingLocus(Denominator(D), Denominator(E));
end function;



// Function computes the length of R/I on Z(J).
function LengthOn(R,I,J)// R : (free) polynomial ring, I,J : ideals of R
    gens := Set(Generators(J));
    skippableSubsets := Set([]);
    ans := 0;
    vprint User1: "r = ", #gens;
    for k in [0..#gens] do
		for S in Subsets(gens, k) do
		    //if IsEmpty(S) then
		     //  continue;
		    //end if;
		    canSkip := false;
		    for T in skippableSubsets do
		    	if T subset S then
		    		canSkip := true;
		    		break;
		    	end if;
		    end for;
		    if canSkip then
		    	continue;
		    end if;
		    
		    f := &* S;
		    Ru,Iu,phi := MyLocalisation(R,I,f);
	//        MyLength(Iu);
			toadd := (-1)^(#S)* MyLength(Iu);
		    ans := ans + toadd;
		    if (toadd eq 0) then
		    	skippableSubsets := skippableSubsets join {S};
		    end if;
		end for;
	end for;
    return ans;
end function;
        

// Random point on curve
function MyRandomPlace(C : maxint := 1000)
	r := Random(maxint);
	_<xC,yC> := FunctionField(C);
	return Decomposition(Numerator(Divisor(xC + r)))[1][1];
end function;
        
        

function map_between_patches(model, patch1, patch2)
  if Type(patch1) eq Tup then
    patch1 := model`patches[patch1];
    patch2 := model`patches[patch2];
  end if;

  // bottom patch = common ancestor of patch1 and patch2
  ancestors1 := ancestors(model, patch1);
  ancestors2 := ancestors(model, patch2);
  assert exists(bottom){idx: idx in ancestors1 | idx in ancestors2}; 

  //assert (bottom eq patch2); (TODO) add suitable assertion

  assert patch1`index[1] gt 0 and patch2`index[1] gt 0; // silly case, not wanted

  // get map from patch1 down to bottom patch 
  patch := patch1;
  map_down := patch`map;
  while patch`parent[1] gt bottom[1] do
    patch := model`patches[patch`parent];
    map_down := [Evaluate(f, map_down) : f in patch`map];
  end while;
  assert patch`parent eq bottom;

  // get map from bottom patch up to patch2, working backwards
  patch := patch2;
  R := Parent(patch`eqns[1]);
  map_up := [R.1, R.2, R.3];

  patch1_to_patch2 := [Evaluate(f, map_down) : f in map_up];
  return patch1_to_patch2;
end function;

// Drag ideal across map, from patch idx1 to patch idx2

function my_drag_ideal(model, I, idx1, idx2)
  Pol := Universe(model`patches[idx2]`eqns);
  idx2_to_idx1 := map_between_patches(model, idx2, idx1);
  return [Evaluate(g, idx2_to_idx1) : g in Generators(I)];
end function;

// Move ideals
function getIdealInDesiredShape(Cp, D1, p : pAdicPrecision := 10)
	vprint User3: "getIdealInDesiredShape started";

	if (p in Keys(D1`I)) then
		vprint User3: "getIdealInDesiredShape finished";
		return D1`I[p], D1`IZ3[p], D1`IZ12[p], D1`Rp[p];
	end if;
	D := D1`Div;

	CpKeys := Keys(Cp`patches);
	I := Ideal(D);
	
	gI := Generators(I);
	for i in [1..#gI] do
		a := LCM([Denominator(c) : c in Coefficients(gI[i])]);
		gI[i] *:= a;
	end for;
	I := Ideal(gI);
	
	origPatches := [];
	origIdealsI := [];
	for j in [1,2,3] do
		if (<1, j> in CpKeys) then
			Append(~origPatches, <1,j>);
		end if;
	end for;
	
	for i in origPatches do
		pat := Cp`patches[i];
		Append(~origIdealsI, Ideal([Evaluate(g, pat`map) : g in Generators(I)]));
	end for;

	IdealsI := [];
	keysList := [];

	for i in CpKeys do
		pat := Cp`patches[i];
		Ipat := Ideal(pat`eqns);
		Append(~keysList, i);
		for j in [1..#origPatches] do
			R := Parent(Generators(origIdealsI[j])[1]);
			if origPatches[j] eq i then
				Append(~IdealsI, Saturation(origIdealsI[j] + Ipat, R!p));
				break;
			end if;
			if origPatches[j] in ancestors(Cp, pat) then
				I1 := Saturation( Ideal(my_drag_ideal(Cp, origIdealsI[j], origPatches[j], i)) + Ipat, R!p );
				Append(~IdealsI, I1);
				break;
			end if;
		end for;
	end for;
	
	fI := AssociativeArray();
	fIZ3 := AssociativeArray();
	fIZ12 := AssociativeArray();
	fRp := AssociativeArray();
	
	for k in [1..#keysList] do
		i := keysList[k];
		pat := Cp`patches[i];
		I := IdealsI[k];
		R := Parent(pat`eqns[1]);
		Ipat := Ideal(pat`eqns);
		UnitIdeal := ideal<R | 1>;
		D3 := [lift_ideal(Ik, R, Cp`res, Cp`pi) : Ik in pat`domain[3]] cat [UnitIdeal];
		D12 := [lift_ideal(Ik, R, Cp`res, Cp`pi) : Ik in pat`domain[1] cat pat`domain[2]] cat [UnitIdeal];
		IZ3 := &*D3;
		IZ12 := IZ3 + &*D12;
		
			//(TODO) store this ring somewhere in the RegularModel data structure
		Rp := ChangeRing(R, pAdicQuotientRing(Cp`pi, pAdicPrecision));
		
		
		phi1 := hom<Integers()->pAdicQuotientRing(Cp`pi, pAdicPrecision) | >;
		phi2 := hom<R->Rp | phi1, [Rp.i : i in [1..Rank(Rp)]] >;
		I := Ideal([phi2(i) : i in Generators(I)]);
		Ipat := Ideal([phi2(i) : i in Generators(Ipat)]);
		IZ3 := Ideal([phi2(i) : i in Generators(IZ3)]);
		IZ12 := Ideal([phi2(i) : i in Generators(IZ12)]);
		
		
		fRp[i] := Rp;
		fI[i] := I + Ipat;
		t := GroebnerBasis(fI[i]);
		fIZ3[i] := IZ3;
		t := GroebnerBasis(fIZ3[i]);
		fIZ12[i] := IZ12;
		t := GroebnerBasis(fIZ12[i]);
		
	end for;
			
	D1`I[p] := fI;
	D1`IZ3[p] := fIZ3;
	D1`IZ12[p] := fIZ12;
	D1`Rp[p] := fRp;

	vprint User3: "getIdealInDesiredShape finished";
	
	return fI, fIZ3, fIZ12, fRp;		
	
end function;

// Horizontal intersection pairing
function pAdicIntersectionPairing(C, p, D, E : pAdicPrecision := 20)
	
	// Assume divisors are effective and coprime
	assert(IsEffective(D`Div));
	assert(IsEffective(E`Div));
	assert(GCD(D`Div,E`Div) eq DivisorGroup(C)!0);
		
	Cp := RegularModel(C, p);	
	ans := 0;
	I, IZ3, IZ12, RpI := getIdealInDesiredShape(Cp, D, p : pAdicPrecision := pAdicPrecision);
	J, IZ3, IZ12, Rp := getIdealInDesiredShape(Cp, E, p : pAdicPrecision := pAdicPrecision);
	for k in Keys(Cp`patches) do	// Compute some intersection pairings
		phi := hom<RpI[k]->Rp[k] | IdentityHomomorphism(BaseRing(Rp[k])), [Rp[k].i : i in [1..Rank(Rp[k])]] >;
		I2 := ideal< Rp[k] | [phi(g) : g in Generators(I[k])] >;
		ans +:= LengthOn(Rp[k], I2+J[k], IZ3[k]) - LengthOn(Rp[k], I2+J[k], IZ12[k]);	
	end for;	
	return ans;

end function;


function pAdicVerticalIntersection(C, p, D, Y : pAdicPrecision := 20)

		// Assume divisor D is effective
	assert(IsEffective(D`Div));
		
	Cp := RegularModel(C, p);
	CpKeys := Keys(Y`explicit);
	I, IZ3, IZ12, RpI := getIdealInDesiredShape(Cp, D, p : pAdicPrecision := pAdicPrecision);

		
	// Get ideals for D and Y
	IY := AssociativeArray();
	phiY := AssociativeArray();
	for i in CpKeys do
		vprint User3: "Get ideals:", i;	
		pat := Cp`patches[i];	
		R := Parent(pat`eqns[1]);
		I1 := Y`explicit[i]`ideal;
		TempIdeal :=  lift_ideal(I1, R, Cp`res, Cp`pi);
		Rp := ChangeRing(R, pAdicQuotientRing(Cp`pi, pAdicPrecision));
		phi1 := hom<Integers()->pAdicQuotientRing(Cp`pi, pAdicPrecision) | >;
		phi2 := hom<R->Rp | phi1, [Rp.j : j in [1..Rank(Rp)]] >;
		IY[i] := Ideal([phi2(g) : g in Generators(TempIdeal)]);
		phiY[i] := hom<Rp->RpI[i] | IdentityHomomorphism(BaseRing(Rp)), [RpI[i].j : j in [1..Rank(RpI[i])]]>; 
	end for;
	
	
	ans := 0;
	for k in CpKeys do
	
		IY2 := ideal<RpI[k] | [phiY[k](g) : g in Generators(IY[k])] >;
	
		// Compute some intersection pairings
		toadd := LengthOn(RpI[k], I[k]+IY2, IZ3[k]) - LengthOn(RpI[k], I[k]+IY2, IZ12[k]);
		ans +:= toadd;
		
	end for;	
	return ans;	

end function;

// Computes non-archimedean contribution to the Neron symbol.
// Note: this is negative of the canonical height pairing
function NonArchimedeanPairing(D, E : Precision := 30)
	C := Curve(D);
	assert(GCD(Numerator(D)+Denominator(D), Numerator(E)+Denominator(E)) eq DivisorGroup(C)!0);
	
	Mnn, Mnd, Mdn, Mdd := MeetingLoci(D,E);
	vprint User3: "Meeting loci computed";
	RR := RealField(Precision);
	ans := RR!0;
	
	nD := MyDivGen(Numerator(D));
	dD := MyDivGen(Denominator(D));
	nE := MyDivGen(Numerator(E));
	dE := MyDivGen(Denominator(E));
	
	vprint User3: "Generated divisors";
	for p in Mnn do
		ans +:= pAdicIntersectionPairing(C, p, nD, nE) * Log(RR!p);
	end for;
	for p in Mnd do
		ans -:= pAdicIntersectionPairing(C, p, nD, dE) * Log(RR!p);
	end for;
	for p in Mdn do
		ans -:= pAdicIntersectionPairing(C, p, dD, nE) * Log(RR!p);
	end for;
	for p in Mdd do
		ans +:= pAdicIntersectionPairing(C, p, dD, dE) * Log(RR!p);
	end for;

	vprint User3: "Computed pAdicIntersectionPairings";	

	for p in MyBadPrimes(C) do
		Cp := RegularModel(C,p);
		if (#Cp`abstract_fibres eq 1) then
			continue;
		end if;
		wD := [];
		wE := [];
		for Y in [Cp`abstract_fibres[i] : i in regular_fibres_indices(Cp)] do
			Append(~wD, pAdicVerticalIntersection(C, p, nD, Y) - pAdicVerticalIntersection(C, p, dD, Y) );
			Append(~wE, pAdicVerticalIntersection(C, p, nE, Y) - pAdicVerticalIntersection(C, p, dE, Y) );
		end for;
		vprint User3: "Computed pAdicVerticalIntersections";		

		ans -:= correction_divisor(wD, wE, IntersectionMatrix(Cp), Multiplicities(Cp)) * Log(RR!p); // Sign issue
	end for;
	

	return ans;
end function;


procedure RaiseAssoc(~A, i, x)
	if not(i in Keys(A)) then
		A[i] := x;
	else
		A[i] +:= x;
	end if;
end procedure;

function NonArchimedeanIntersectionNumbers(D, E)
	C := Curve(D);
	assert(GCD(Numerator(D)+Denominator(D), Numerator(E)+Denominator(E)) eq DivisorGroup(C)!0);
	
	Mnn, Mnd, Mdn, Mdd := MeetingLoci(D,E);
	vprint User3: "Meeting loci computed";
	intersectionMap := AssociativeArray();
	
	nD := MyDivGen(Numerator(D));
	dD := MyDivGen(Denominator(D));
	nE := MyDivGen(Numerator(E));
	dE := MyDivGen(Denominator(E));
	
	vprint User3: "Generated divisors";
	for p in Mnn do
		RaiseAssoc(~intersectionMap, p, pAdicIntersectionPairing(C, p, nD, nE));
	end for;
	for p in Mnd do
		RaiseAssoc(~intersectionMap, p, -pAdicIntersectionPairing(C, p, nD, dE));
	end for;
	for p in Mdn do
		RaiseAssoc(~intersectionMap, p,  -pAdicIntersectionPairing(C, p, dD, nE));
	end for;
	for p in Mdd do
		RaiseAssoc(~intersectionMap, p, pAdicIntersectionPairing(C, p, dD, dE));
	end for;

	vprint User3: "Computed pAdicIntersectionPairings";	

	for p in MyBadPrimes(C) do
		Cp := RegularModel(C,p);
		if (#Cp`abstract_fibres eq 1) then
			continue;
		end if;
		wD := [];
		wE := [];
		for Y in [Cp`abstract_fibres[i] : i in regular_fibres_indices(Cp)] do
			Append(~wD, pAdicVerticalIntersection(C, p, nD, Y) - pAdicVerticalIntersection(C, p, dD, Y) );
			Append(~wE, pAdicVerticalIntersection(C, p, nE, Y) - pAdicVerticalIntersection(C, p, dE, Y) );
		end for;
		vprint User3: "Computed pAdicVerticalIntersections";		

		RaiseAssoc(~intersectionMap, p, correction_divisor(wD, wE, IntersectionMatrix(Cp), Multiplicities(Cp))); // Sign issue
	end for;
	
	ans := [];

	for p in Sort(SetToSequence(Keys(intersectionMap))) do
		if intersectionMap[p] ne 0 then
			Append(~ans, <p, intersectionMap[p]>);
		end if;
	end for;

	return ans;
end function;



// Decompose effective curve divisor into RS divisors
function AJ_Decompose(RS, D)
	nD := [];
        gradings := Gradings(Ambient(Curve(D))); 
        assert IsOne(gradings[1,3]);
	assert(IsEffective(D));
	for P in Decomposition(D) do
		Q := Eltseq(RepresentativePoint(P[1]));
		assert(Q[3] ne 0);
		Q := [Q[i]/Q[3]^gradings[1,i] : i in [1..3]];
		for i in [1..#Conjugates(Q[1])] do
			for j in [1..P[2]] do
				Append(~nD, AbelJacobi(RS! [Conjugates(Q[1])[i], Conjugates(Q[2])[i] ]  : Reduction := 2));
			end for;
		end for;
	end for;
	return nD;
end function;

// Complex analytic intersection stuff
function AJ_Intersection(RS, g, AJ_E1, AJ_E2, AJ_P1, AJ_Q1, corr : Precision := 30)
	B := SmallPeriodMatrix(RS);
	ab := Transpose(Matrix([[ 0.0 : i in [1..2*g]]]));

	AJ_E1 := g*AJ_E1;	// (TODO) check for special divisor
	AJ_E2 := g*AJ_E2;	// I got a wrong answer in example 5 because of this.

	FirstTerm := Theta(ab, (AJ_P1) - (AJ_E1 + corr), B);
	SecondTerm := Theta(ab, (AJ_Q1) - (AJ_E2 + corr), B);
	ThirdTerm  := Theta(ab, (AJ_P1) - (AJ_E2 + corr), B);
	FourthTerm := Theta(ab, (AJ_Q1) - (AJ_E1 + corr), B);
	BigFirstTerm := -Log(Abs(FirstTerm*SecondTerm/(ThirdTerm*FourthTerm)));

	BigSecondTerm := ( -2*Pi(RealField(Precision)) * ImMatrix(Transpose(AJ_E1 - AJ_E2)) * ImMatrix(B)^(-1) * ImMatrix((AJ_P1 - AJ_Q1)) )[1][1];
	return (BigFirstTerm + BigSecondTerm) / g;
end function;


// Computes archimedean contribution to the Neron symbol.
// Note: this is negative of the canonical height pairing
function ArchimedeanPairing(D, E, K : Precision := 30, RS := -1)

	C := Curve(D);
	g := Genus(C);
	_<X,Y> := PolynomialRing(Rationals(), 2);
	f := Evaluate(Equation(C), [X, Y, 1]);
	if not(Type(RS) eq RieSrf) then
		assert(false);
		//assert(RS`DefiningPolynomial eq f);	
	end if;
	B := SmallPeriodMatrix(RS);

	AJ_K := AbelJacobi(RS`BasePoint : Reduction := 2);
	for P in Decomposition(K) do
		Q := Eltseq(RepresentativePoint(P[1]));
		assert(Q[3] ne 0);
		Q := [Q[i]/Q[3] : i in [1..3]];
		for i in [1..#Conjugates(Q[1])] do
			vprint User5: "Adding ", [Conjugates(Q[1])[i], Conjugates(Q[2])[i] ];
			AJ_K := AJ_K + P[2]*AbelJacobi(RS! [Conjugates(Q[1])[i], Conjugates(Q[2])[i] ] : Reduction := 2 );
		end for;
	end for;
	
	// Decompose numerator/denominator D/E
	nD := AJ_Decompose(RS, Numerator(D));
	dD := AJ_Decompose(RS, Denominator(D));
	nE := AJ_Decompose(RS, Numerator(E));
	dE := AJ_Decompose(RS, Denominator(E));
	assert(#nD eq #dD);
	assert(#nE eq #dE);
	
	if (#nE eq 0) then
		return RealField(Precision)!0;
	end if;

        AJ_Ps := [];
        for j := 1 to g-1 do
          Append(~AJ_Ps, AJ_Decompose(RS, Numerator(Divisor(MyRandomPlace(Curve(D)))))[1]);
        end for;
        vprint User5: "AJ_Ps =", AJ_Ps;
        for j :=  1 to g-2 do
          for k := j+1 to g-1 do
            assert(AJ_Ps[k] ne AJ_Ps[j]);	// (TODO) Should be compared using inequality.
          end for;
        end for;
	
	
        /*
	AJ_P1 := AJ_Decompose(RS, Numerator(Divisor(MyRandomPlace(Curve(D)))))[1];
	AJ_Q1 := AJ_Decompose(RS, Numerator(Divisor(MyRandomPlace(Curve(D)))))[2];
	vprint User5: "AJ_P1 =", AJ_P1;
	vprint User5: "AJ_Q1 =", AJ_Q1;
	assert(AJ_P1 ne AJ_Q1);	// (TODO) Should be compared using inequality.
        */
	
	// Computation of correction term
	ab := Transpose(Matrix([[ 0.0 : i in [1..2*g]]]));
	AJ_c := [ [Parent(AJ_K[1][1])!B2I(i in a)/2 : i in [1..2*g] ] : a in Subsets({1..2*g})  ];
	AJ_cb := [ Transpose( Matrix([[Parent(B[1][1])!i[n] : n in [1..g]]]) + Matrix([[Parent(B[1][1])!i[n+g] : n in [1..g]]])*B ) : i in AJ_c];
        sum_AJPs := IsEmpty(AJ_Ps) select 0 else &+AJ_Ps;
	for x in AJ_cb do
		//y := Abs(Theta(ab, AJ_P1+AJ_Q1-0.5*AJ_K+x, B));	// (TODO) Check if this is accurate for genus > 3.
                y := Abs(Theta(ab, sum_AJPs -0.5*AJ_K+x, B));	// (TODO) Check if this is accurate for genus > 3.
		vprint User5: "y =", y;
		if (y le (RealField(Precision)!10)^(-Precision/4) ) then	// (TODO) There have been problems with this precision. Maybe look for the smallest (and compare the two smallest).
			corr := -0.5*AJ_K+x;	// (TODO) Increase precision if no corr is found
			vprint User4: "It worked!";
		end if;
	end for;
	
	// Computation of height pairing
	ans := RealField(Precision)!0;
	for i in [1..#nD] do
	for j in [1..#nE] do
		ans +:= AJ_Intersection(RS, g, nD[i], dD[i], nE[j], dE[j], corr);
	end for;
	end for;

	return ans;

end function;

// Move away D from E (TODO: maybe replace this with a better function using the StrongApproximationSimple)
function MoveAway(D, E)
	n := 1;
	while (true) do
		Dred2num, r1, A := Reduction(Numerator(n*D));
		Dred2den, r2 := Reduction(Denominator(n*D), A);
		if GCD(Dred2num + Dred2den + Abs(r1 - r2)*A, Numerator(E) + Denominator(E)) eq DivisorGroup(Curve(D))!0 then
			return Dred2num - Dred2den + (r1 - r2)*A, n;
		end if;
		n +:= 1;
		if (n ge 100) then
			error "MoveAway failed!";
		end if;
	end while;
end function;

// Improved move away D from E
function BetterMoveAway(D, E : P := 0)

	// Find some base point to use
	if (Type(P) eq RngIntElt) and (P eq 0) then
		for pl in Decomposition(D) do
			if GCD(pl[1], Numerator(E) + Denominator(E)) eq (Parent(E)!0) then
				P := pl[1];
				break;
			end if;
		end for;
		if (Type(P) eq RngIntElt) and (P eq 0) then
			error "No base point found!";
		end if;
	end if;

	L := [FunctionFieldPlace(Pl[1]) : Pl in Decomposition(E)];
	M := [Pl[1] : Pl in Decomposition(E)];
	P := FunctionFieldPlace(P);
	for i in [1..#L] do
		f := StrongApproximationSimple(P, i, L);
		D +:= Valuation(D,M[i]) * CurveDivisor(Curve(D), Divisor(f));
	end for;
	return D, 1;

end function;

// Even better (?) move away D from E (TODO), yes this is better, but still a bit horrible, we run into trouble factoring the number in MeetingLocus
function BestMoveAway(D, E : P := 0)

	// Find some base point to use
	if (Type(P) eq RngIntElt) and (P eq 0) then
		for pl in Decomposition(D) do
			if GCD(pl[1], Numerator(E) + Denominator(E)) eq DivisorGroup(Curve(D))!0 then
				P := pl[1];
				break;
			end if;
		end for;
		if (Type(P) eq RngIntElt) and (P eq 0) then
			vprint User4: "No base point found. Trying with random point.";
			P := MyRandomPlace(Curve(D));
		end if;
	end if;
	P := Divisor(P);

	n := 1;
	while (true) do
		Dred2num, r1 := Reduction(Numerator(n*D), P);
		Dred2den, r2 := Reduction(Denominator(n*D), P);
		if GCD(Dred2num + Dred2den + Abs(r1 - r2)*P, Numerator(E) + Denominator(E)) eq DivisorGroup(Curve(D))!0 then
			return Dred2num - Dred2den + (r1 - r2)*P, n;
		end if;
		n +:= 1;
	end while;

end function;


// Find InfDiv
function FindInfDiv(C)
    _<xC,yC> := FunctionField(C);
    InfDivNonReduced := Denominator(Divisor(xC)) + Denominator(Divisor(yC));
    InfDiv := DivisorGroup(C)!0;
    for P in Decomposition(InfDivNonReduced) do
        InfDiv +:= P[1];
    end for;
    return InfDiv;
end function;


// HeightPairing
function NTHeightPairing(D1, D2, K, InfDiv : Precision := 30)
	assert (IsEffective(InfDiv));
	assert (GCD(Numerator(K) + Denominator(K), InfDiv) eq DivisorGroup(Curve(D1))!0);
	E1, n1 := BestMoveAway(D1, InfDiv);
	assert(IsLinearlyEquivalent(n1*D1, E1));
	vprint User4: "D1 moved away from InfDiv";
	E2, n2 := BestMoveAway(D2, InfDiv + Numerator(E1) + Denominator(E1));
	assert(IsLinearlyEquivalent(n2*D2, E2));
	vprint User4: "D2 moved away from D1 and InfDiv";
	//E1 := D1;	// This is just temporarily here because our MoveAway doesn't seem to work well for hyperelliptics.	
	//E2 := D2; n1 := 1; n2 := 1;
	if (not(assigned(Curve(D1)`RiemannSurface)) or (Curve(D1)`RiemannSurface`Prec lt Precision)) then
		C := Curve(D1);
		_<X,Y> := PolynomialRing(Rationals(), 2);
		f := Evaluate(Equation(C), [X, Y, 1]);
		RS := RiemannSurface(f : Prec := Precision);	
		C`RiemannSurface := RS;
	end if;
	RS := Curve(D1)`RiemannSurface;
	return (-ArchimedeanPairing(E1, E2, K : Precision := Precision, RS := RS) -NonArchimedeanPairing(E1, E2 : Precision := Precision)) / (n1*n2);
end function;

// Lazy HeightPairing
function NTHP(D1, D2 : Precision := 30)
    C := Curve(D1);
    K := CanonicalDivisor(C);
    InfDiv := FindInfDiv(C);
    K2 := BetterMoveAway(K, InfDiv);
    assert(IsCanonical(K2));
    vprint User4: "Go to regular function";
    return NTHeightPairing(D1, D2, K2, InfDiv : Precision := Precision);
end function;
