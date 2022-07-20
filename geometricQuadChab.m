/*
Code for the paper "Geometric quadratic Chabauty and p-adic Heights"


Authors: Juanita Duque Rosero, Sachi Hashimoto, Pim Spelier, 2022
*/

AttachSpec("spec");
load "QCMod/coleman.m";
load "QCMod/symplectic_basis.m";
load "QCMod/qc_init_g2.m";
load "QCMod/divisor_heights.m";
load "Heights/nonhyperellipticheights.m";
load "BalancedDivisorOddDeg.m";

outputQ := "DfoverQ.txt"; //Df over the rational numbers
outputZ := "DfoverZ.txt"; //Df over the integers
outputB := "BoverZ.txt"; //fiber over basepoint P0
outputC := "CoverZ.txt"; //diagonal

// Variables x,y,u,v are reserved by the endomorphisms code
QQ := Rationals();
QQt<t> := PolynomialRing(QQ);
SetDebugOnError(true);

// ==========================================================
// ===                   User Inputs                      ===
// ==========================================================


// *********************
//      X_0(67)^+
// *********************

p:= 7; //prime
//precision (the default values should be fine)
maxPrec:= p*5; // need high precision to work with points at infinity
prec := p; //working precision for heights

//Curve
f := t^5-t;
h :=t^3+t+1;
X := HyperellipticCurve(f,h);
b := X ! [1,0,1]; //base point in the affine chart

M:=Matrix(QQ,[[1,-2],[-2,-1]]); //Trace zero matrix
g := 2; //The genus of X

//Generators for J(Q) given as sums of rational points and mumford divisors
P := X![0,-1];
iP := X![0,0];
Q:= X![-1,0];
G1list := [<1, P>, <-1, iP>];
G2list := [<1,P>, <1,Q>, <-2,iP>];
Tors := []; //list of generators for the torsion part of J(Q) given in the same format as G1list, G2list
ResidueDisk := [0,-1,1];

BadSet:= [X![1,-10, 2], X![1, -3, 2]]; //Points where we are not able to compute heights on the odd degree model, since they transform to points in an infinite disk
//The code tries to avoid using these points in heights computations

// *********************
//      X_0(73)^+
// *********************
/*
p:= 11; //prime
//precision (the default values should be fine)
maxPrec:= p*5; // need high precision to work with points at infinity
prec := p; //working precision for heights

//Curve
f := t^3-t;
h :=t^3+t^2+1;
X := HyperellipticCurve(f,h);
b := X ! [1,0,1]; //base point in the affine chart
M:=Matrix(QQ,[[-1,2],[2,1]]); //Trace zero matrix 2T2+3I
g := 2; //The genus of X

// A list of points, just in case we need them
P:=X![0,0];
inf:=X![1,0,0];
Q:=X![1,0,1];
R:=X![1,-3,2];
iP,iinf,iQ,iR,ib:=Explode([Involution(PP): PP in [P,inf,Q,R,b]]);
//Generators for J(Q) given as sums of rational points and mumford divisors
// G1list := [<1, P>, <-1, inf>];
G1list := [ <-3, X![1, -3, 1]>, <2, X![0, -1, 1]>, <-2, X![1, -8, 2]>, <3, X![-1, 0, 1]>];
// G2list := [<1, iP>, <-1, inf>];
G2list := [ <-1, X![0, -1, 1]>, <-1, X![-1, 0, 1]>, <1, X![1, -8, 2]>, <1, X![1, -3, 1]> ];
Tors := []; //list of generators for the torsion part of J(Q) given in the same format as G1list, G2list
ResidueDisk := [5,5,1];//this and (5 : 9 : 1) are the ones that bad reduction should care about

BadSet:= []; //Points where we are not able to compute heights on the odd degree model, since they transform to points in an infinite disk
//The code tries to avoid using these points in heights computations
*/

// ==========================================================
// ===              Find Odd Degree Model                 ===
// ==========================================================

//Set up polynomial rings
Qp := pAdicField(p, maxPrec);
Qps<ss> := PolynomialRing(Qp);
Fp := GF(p);
Gfz<zz> := PolynomialRing(Fp);
XFp := ChangeRing(X, GF(p));
XQp := ChangeRing(X, Qp);
Qpst<tt> := PolynomialRing(Qps);

function has_odd_degree_model_at_p_g2(C : L:= Qp)

//This function was written by Steffen Muller and Jennifer Balakrishnan
//we just added a couple lines of code to deal with curves not of the form y^2 = f(x) and extensions of Qp

  // Find an odd degree model over L/Qp if one exists.
  Cp := ChangeRing(C, L);
  g := Genus(Cp);
  error if g ne 2, "Currently only implemented for genus 2";
  n := 2*g+2;
  fp, hp := HyperellipticPolynomials(Cp);
  fp := fp + (hp/2)^2; //complete the square;
  Xsq := HyperellipticCurve(fp); //need to fix Cp, and then return composite map
  _, complSq := IsIsomorphic(Cp, ChangeRing(Xsq, L));
  if Cp eq Xsq then //apparently does not count as isomorphic
  	complSq := IdentityMap(Cp);
  end if;
  Cp := ChangeRing(Xsq, L);
  if IsOdd(Degree(fp)) then
    _, phi := Transformation(Cp, [1,0,0,1]);
    return true, Cp, phi, complSq;
  end if;

  b, rt := HasRoot(fp);
  if not b then return false, _, _; end if;

  is_zero := MakeIsZero(BaseRing(fp));
  x1 := rt*Parent(fp).1 +1;
  z1 := Parent(fp).1;
  odd_fp := &+[Coefficient(fp,i)*x1^i*z1^(n-i) : i in [0..n] | not is_zero(Coefficient(fp, i))];
  assert is_zero(Coefficient(odd_fp, n));

  odd_fp := Polynomial(L, [Coefficient(odd_fp, i) : i in [0..n-1]]);
  Ep := HyperellipticCurve(odd_fp);
  lc := LeadingCoefficient(odd_fp);
  Fp := Transformation(Ep, [lc, 0,0,1], lc^2); // monic model

  // construct map from Cp to Ep.
  // We prefer MapIsoSch, but due to precision issues this might not be possible.
  bool := IsIsomorphic(Cp, Fp);
  if bool then _, phi :=IsIsomorphic(Cp, Fp); end if;
  if not bool then
    bool2, psi := IsIsomorphic(Fp, Cp);
    if not bool2 then
      P2C<XC,YC,ZC> := Ambient(Cp);
      P2F<XF,YF,ZF> := Ambient(Fp);
      phi :=  map<P2C -> P2F | [lc*ZF, lc^2*YF, XF-rt*ZF]>;
    else
      phi := Inverse(psi);
    end if;
  end if;
  return true, Fp, phi, complSq;
end function;

hasoddDegModel, oddDegModel, regToOddDeg, complSq := has_odd_degree_model_at_p_g2(X);

if not hasoddDegModel then
	print("Error: there is no oddd degree model for this curve at the given prime");
	assert hasoddDegModel;
end if;

// ==========================================================
// ===         Q-points  and Mordell--Weil sieve          ===
// ==========================================================


//Do a Mordell--Weil sieve on resdiue disks (we assume G1, G2 are saturated)

data:= coleman_data(s^2 + h*s - f, p, prec);
recpts := Q_points(data, 1000); //search for rational points in a box

function recFormatToCurvePoint(recpt, C)
		if not recpt`inf then
			xcoord := Roots(ChangeRing(PowerRelation(recpt`x,1), PolynomialRing(Rationals())))[1][1];
			ycoord := Roots(ChangeRing(PowerRelation(recpt`b[2],1), PolynomialRing(Rationals())))[1][1];
			return C![xcoord,ycoord, 1];
	else
		return C![1,recpt`b[2], recpt`x];
	end if;
end function;

Qpts:= [recFormatToCurvePoint(recpts[i], X) : i in [1 .. #recpts]];

J:= Jacobian(X);
JFp:= BaseChange(J, GF(p));
A, iso:= AbelianGroup(JFp);
iso := iso^(-1);
A:= GenericAbelianGroup(A);

function listToJac(list)
	elementJac := Jacobian(X)!0;
	deg := 0;
	for pt in list do
		elementJac := elementJac + pt[1]*(pt[2]-list[1][2]);
		deg := deg + pt[1];
	end for;
	if(deg ne 0) then
		error "Non-zero degree divisor can't be mapped to element of jacobian";
	end if;
	return elementJac;
end function;

G1 := listToJac(G1list);
G2 := listToJac(G2list);

G1modp := JFp!G1;
G2modp := JFp!G2;

function MordellWeilSieve(G1modp, G2modp: Tor:=Tors)
	//Tors is a list of genreators for the torsion or empty
	Torsmodp := [JFp!listToJac(Tor[i]) : i in [1.. #Tor]];
	G1G2modp := [A!iso(G1modp), A!iso(G2modp)];
	JacModp := [G1G2modp[1], G1G2modp[2]];
	for tor in Torsmodp do
		Append(~Torsmodp, tor);
	end for;
	subgroup := sub<A | JacModp>;  //this is subgroup
	imCFp := [x - XFp!b : x in IndexedSetToSequence(Points(XFp))];
	nonresidues := [];
	for i in [1.. #imCFp] do
		if not A!iso(imCFp[i]) in subgroup then
			Append(~nonresidues, imCFp[i]);
		end if;
	end for;
	return nonresidues; //list of things that fail the Mordell--Weil sieve
end function;

nonres := MordellWeilSieve(G1modp, G2modp);

//The Mordell--Weil sieve rules out any element from non-residues, so we don't have to consider these resdue disks of J

// ==========================================================
// ===                 COMPUTE DIVISORS                   ===
// ==========================================================

function calculateDf(X, b, M)
	// Input: Hyperelliptic curve X, base point b in the finite chart, and M trace zero matrix
	// M is the action of an endomorphism on J
	// Output: Df a correspondence for M
	print "Calculating Divisor representation...";
	time test, fs := DivisorFromMatrixAmbientSplit(X, b, X, b, M : LowerBound := 1);
	listofeq :=Equations(fs);
	S<v,y,u,x>:=Parent(listofeq[1]);
	newfs := [S!f : f in listofeq ];
	return newfs;
end function;

Df_over_Q := calculateDf(X, b, M);
Write(outputQ, Sprint(Df_over_Q));

function clearDenoms(eqns)
	neweqns := [];
	for fn in eqns do
		coeffs := Coefficients(fn);
		denoms := [];
		for c in coeffs do
			Append(~denoms, Denominator(c));
		end for;
		D := LCM(denoms);
		Append(~neweqns, D*fn);
	end for;
	return neweqns;
end function;
Df_over_Z := clearDenoms(Df_over_Q);


Write(outputZ, Sprint(Df_over_Z));

function makeBandC(eqns, b)
	Beqns := [];
	Ceqns := [];
	S<v,y,u,x>:=Parent(eqns[1]);
	for fn in eqns do
		//order of variables is v, y, u, x
		Append(~Beqns,Evaluate(fn, [b[2]/b[3]^(g+1),y, b[1]/b[3], x]));
		Append(~Ceqns,Evaluate(fn, [y,y, x, x]));
	end for;
	return Beqns, Ceqns;
end function;

BoverZ, CoverZ:= makeBandC(Df_over_Z, b);
print "found B and C";

Write(outputB, Sprint(outputB));
Write(outputC, Sprint(outputC));

S<v,y,u,x> := PolynomialRing(Integers(),[g+1, 0, 1, 0]); //construct as weighted ring
Df_over_Z := [S!Df_over_Z[i] : i in [1 .. #Df_over_Z]]; //change parent ring of Df_over_Z
SH<vh,yh,uh,xh,Hh> := PolynomialRing(Integers(),[g+1,0,1,0,1]);

function homogenizePolynomial(poly,ring)
  // Given a polynomial and a new ring with one more variable as Parent(poly), it homogenizes poly
  coeffs, mons := CoefficientsAndMonomials(poly);
  deg := Degree(LeadingMonomial(poly));
  numberOfVariables := #VariableWeights(Parent(poly));
  assert(&and[Degree(Parent(poly).i) eq Degree(ring.i): i in [1..numberOfVariables]]);
  variables := [ring.i : i in [1..numberOfVariables]];
  HV := ring.(numberOfVariables+1);
  homogenized := &+[coeffs[i]*Evaluate(mons[i],variables)*HV^(deg-Degree(mons[i])):i in [1..#mons]];
  return homogenized;
end function;
hom_Df_over_Z := [homogenizePolynomial(Df_over_Z[i],SH):i in [1..#Df_over_Z]];

// ==========================================================
// ===             computations with G_i                  ===
// ==========================================================

function normalizeList(list)
	//given a divisor in list form, remove anything of the form (+1, P), (-1,P) that can be canceled and the elements with coefficients 0.
	newlist:=[];
	for pair1 in list do
		pt := pair1[2];
		numofpt := 0;
		for pair2 in list do
			if pair2[2] eq pt then
				numofpt := numofpt + pair2[1];
			end if;
		end for;
		Append(~newlist, <numofpt, pt>);
	end for;
	newlist:=Set(newlist); //get rid of duplicates
  newList:=SetToSequence(newlist);
	return [pair:pair in newList|pair[1] ne 0];
end function;

G1list := normalizeList(G1list);
G2list  := normalizeList(G2list);

function listToListOdd(list)
	return [<pt[1], regToOddDeg(complSq(pt[2]))> : pt in list];
end function;

function listToDivisor(Glist)
	//turns G as a list [<1, P>, <-1, Q>] of points on a hyperelliptic curve into a G as a divisor (sum of places)
	placeG := Glist[1][1]*Place(Glist[1][2]);
	for i in [2..#Glist] do
		placeG := placeG + Glist[i][1]*Place(Glist[i][2]);
	end for;
	return placeG;
end function;

function divisorAsSumOfPoints(D,points:bound:=10, numberPoints := 6)
	// Input: divisor D of degree 0 as a Jacobian point
	// Output: list of rational points and coefficients that D is equivalent to
	for i in [2..Ceiling(numberPoints/2)] do
		numberOfPoints := i*2;
		points4 := CartesianPower(points, numberOfPoints);
	  listCoeff := [i: i in ([0..bound] cat [-bound..-1])];
	  coeff := CartesianPower(listCoeff, i);
	  for t in points4 do
	    for c in coeff do
				divisor := &+[c[j]*(t[2*j-1]-t[2*j]) : j in [1..i]];
	      if divisor eq D then
					listOfPoints := &cat[[<c[j],t[2*j-1]>,<-c[j],t[2*j]>] : j in [1..i]];
					listOfPoints := normalizeList(listOfPoints); //get rid of multiples
					return listOfPoints;
	      end if;
	    end for;
	  end for;
	end for;
end function;

print "Rewriting generators without infinity";
for pt in G1list do
	if pt[2] in PointsAtInfinity(X) then
		G1list := divisorAsSumOfPoints(listToJac(G1list), SetToSequence(Set(Qpts) diff PointsAtInfinity(X)));
		break;
	end if;
end for;
print "done with G1", G1list;

for pt in G2list do
	if pt[2] in PointsAtInfinity(X) then
		G2list := divisorAsSumOfPoints(listToJac(G2list), SetToSequence(Set(Qpts) diff PointsAtInfinity(X)));
		break;
	end if;
end for;
print "done with G2", G2list;

newTors:=[];
for i in [1..#Tors] do
	TorPt := Tors[i];
	for pt in TorPt do
		if pt[2] in PointsAtInfinity(X) then
 			TorPt := divisorAsSumOfPoints(listToJac(TorPt), SetToSequence(Set(Qpts) diff PointsAtInfinity(X)));
 			break;
 		end if;
 	end for;
 Append(~newTors, TorPt);
end for;
Tors:= newTors;

function applyf(Dlist,Dfeqns:Glist:= [G1list, G2list], bd:=10)
	places := [];
	ans := [];
	F<z,w> := FunctionField(X);

	for G in Glist do
		Append(~places, listToDivisor(G));
	end for;

	divD := Parent(Divisor(w))!0;
	for pt in Dlist do
		P := pt[2];
		n := pt[1];
		evalP := [];
		for fn in Dfeqns do
			S<v,y,u,x>:=Parent(fn);
			Append(~evalP, Evaluate(fn, [v, P[2]/P[3]^(g+1), u, P[1]/P[3]]));
		end for;
		evalP := GroebnerBasis(evalP);
		newgb:=[];
		for i in [1 .. #evalP] do
			Append(~newgb, Evaluate(evalP[i],[w,0,z,0]));
		end for;
		divP := GCD(Divisor(newgb[1]),Divisor(newgb[2]));
		if n gt 0 then
			for i in [1 .. n] do
				divD := divD + divP;
			end for;
		elif n lt 0 then
			for i in [1 .. -n] do
				divD := divD - divP;
			end for;
		end if;
  end for;

  return divisorAsSumOfPoints(JacobianPoint(J,divD), SetToSequence(Set(Qpts) diff PointsAtInfinity(X)):bound:=bd);

end function;

print "Applying f";
fofG1 := normalizeList(applyf(G1list, Df_over_Q));
fofG2 := normalizeList(applyf(G2list, Df_over_Q));
fofTors := [];
for tor in Tors do
  Append(~fofTors,applyf(tor, Df_over_Q));
end for;
print "Applied f";
print fofG1, fofG2, fofTors;


//Input: D of degree 0
//Output: Write D as a linear combination of G1 and G2
function linearCombinationDiv(D: Glist :=[G1list,G2list],bound:=10)
  gen1 := listToDivisor(G1list);
  gen2 := listToDivisor(G2list);
  coeff := CartesianPower([i:i in [-bound..bound]], 2);
  for c in coeff do
    if IsLinearlyEquivalent((c[1]*gen1+c[2]*gen2),D) then
			b,g := IsLinearlyEquivalent((c[1]*gen1+c[2]*gen2),D);
      newDivList := [];
      for pt in G1list do
        Append(~newDivList,<c[1]*pt[1],pt[2]>);
      end for;
      for pt in G2list do
        Append(~newDivList,<c[2]*pt[1],pt[2]>);
      end for;
      return newDivList;
    end if;
  end for;
end function;


// ==========================================================
// ===                    compute  c                      ===
// ==========================================================


function gcdDivCrv(L)
	G := L[1];
	for i in [2 .. #L] do
		G := GCD(L[i], G);
	end for;
	return G;
end function;

function removeInf(D, X)
	Inf := PointsAtInfinity(X);
	if #Inf eq 2 then
		inf1 := Place(Inf[1]);
		inf2 := Place(Inf[2]);
		S, m := Support(D);
		n1 := 0;
		n2 := 0;
		for s in [1 .. #S] do
			if S[s] eq inf1 then
				n1 := n1+m[s];
			elif S[s] eq inf2 then
				n2 := n2+m[s];
			end if;
		end for;
		D := D - n1* inf1 - n2*inf2;
	elif #Inf eq 1 then
		inf1 := Place(Inf[1]);
		S, m := Support(D);
		n1 := 0;
		for s in [1 .. #S] do
			if S[s] eq inf1 then
				n1 := n1+m[s];
			end if;
		end for;
		D := D - n1* inf1;
	end if;
	return D;
end function;

S<v,y,u,x>:=Parent(Df_over_Q[1]);
DfbxX:=[];
for fn in Df_over_Q do
	Append(~DfbxX,Evaluate(fn,[v, b[2]/b[3]^(g+1), u, b[1]/b[3]]));
end for;

F<z,w> := FunctionField(X);
newDfbxX:=[];
Dlist:= [Evaluate(DfbxX[i],[w,0,z,0]) : i in [1 ..#DfbxX]];
Dlist:= [Divisor(Dlist[i]) : i in [1.. #Dlist] | Dlist[i] ne 0];
gcdD := gcdDivCrv(Dlist);

DfnoInf:= removeInf(gcdD, X);
Blist:= [Evaluate(BoverZ[i], [0,w,0,z]) : i in [1 ..#BoverZ]];
Blist:= [Divisor(Blist[i]) : i in [1.. #Blist] | Blist[i] ne 0];
gcdB := gcdDivCrv(Blist);
BnoInf:= removeInf(gcdB,X);
Clist:= [Evaluate(CoverZ[i], [0,w,0,z]) : i in [1 ..#CoverZ]];
Clist:= [Divisor(Clist[i]) : i in [1.. #Clist] | Clist[i] ne 0];
gcdC := gcdDivCrv(Clist);

CnoInf:= removeInf(gcdC,X);
D := DfnoInf+BnoInf-CnoInf;

print "computing c";
c_constant := linearCombinationDiv(D:bound:=15);

// ==========================================================
// ===              Compute the eij matrix                ===
// ==========================================================

PtMinb := XFp!ResidueDisk-XFp!b;

function kernelOfReduction(p, G1, G2)
	J:= Jacobian(X);
	Jp:= BaseChange(J, GF(p));
	A, iso:= AbelianGroup(Jp);
	iso := iso^(-1);
	AG1 := iso(Jp!G1);
	AG2 := iso(Jp!G2);
	A:= GenericAbelianGroup(A);
	AG1 := A! AG1;
	AG2 := A! AG2;

	lincombstilde := []; // find all linear combinations of AG1 and AG2 that vanish
	for i in [0 .. #A] do
		for j in [0 .. #A] do
			if i*AG1 + j*AG2 eq A!0 then
				Append(~lincombstilde,[i,j]);
			end if;
		end for;
	end for;

	lincombstilde := LLL(Matrix(lincombstilde))[1..2];

	return lincombstilde;

end function;

kernelOfReductionMordellWeil := kernelOfReduction(p, G1, G2);


function finde0(D:coeffBound:=10)
	J:= Jacobian(X);
	Jp:= BaseChange(J, GF(p));
  coeff := CartesianPower([i:i in [-coeffBound..coeffBound]], 2);
  for c in coeff do
    if (c[1]*Jp!G1+c[2]*Jp!G2) eq D then
      return [c[1],c[2]];
    end if;
  end for;
end function;

e01,e02 :=Explode(finde0(PtMinb));

e := [<"",e01,e02>,<"",kernelOfReductionMordellWeil[1][1],kernelOfReductionMordellWeil[1][2]>,<"",kernelOfReductionMordellWeil[2][1],kernelOfReductionMordellWeil[2][2]>];

// ==========================================================
// ===                     Heights                        ===
// ==========================================================

Gprime, _ := HyperellipticPolynomials(oddDegModel);
Gprime := ChangeRing(Gprime, Rationals());
data := coleman_data(s^2-Gprime, p, prec : useU :=false, heights);
data`ordinary := true;
data`cpm := -cup_product_matrix(data`basis, data`Q, 2, data`r, data`W0);

function setPoint(P,data)
  if (not IsZero(P[3])) and Valuation(P[1]) ge 0 then
    b := set_point(P[1], P[2], data);
  else
    b := set_bad_point(P[3]/P[1],[1,P[2]/P[1]^3],true,data);
  end if;
  return b;
end function;

function colemanInt(x,data)
	//x is a divisor given as a list of points
	//b is basepoint on odd degree model
	b := setPoint(x[1][2],data);
  sum, _ := coleman_integrals_on_basis(b,b,data);
	for pt in x do
		P := setPoint(pt[2],data);
    colemanVal, Nprec := coleman_integrals_on_basis(b,P,data);
		for i in [1..g] do
			sum[i] := sum[i]+pt[1]*colemanVal[i];
		end for;
	end for;
	return <sum[i]/2 : i in [1..g]>,Nprec; //We scaled this so it matches the Sage code.
end function;

function divTimesDivToN(x, y)

  bigPrec := prec;
  biggerData := coleman_data(s^2-Gprime, p, bigPrec : useU :=false, heights);
  biggerData`ordinary := true;
  biggerData`cpm := -cup_product_matrix(biggerData`basis, biggerData`Q, 2, biggerData`r, biggerData`W0);
  logx,_ := colemanInt(x,data);
  repeat
    try
    	logyTry, Nprec := colemanInt(y,biggerData);
      if Nprec le 0 then
        bigPrec +:= p;
        biggerData := coleman_data(s^2-Gprime, p, bigPrec : useU :=false, heights);
        biggerData`ordinary := true;
        biggerData`cpm := -cup_product_matrix(biggerData`basis, biggerData`Q, 2, biggerData`r, biggerData`W0);
      else
        logy := logyTry;
      end if;
    catch e
      bigPrec +:= p;
      biggerData := coleman_data(s^2-Gprime, p, bigPrec : useU :=false, heights);
      biggerData`ordinary := true;
      biggerData`cpm := -cup_product_matrix(biggerData`basis, biggerData`Q, 2, biggerData`r, biggerData`W0);
    end try;
  until assigned logy;
  repeat
    try
    	newx := [];
    	for pt in x do
    		P := setPoint(pt[2],biggerData);
    		Append(~newx, <P,pt[1]>);
    	end for;
    	newy := [];
    	for pt in y do
        P := setPoint(pt[2],biggerData);
    		Append(~newy, <P,pt[1]>);
    	end for;

    	hpxy := local_height_divisors_p([newx], [newy], biggerData); //requires x, y to be of the form P - Q, R- S
    catch e

      bigPrec +:= p;
      biggerData := coleman_data(s^2-Gprime, p, bigPrec : useU :=false, heights);
      biggerData`ordinary := true;
      biggerData`cpm := -cup_product_matrix(biggerData`basis, biggerData`Q, 2, biggerData`r, biggerData`W0);
    end try;
  until assigned hpxy;
	return <logx, logy, hpxy>;
end function;

function listToPairs(list)
	// Turns a divisor given as a list [<ni,Pi>] into pairs <coeff,<1,P>,<-1,Q>> for the heights code
	pairs := [];
	coord1 := 1;
	while coord1 le #list do
		point1 := list[coord1][2];
		coeff1 := list[coord1][1];
		if Sign(coeff1) eq 1 then
			coord2 := 1;
			while coeff1 ne 0 do
				if coord1 ne coord2 then
					coeff2 := list[coord2][1];
					if Sign(coeff2) eq -1 then
						point2 := list[coord2][2];
						if Abs(coeff2) ge Abs(coeff1) then
							Append(~pairs,<coeff1,[<1,point1>,<-1,point2>]>);
							Remove(~list, coord2);
							if coord2 le coord1 then
								coord1 := coord1 - 1;
							end if;
							coeff1 := 0;
							if Abs(coeff2) ne Abs(coeff1) then
								Append(~list, <coeff1+coeff2,point2>);
							end if;
						else
							Append(~pairs,<Abs(coeff2),[<1,point1>,<-1,point2>]>);
							Remove(~list, coord2);
							if coord2 le coord1 then
								coord1 := coord1 - 1;
							end if;
							coeff1 := coeff1+coeff2;
							coord2 := coord2 - 1;
						end if;
					end if;
				end if;
				coord2 := coord2 + 1;
			end while;
			Remove(~list,coord1);
			coord1 := coord1 - 1;
		end if;
		coord1 := coord1 + 1;
	end while;
	return pairs;
end function;



Fpn<n1, n2> := PolynomialRing(Fp,2);

function tensor1(Q1, Q2, a, b)
	//a*_1Q1 +_1 b *_1 Q_2
	assert Fpn!(Q1[1][1]) eq Fpn!(Q2[1][1]) and Fpn!(Q1[1][2])eq Fpn!(Q2[1][2]); //Sanity check (perhaps add more prec)
	x0 := <a* Q1[1][1] + b* Q2[1][1],a* Q1[1][2] + b* Q2[1][2]>;
	x1 := Q1[2];
	x2 := a* Q1[3] + b* Q2[3];
	return <x0,x1,x2>;
end function;

function tensor2(Q1, Q2, a, b)
	//a*_1Q1 +_1 b *_1 Q_2
	assert Fpn!Q1[1][1] eq Fpn!Q2[1][1] and Fpn!(Q1[1][2]) eq Fpn!(Q2[1][2]); //Sanity check (perhaps add more prec)
	x0 := Q1[1];
	x1 := <a* Q1[2][1] + b* Q2[2][1],a* Q1[2][2] + b* Q2[2][2]>;
	x2 := a* Q1[3]+ b* Q2[3];
	return <x0,x1,x2>;
end function;

function divTimesDivToNList(listx, listy, nvals)
	listx := listToPairs(listx);
	listy := listToPairs(listy);
	initializingY := false;
	initialY := <0,0>;
	for x in listx do
    colx, _ :=colemanInt(x[2],data);
		sumXFixed := <colx,<0,0>,0>;
		for y in listy do
			divxy := divTimesDivToN(x[2], y[2]);
			sumXFixed := tensor2(sumXFixed,divxy,1,y[1]);
			initialY := sumXFixed[2];
		end for;
		if not initializingY then
			total := <<0,0>,initialY,0>;
			initializingY := true;
		end if;
		total := tensor1(total,sumXFixed,1,x[1]);
	end for;
	n1, n2 := Explode(nvals);
	total := < <total[1][1]/n1, total[1][2]/n1>, <total[2][1]/n2, total[2][2]/n2>, total[3]*(1/n1 )*(1/n2)>;
	return total;
end function;


function constructListsToPair(list1,list2:badPts:=[])
	// Construsts a linear equivalence that can be used when taking heights
	// Checks if list1 has any bad points

	list1:= normalizeList(list1);
	list2:= normalizeList(list2);
	list1Jac := listToJac(list1);
	list2Jac := listToJac(list2);

	done := false;
	i := 1;
	while not done and i le #list1 do
		n1 := 1;
		if list1[i][2] in badPts then
			for n1val in [2.. 7] do
				n1 := n1val;
				try
					list1 := divisorAsSumOfPoints(n1*list1Jac,SetToSequence(Set(Qpts) diff Set(badPts)):bound:=10);
					break;
				catch e
					continue;
				end try;
			end for;
			done := true;
		end if;
		i := i+1;
	end while;

	// Finds the points that list2 can have
	allowedPts := [];
	for pt in Qpts do
		allowable := true;
		if pt in badPts then
			allowable := false;
		end if;
		for pair in list1 do
			if pair[2] eq pt then
				allowable := false;
        break;
			end if;
		end for;
		if allowable then
			Append(~allowedPts,pt);
		end if;
	end for;
	n2:= 1;
	list2OK := true;
	for pair in list2 do
	 if pair[2] notin allowedPts then
	 	list2OK := false;
	 	 break;
	 	end if;
	end for;

	if not list2OK then
		for n2val in [2..10] do
			try
				n2 := n2val;
				list2 := 	divisorAsSumOfPoints(n2*list2Jac,allowedPts:bound:=10);
				break;
			catch e
				if n2 eq 10 then
					error "no valid list found";
				else continue;
				end if;
			end try;
		end for;
	end if;
	return list1, list2, [n1, n2];
end function;

// ==========================================================
// ===                Integer Points                      ===
// ==========================================================

// Calculates \sum_{q =/= p} h_q(D,E)
function LogIntersectionNumbers(D,E)
	ans := 0;
	for i in NonArchimedeanIntersectionNumbers(D,E) do
		if i[1] ne p then
			ans +:= i[2]*Log(Qp!i[1]);
		end if;
	end for;
	return -ans; // Sign issue
end function;


function createQij()
Glist:=[G1list,G2list];
	for i in [1 .. #Tors] do
		Append(~Glist, Tors[i]);
	end for;
fGlist:=[c_constant, fofG1, fofG2];
for i in [1.. #fofTors] do
	Append(~fGlist, fofTors[i]);
end for;
Qijlist := [[]];
	for i in [1..2] do
		Append(~Qijlist,[]);
		for j in [1..3] do
    if (#Glist[i])*(#fGlist[j]) ne 0 then
 			l1,l2, nvals := constructListsToPair(Glist[i],fGlist[j]: badPts:= BadSet);
 			Qijlist[i+1][j] :=  divTimesDivToNList(listToListOdd(l1), listToListOdd(l2), nvals);
			Qijlist[i+1][j][3] +:= LogIntersectionNumbers(listToDivisor(l1),listToDivisor(l2))/(nvals[1]*nvals[2]);
 			print "Computed the next Qij";
 			print(Qijlist[i+1][j]);
    else
      print "Something is still empty";
    end if;
		end for;
	end for;
	return Qijlist;
end function;

print "Creating Qij";
Qij := createQij();
print "done with Qij";

Q10, Q11, Q12 := Explode(Qij[2]);
Q20, Q21, Q22 := Explode(Qij[3]);

function constructPij(i,j)
	LHS := tensor2(Q11, Q12, e[j][2],e[j][3]);
	RHS := tensor2(Q21, Q22, e[j][2],e[j][3]);
	Pij := tensor1(LHS, RHS, e[i][2],e[i][3]);
	return Pij;
end function;

function construct_ttilde()
	LHS1 := tensor2(Q11, Q12, e[1][2],e[1][3]);
	LHS := tensor2(LHS1, Q10,1,1);
	RHS1 := tensor2(Q21, Q22, e[1][2],e[1][3]);
	RHS := tensor2(RHS1, Q20, 1,1);
	ttilde := tensor1(LHS, RHS, e[1][2], e[1][3]);
	return ttilde;
end function;

function constructRit(i)
	LHS1 := tensor2(Q11, Q12, e[1][2],e[1][3]);
	LHS := tensor2(LHS1, Q10,1, 1);
	RHS1 := tensor2(Q21, Q22, e[1][2],e[1][3]);
	RHS := tensor2(RHS1, Q20, 1,1);
	Rit := tensor1(LHS, RHS, e[i][2], e[i][3]);
	return Rit;
end function;

function constructStj(j)
	LHS := tensor2(Q11, Q12, e[j][2], e[j][3]);
	RHS := tensor2(Q21, Q22, e[j][2], e[j][3]);
	Stj := tensor1(LHS, RHS, e[1][2], e[1][3]);
	return Stj;
end function;

Stj := <"", constructStj(2), constructStj(3)>;
Rit := <"", constructRit(2), constructRit(3)>;
Pij := <<"","","">,<"", constructPij(2,2), constructPij(2,3)>,<"", constructPij(3,2), constructPij(3,3)>>;
Qpn<n1, n2> := PolynomialRing(Qp,2);

function constructAttilde(Stj)
	Attilde := tensor2(Stj[2], Stj[3], n1, n2);
	return Attilde;
end function;

function constructBttilde(Rit)
	Bttilde := tensor1(Rit[2], Rit[3], n1, n2);
	return Bttilde;
end function;


function constructC(Pij)
	innersum1 := tensor2(Pij[2][2], Pij[2][3], n1,n2);
	innersum2 := tensor2(Pij[3][2], Pij[3][3], n1,n2);
	outersum := tensor1(innersum1, innersum2, n1, n2);
	return outersum;
end function;

Attilde := constructAttilde(Stj);
Bttilde := constructBttilde(Rit);
Cofn := constructC(Pij);
ttilde := construct_ttilde();

function constructDttilde(A,B,C,t)
	sum1 := tensor2(C, B, 1, 1);
	sum2 := tensor2(A, t, 1, 1);
	Dttilde := tensor1(sum1, sum2, 1, 1);
	return Dttilde;
end function;

Dttilde := constructDttilde(Attilde, Bttilde, Cofn, ttilde);

function constructkappa(Dttilde)
	logx := <Evaluate(Dttilde[1][1],[(p-1)*n1, (p-1)*n2]),Evaluate(Dttilde[1][2],[(p-1)*n1, (p-1)*n2])>;
	logy := <Evaluate(Dttilde[2][1],[(p-1)*n1, (p-1)*n2]),Evaluate(Dttilde[2][2],[(p-1)*n1, (p-1)*n2])>;
	hp := Evaluate(Dttilde[3],[(p-1)*n1, (p-1)*n2]);
	return <logx, logy, hp>;
end function;

kappa := constructkappa(Dttilde);
logG1,_ := colemanInt(listToListOdd(G1list),data);
logG2,_ := colemanInt(listToListOdd(G2list),data);
logPtminb := <e01*logG1[1] + e02*logG2[1],e01*logG1[2] + e02*logG2[2]>;

Fpn<n1, n2> := PolynomialRing(GF(p),2);

function kappainparamsatP(kappa, logPminb)
	kappa00 := Fpn!((kappa[1][1] - logPminb[1])* (1/p));
	kappa01 := Fpn!((kappa[1][2] - logPminb[2])* (1/p));
	kappa2 := Fpn!((1/p)*kappa[3]);
	return <kappa00, kappa01, kappa2>;
end function;

S3 := pAdicField(p,3);
S3n<n1, n2> := PolynomialRing(S3,2);

function kappainparamsatPprec3(kappa, logPminb)
	kappa00 := S3n!((kappa[1][1] - logPminb[1])* (1/p));
	kappa01 := S3n!((kappa[1][2] - logPminb[2])* (1/p));
	kappa2 := S3n!((1/p)*kappa[3]);
	return <kappa00, kappa01, kappa2>;
end function;

kappainparams := kappainparamsatP(kappa, logPtminb);
print "This is kappa";
print kappainparams;

// ==========================================================
// ===            Constructing jbtilde                    ===
// ==========================================================


function convertFuncFieldToPoly(expression)
	listOfCoeff,listOfMon := CoefficientsAndMonomials(expression);
	newPoly := Parent(s)!0;
	w := Parent(expression).2;
	for i in [1..#listOfCoeff] do
		for j in [0..1] do
			if w^j eq listOfMon[i] then
				newPoly := newPoly+Evaluate(listOfCoeff[i],s)*t^j;
			end if;
		end for;
	end for;
	return newPoly;
end function;

function findParam(xcoord, ycoord, XQp)
	pt := (XFp![xcoord,ycoord]);
	f, h := HyperellipticPolynomials(XQp);
	if IsWeierstrassPlace(Place(pt)) then
		P := ycoord^2 + h*ycoord - f;
		for r in Roots(P) do
			if Fp!r[1] eq Fp!xcoord then
				return r[1],ycoord;
			end if;
		end for;
	else
		R<y> := PolynomialRing(BaseRing(XQp));
		P := y^2 + Evaluate(h,xcoord)*y - Evaluate(f,xcoord);
		for r in Roots(P) do
			if Fp!r[1] eq Fp!ycoord then
				return xcoord,r[1];
			end if;
		end for;
	end if;
end function;

	// findParam(Qp!7,Qp!(-1),X);
	//P1x := Qp!(7); //Coordinates of P1
	//P1y := (6 + 6*7 + 6*7^2 + 5*7^3 + 5*7^4 + 4*7^5 + 4*7^6 + 5*7^7 + 7^8 + 7^9  );


function explicitCantor(oddDegPts, xcoord, ycoord, L: curvepoly := Gprime, lowerbd:= 1)
	//Input: oddDegPts, the points for DfPnu x X on the odd degree model, and (xcoord, ycoord) = Pnu, L/Qp field of defn for OddDegPts
	//also takes an optional lower bound for the number of times it addes DfPnux X
	//Output: some multiple of E = DfPnu x X such that it splits into points over Qp, and the points that it splits into, the multiple, and the linear equivalents between the splitting and the multiple of the divisor
	//So far n is always 2
	Expoly, Eypoly := createMumford(oddDegPts[1], oddDegPts[2]);
	R<xx> := PolynomialRing(L);
	Expoly  := R!Expoly;
	Expoly := (Expoly mod xx^2) + xx^2; //force to be monic
	Eypoly  := R!Eypoly;
	E := [ Expoly, Eypoly];
	f, h:= HyperellipticPolynomials(X);
	linequiv := 1;
	n:= 1;
	addend := E;
	while(true) do
		apoly,bpoly := Explode(Compose(addend, E,curvepoly));
		rdiv := Reduce(<apoly,bpoly>,curvepoly,2);
		n:= n+1;

		XregQp := ChangeRing(X, Qp);
		Pnu:= regToOddDeg(complSq(XregQp![xcoord, ycoord]));
		boddDeg := regToOddDeg(complSq(b));
		P1evalb  := Pnu[2] - Evaluate(bpoly, Pnu[1]);
		bevalb := boddDeg[2] - Evaluate(bpoly, boddDeg[1]);

		P1evalc := Evaluate(rdiv[1], Pnu[1]);
		bevalc := Evaluate(rdiv[1], boddDeg[1]);

		linequiv:= Qp!((P1evalb /bevalb)/(P1evalc/ bevalc)) *linequiv;

		roots := Roots(rdiv[1]);
		if #roots eq Degree(rdiv[1]) and n gt lowerbd then //checking if there are Q1, Q2 such that nE = Q1+ Q2 +inf*(2n-deg(rdiv))
			Q := [[Qp!r[1],Qp!Evaluate(rdiv[2],r[1])] : r in roots];
			return Q, n, linequiv;
		end if;
		addend :=  rdiv;
	end while;
	return false;

end function;

function LogExt(x)
  return Log(x * p^(-Valuation(x)));
end function;

// Input: FpPoint are the integers corresponding to the x and y coordinates of P in F_p.
// 				nu is the deformation parameter.
// 				Df are the equations for the divisor on the chart given by X
//				gCminB=[gnum,gdenom], C-B = div(gnum/gdenom) +(sum of rational points).
// Output: Returns:
// 				Q = [Q_1, Q_2], n such that n D_nu  = Q1+Q2 up to lin equiv
// 				log such that h_7(P_nu-b,D_nu + C - B)\\ = \frac1n h_7(P_nu-b,Q_1+Q_2 .. +n\infty + n(4\infty_-  - \iota b - 5 \iota Q)) - 1/n * log + \log g(P_nu-b)
function makeDfPnuxX(nu,FpPoint, gBminC)
  print "making DfPnu";
  error if FpPoint[3] eq 0, "Infinity case not implemented";
  FpPoint:=[FpPoint[1]/FpPoint[3],FpPoint[2]/FpPoint[3]^3];
	gnum, gdenom := Explode(gBminC);
	if IsWeierstrassPlace(Place(XFp!FpPoint)) then
		xcoord, ycoord := findParam(FpPoint[1],FpPoint[2] + nu * p,XQp);
	else
		xcoord, ycoord := findParam(FpPoint[1]+ nu*p,FpPoint[2],XQp);
	end if;
	xcoord := Integers()!xcoord;
	ycoord := Integers()!ycoord;
	S<v,y,u,x,h>:=Parent(hom_Df_over_Z[1]);

	DfPxX:=[];
	for i in [1 .. #hom_Df_over_Z] do
		  //order of variables is v, y, u, x
	    Append(~DfPxX, Evaluate(hom_Df_over_Z[i],[v,ycoord,u,xcoord,1]));
	end for;
	Append(~DfPxX, p^maxPrec);
	DfPxX:= GroebnerBasis(DfPxX);
  if #DfPxX ne 3 then
    coefs, mons := CoefficientsAndMonomials(DfPxX[2]);
    assert &and[Valuation(coefs[i],p) ge 1 : i in [2..#coefs]] and Valuation(coefs[1],p) eq 1;
    Append(~DfPxX, &+[Parent(mons[i])!(coefs[i]/p)*mons[i]:i in [1..#coefs]]);
    DfPxX:= GroebnerBasis(DfPxX);
    print DfPxX;
    assert #DfPxX eq 3;
  end if;
	E := [DfPxX[2],Evaluate(-DfPxX[1],[0,0,u,0,h])]; //We want to have this in terms of u and z (living in the right place).

	inj := hom<S->Qps|0,0,ss,0,1>;
	E := [inj(E[i]) : i in [1..2]];

	// We factor the quadratic polynomial E[1]
	Rts:= Roots(Gfz!E[1]);

	Pnureg := [xcoord,ycoord];

	PN:= Evaluate(Evaluate(gnum,Pnureg[1]),Pnureg[2]);

	PD := Evaluate(Evaluate(gdenom,Pnureg[1]),Pnureg[2]);

	BN := Evaluate(Evaluate(gnum,b[1]/b[3]),b[2]/b[3]^(g+1));

	BD := Evaluate(Evaluate(gdenom,b[1]/b[3]),b[2]/b[3]^(g+1));

	//print (PN * BD ) / ( PD * BN);
	if #Rts eq 1 and Rts[1][2] eq 2 then
		// Subtract before taking integers, otherwise it breaks.
		linearRoot := Integers()!(-Rts[1][1]);
		if Rts[1][1] eq 0 then
			linearRoot:= -p;
		end if;
		E1 := Evaluate(E[1], ss-linearRoot); //make E[1] an Eisenstein polynomial, since mod 7 this factors as (x-linearRoot)^2
		L := ext<Qp|E1>;
		T<yy>:= PolynomialRing(L);
		xroots:= Roots(T!E1);
		E2 := T!E[2];
		pts := [];
		for r in xroots do
			xSolution := r[1] - linearRoot;
			ySolution := Evaluate(E2, xSolution);
			Append(~pts, [xSolution, ySolution]);
		end for;

	elif #Rts eq 0 then
		E1:= E[1];
		L := ext<Qp|E1>;
		T<yy>:= PolynomialRing(L);
		xroots:= Roots(T!E1);
		E2 := T!E[2];
		pts := [];
		for r in xroots do
			xSolution := r[1];
			ySolution := Evaluate(E2, xSolution);
			Append(~pts, [xSolution, ySolution]);
		end for;
	else
		assert #Rts eq 2 and Rts[1][2] eq 1;
		//In this case we are on XQp, not the odd degree model, have to change model
		L := Qp;
		E1:= E[1];
		T<yy>:= PolynomialRing(L);
		xroots:= Roots(T!E1);
		E2 := T!E[2];
		pts := [];
		for r in xroots do
			xSolution := r[1];
			ySolution := Evaluate(E2, xSolution);
			Append(~pts, [xSolution, ySolution]);
		end for;
		XL := ChangeRing(X, L);
		_, oddDegL, regToOddDegL, complSqL := has_odd_degree_model_at_p_g2(XL : L:= L);
		ptsodd := [];
		for Q in pts do
			Qnew := regToOddDegL(complSqL(XL!Q));
			Append(~ptsodd, [Qnew[1]/Qnew[3], Qnew[2]/Qnew[3]^3]);
		end for;
		return ptsodd, 1, 0, LogExt(PN * BD) - LogExt(PD * BN);
	end if;


	XL := ChangeRing(X, L);
	_, oddDegL, regToOddDegL, complSqL := has_odd_degree_model_at_p_g2(XL : L:= L);
	oddDegPts := [];
	for pt in pts do
		dummyvar := XL!pt; //just a sanity check
		Append(~oddDegPts,regToOddDegL(complSqL(XL![pt[1],pt[2]])));
	end for;
	if FpPoint[1] eq -1 and FpPoint[2] eq 0 then
		bd := 2;
	else
		bd:= 1;
	end if;

	Q, n, linequiv:= explicitCantor(oddDegPts, xcoord,ycoord,L: lowerbd:= bd);

	return Q, n, LogExt(linequiv), LogExt(PN * BD ) - LogExt( PD * BN);
end function;


BminC := BnoInf-CnoInf;

function allowablePts(Qpts, Fppoint: excudedpts:=[])
	goodpts := [];
	for pt in Qpts do
		if pt in excudedpts or pt eq b then
			continue;
		elif GF(p)!pt[1] eq Fppoint[1] and GF(p)!pt[2] eq Fppoint[2]  and GF(p)!pt[3] eq Fppoint[3] then
			continue;
		else
			Append(~goodpts, pt);
		end if;
	end for;
	return goodpts;
end function;

allowedPts:= allowablePts(Qpts, ResidueDisk);
assert #allowedPts ne 0; //no good qpoints known, deal with this
pt1:=allowedPts[1];
BminCdeg0 := BminC-Degree(BminC)*Place(pt1);
ptlistBminC := divisorAsSumOfPoints(JacobianPoint(J,BminCdeg0), allowedPts);
Append(~ptlistBminC, <Degree(BminC), pt1>);
placeBminC := listToDivisor(ptlistBminC);
_, gequiv := IsLinearlyEquivalent(BminC, placeBminC);
gequivPoly := convertFuncFieldToPoly(gequiv);
gNumQQ := Numerator(gequivPoly);
gDenomQQ := Denominator(gequivPoly);
gnum := Qpst!gNumQQ;
gdenom := Qpst!gDenomQQ;
gBminC :=[gnum,gdenom];


function localHeightPnu(Fppoint, Q, log, geval, nu, n)
	// assert m = 2
	//E  = [(1,Q1),(1,Q2),(2n - 2,infinity_odd_deg)]
	//BminC = [(4,infmin), (-1,ib), (-5, iQ)] this is degree -2
	//want to add E plus n * BminC  this is degree 2n - 2n = 0

  //Q = [Q_1, Q_2], n such that n D_nu  = Q1+Q2 up to lin equiv
  //log such that h_7(P_nu-b,D_nu + C - B)\\ = \frac1n h_7(P_nu-b,Q_1+Q_2 .. +n\infty + n(4\infty_-  - \iota b - 5 \iota Q)) - 1/n * log + \log g(P_nu-b)

	assert #Q eq 2;

	Q1 := Q[1];
	Q2 := Q[2];
	Q1 := oddDegModel!Q1;
	Q2 := oddDegModel!Q2;
	if IsWeierstrassPlace(Place(XFp!Fppoint)) then
		xcoord, ycoord := findParam(Fppoint[1],Fppoint[2] + nu * p,XQp);
	else
		xcoord, ycoord := findParam(Fppoint[1]+ nu*p,Fppoint[2],XQp);
	end if;
	Pnu := regToOddDeg(complSq((XQp![xcoord, ycoord])));
	bOddDeg := regToOddDeg(complSq(b));
	Div := [<1, Pnu>, <-1,bOddDeg>];
	ptlistBminCOdd:= listToListOdd([<n*ptlistBminC[i][1],ptlistBminC[i][2]>:i in [1..#ptlistBminC]]);
	infOddDeg := oddDegModel![1,0,0];
	Append(~ptlistBminCOdd, <2*n-2, infOddDeg>);
  Append(~ptlistBminCOdd, <1, Q1>);
  Append(~ptlistBminCOdd, <1, Q2>);

	PnuonN := divTimesDivToNList(Div, ptlistBminCOdd, [1,1]);
  print "done with PnuonN";

	return <<PnuonN[1][1] - logPtminb[1],PnuonN[1][2] - logPtminb[2]>, PnuonN[3]/n + geval + log/n>;
end function;

function lineBetween(values,xValues)
  r0,r1 := Explode([Fp!(v/p):v in values]);
  return Gfz!((r1-r0)/(xValues[2]-xValues[1])*(zz-xValues[1])+r0);
end function;

function findJbTilde(ResidueDisk, gBminC)
  Q0, n0, logMumford0, geval0 := makeDfPnuxX(0, ResidueDisk, gBminC);
  lh0 := localHeightPnu(ResidueDisk,Q0, logMumford0,geval0, 0, n0);
  print("this is local height pnu 0");
  print(lh0);

  Q1, n1, logMumford1, geval1 := makeDfPnuxX(1, ResidueDisk, gBminC);
  lh1:=localHeightPnu(ResidueDisk,Q1, logMumford1,geval1, 1, n1);
  print("this is local height pnu 1");
  print(lh1);


  jbt:=[lineBetween([lh0[1][i],lh1[1][i]],[0,1]): i in [1,2]] cat [lineBetween([lh0[2],lh1[2]],[0,1])];

  // Check that we get a line
  Q2, n2, logMumford2, geval2 := makeDfPnuxX(2, ResidueDisk, gBminC);
  lh2:=localHeightPnu(ResidueDisk,Q2, logMumford2,geval2, 2, n2);
  print("this is local height pnu 2");
  print(lh2);
  newjbt := [lineBetween([lh1[1][i],lh2[1][i]],[1,2]): i in [1,2]] cat [lineBetween([lh1[2],lh2[2]],[1,2])];
  assert jbt eq newjbt;

  return jbt;
end function;

jbtilde := findJbTilde(ResidueDisk,gBminC);

function intersectKappaJbTilde(kappaInParams,jbTilde)
  GB<x,y,z,t> := PolynomialRing(GF(p),4);
  I := ideal<GB|[x-Evaluate(jbTilde[1],t),y-Evaluate(jbTilde[2],t),z-Evaluate(jbTilde[3],t)]>;
  relationsjbt := Generators(EliminationIdeal(I,{x,y,z}));
  toEvaluate := [poly:poly in kappaInParams] cat [0];
  equationsToSolve := GroebnerBasis(ideal<Fpn|[Evaluate(poly,toEvaluate):poly in relationsjbt]>);
  solutions:=[];
  for sol in CartesianPower(Fp,2) do
    if &and[IsZero(Evaluate(poly,sol)) : poly in equationsToSolve] then
      Append(~solutions,sol);
    end if;
  end for;
  error if #solutions gt 2, "GQC mod p^2 does not give an upper bound in this residue disk";
  completeSolutions := [];
  i:=1;
  coeff:=Coefficients(jbTilde[i]);
  while #coeff eq 1 and i le 3 do
    i +:= 1;
    coeff:=Coefficients(jbTilde[i]);
  end while;
  for sol in solutions do
    Append(~completeSolutions,<(Evaluate(kappaInParams[i],sol)-coeff[1])/coeff[2],sol>);
  end for;
  return completeSolutions;
end function;

intersectKappaJbTilde(kappainparams,jbtilde);
