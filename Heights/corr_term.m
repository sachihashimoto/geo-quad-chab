// Compute the Moore-Penrose pseudoinverse of a square matrix A.
function pseudoinverse(A)
  k := Nrows(A);
  assert k eq Ncols(A); // A must be square  
  K := FieldOfFractions(BaseRing(A));
  S := Matrix(K, k, [K ! (1 / k) : i in [1..k^2]]);
  return (A - S)^(-1) + S;
end function;


// Compute the intersection (Phi(D).EE)_p, where D and E are divisors of degree 0
// with Zariski closures DD and EE, respectively, p is a finite prime and Phi(D) 
// is a Q-fibral divisor such that (DD+Phi(D).C_i)_p=0 for all irreducible componente
// C_i of the special fiber above p.
// We only need the lists wD and wE of intersection multiplicities (DD.C_i)_p and
// (EE.C_i)_p, the intersection matrix I of the special fiber and the vector of its
// multiplicities. 
function correction_divisor(wD, wE, I, mults)
  I := ChangeRing(I, Rationals());
  r := #mults;
  A := Matrix(Rationals(), r, r, [[mults[i]*mults[j]*I[i,j] : j in [1..r]] : i in [1..r]]);
  sD := [wD[i]*mults[i] : i in [1..r]];
  sE := [wE[i]*mults[i] : i in [1..r]];
  assert IsZero(&+sD) and IsZero(&+sE);
  vD := Matrix(Rationals(), 1, sD);
  vE := Matrix(Rationals(), 1, sE);
  phi1 := (Transpose(vE) * pseudoinverse(A) * vD)[1,1];
  // sanity check:
  phi2 := (Transpose(vD) * pseudoinverse(A) * vE)[1,1];
  assert phi1 eq phi2;
  return phi1;
end function;

