p = 7
g=2
prec = 15
S = pAdicField(p,prec)
Qpx.<x>= pAdicField(p,prec)[]
poly= x^6 + 4*x^5 + 2*x^4 + 2*x^3 + x^2 - 2*x + 1
beta=-poly.factor()[0][0][0]
Hinf=HyperellipticCurve(x-x^5,x^3+x^2+1)
Hfin = HyperellipticCurve(x^5-x,x^3+x+1)
A = poly(beta*x/(x-1))*(x-1)^6
A.reduce()
m = Qpx(A).list()[5].nth_root(5)
Gprime = Qpx(A(x/m))[:6]
XK= HyperellipticCurve(Gprime)

# infChart is true if (a,b) is a point in the infinite chart
# In homogeneous coordinates: [X:Y:Z] -> [X:X^3+Z^2X+2Y+Z^3:Z]
def changeRegModtoY2(a,b,infChart):
#change from regular model to y^2 = x^6 model, but not x^5 model
#$.1
#$.1^3 + $.1*$.3^2 + 2*$.2 + $.3^3
#$.3
	if infChart == False:
		return a, a^3 + a + 2*b + 1
	else: 
		# In the infinite chart (a,b) corresponds to (z,y)
		return 	a, 1+a^2+2*b+a^3

# $(x'',y'') \mapsto (\beta (x''/mon)/((x''/mon)-1), (y''/\beta^3) \beta^3 / ((x''/mon) - 1)^3)$
def changeOddDegreeModeltoRegModel(a,b):
	return beta*(a/m)/((a/m)-1) , (b/beta^3)*beta^3/((a/m)-1)^3

R.<x,y>= PolynomialRing(S,2)
# Check that the first variable is x and the second is y
def changePolyRegModelToOddDegree(f):
	print("Be careful, first variable is x and second is y")
	return f(beta*(x/m)/((x/m)-1),(y/beta^3)*beta^3/((x/m)-1)^3)

# H is the hyperelliptic curve
def solvefory(xcoord, yval,H):
#Only works for non-Weierstrass Disks
	R.<y> = S[]
	f,h = H.hyperelliptic_polynomials()
	P = y^2 + h(xcoord)*y - f(xcoord)
	for r in P.roots():
		if r[0] % p  == yval % p:
			return r[0]					

def changeEvenDegtoOddDeg(a,b,c, XK=XK):
	#changes from x^6 to x^5 model
	xprime = a/(a-beta*c)
	yprime = b/(a-beta*c)^3
	x0 = m*xprime
	y0 = beta^3*yprime
	assert y0^2 == Gprime(x0)
	return XK(x0,y0)

def changeRegtoOddDeg(a,b):
	a, b  = changeRegModtoY2(a,b,False)
	P = changeEvenDegtoOddDeg(a,b,1) 
	return P


def localht(P, Q, R, S, nus):
	H = Hfin
	L = []
	for (i,Fppoint) in enumerate([P, Q, R, S]):
		ycoord = solvefory(Fppoint[0] +p*nus[i], Fppoint[1],H)
		a1,a2 = changeRegModtoY2(Fppoint[0] + p*nus[i], ycoord,False)
		Pnu = changeEvenDegtoOddDeg(a1,a2,1)
		L.append(Pnu)

	D = [(1, L[0]), (-1,L[1])]
	E = [(1, L[2]), (-1,L[3])]
	h = XK.height(D, E)

	return h

#assume F_{2, 1}= Q_1 - Q_0
#assume now F_{2,2}= i(P)_1 - i(P)_0


#print(localht([0, -1], [1,0], [-1,0],[-1,0], [0,0,1,0])
# this D,F_{2,1}
#5*7 + 5*7^2 + 3*7^4 + 5*7^5 + 3*7^6 + 6*7^7 + 5*7^8 + 3*7^9 + 3*7^10 + 6*7^11 + 4*7^12 + 6*7^13 + O(7^15)

#print(localht([0, -1], [1,0], [0,0],[0,0], [0,0,1,0]))
#this is D, F_{2,2}
#4*7 + 3*7^2 + 6*7^3 + 2*7^4 + 4*7^6 + 2*7^7 + 4*7^8 + 3*7^9 + 4*7^10 + 4*7^11 + 7^12 + 7^13 + 4*7^14 + 4*7^15 + O(7^16)
#so this is P, b, i(P), i(P)

#print(localht([0, -1], [0,-1], [-1,0],[-1,0], [1,0,1,0]))
#this is F_{1,1} = P_1 - P_0 , F_{2,1} = Q_1  - Q_0
#5*7^3 + 3*7^4 + 7^5 + 2*7^6 + 2*7^7 + 2*7^8 + 7^9 + 4*7^10 + 5*7^11 + 7^12 + 2*7^13 + 7^14 + 4*7^15 + O(7^16)

#print(localht([1,0], [1,0], [0,0],[0,0], [1,0,1,0]))
#this is F_{1, 2} = b_1 - b_0 , F_{2,2} = i(P)_1, i(P)_0
#3*7^2 + 6*7^4 + 2*7^5 + 3*7^6 + 5*7^7 + 4*7^9 + 6*7^10 + 4*7^11 + 7^12 + 5*7^13 + 6*7^14 + 5*7^15 + O(7^16)

#print(localht([0, -1], [0,-1], [0,0],[0,0], [1,0,1,0]))
#this is F_{1, 1} = b_1 - b_0 , F_{2,2} = i(P)_1, i(P)_0
#4*7^2 + 7^4 + 3*7^5 + 2*7^6 + 4*7^8 + 6*7^9 + 7^10 + 6*7^11 + 3*7^12 + 4*7^13 + O(7^14)

print(localht([1,0], [1,0], [-1,0],[-1,0], [1,0,1,0]))
#this is F_{1,2} = b_1 - b_0, F_{2,1} = Q_1 - Q_0
#7^2 + 7^3 + 3*7^4 + 5*7^5 + 4*7^6 + 3*7^7 + 2*7^8 + 7^9 + 5*7^10 + 7^11 + 6*7^12 + 3*7^14 + O(7^16)


