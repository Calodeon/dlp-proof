

// p is the characteristic: 2,3, or anything else
// in case p = 2 or 3, assumes the curve is ordinary
verify := procedure(p);

	if p eq 2 then

		Z := FiniteField(p);
		R0<A,B,xQ,yQ,x1,y1,z1> := PolynomialRing(Z,7);
		R<x,y> := PolynomialRing(R0,2);

		weier := x^3 + A*x^2 + B - x*y;

		// add two points (projective coordinates (x,y,z) = (P[1],P[2],P[3]))
		add := function(P,Q);
			x1 := (R!P[1])/(R!P[3]);
			y1 := (R!P[2])/(R!P[3]);
			x2 := (R!Q[1])/(R!Q[3]);
			y2 := (R!Q[2])/(R!Q[3]);

			X := x1 + x2;
			Y := y1 + y2;

			x3 := X + A + Y/X + (y1^2 + y2^2)/(x1^2 + x2^2);
			y3 := y1 + x3 + (x1 + x3)*Y/X;

			g := GCD(Denominator(x3), Denominator(y3));

			return [(Numerator(x3)*Denominator(y3)) div g, (Numerator(x3)*Denominator(x3)) div g, (Denominator(x3)*Denominator(y3)) div g];
		end function;

		neg := function(P);
			return [P[1], P[1]+P[2], P[3]];
		end function;

		// double a point (projective coordinates)
		dou := function(Q);
			x1 := Q[1]/Q[3];
			y1 := Q[2]/Q[3];

			x3 := (x1^4 + B)/x1^2;
			y3 := y1 + x3 + (x1^2 + y1)*(x1 + x3)/x1;

			g := GCD(Denominator(x3), Denominator(y3));

			return [(Numerator(x3)*Denominator(y3)) div g, (Numerator(x3)*Denominator(x3)) div g, (Denominator(x3)*Denominator(y3)) div g];
		end function;

	elif p eq 3 then

		Z := FiniteField(p);
		R0<A,B,xQ,yQ,x1,y1,z1> := PolynomialRing(Z,7);
		R<x,y> := PolynomialRing(R0,2);

		weier := x^3 + A*x^2 + B;

		// add two points (projective coordinates (x,y,z) = (P[1],P[2],P[3]))
		add := function(P,Q);
			x1 := (R!P[1])/(R!P[3]);
			y1 := (R!P[2])/(R!P[3]);
			x2 := (R!Q[1])/(R!Q[3]);
			y2 := (R!Q[2])/(R!Q[3]);

			L := (y2-y1)/(x2 - x1);

			x3 := L^2 - A - x1 - x2;
			y3 := L*(x1 - x3) - y1;

			g := GCD(Denominator(x3), Denominator(y3));

			return [(Numerator(x3)*Denominator(y3)) div g, (Numerator(x3)*Denominator(x3)) div g, (Denominator(x3)*Denominator(y3)) div g];
		end function;

		neg := function(P);
			return [P[1], -P[2], P[3]];
		end function;

		// double a point (projective coordinates)
		dou := function(Q);
			x1 := Q[1]/Q[3];
			y1 := Q[2]/Q[3];

			L := A*x1/y1;

			x3 := L^2 - A + x1;
			y3 := L * (x1 - x3) - y1;

			g := GCD(Denominator(x3), Denominator(y3));

			return [(Numerator(x3)*Denominator(y3)) div g, (Numerator(x3)*Denominator(x3)) div g, (Denominator(x3)*Denominator(y3)) div g];
		end function;

	else

		Z := RingOfIntegers();
		R0<A,B,xQ,yQ,x1,y1,z1> := PolynomialRing(Z,7);
		R<x,y> := PolynomialRing(R0,2);

		weier := x^3 + A*x + B;

		// add two points (projective coordinates (x,y,z) = (P[1],P[2],P[3]))
		add := function(P,Q);
			T0 := P[2]*Q[3];
			T1 := P[3]*Q[2];
			T := T0-T1;
			U0 := P[1]*Q[3];
			U1 := P[3]*Q[1];
			U := U0-U1;
			U2 := U^2;
			V := P[3]*Q[3];
			W := T^2*V - U2*(U0+U1);
			U3 := U*U2;
			return [U*W, T*(U0*U2 - W) - T0*U3, U3*V];
		end function;

		neg := function(P);
			return [P[1], -P[2], P[3]];
		end function;

		// double a point (projective coordinates)
		dou := function(Q);
			T := 3*Q[1]^2 + A*Q[3]^2;
			U := 2*Q[2]*Q[3];
			V := 2*U*Q[1]*Q[2];
			W := T^2 - 2*V;
			return [U*W, T*(V-W) - 2*(U*Q[2])^2, U^3];
		end function;

	end if;


	// given a polynomial f in R, eliminate all the even powers of y (mod the elliptic curve equation)
	// I.e., write f in the form g(x) + y*h(x)
	// Needs to be applied recursively when p = 2 because y appears in weier
	reduce := function(f);
		if (Degree(f,y) le 1) then
			return f;
		end if;
		co,mo := CoefficientsAndMonomials(f);
		mo := [(x^Degree(m,x)) * (weier^(Degree(m,y) div 2)) * y^(Degree(m,y) mod 2) : m in mo];
		return $$(&+[co[i]*mo[i] : i in [1..#co]]);
	end function;

	// given a REDUCED polynomial f in R, returns the highest degree monomials of the reduced form (mod the elliptic curve equation)
	lead_reduced := function(f);
		if IsZero(f) then
			return f;
		end if;
		co,mo := CoefficientsAndMonomials(f);
		degrees := [2*Degree(m,x)+3*Degree(m,y) : m in mo];
		// in reduced form, the monomials all have distinct degree
		degree, index := Maximum(degrees);
		return co[index]*mo[index];
	end function;

	// given a polynomial f in R, returns the highest degree monomials of the reduced form (mod the elliptic curve equation)
	lead := function(f);
		if IsZero(f) then
			return f;
		end if;
		co,mo := CoefficientsAndMonomials(f);
		degrees := [2*Degree(m,x)+3*Degree(m,y) : m in mo];
		degree, index := Maximum(degrees);
		g := R!0;
		while degree ge 0 do
			// we compute the term of degree "degree" in the reduced form
			indices := [i : i in [1..#co] | degrees[i] eq degree];
			if #indices gt 0 then
				g +:= &+[co[i]*mo[i] : i in indices];
			end if;
			g_red := reduce(g);
			g_lead := lead_reduced(g_red);
			// if the term of degree "degree" in the reduced form is non-zero, then it is the leading term
			if (2*Degree(g_lead,x)+3*Degree(g_lead,y)) eq degree then
				return g_lead;
			end if;
			// otherwise, the leading term has degree lower than expected (i.e., large degree terms cancelled each other)
			degree -:= 1;
		end while;
		return R!0;
	end function;


	reduce_fraction := function(L);
		if (IsZero(L[1]) or IsZero(L[2])) then
			return L;
		end if;
		g := GCD(L[1],L[2]);
		return [L[1] div g,L[2] div g];
	end function;

	P := [x,y,1];
	Q := [xQ,yQ,1];
	D := [x1,y1,z1];

	P_D := add(P,D);
	u := reduce_fraction([P_D[1],P_D[3]]); 

	du_dx := reduce_fraction([Derivative(u[1],x)*u[2] - u[1]*Derivative(u[2],x), u[2]^2]);
	du_dy := reduce_fraction([Derivative(u[1],y)*u[2] - u[1]*Derivative(u[2],y), u[2]^2]);

	D1 := [x1,y1,1];
	D2 := neg(add(D1,dou(P)));

	atDivisor := function(f,D);
		if IsZero(f) then
			return f;
		end if;
		co,mo := CoefficientsAndMonomials(f);
		co := [Evaluate(c, [A,B,xQ,yQ] cat D) : c in co];
		return &+[co[i]*mo[i] : i in [1..#co]];
	end function;

	du1_dx := [atDivisor(du_dx[1], D1), atDivisor(du_dx[2], D1)];
	du1_dy := [atDivisor(du_dy[1], D1), atDivisor(du_dy[2], D1)];
	du2_dx := reduce_fraction([atDivisor(du_dx[1], D2), atDivisor(du_dx[2], D2)]);
	du2_dy := reduce_fraction([atDivisor(du_dy[1], D2), atDivisor(du_dy[2], D2)]);

	L1 := reduce_fraction([du1_dx[1]*du2_dx[2] - du2_dx[1]*du1_dx[2], du1_dx[2]*du2_dx[2]]);
	L2 := reduce_fraction([du1_dy[1]*du2_dy[2] - du2_dy[1]*du1_dy[2], du1_dy[2]*du2_dy[2]]);

	g := GCD(L1[2],L2[2]);

	L := [	(L1[1])*(L2[2] div g), (L2[1])*(L1[2] div g)];

	M := Matrix([[Derivative(y^2-weier,x),Derivative(y^2-weier,y)],L]);
	det := reduce(Determinant(M));
	l1 := lead(det);
	l2 := lead(det - l1);

	if (p eq 2) or (p eq 3) then
		"In characteristic", p, "the leading term is", l1;
	else
		"In characteristic greater than 3 the two leading terms are", l1, "and", l2;
	end if;
end procedure;

verify(2);
verify(3);
verify(-1);



