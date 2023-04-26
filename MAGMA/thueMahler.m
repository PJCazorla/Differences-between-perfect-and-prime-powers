/*************************************************
** MODULE NAME: thueMahler.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module includes a function to 
**              associate a Thue-Mahler equation to the
**              Lebesgue-Ramanujan-Nagell equation:
**                C1x^2 + q^alpha = y^p,
**              It is recommended that this is only used
**              for small p (p = 5, 7).
**************************************************/

load "solveThueMahler.m";
/******************************************************
** Name:generateThueMahlerYEven
** Description: Given the two coefficients C1, q in the
**              Lebesgue-Ramanujan-Nagell equation, as well as the
**              information on whether alpha is odd or even, 
**              exponent n, this function 
**              returns all tuples (C1, q, x, y, alpha, n), where
**              (x,y) is a solution to the generalised
**              Lebesgue-Ramanujan-Nagell equation:
**                C1x^2 + q^alpha = y^n,
**              with y even. This function essentially generates 
**              Thue-Mahler equations and solves them.
**
** Arguments: C1, q -> Coefficients of the equation as above.
**            alphaOdd -> Boolean value indicating whether alpha is odd or not.
**            n -> A fixed exponent on the equation.
**            
** Output: Set of tuples (C1, C2, x, y, alpha, n), where (x,y) are 
**         solutions of C1x^2+q^alpha = y^n.
******************************************************/

function generateThueMahlerYEven(C1, q, alphaOdd, n)

	solutions := {};
	
	/* The value of c is different depending on the parity of alpha. */
	if alphaOdd then
		c := C1*q;
	else
		c := C1;
	end if;
	
	/* We construct the field of interest K = Q(sqrt(-c)) and
	   the associated ring of integers. */
	K<a> := QuadraticField(-c);
	O := MaximalOrder(K);
	
	/* Error control */
	assert IsSquarefree(C1) and Gcd(C1, q) eq 1;
	assert IsPrime(n) and n gt 3;
	
	/* We define several polynomial rings for technical conditions - 
	   We need to be able to create the Thue-Mahler equation in the field
	   K and work with rational polynomials as well. */
	P<U,V> := PolynomialRing(Rationals(), 2);
	P2<X, Y> := PolynomialRing(K, 2);
	
	/* We construct an ideal which is the product of all prime ideals over
	   C1 */
	fact := Factorisation(C1*O);
	
	pc1 := 1*O;
	
	for el in fact do
		pc1 := pc1*el[1];
	end for;
	
	/* We need to work with each of the ideals over 2 */
	fact := Factorisation(2*O);
	
	for ideal in fact do 
	
		/* We build the relevant ideal I = pc1*p2^(n-2) */
		
		I := pc1*ideal[1]^(n-2);
		
		/* We compute all class group representatives J_i to check for
		   which i we have that I*J_i^(-n) is a principal ideal */
		reps := ClassGroupPrimeRepresentatives(O, 1*O);
		dom := Domain(reps);
		
		for el in dom do
			
			/* We check for principality of the ideal I*J_i^(-n). */
			princ, gamma := IsPrincipal(I*(reps(el)^(-n)));
			
			if princ then
			
			/* We generate the right hand side of the Thue polynomial. In particular, we 
				   find f such that f(X, Y) = d */
				   
				f :=  2*gamma*(X+Y*(1+a)/2)^n;
				
				coeffsReal := [Eltseq(x)[1] : x in Coefficients(f)];
				coeffsImaginary := [Eltseq(x)[2] : x in Coefficients(f)];
				
				/* In order for both polynomials to have integer coefficients, 
				we compute the smallest number which makes it an integer polynomial and multiply by it */
				denominatorReal := Lcm([Denominator(c) : c in coeffsReal]);
				denominatorImaginary := Lcm([Denominator(c) : c in coeffsImaginary]);
				
				coeffsReal := [Integers()!(denominatorReal*x) : x in coeffsReal];
				coeffsImaginary := [Integers()!(denominatorImaginary*x) : x in coeffsImaginary];
				
				/* We solve the associated Thue-Mahler equation, and recover all solutions */
				sols := solveThueMahler(coeffsImaginary, denominatorImaginary, [q] : coprime := false);

				/* In order to reconstruct the value of x, we need the real part of the polynomial. */
				fReal := 0;
				
				for i in [0..n] do
					fReal := fReal + coeffsReal[i+1]*X^(n-i)*Y^(i);
				end for;
				
				fReal := P!fReal;

				/* For each solution of the Thue-Mahler equation... */
				for solution in sols do

					/* We reconstruct the associated x and alpha from the solution of the Thue equation.  */
					
					/* This is equivalent to x := Real(Evaluate(f, solution)), but this guarantees
					   that the element x will be an integer to MAGMA. */
					x := Evaluate(fReal, [solution[1], solution[2]]);
					x := x/(denominatorReal*C1);
			
					/* We recover alpha from the solution of the Thue-Mahler equation. */
					if alphaOdd then
						alpha := 2*solution[3]+1;
					else
						alpha := 2*solution[3];
					end if;
					
					/* If x is an integer and alpha is greater than zero, we reconstruct y 
						and check for all compatibility conditions */
					if IsIntegral(x) and alpha gt 0 then					
						x := Integers()!x;
	
						y := (C1*x^2+q^alpha)^(1/n);
						
						if x gt 0 and IsIntegral(y) then
						
							x := Integers()!AbsoluteValue(x);
							y := Integers()!y;
							
							if Gcd(Gcd(C1*x, q), y) eq 1 then 
								solutions := solutions join {[C1, q, x, y, alpha, n]};
							end if;
						end if;
					end if;
				end for;
			
			end if;
			
		end for;
		
	end for;

	return solutions;

end function;


/* TESTING

function bruteForceCheck(C1, p)

	solutions := {};
	for y in [x: x in [0..1000] | IsEven(x)] do
		for alpha in [1..10] do
			for n in [5] do 
				x2 := (y^n-p^alpha)/C1; 
				
				x := Sqrt(x2);
			
				if IsIntegral(x) then
					x := Integers()!x;
					if Gcd(C1*x, y) eq 1 and Gcd(C1*x, p) eq 1 and Gcd(y, p) eq 1 and IsPrime(n) then
						solutions := solutions join {[Integers()!C1, Integers()!p, Integers()!x, Integers()!y, Integers()!alpha, n]};
					end if;
				end if;
			
			
			end for;

		end for;
	end for;

	return solutions;


end function;

function areSolutions(solutions)

	for sol in solutions do
		C1 := sol[1];
		q := sol[2];
		x := sol[3];
		y := sol[4];
		alpha := sol[5];
		n := sol[6];
		
		if not ((C1*x^2+q^alpha) eq y^n) then
			return false;
		end if;
	
	end for;
	
	return true;

end function;

goodPairs := [];
badPairs := [];

allSolutions := {};

for C1 in [x : x in [1..20] | IsOdd(x)] do

	q := 2;
	while q le 18 do
	
		solutions := {};
		solutions2 := {};
		
		q := NextPrime(q);
		
		if IsSquarefree(C1) and Gcd(C1, q) eq 1 then
		
			if (C1 mod 8) eq 7 then
				solutions := solutions join generateThueMahlerYEven(C1, q, false, 5);
				solutions := solutions join generateThueMahlerYEven(C1, q, false, 7);
			end if;
			
			if (C1*q mod 8) eq 7 then
				solutions := solutions join generateThueMahlerYEven(C1, q, true, 5);
				solutions := solutions join generateThueMahlerYEven(C1, q, true, 7);
			end if;
			
			solutions2 := bruteForceCheck(C1, q);
			
			if solutions eq solutions2 and areSolutions(solutions) then
				goodPairs := goodPairs cat [[C1, q]]; 
				allSolutions := allSolutions join solutions;
				print "All good with C1=", C1, ", q=", q;
			else
				badPairs := badPairs cat [[C1, q]];
				print "Problems with C1=", C1, ", q=", q;
			end if;
		end if;
	
	end while;

end for;

*/
