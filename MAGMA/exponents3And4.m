/*************************************************
** MODULE NAME: exponents3And4.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module includes all the necessary
**              functions to solve the generalised 
**              Lebesgue-Ramanujan-Nagell equation
**                  C1x^2 + q^alpha = y^n,
**              where q is a prime number, and n = 3,4.
**************************************************/

/******************************************************
** Name:solveForN3And4
** Description: Given the two coefficients C1, q in the
**              Lebesgue-Ramanujan-Nagell equation, this 
**              function returns a list of all solutions
**              (C1, q, x, y, alpha, n), where n=3 or n=4, and
**              such that x > 0, gcd(C1x, q, y) = 1.
**
**              This is performed by computing {q}-integral 
**              points on certain elliptic curves.
**
**
** Arguments: C1, q -> Coefficients of the equation as above.
**            
** Output: List of solutions of the equation with n=3 or n=4.
******************************************************/
function solveForN3And4(C1, q)

	solutions := {};
	
	/* Error handling */
	assert IsSquarefree(C1) and Gcd(C1, q) eq 1;	
	
	/* Case n = 3 */
	
	/* We find solutions by looking for S-integral points in 
	   the curve z^2 = t^3-C1^3*q^i, where i=0,1, 2, 3, 4, 5. 
	   Here, S = [q]. */
	   
	for i in [0..5] do
		E := EllipticCurve([0,0,0,0, -C1^3*q^i]);
		pts := SIntegralPoints(E, [q]);
		
		/* For each integral point (t,z), we have to check if 
	    the corresponding (x',y') = (|z|/C1^2, t/C1) is an
	    q-integral pair. If it is, we reconstruct the rele-
	    vant pair by removing denominators. */
	   
		for p in pts do
			
			x2 := AbsoluteValue(p[2]/C1^2);
			y2 := p[1]/C1;

			valx := Valuation(1*x2, q);
			valy := Valuation(y2, q);
			
			/* This ensures that the point is [q]-integral, but not integral and that 
			   the final solution (x,y) will verify gcd(x, q) = gcd(y, q) = 1. */
			if valx le 0 and (valx mod 3) eq 0 and valy le 0 and (valy mod 2) eq 0 and (valx/3 eq valy/2) then
				alpha := i - 3*valy;
				x := x2*q^(-valx);
				y := y2*q^(-valy);
				/* We check that the solutions satisfy our coprimality
			    condition and x > 0 */
				if IsIntegral(x) and IsIntegral(y) and x gt 0 then 
					x := Integers()!x;
					y := Integers()!y;
					if Gcd(Gcd(C1*x, q), y) eq 1 then
						solutions := solutions join {[C1, q, x, y, alpha, 3]};
					end if;
				end if;
			end if;
	    end for;
	end for;
	
	/* Case n = 4 */
	
	/* We find solutions by looking for S- integral points in 
	   the curve z^2 = t^3-C1^2*q^i*t for t=0,1,2,3. Here,
       we have that S = [q];	   */
	   
	for i in [0..3] do
		E := EllipticCurve([0,0,0,-C1^2*q^i, 0]);
		pts := SIntegralPoints(E, [q]);
		
		/* For each integral point (t,z), we have to check if 
	    the corresponding (x,y) = (|z|/(C1^2*sqrt(t/C1)), 
	    +sqrt(t/C1)) is a q-integral pair. If it is, we recons-
        truct the integer point by removing denominators.	*/
		
		for p in pts do 
			square, y2 := IsSquare(p[1]/C1);
			
			if square and y2 gt 0 then 
			
				/* We need the absolute value since the function S-integral 
				   points returns the points up to sign. */
				x2 := AbsoluteValue(p[2]/(C1^2*y2));

				valx := Valuation(x2, q);
				valy := Valuation(y2, q);		
				
				if valx le 0 and (valx mod 2) eq 0 and valy le 0 and (valx/2 eq valy) then
					alpha := i - 4*valy;
					x := x2*q^(-valx);
					y := y2*q^(-valy);
					
					/* We check that the solutions satisfy our coprimality
					condition and x > 0 */
					if IsIntegral(x) and IsIntegral(y) and x gt 0 then 
						x := Integers()!x;
						y := Integers()!y;
						if Gcd(Gcd(C1*x, q), y) eq 1 then
							solutions := solutions join {[C1, q, x, y, alpha, 4]};
						end if;
					end if;
				end if;
			end if;
			

		end for;
	
	
	
	end for;
	   
	return solutions;

end function; 

/********************************************************
** COMPUTATION OF SOLUTIONS *****************************
********************************************************/

/*

solutions := {};

for C1 in [1..20] do

	p := 20;
	while p lt 23 do 
	
		p := NextPrime(p);
		
		if IsSquarefree(C1) and Gcd(C1, p) eq 1 then
			solutions := solutions join solveForN3And4(C1, p);
		end if;
	end while;
end for;

for sol in Sort(SetToSequence(solutions)) do
	print "Solution: C1 =",sol[1],", q =",sol[2],", x =",sol[3],", y =",sol[4],", alpha =",sol[5], "n=", sol[6];	
end for;



/*

TESTING 
function bruteForceCheck(C1, p)

	solutions := {};
	for x in [0..10000] do
		for alpha in [0..10] do
			yn := C1*x^2+p^alpha;
			
			y3 := yn^(1/3);
			y4 := yn^(1/4);
			
			if IsIntegral(y3) then
				y3 := Integers()!y3;
				if Gcd(x, y3) eq 1 and Gcd(x, p) eq 1 and Gcd(y3, p) eq 1 then
					solutions := solutions join {[Integers()!C1, Integers()!p, Integers()!x, Integers()!y3, Integers()!alpha, 3]};
				end if;
			end if;
			
			if IsIntegral(y4) then
				y4 := Integers()!y4;
				if  Gcd(x, y4) eq 1 and Gcd(x, p) eq 1 and Gcd(y4, p) eq 1 then
					solutions := solutions join {[Integers()!C1, Integers()!p, Integers()!x, Integers()!y4, Integers()!alpha, 4]};
				end if;
			end if;
			
		end for;
	end for;

	return solutions;


end function;




for C1 in [1..20] do

	p := 1;
	for j in [0..10] do
	
		p := NextPrime(p);
		
		if IsSquarefree(C1) and Gcd(C1, p) eq 1 then
		
			solutions := solveForN3And4(C1, p);
			
			solutions2 := bruteForceCheck(C1, p);
			
			if solutions eq solutions2 then
				print "All good with C1=", C1, ", q=", p;
			else
				print "Problems with C1=", C1, ", q=", p;
			end if;
		end if;
		
	
	
	end for;

end for;
*/

