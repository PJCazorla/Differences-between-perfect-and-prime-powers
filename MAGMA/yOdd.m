/*************************************************
** MODULE NAME: yOdd.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module includes all the necessary
**              functions to solve the generalised 
**              Lebesgue-Ramanujan-Nagell equation
**                  C1x^2 + q^alpha = y^n,
**              where q is a prime number and the exponent
**              n >= 3 is a prime number, with y being odd.
**************************************************/

load "solveThueMahler.m";

/******************************************************
** Name:findExponentsAlphaOdd
** Description: Given the two coefficients C1, q in the
**              Lebesgue-Ramanujan-Nagell equation, this 
**              function returns a list of all potential
**              exponents n >= 3, for which there may be
**              a solution. In the case where the only
**              potential solutions with n=7 correspond to
**              y = 3, 5 or 9, n=7 is not returned.
**
**              In addition, the exponents are split in two
**              lists, depending on whether n divides the
**              class number of Q(sqrt(-C1*q)) or not. 
**
**              Note that this function assumes that alpha 
**              is odd.
**
** Arguments: C1, q -> Coefficients of the equation as above.
**            
** Output: Two lists of potential exponents, as follows:
**
**         - primes: Potential values of n not dividing the 
**                   class number of Q(sqrt(-C1q)).
**
**         - badprimes: The rest of potential values of n.
******************************************************/
function findExponentsAlphaOdd(C1, q)

	/* Since n = 3, 5 are two of the possibilities in the theorem, 
       we include them in the potential primes. This is alternative
	   i) in the theorem, and note that n = 3 can be solved via 
	   looking at S-integral points, but we include it here 
	   anyway. */
	primes := {3, 5};
	
	/* All values of the exponent for which it is necessary
       to solve a Thue equation.	*/
	badprimes := {};
	
	/* Error handling */
	assert IsSquarefree(C1) and IsPrime(q) and Gcd(C1, q) eq 1;
						
	c := C1*q;
	
	/* If c/3 is a square, then we need to solve a Thue equation
	   for p = 3. */
	if IsSquare(c/3) then
		Include(~badprimes, 3);
		Exclude(~primes, 3);
	end if;
						
	P<x> := PolynomialRing(Rationals());
	K := NumberField(x^2+c);
						
	/* We compute all divisors of the class number of Q(-c). 
	   This is alternative iii) in the theorem. */
	for p in PrimeDivisors(ClassNumber(K)) do
		if p ge 3 then
			badprimes := badprimes join {p};
		end if;
	end for;
				
	/* There is no need to consider primes verifying alternative
	   (iv) in the theorem, since there are no relevant primes. */

	/* Since all primes dividing the class number will require the
	   solution of Thue equations, we remove these from the list
	   primes. */
	primes := primes diff badprimes;
	
	return primes, badprimes;
	
end function;

/******************************************************
** Name:findExponentsAlphaEven
** Description: Given the two coefficients C1, q in the
**              Lebesgue-Ramanujan-Nagell equation, this 
**              function returns a list of all potential
**              exponents n >= 3, for which there may be
**              a solution. In the case where the only
**              potential solutions with n=7 correspond to
**              y = 3, 5 or 9, n=7 is not returned.
**
**              In addition, the exponents are split in two
**              lists, depending on whether n divides the
**              class number of Q(sqrt(-C1*q)) or not. 
**
**              Note that this function assumes that alpha 
**              is even.
**
** Arguments: C1, q -> Coefficients of the equation as above.
**            
** Output: Two lists of potential exponents, as follows:
**
**         - primes: Potential values of n not dividing the 
**                   class number of Q(sqrt(-C1q)).
**
**         - badprimes: The rest of potential values of n.
******************************************************/
function findExponentsAlphaEven(C1, q)

	/* Since n = 3, 5 are two of the possibilities in the theorem, 
       we include them in the potential primes. This is alternative
	   i) in the theorem, and note that n = 3 can be solved via 
	   looking at S-integral points, but we include it here 
	   anyway. */
	primes := {3, 5};
	
	/* All values of the exponent dividing the class number */
	badprimes := {};
	
	/* Error handling */
	assert IsSquarefree(C1) and IsPrime(q) and Gcd(C1, q) eq 1;
						
	c := C1;
	
	/* If c/3 is a square, then we need to solve a Thue equation
	   for p = 3. */
	if IsSquare(c/3) then
		Include(~badprimes, 3);
		Exclude(~primes, 3);
	end if;
						
	P<x> := PolynomialRing(Rationals());
	K := NumberField(x^2+c);
						
	/* We compute all divisors of the class number of Q(-c). 
	   This is alternative iii) in the theorem. */
	for p in PrimeDivisors(ClassNumber(K)) do
		if p ge 3 then
			badprimes := badprimes join {p};
		end if;
	
	end for;
				
	/* We check for alternative (iv) in the theorem here. First, 
        if q = 2, there are no relevant primes in (iv). Otherwise,
        l = q is the only relevant prime.		*/
	if not (q eq 2) then
		for p in PrimeDivisors(q-LegendreSymbol(-c, q)) do
			if p ge 3 then
				primes := primes join {p};
			end if;
		end for;
	end if;
	   

	/* Since all primes dividing the class number will require the
	   solution of Thue equations, we remove these from the list
	   primes. */
	primes := primes diff badprimes;
	
	return primes, badprimes;
	
end function;

/******************************************************
** Name:checkSolutionsForN7
** Description: Given the two coefficients C1, q in the
**              Lebesgue-Ramanujan-Nagell equation, this 
**              function returns all solutions with n=7
**              and y = 3, 5 or 9. These correspond to
**              alternative ii) in the theorem.
**
** Arguments: C1, q -> Coefficients of the equation as above.
**            
** Output: Set of tuples (C1, C2, x, y, alpha, 7), where (x,y) are 
**         solutions of C1x^2+C2 = y^7 and y=3, 5, or 9.
******************************************************/
function checkSolutionsForN7(C1, q)

	solutions := {};
	
	/* Error handling */
	assert IsSquarefree(C1) and IsPrime(q) and Gcd(C1, q) eq 1;
	
	/* We just check every possible value of y, and check whether the
	   corresponding x is integral, greater than 0 and the coprimality
	   condition is satisfied. For each value, we need to consider all 
	   possible alphas less than 7*log_q(y). */
	   
	for y in [3,5,9] do
		alphaBound := Floor(7*Log(q, y));
		
		for alpha in [1..alphaBound] do
			x0 := Sqrt(((y^7-q^alpha)/C1));
			if IsIntegral(x0) and x0 gt 0 and Gcd(Gcd(Integers()!x0, y), q) eq 1 then
				solutions := solutions join {[C1, q, Integers()!x0, y, alpha, 7]};
			end if;
		end for;
	end for;

	return solutions;

end function;

/******************************************************
** Name:localRoots
** Description: Given an integer polynomial and a prime
**              q, this function returns the highest n such that
**              f has a root modulo q^n.
**
** Arguments: f -> Polynomial with integer coefficients.
**            q -> A prime number. 
**            
** Output: The biggest n such that f = 0 mod q^n has a 
**         solution, or Infinity if there is no such n.
******************************************************/
function localRoots(f, q)

	/* We begin by simplifying f as much as possible. */
	P<X> := PolynomialRing(Integers());
	commonFactor := Gcd(Coefficients(f));
	
	fSimplified:= P!(f div commonFactor);
	
	Zp := pAdicRing(q);
	Q<T> := PolynomialRing(Zp);
	
	fAux := fSimplified;
	deg := Degree(fAux);
	an := LeadingCoefficient(fAux);
	
	while not IsUnit(Zp!an) do
		fAux -:= an*X^deg;
		deg := Degree(fAux);
		an := LeadingCoefficient(fAux);
	end while;
	
	rt := Roots(Q!fAux);
	
	/* If the polynomial has a q-adic root, then it will
	   have a root mod q^n for all n. */
	if rt eq [] then
		n := 1;
		
		/* If not, we iterate until we find the relevant
		   value of n, and return it. */
		while true do 

			roots := false;
			
			for i in [0..q^n-1] do
				if (Evaluate(fSimplified, i) mod q^n eq 0) then
					roots := true;
					break;
				end if;
			end for;
			
			if not roots then
				return n-1;
			end if;
			
			n +:= 1;
		end while;
		
	
	else
		return Infinity();
	end if;


end function;

/******************************************************
** Name: findSolutionsAlphaGoodPrimes
** Description: Given the two coefficients C1, q and an
**              exponent n in the generalised Lebesgue-Ramanujan-Nagell
**              equation
**                 C1x^2 + q^alpha = y^n,
**              this function computes all solutions under the assumption
**              that y is odd. It is necessary to specify the parity of 
**              the exponent alpha. 
**              Solutions are returned in the format:
**                (C1, C2, x, y, alpha, n).
**
** Arguments: C1, q -> Coefficients of the equation as above.
**            n -> Exponent of the equation. 
**            alphaOdd -> A boolean value indicating whether alpha is odd.
**            
** Output: All solutions where y is odd.
******************************************************/
function findSolutionsAlphaGoodPrimes(C1, q, n, alphaOdd)

	solutions := {};
	
	/* Error handling */
	assert IsSquarefree(C1) and IsPrime(q) and Gcd(C1, q) eq 1;
	assert IsPrime(n) and n ge 3;
	
	/* We define the quadratic field Q(-c) on which
	   we will need to work. This will depend on whether
	   alpha is odd or even. In both cases, k will be such that
	   alpha = 2k+1, or alpha = 2k. */
	   
	if alphaOdd then 
		c := C1*q;
	else 
		c := C1;
	end if;
	
	K<a> := QuadraticField(-c);
	
	/* We check that n is indeed a good exponent. */
	assert not((ClassNumber(K) mod n) eq 0);
	assert (not(n eq 3) or not(IsSquare(c/3)));
	
	/* We define three rings of polynomials that we will need to
	   work with. */
	P<X, Y> := PolynomialRing(Integers(), 2);
	Q<r, s> := PolynomialRing(K, 2);
	R<T> := PolynomialRing(Integers());
	
	/* We will need to do slightly different things depending on 
	   whether -c is congruent to 1 modulo 4 or not, so we control
	   this here.	   */
	includeTwo := ((-c) mod 4) eq 1;

	/* We compute the left-hand side of the polynomial that we 
	   need to work with. This is the same in all circumstances 
	   and is a polynomial with integer coefficients on two variables. */
	fs := P!(Q!(((r+s*a)^n-(r-s*a)^n)/(2*s*a)));
	
	/* PART 1: This includes the situations where s = +-1, +-2 and we 
			   have to deal with Thue-Mahler equations. The situations
			   changes slightly depending on the congruence class of c
			   mod 4. */
			   
	if includeTwo then 
		rhs := 2^n*C1^((n-1) div 2);
		sValues := [1,2];
	else
		rhs := C1^((n-1) div 2);
		sValues := [1];
	end if;
		
	/* For each of the values of s0, we essentially have to solve
	   the Thue-Mahler equation
		f_s(X,Y) = rhs*q^k/s, 
	   under the additional assumption that s = +-s0 */
	for s0 in sValues do

		f := Evaluate(fs, [T, s0]);
		order := localRoots(f, q);
	
		/* If the polynomial f_s(T, s_0) has a qAdic root, we won't
		   be able to bound k by using elementary methods alone, so 
		   we do need to solve a Thue-Mahler equation.

		   If it doesn't, we will be able to exploit more elementary
		   methods to obtain a faster solution.
		*/
		if order eq Infinity() then
			alist := Reverse(Coefficients(f));
			a := rhs div s0;
			primelist := [q];
				
				
			/* If the polynomial is reducible, the situation simplifies considerably, 
			   since, given an expression of the form:
				f_1(r)f_2(r)...f_n(r) = a*q^k,
			   we may compute the Gcd(f_i), which will be 1. It is then sufficient
			   to look for roots for each of the factors. */
			   
			if not IsIrreducible(f) then
				sols1 := {};
				sols2 := {};
				
				factors := Factorisation(f);
				for factor in factors do
					poly := factor[1];
					for divisor in Divisors(AbsoluteValue(a)) do 
						if Gcd(divisor, a div divisor) eq 1 then
							for r1 in Roots(poly-divisor) do
								k := Valuation(Evaluate(f, r1[1]), q);
								sols1 := sols1 join  {[r1[1], 1, k]};
							end for;
							
							for r2 in Roots(poly+divisor) do 
								k := Valuation(Evaluate(f, r2[1]), q);
								sols2 := sols2 join {[r2[1], 1, k]};
							end for;
						end if;
					end for;
				end for;
				
			else
				/* Otherwise, we solve the two Thue-Mahler equations corresponding to a choice of 
				   sign. Since we have substituted the value of s_0 in the polynomial
				   defining the Thue-Mahler equation, we will only be concerned with 
				   solutions with s = 1, so we may assume that it is coprime with 
				   any coefficient. */
				sols1 := solveThueMahler(alist, a, primelist : coprime := true);
				sols2 := solveThueMahler(alist, -a, primelist : coprime :=  true);
			end if;
				
			for sol in sols1 join sols2 do
				rsol:= sol[1];
				ssol := sol[2];
				ksol := sol[3];
					
				/* As mentioned above, the only solutions that we are interested in 
				   are those where s = 1, since they correspond to the appropiate 
				   value of s0. 
				   */
				if ssol eq 1 then
						
					/* We reconstruct the values of x, y appropiately. */
					if includeTwo then 
						y := (rsol^2+c*s0^2)/(4*C1);
					else
						y := (rsol^2+c*s0^2)/C1;
					end if;
							
					if alphaOdd then 
						alpha := 2*ksol + 1;
					else 
						alpha := 2*ksol;
					end if;
					
					x2 := (y^n-q^(2*ksol))/C1;
							
					sq, x := IsSquare(x2);
							
					if IsIntegral(y) and sq and IsIntegral(x) and x gt 0 then 
						x := Integers()!x;
						y := Integers()!y;
						
						/* If all conditions are satisfied, we add the solution to 
						   our list. */
						if Gcd(C1*x, y) eq 1 and Gcd(q, y) eq 1 and (alphaOdd or alpha gt 0) then
							solutions := solutions join {[C1, q, x, y, alpha, n]};
						end if;
					end if;
						
				end if;
				
			end for;
		
		/* In this situation, k is automatically bounded above, by the maximum k_0
		   such that f_s(T, s0) has a root modulo q^k_0, so we only need to look 
		   for integer roots for all possibilities. */
		else
		
			for k in [0..order] do
				/* We compute the roots for the two relevant signs and all rele-
				   vant exponents. */
				rts1 := Roots(f-(rhs div s0)*q^k);
				rts2 := Roots(f+(rhs div s0)*q^k);
				
				/* For every root, we reconstruct all solutions as appropiate. */
				for rt in rts1 cat rts2 do
					r0 := rt[1];
					
					if includeTwo then 
						y := (r0^2+c*s0^2)/(4*C1);
					else
						y := (r0^2+c*s0^2)/C1;
					end if;
					
					if alphaOdd then
						alpha := 2*k+1;
					else
						alpha := 2*k;
					end if;
					
					x2 := (y^n-q^alpha)/C1;
						
					sq, x := IsSquare(x2);
						
					if IsIntegral(y) and sq and IsIntegral(x) and x gt 0 then 
						x := Integers()!x;
						y := Integers()!y;
						if Gcd(C1*x, y) eq 1 and Gcd(q, y) eq 1 and (alphaOdd or alpha gt 0) then
							solutions := solutions join {[C1, q, x, y, alpha, n]};
						end if;
					end if;
						
				end for;
				
				
			end for;
		end if;
		
	end for;
	
	/* PART 2: This includes the situations where q | s and we 
			   have to deal with Thue equations. The situations
			   changes slightly depending on the congruence class of c
			   mod 4. */
	   
	/* To simplify the readability of the code, we will write the 
	   right-hand side in two parts, so that rhs = rhsBase*fact, 
	   for some fact in rhsFactors. From there onwards, we simply have
	   to solve the Thue equation:
		f_s(X, Y) = +-rhs*q^k,
	   under the assumption that q| Y. */
		   
	/* Note: the correspondences between the rhsFactors and the 
			 values of s if (-c) is congruent to 1 mod 4, 
			 is the following:
			 
			 rhsFactor = 1 -> s = 2*q^k,
			 rhsFactor = 2 -> s = q^k,
			 
			 rhsFactor = q -> s = 2*q^(k-1),
			 rhsFactor = 2q -> s = q^(k-1),
			 
			 with the last two possibilities only being possible 
			 if q | n. Note that, in all cases, s*rhsFactor = 2*q^k. */
	if includeTwo then 
		rhsBase := 2^(n-1)*C1^((n-1) div 2);
		rhsFactors := [1, 2];
		
		if ((n  mod q) eq 0) then
			rhsFactors := rhsFactors cat [q, 2*q];
		end if;
		
	/* Note: the correspondences between the rhsFactors and the 
			 values of s if (-c) is notcongruent to 1 mod 4, 
			 is the following:
			 
			 rhsFactor = 1 -> s = q^k,
			 
			 rhsFactor = q -> s = q^(k-1),
			 
			 with the last possibility only being possible 
			 if q | n. Note that in all cases, s*rhsFactor = q^k. */
	else
		rhsBase := C1^((n-1) div 2);
		rhsFactors := [1];
		
		if ((n  mod q) eq 0) then
			Append(~rhsFactors, q);
		end if;
		
	end if;
		
	/* For each of the factors, we solve the relevant Thue
	   equation */
	for fact in rhsFactors do
		
		rhs := rhsBase*fact;
		
		/* We have to pick a sign, so we have two Thue equations to 
		   solve. The left-hand side is the same for both. Before 
           solving the Thue equation, and exploiting the fact that 
           q^k (or q^(k-1)) | s, we can try to bound the exponent k-1
           by using modulo q techniques.		   */
		order1 := localRoots(Evaluate(fs, [T, 0])-rhs, q);
		order2 := localRoots(Evaluate(fs, [T, 0])+rhs, q);
		Th := Thue(Evaluate(fs, [T, 1]));

		if order1 lt Infinity() then

			sols1 := [];
						
			if (fact mod q) eq 0 then
				kmax := (order1+2) div 2;
			else
				kmax := order1 div 2;
			end if;
			
			for k in [0..kmax] do
				if includeTwo then
					s0 := (2*q^k) div fact;
				else
					s0 := q^k div fact;
				end if;
				
				rt := Roots(Evaluate(fs, [T, s0])-rhs);
				
				for r0 in rt do 
					Append(~sols1, [r0[1], s0]);
				end for;
				
			end for;

		else
			try
				sols1 := Solutions(Th, rhs);
			catch e
				print "There is an error when solving the Thue equation with C1=", C1, ", q=", q, ", alpha odd and n=", n;
				print e;
			end try;
		end if;
		
		if order2 lt Infinity() then
			
			sols2 := [];
						
			if (fact mod q) eq 0 then
				kmax := (order2+2) div 2;
			else
				kmax := order2 div 2;
			end if;
			
			for k in [0..kmax] do
				if includeTwo then
					s0 := (2*q^k) div fact;
				else
					s0 := q^k div fact;
				end if;
				
				rt := Roots(Evaluate(fs, [T, s0])+rhs);
				
				for r0 in rt do 
					Append(~sols2, [r0[1], s0]);
				end for;
				
			end for;

		else
			try
				sols2 := Solutions(Th, rhs);
			catch e
				print "There is an error when solving the Thue equation with C1=", C1, ", q=", q, ", alpha even and n=", n;
				print e;
			end try;
		end if;
			
		/* For each solution, we need to have that q | s. In this case,
		   we may reconstruct k as the q-valuation of s, or the q-valuation
		   of s +1, depending on the above correspondence. */	
		
		for sol in [x: x in sols1] cat [x: x in sols2] do
			rsol := sol[1];
			ssol := sol[2];
			
			if (ssol mod q) eq 0 and ssol gt 0 then
				if (fact mod q) eq 0 then
					k := Valuation(ssol, q)+1;
				else
					k := Valuation(ssol, q);
				end if;
				
				/* We reconstruct the values of y and x as appropiate. */
				
				if includeTwo then 
					y := (rsol^2+c*ssol^2)/(4*C1);
				else 	
					y := (rsol^2+c*ssol^2)/C1;
				end if;
				
				if alphaOdd then
					alpha := 2*k+1;
				else
					alpha := 2*k;
				end if;
				
				x2 := (y^n-q^alpha)/C1;
						
				sq, x := IsSquare(x2);
						
				if IsIntegral(y) and sq and IsIntegral(x) and x gt 0 then 
					x := Integers()!x;
					y := Integers()!y;
					if Gcd(C1*x, y) eq 1 and Gcd(q, y) eq 1  and (alphaOdd or k gt 0) then
						solutions := solutions join {[C1, q, x, y, alpha, n]};
					end if;
				end if;

			end if;
				
			
		end for;
			
	end for;

	
	return solutions;

end function;

/******************************************************
** Name: solveThueMahlerNotCoprime
** Description: Given the list of coefficients, primes and independent
**              coefficient of a Thue-Mahler equation:
**                F(x, y) = a*q_1^k_1*q_2^k_2...q_n^k_n,
**              this function returns all solutions (x,y, k_1, ..., k_n),
**              including those for which x,y are not coprime and k_i is minimal.
**
**              Note that we make use of Gherga-Siksek's Thue-Mahler solver.
**              Solutions are returned in the format:
**                (C1, C2, x, y, alpha, n).
**
** Arguments: alist, a, primelist -> Coefficients of the equation as above.
**
** Parameters: coprime -> Parameter indicating whether gcd(a_0, y) = 1 or not.
**            
** Output: All solutions to the Thue-Mahler equation with k minimal.
******************************************************/
function solveThueMahlerNotCoprime(alist, a, primelist : coprime := false)

	/* We find the degree of the Thue-Mahler equation. */
	n := #alist-1;
	sols := {};
	
	/* Note that for every divisor d of a, we would need to solve the equation
	   F(x,y) = (a/d)*q_1^k_1...q_n^k_n, with x, y coprime. This corresponds to
	   the case where d is an n-th power and d^(1/n) divides x, y. */
	for divisor in Divisors(AbsoluteValue(a)) do
	
		if divisor gt 1 then 
			pow, base, exp := IsPower(divisor);
		end if;
						
		/* If the divisor is not 1, we require the divisor to be a perfect n-power, and 
		   solve the corresponding Thue-Mahler equation with x,y coprime. The solutions
		   will be those coprime solutions multiplied by the relevant factor. */
		if divisor eq 1 or (pow and (exp mod n) eq 0) then
			solsCoprime := solveThueMahler(alist, a div divisor, primelist : coprime);
			sols := sols join {[base^(exp div n)*solcoprime[1], base^(exp div n)*solcoprime[2]] cat solcoprime[3..#primelist+2] : solcoprime in solsCoprime}; 
		end if;
	
	
	end for;

	return sols;

end function;

/******************************************************
** Name:generateThueMahlerYOdd
** Description: Given the two coefficients C1, q in the
**              generalised Lebesgue-Ramanujan-Nagell equation and a 
**              exponent n >= 3 which either divides the class
**              number of Q(sqrt(-c)) or n = 3 and c = 3,
**              this function returns all tuples (C1, q, x, y, alpha, n), 
**              where (x,y) is a solution to the generalised
**              Lebesgue-Ramanujan-Nagell equation with
**              y odd, by solving Thue-Mahler equations.
**
**              Note that the parity of alpha must be specified beforehand.
**
** Arguments: C1, q -> Coefficients of the equation as above.
**            n -> A fixed exponent on the equation, prime and >= 3.
**            alphaOdd -> Boolean value indicating whether alpha is odd.
**            
** Output: Set of tuples (C1, C2, x, y, alpha, n), where (x,y) are 
**         solutions of C1x^2+q^alpha = y^n.
******************************************************/
function generateThueMahlerYOdd(C1, q, n, alphaOdd)

	solutions := {};
	
	/* We set up the values differently, depending on 
	   if alpha is odd or not. */
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
	assert IsPrime(n) and n ge 3;
	assert ((ClassNumber(O) mod n) eq 0) or (n eq 3 and IsSquare(c div 3));
	
	/* We define several polynomial rings for technical conditions - 
	   The Thue solver requires the polynomial to have integer coefficients,
	   but in order to build the polynomials we need to be able to work with
	   polynomials in two variables over the number field K */
	P<U,V> := PolynomialRing(Rationals(), 2);
	P2<X, Y> := PolynomialRing(K, 2);
	P3<T> := PolynomialRing(Integers());
	P4 := PolynomialRing(Integers(), 2);
	
	/* We construct an ideal which is the product of all prime ideals over
	   C1 */
	fact := Factorisation(C1*O);
	
	I := 1*O;
	
	for el in fact do
		I := I*el[1];
	end for;
	
	/* We compute all class group representatives J_i to check for
	   which i we have that I*J_i^-n is a principal ideal */
  	
	reps := ClassGroupPrimeRepresentatives(O, 1*O);
	dom := Domain(reps);
	
	for el in dom do
		
		/* We check for principality of the ideal I*J_i^-n. */
		princ, gener := IsPrincipal(I*(reps(el))^(-n));
		
		if princ then
			
			/* We compute all relevant units of our number field. 
			   They will all be trivial, except if we are working in Q(sqrt(-3))
			   and the exponent is n = 3. */
			   
			if n eq 3 and c eq 3 then
				omega := (-1+a)/2;
				units := [1, omega, omega^2];
			else
				units := [1];
			end if;
			
			for mu in units do 
			
				/* We generate the element such that (C1x+q^ksqrt(-c)) = mu*gener*gamma^n. */
				if ((-c) mod 4) eq 1 then
					f := mu*gener*(X + Y*(1+a)/2)^n;
				else
					f := mu*gener*(X + Y*a)^n;
				end if;
				
				/* We build the real and imaginary parts of the previous equation. It will be 
				   sufficient to solve the imaginary part, when regarded as a Thue-Mahler 
				   equation. */
				coeffsReal := [Eltseq(x)[1] : x in Coefficients(f)];
				coeffsImaginary := [Eltseq(x)[2] : x in Coefficients(f)];
					
				fReal := 0;
				fImaginary := 0;
					
				for i in [0..n] do
					fReal := fReal + coeffsReal[i+1]*X^(n-i)*Y^(i);
					fImaginary := fImaginary + coeffsImaginary[i+1]*X^(n-i)*Y^(i);
				end for;
				
				fReal := P!fReal;
				fImaginary := P!fImaginary;
				
				/* In order for both polynomials to have integer coefficients, 
					we compute the smallest number which makes it an integer polynomial and multiply by it */
					
				denominatorReal := Lcm([Denominator(c) : c in coeffsReal]);
				denominatorImaginary := Lcm([Denominator(c) : c in coeffsImaginary]);

				fReal := P4!(denominatorReal*fReal);
				fImaginary := P4!(denominatorImaginary*fImaginary);
				
				/* We solve the Thue-Mahler equation. */
				alist := Coefficients(fImaginary);
				coeffA := denominatorImaginary;
				primelist := [q];

				/* CASE 1: The polynomial fImaginary is irreducible. Then, we know that it defines a 
				           Thue-Mahler equation, and it is enough to solve it, without assuming that 
						   x,y are coprime. */
				if IsIrreducible(fImaginary) then 
						sols := solveThueMahlerNotCoprime(alist, coeffA, primelist : coprime := false);
						
				/* CASE 2: The polynomial fImaginary is reducible. In this case, and since we may assume 
				           that all factors are irreducible and coprime, we try to reduce this to a so-
						   lution of a finite number of Thue equations. */
				else
					
					/* We simplify the equation by dividing both sides of the equation by 
					   their gcd. */
					gcdCoefficients := Gcd(alist);
					fImaginary := fImaginary div gcdCoefficients;
					gcdCoefficients := gcdCoefficients div q^Valuation(gcdCoefficients, q);
					
					/* If the polynomial has a factor which is not present in the right-hand side,
					   then trivially there are no solutions. */
					if not ((coeffA mod gcdCoefficients) eq 0) then 
						sols := {};
					else
						/* Otherwise, we consider each of the factors, and try to solve them. */
						sols := {};
						coeffA := coeffA div gcdCoefficients;
						fact := Factorisation(fImaginary);
						
						/* We can only work if the polynomial does not have more than one linear
                           factor.						*/
						if #[pol : pol in fact | Degree(pol[1]) eq 1] lt 2 then 
						
							for factor in fact do
								poly := factor[1];
								multiplicity := factor[2];
								
								/* We look for a polynomial whose degree is more than 1, and proceed
                                   to solve either a Thue or a Thue-Mahler equation. */
								if Degree(poly) gt 1 then 
								
									/* If the multiplicity is greater than 1, we simplify both sides by 
									   taking the appropiate 1^n-power. */
									if multiplicity gt 1 then 
										
										pow, base, exponent := IsPower(coeffA);
										
										if (not pow) or not((exponent mod multiplicity) eq 0) then
											continue;
										else
											coeffA := base^(exponent div multiplicity);
										end if;
									end if;
									
									/* If there no linear polynomials, we may solve Thue equations, by
									   coprimality and simply assuming that the q-power is in some other
									   factor. */
									if Min([Degree(pol[1]): pol in fact]) gt 1 then
										Th := Thue(Evaluate(poly, [T,1]));
									end if;
									
									/* We need to solve the equation for all possible divisors of the coefficient. */
									for divisor in Divisors(coeffA) do
									
										/* This condition ensures coprimality between all factors of the polynomial. */
										if Gcd(divisor, coeffA div divisor) eq 1 then
										
											/* If there are no linear factors, it is enough to solve Thue equations. */
											if Min([Degree(pol[1]): pol in fact]) gt 1 then
												solThue := Solutions(Th, divisor);
												for solutionThue in solThue do
													sols := sols join {[solutionThue[1], solutionThue[2], Valuation(Evaluate(fImaginary, solutionThue), q)]};
												end for;
												
												solThue := Solutions(Th, -divisor);
												for solutionThue in solThue do
													sols := sols join {[solutionThue[1], solutionThue[2], Valuation(Evaluate(fImaginary, solutionThue), q)]};
												end for;
												
											/* If there is a linear factors, since we cannot work with it, we need to assume 
                                               that all powers of q are in our relevant factor. */											
											else
												sols := sols join solveThueMahlerNotCoprime(Coefficients(poly), divisor, [q] );
												sols := sols join solveThueMahlerNotCoprime(Coefficients(poly), -divisor, [q]);
												
											end if;
										end if;
									
									end for;

								end if;
								
							end for;
							
						else
							print "One of the Thue-Mahler equation has too many linear factors.";
							return -1;
						end if;
						
					end if;
				
				end if; 
					
				/* For each of the values, we reconstruct the solution from the solution of 
				   the Thue-Mahler equation. */
				for solution in sols do
				
					k := solution[3];
					
					/* We reconstruct x from the solutions of the Thue-Mahler equation  */
					x := Evaluate(fReal, [solution[1], solution[2]])/(C1*denominatorReal);
					
					/* If x is an integer, we reconstruct y and check for all compatibility conditions */
					if IsIntegral(x) then
						
						x := Integers()!x;
						
						if alphaOdd then 
							alpha := 2*k+1;
						else
							alpha := 2*k;
						end if;
						
						y := (C1*x^2+q^alpha)^(1/n);
						
						if x gt 0 and IsIntegral(y) then
						
							y := Integers()!y;
							
							if Gcd(Gcd(C1*x, q), y) eq 1 and (alphaOdd or k gt 0) then 
								solutions := solutions join {[C1, q, x, y, alpha, n]};
							end if;
						end if;
					end if;
				end for;
			end for;
		end if;
	end for;
	
	return solutions;
	
end function;

/***************************************************************************+
***** Computation of all solutions in our range *****************************
****************************************************************************/

solutions := {};

for C1 in [1..20] do

	q := 1;
	while q lt 18 do 
	
		q := NextPrime(q);
		
		if IsSquarefree(C1) and Gcd(C1, q) eq 1 then
		
		print "C1=", C1, ", q=", q;
			
			expAlphaOdd, badexpAlphaOdd := findExponentsAlphaOdd(C1,q);
			expAlphaEven, badexpAlphaEven := findExponentsAlphaEven(C1, q);

			solutions := solutions join checkSolutionsForN7(C1, q);

			for n in expAlphaOdd do 
				if n gt 3 then 
					solutions := solutions join findSolutionsAlphaGoodPrimes(C1, q, n, true);
				end if;
			end for;

			for n in expAlphaEven do 
				if n gt 3 then 
					solutions := solutions join findSolutionsAlphaGoodPrimes(C1, q, n, false);
				end if;
			end for;

			for n in badexpAlphaOdd do
				if n gt 3 then 
					solutions := solutions join generateThueMahlerYOdd(C1, q, n, true);
				end if;
			end for;
			
			for n in badexpAlphaEven do
				if n gt 3 then 
					solutions := solutions join generateThueMahlerYOdd(C1, q, n, false);
				end if;
			end for;
			
		end if;
	end while;
end for;

for sol in Sort(SetToSequence(solutions)) do
	print "Solution: C1 =",sol[1],", q =",sol[2],", x =",sol[3],", y =",sol[4],", alpha =",sol[5], "n=", sol[6];	
end for;


/* TESTING

function bruteForceCheck(C1, p)

	solutions := {};
	for y in [x: x in [0..200] | IsOdd(x)] do
		for alpha in [1..10] do
			for n in [5..20] do 
				x2 := (y^n-p^alpha)/C1; 
				
				x := Sqrt(x2);
			
				if IsIntegral(x) then
					x := Integers()!x;
					if Gcd(x, y) eq 1 and Gcd(x, p) eq 1 and Gcd(y, p) eq 1 and IsPrime(n) then
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

for C1 in [1..20] do

	q := 1;
	while q le 18 do
	
		solutions := {};
		solutions2 := {};
		
		q := NextPrime(q);
		
		if IsSquarefree(C1) and Gcd(C1, q) eq 1 then
		
			expAlphaOdd, badexpAlphaOdd := findExponentsAlphaOdd(C1,q);
			expAlphaEven, badexpAlphaEven := findExponentsAlphaEven(C1, q);

			for n in expAlphaOdd do 
				if n gt 3 then 
					solutions := solutions join findSolutionsAlphaGoodPrimes(C1, q, n, true);
				end if;
			end for;

			for n in expAlphaEven do 
				if n gt 3 then 
					solutions := solutions join findSolutionsAlphaGoodPrimes(C1, q, n, false);
				end if;
			end for;

			for n in badexpAlphaOdd do
				if n gt 3 then 
					solutions := solutions join generateThueMahlerYOdd(C1, q, n, true);
				end if;
			end for;
			
			for n in badexpAlphaEven do
				if n gt 3 then 
					solutions := solutions join generateThueMahlerYOdd(C1, q, n, false);
				end if;
			end for;
			
			solutions2 := bruteForceCheck(C1, q);
			
			if solutions eq solutions2 and areSolutions(solutions) then
				goodPairs := goodPairs cat [[C1, q]]; 
				print "All good with C1=", C1, ", q=", q;
			else
				badPairs := badPairs cat [[C1, q]];
				print "Problems with C1=", C1, ", q=", q;
			end if;
		end if;
	
	end while;

end for;

*/