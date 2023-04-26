/*************************************************
** MODULE NAME: boundExponent.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module includes all the necessary
**              functions to bound the exponent in the 
**              generalised Lebesgue-Ramanujan-Nagell 
**              equation with prime powers:
**                C1x^2 + q^alpha = y^p.
**************************************************/

/********************************************************
********* Methods for bounding the exponent *************
********************************************************/

/******************************************************
** Name: preliminaryBound
** Description: Given a newform f arising modulo p from the 
**              Frey curve associated to the generalised Lebesgue-Ramanujan-Nagell
**              equation, this function finds a preliminary bound for the exponent p.
**
** Arguments: f -> Newform arising mod p from F.
**            nPrimes -> Number of coefficients Bl that we want to compute
**
** Output: Set of possible values >= 7 for the exponent p. 
**         {-1} if the method is unsuccessful.
******************************************************/
function preliminaryBound(f, nPrimes)
	
	l := 2;
	N := Level(f);
	
	bound := 0;
	primes := {};
	
	for j in [1..nPrimes] do
		
		l := NextPrime(l);
		while((N mod l) eq 0) do
			l := NextPrime(l);
		end while;
		
		/* Computation of the upper and lower limits of the set Sl. */
		limit := Floor(2*Sqrt(l));
	
		/* We access the l-th coefficient of the newform */
		cl := Coefficient(f, l);	
	
		/* Construction of the set Sl and computation of the second
		part of Bl'(f), corresponding to good reduction. */
		y := 1;
		for i in [-limit..limit] do
			if (i mod 2) eq 0 then
				y := y * Norm(i - cl);
			end if;
			
		end for;
		
		/* Computation of the second part of Bl'(f), corresponding to
		bad multiplicative reduction */
		x := Norm((l+1)^2 - cl^2);
		
		/* We compute Bl(f), by multiplying by l if necessary */
		if Degree(Parent(Coefficient(f, l))) eq 1 then
			Bl := Integers()!(x*y);
		else
			Bl := Integers()!(l*x*y);
		end if;
		
		bound := Gcd(Bl, bound);
	end for;

	if bound eq 0 then
		return {-1};
	else 
		for p in PrimeDivisors(bound) do
			if p gt 5 then
				primes := primes join {p};
			end if;
		end for;
		
		return primes;
	end if;
	
end function;

/******************************************************
** Name: imageOfInertia
** Description: Given a newform f arising modulo p from the 
**              Frey curve associated to the generalised Lebesgue-Ramanujan-Nagell
**              equation and the coefficient C1 of said equation, this function
**              tries to bound p by exploiting an image of inertia argument. In 
**              particular, no prime dividing C1 may divide the denominator of 
**              the j-invariant of the elliptic curve associated to f.
**
** Arguments: f -> Newform arising mod p from F. It must be rational for this
**                 method to work.
**            C1 -> Coefficient C1 in the generalised LRN equation.
**
** Output: Set of possible values >= 7 for the exponent p. 
**         {-1} if the method is unsuccessful.
******************************************************/
function imageOfInertia(f, C1) 

	assert IsSquarefree(C1);
	
	/* We first check if the newform is rational. If not,
	   this method is inapplicable. */
	rational := Degree(Parent(Coefficient(f, 1))) eq 1;
	if not rational then
		return {-1};
	end if;
	
	/* We build the elliptic curve associated to f and the 
	   denominator of the j-invariant. */
	E := EllipticCurve(f);
	D := Denominator(jInvariant(E));
	
	primes := {};
	bounded := false;
	
	/* For every prime divisor of C1, we have to check if it
	   divides the denominator of the j-invariant. */
	for p in PrimeDivisors(C1) do
	
		if (D mod p) eq 0 then
			bounded := true;
			
			if p gt 5 then 
				primes := primes join {p};
			end if;
		end if;
	
	end for;

	if not bounded then
		return {-1};
	else
		return primes;
	end if;

end function;

/******************************************************
** Name: quadraticTwistBound
** Description: Given a newform f arising modulo p from the 
**              Frey curve associated to the generalised Lebesgue-Ramanujan-Nagell
**              equation, the coefficient C1 of said equation and all newforms
**              of level N = 2C1^2q, this function aims to bound the 
**              exponent p by exploiting properties of the quadratic twist.
**              In particular, any bound will always be >= 13.
**
** Arguments: f -> Newform arising mod p from F. It must be rational for this
**                 method to work.
**            NFs -> All conjugacy classes of newforms of level N. This is only
**                   to minimise computation. 
**            C1 -> Coefficient C1 in the generalised LRN equation.
**
** Output: Set of possible values >= 7 for the exponent p. 
**         {-1} if the method is unsuccessful.
******************************************************/
function quadraticTwistBound(f, NFs, C1)

	assert IsSquarefree(C1);
	
	/* We first check if the newform is rational. If not,
	   while this method could be applicable, we get much
	   better bounds by looking at the preliminary bound. */
	rational := Degree(Parent(Coefficient(f, 1))) eq 1;
	if not rational then
		return {-1};
	end if;

	E := EllipticCurve(f);
	N := Conductor(E);
	
	/* Initially, our bound consists of all primes > 5 and 
	   < 17. */
	bound := false;
	primes := {7, 11, 13};

	/* In this set, we will keep all primes which arise from every
	   divisor of C1. */
	primesAux := {};
	
	/* We get a quadratic twist for each divisor l of C1. */
	for l in PrimeDivisors(C1) do
	
		primesl := {};
		
		/* We have to look only at those quadratic twists 
		   by d, congruent to 1 modulo 4 */
		if (l mod 4) eq 1 then
			d := l;
		else
			d := -l;
		end if;
		
		/* We construct the corresponding quadratic twist. */
		Eprime := QuadraticTwist(E, d);
		Nprime := Conductor(Eprime);
		
		/* If the conductors are different, then we are guaranteed to
		   find a good bound. */
		if not(Nprime eq N) then
			bound := true;
			
			p := 3;
			
			while (N mod p) eq 0 do
				p := NextPrime(p);
			end while;
			
			/* We have to check each newform, and try to compute the corresponding 
			   quantity to bound. */
			for newform in NFs do 
			
				/* Since the newform f' arises modulo p from the elliptic curve
				   E', we have that p divides this quantity. */
				quantity := Coefficient(newform[1], p)-TraceOfFrobenius(Eprime, p);
				
				/* This quantity may  be zero, but it will not be for all p, so if it 
				   is the case, we change p and recompute the quantity. */
				while(quantity eq 0) do 
				
					p := NextPrime(p);
					while (N mod p) eq 0 do
						p := NextPrime(p);
					end while;
				
					quantity := Coefficient(newform[1], p)-TraceOfFrobenius(Eprime, p);				
				
				end while;
				
				/* We simply add all primes >= 17 dividing the quantity. */
				for prime in PrimeDivisors(Integers()!Norm(quantity)) do
				
					if prime gt 13 then
						primesl := primesl join {p};
					end if;
				
				end for;
			
			
			end for;
				
				
		end if;
		
		/* We add the primes to the relevant list. */
		if primesAux eq {} then
			primesAux := primesl;
		else
			primesAux := primesAux meet primesl;
		end if;
	
	
	end for;
	
	if bound then
		return primes join primesAux;
	else
		return {-1};
	end if;
	
end function;

/******************************************************
** Name: GaloisTheoryBound
** Description: Given a newform f arising modulo p from the 
**              Frey curve associated to the generalised Lebesgue-Ramanujan-Nagell
**              equation, the two coefficients C1, q of said equation, the parity
**              of the exponent alpha and a number of primes to try, this function aims 
**              to bound the exponent p of the equation by exploiting Galois Theory arguments. 
**
** Arguments: f -> Newform arising mod p from F. It must be rational for this
**                 method to work.
**            C1, q -> Coefficients C1, q in the generalised LRN equation.
**            alphaOdd -> Boolean indicating if alpha is odd (true) or not (false)
**            nPrimes -> Number of primes that we want to use to try to bound 
**                       the prime p.
**
** Output: Set of possible values >= 7 for the exponent p. 
**         {-1} if the method is unsuccessful.
******************************************************/
function GaloisTheoryBound(f, C1, q, alphaOdd, nPrimes)

	/* We first check if the newform is rational. If not,
	   this method is inapplicable. */
	rational := Degree(Parent(Coefficient(f, 1))) eq 1;
	if not rational then
		return {-1};
	end if;
	
	E := EllipticCurve(f);
	N := Conductor(E);
	
	/* We set the exponent of q in the determinant modulo squares. */
	if alphaOdd then
		qExponent := 1;
	else
		qExponent := 0;
	end if;
	
	/* Initially, we have not bounded anything and the set is 
	   empty. */
	l := 2;
	bound := 0;
	primes := {};
	
	for j in [1..nPrimes] do
	
		l := NextPrime(l);
		
		/* By demanding that the discriminant is a square modulo l, we may ensure
		   that the Frey curve has full 2-torsion */
		while ((N mod l) eq 0) or (LegendreSymbol(-C1*q^qExponent, l) eq -1) do
			l := NextPrime(l);
		end while;
		
		/* Computation of corresponding Bl */
		limit := Floor(2*Sqrt(l));
	
		/* We access the l-th coefficient of the newform */
		cl := TraceOfFrobenius(E, l);	
	
		/* Construction of the set Sl and computation of the second
		part of Bl'(f), corresponding to good reduction. */
		y := 1;
		for i in [-limit..limit] do
		
			/* Note that now we may assume that the Frey curve has a
			   a point of order 4, so we may be more precise when 
			   computing the bound */
			if (i mod 4) eq ((l+1) mod 4) then
				y := y *(i - cl);
			end if;
			
		end for;
		
		/* Computation of the second part of Bl'(f), corresponding to
		bad multiplicative reduction */
		x := ((l+1)^2 - cl^2);
		
		/* We compute Bl(f), by multiplying by l if necessary */
		Bl := Integers()!(x*y);
		
		bound := Gcd(Bl, bound);
		
	end for;

	if bound eq 0 then
		return {-1};
	else 
		for p in PrimeDivisors(bound) do
			if p gt 5 then
				primes := primes join {p};
			end if;
		end for;
		
		return primes;
	end if;

end function;

/*

	for C1 in [x : x in [1..20] | IsOdd(x) and IsSquarefree(x)] do
	
		q := 2;
		
		while q le 17 do
			q := NextPrime(q);
			
			if (C1*q mod 8) eq 7 or (C1 mod 8) eq 7 then
			
				NFs := Newforms(CuspForms(2*C1^2*q));
				
				preliminaryNewforms := 0;
				imageNewforms := 0;
				quadraticNewforms := 0;
				galoisNewforms := 0;
				unboundableNewforms := 0;
				
				primes := {};
				
				
				for ff in NFs do
					f := ff[1];
					   
					ret := preliminaryBound(f, 100);
					if ret eq {-1} then
						ret := imageOfInertia(f, C1);
						if ret eq {-1} then
							ret := quadraticTwistBound(f, NFs, C1);
							if ret eq {-1} then
								
								ret1 := {};
								ret2 := {};
								
								if (C1*q mod 8) eq 7 then 
									ret1 := GaloisTheoryBound(f, C1, q, true, 100);
								end if;
								
								if (C1 mod 8) eq 7 then 
									ret2 := GaloisTheoryBound(f, C1, q, false, 100);
								end if;
								
								if ret1 eq {-1} or ret2 eq {-1} then
									ret := {-1};
									unboundableNewforms +:= 1;
								else 
									ret := ret1 join ret2;
									galoisNewforms +:= 1;
								end if;
							
							
							else
								quadraticNewforms +:= 1;
							end if;
							
						else
							imageNewforms +:= 1;
						end if;
						
					else
						preliminaryNewforms +:= 1;
					end if;
					
					if ret eq {-1} then
						print "The case C1=", C1, ", q=", q, "and f corresponding to the EC ", CremonaReference(EllipticCurve(f)), 
						" requires separate treatment via LFL.";
					else
						primes := primes join ret;
					end if;
				
				end for;
				
				print "--------------------------------------------";
				print "Summary of newforms for the case C1=", C1, ", q=", q, ":\n  TotalNumber: ", #NFs, ",\n  Bounded with preliminary method:", preliminaryNewforms, 
				"\n  Bounded with inertia arguments:", imageNewforms, "\n  Bounded with quadratic twists:", quadraticNewforms, "\n  Bounded with Galois theory:", galoisNewforms, 
				"\n  Unboundable: ", unboundableNewforms;			
				print "Primes to consider (irrespective of newform): ", primes;
				print "--------------------------------------------";				
			end if;
		end while;
	end for;








*/
