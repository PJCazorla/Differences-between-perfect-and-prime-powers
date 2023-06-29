/*************************************************
** MODULE NAME: specificExponents.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module includes a function to 
**              use the modular method to prove that 
**              there are no solutions to the Lebesgue-Ramanujan-Nagell
**              equation 
**                C1x^2 + q^alpha = y^p,
**              for a specific value of p.
**************************************************/

/******************************************************
****************** AUXILIARY FUNCTIONS ****************
******************************************************/

/******************************************************
** Name: squaresModuloP
** Description: Given a prime p, this function returns all
**              non-zero squares modulo p, multiplied by
**              an optional factor.
**
** Arguments: p -> A prime number.
**
** Parameters: factor -> An optional factor which multiplies
**                       all non-zero squares.
**
** Output: A list of all values in {1, ..., p-1} which are 
**         squares, multiplied by a factor.
******************************************************/
function squaresModuloP(p : factor := 1)

	L := [];
	
	/* Safety check */
	assert IsPrime(p);
	
	/* We find a generator of all non-zero squares 
	   in Fp. */
      	
	generator := PrimitiveRoot(p);
	genSq := Modexp(generator, 2, p);
	
	/* We build all squares, beginning with the
	   element given by the optional parameter 
	   factor. */
	element := factor mod p;
	
	for i in [0..(p-3) div 2] do
		Append(~L, element);
		element := (element*genSq) mod p;
	end for;
	
	return L;

end function;

/******************************************************
** Name:rootsOfUnity
** Description: This auxiliary function computes and returns all
**              n-th roots of unity mod l, for some even n.
**
** Further reference: None.
**
** Arguments: n -> A positive integer, which is assumed to be even.
**            l -> A positive integer, which is assumed to be prime.
**
** Output: All n-th roots of unity mod. l.
******************************************************/
function rootsOfUnity(n, l)
	
	/* Safety check */
	assert IsEven(n);
	assert IsPrime(l);
	
	/* We find a generator for the unit group of Fl, 
	   which is cyclic of order l-1 */
	gen := PrimitiveRoot(l);
	
	/* We find the largest integer dividing both l-1 
	   and n. This is because the element g^(l-1)/d
	   will be a generator for the corresponding 
	   subgroup of elements of order n. */
	d := Gcd(l-1, n);
	gen2 := Modexp(gen, Integers()!((l-1)/d), l);
	
	/* We compute the corresponding elements */
	
	return {Modexp(gen2, i, l) : i in [0..d-1]};
	
end function;


/******************************************************
** Name:nextValue
** Description: This auxiliary function returns the next prime of the form 
**              l = 2kp + 1, where k > 0 and p is a given prime.
**
** Arguments: l -> A prime of the form 2k'p + 1.
**            p -> A prime.
**
** Output: The next prime of the form 2kp + 1.
******************************************************/
function nextValue(l, p)

	laux := l + 2*p;

	while not(IsPrime(laux)) do
		laux := laux+2*p;
	end while;

	return laux;
	
end function;

/**********************************************************************
****************** MAIN FUNCTIONS *************************************
**********************************************************************/

/******************************************************
** Name: symplecticMethod
** Description: Given a tuple (C1, q, p) for the generalised
**              Lebesgue-Ramanujan-Nagell equation
**                C1x^2+q^alpha = y^p,
**              this function returns a list of the possible values
**              of alpha mod p, under the assumption that p does not 
**              divide alpha.
**
**              Note that, if f is an irrational newform, this method is
**              not applicable, so we return all possible values of alpha
**              (again, assuming that p does not divide alpha).
**
** Arguments: p -> A fixed exponent, which is assumed to be a prime.
**            f -> Newform arising mod p from F. 
**            C1, q -> Coefficients C1, q in the generalised LRN equation.
**
** Output: A list of possible values of alpha mod p if f is rational.
**         All values {1, 2, ...,p-1} if f is irrational.
******************************************************/
function symplecticMethod(p, f, C1, q)

	/* Sanity checks on the arguments. */
	assert IsPrime(p);
	assert IsSquarefree(C1);
	assert Gcd(C1, q) eq 1;

	/* We first check if the newform is rational. If not,
	   this method is inapplicable so all values of alpha
       not congruent to 0 mod p are possible.	   */
	rational := Degree(Parent(Coefficient(f, 1))) eq 1;
	if not rational then
		return {1..p-1};
	end if;
	
	/* We construct the associated elliptic curve. We know that 
	   the primes of multiplicative reduction are 2 and q. */
	E := EllipticCurve(f);
	Delta := Discriminant(MinimalModel(E));
	
	v2 := Valuation(Delta, 2);
	vq := Valuation(Delta, q);
	
	/* According to the theory of symplectic Galois representations, 
		we have that ((2p-12)*alpha)/(v2*vq)) must be congruent to a 
	   square modulo p. Consequently, we return all values of alpha 
	   which verify this fact. */
	
	squareCandidate := -3*v2*vq;
	
	/* If the previous quantity is zero, we actually have no information
	   on the possible values of alpha. */
	if (squareCandidate mod p) eq 0 then
		return {1..p-1};
	end if;
	
	inverse := InverseMod(squareCandidate, p);
		
	return squaresModuloP(p : factor := inverse);
	
end function;

/******************************************************
** Name: modifiedKraus
** Description: This function tries to prove that there are no solutions to the equation
**              C1x^2 + q^alpha = y^p for a fixed value of p. This is done by combining
**              Kraus's method with information provided by the symplectic method.
**
**              NOTE: This method is very ineffective is p is large. It only makes sense
**                    to use this procedure if p is around (or less than) 10^4.
**
** Arguments: C1, q -> Coefficients of the equation as above.
**            p -> Fixed prime exponent.
**            alphaOdd -> Boolean value indicating whether alpha is odd or not.
**            f -> Newform which arises modulo p from our Frey curve.
**            tries -> Maximum number of primes to check.
**
** Parameters: quadraticTwists -> Boolean value indicating whether we want to rule 
**                                out all quadratic twists of the newform f.
**
** Output: true if the equation DOES NOT have any solutions.
**
**         false, alphaMod2P if we are unable to prove the non-existence of sols.
**                Here, alphaMod2P is the subset of possible values of alpha mod 2p
**                (which is often strictluy smaller than all values).
**         
*******************************************************/
function modifiedKraus(C1, q, p, alphaOdd, f, tries : quadraticTwists := true)

	/* Safety check on the arguments */
	assert IsPrime(q) and IsPrime(p);
	assert IsSquarefree(C1);
	assert Gcd(C1, q) eq 1;
	
	N := Level(f);
	
	/* We first determine if the newform is rational and hence arises
	from an elliptic curve. We do this mainly to speed up computations
	with the use of dedicated functions. */
	rational := Degree(Parent(Coefficient(f, 1))) eq 1;
	
	if rational then
		E := EllipticCurve(f);
	end if;
	
	/* This is the case where p does not divide alpha. 
	   In this situation, the symplectic method is applicable
	   (if f is rational) and provides information on alpha. */
	if (N mod q) eq 0 then
		alphaModP := symplecticMethod(p, f, C1, q);
	/* This is the case where p divides alpha. The only 
       possibility modulo p is alpha = 0.	*/
	else
		alphaModP := {0};
	end if;
	
	/* We combine the extra information on alpha in order to 
	   build the set of possible values of alpha modulo 2p. */
	if alphaOdd then
		alphaMod2P := {a+((a+1) mod 2)*p : a in alphaModP};
	else
		alphaMod2P := {a+(a mod 2)*p : a in alphaModP};
	end if;
	
	/* We apply Kraus's method, trying to find a prime l ruling 
	   out the existence of solutions. */
	l := 1;
	
	for i in [0..tries-1] do
	
		/* We try the next suitable prime of the for l = 2kp+1.  */
		l := nextValue(l, p);
		
		/* Here, we check if l is a prime not dividing the level N
		   and different from q. */
		suitable := (not ((N*q mod l) eq 0));
		
		/* In order for the prime to be suitable, we have to rule out 
		   the possibility l | y. We check that here. */
		if suitable then 
		
			if rational then 
				cl := FrobeniusTraceDirect(E, l);
			else
				cl := Coefficient(f, l);
			end if;
				
			if alphaOdd then
				suitable := suitable and ((LegendreSymbol(-q*C1, l) eq -1) or not (Integers()!(Norm(cl^2-4)) mod p) eq 0);
			else
				suitable := suitable and ((LegendreSymbol(-C1, l) eq -1) or not (Integers()!(Norm(cl^2-4)) mod p) eq 0);
			end if;
		end if;
		
		/* We iterate until we find a suitable prime, with the same conditions as above. */
		while not suitable do
			l := nextValue(l, p);
			
			/* If the prime l is too large, this is computationally unfeasible, so
			   we quit. */
			if ((l-1) div p) gt 1e3 then
				return false, {-1};
			end if;
							
			suitable := (not ((N*q mod l) eq 0));
		
			if suitable then 
				if rational then 
					cl := FrobeniusTraceDirect(E, l);
				else
					cl := Coefficient(f, l);
				end if;
				
				if alphaOdd then
					suitable := suitable and ((LegendreSymbol(-q*C1, l) eq -1) or not (Integers()!(Norm(cl^2-4)) mod p) eq 0);
				else
					suitable := suitable and ((LegendreSymbol(-C1, l) eq -1) or not (Integers()!(Norm(cl^2-4)) mod p) eq 0);
				end if;
			end if;
		end while;
		
		/* precomputations -> We will use these quantities extensively, 
           so we precompute them to speed up the process.*/
		   
		/* Roots of unity relevant in our case. */
		roots := rootsOfUnity((l-1) div p, l);
		
		/* We will use these quantities to define the Frey curve */
		c1inv := InverseMod(C1, l);
		inv4 := InverseMod(4, l);
		inv64 := InverseMod(64, l);
		
		/* If the newform is rational, it is useful to precompute #E. */
		if rational then 
			cardinalityE := l+1-cl;
		end if;
		
		/* We will store the beta which we can rule out in this set. */
		removedBeta := {};
				
		for beta in alphaMod2P do
		
			ruledOutBeta := true;
			qbeta := Modexp(q, beta, l);
			
			/* We need to iterate for every root of unity. */
			for r in roots do
		
				/* If there is no solution w to the equation
				   C1w^2 + q^beta = r mod l, we have nothing to check. */
				if not(LegendreSymbol((r-qbeta)*c1inv, l) eq -1) then 
				
					/* If there is a solution, we recover it. Note that, in principle, we 
                       would need to check both for w and for l-w. In this second case, the
                       elliptic curve F is a quadratic twist by -1 of the first one (over Fl). */
					w := Modsqrt((r-qbeta)*c1inv, l);
					
					/* We define the Frey curve. */
					F := EllipticCurve([FiniteField(l)! 1, inv4*(C1*w-1), 0, inv64*(C1^2*w^2+C1*qbeta), 0]);
					
					/* SHORTCUT to avoid computing #F unless strictly necessary. If n is large enough and 
                       f is rational, then we must have that #E(Fl) = #F(Fl), so for any point P on F(fl), we 
                       must have that #E(Fl)*P = 0. We check this here.		   */
					
					if rational and p^2 gt 4*l then 
						randomPoint := Random(F);
						if not(cardinalityE*randomPoint eq Identity(F)) and not((2*l+2-cardinalityE)*randomPoint eq Identity(F)) then 
							continue;
						end if;
					end if;
					
					/* If the shortcut has been unsuccessful, we do need to compute #F. We do 
                       so here.	*/
					cardF := #F;
					
					/* Here, we check the relevant condition for w. This condition rules
					   out all quadratic twists simultaneously and needs to be used 
					   if (-1/l) = -1, (q/l) = -1 or if we want to rule out all quadratic
					   twists. 					   */
					   
					if LegendreSymbol(-1, l) eq -1 or LegendreSymbol(q, l) eq -1 or quadraticTwists then 
						if (Integers()!(Norm(cl^2-(2-cardF)^2)) mod p eq 0) then
							ruledOutBeta := false;
							break;
						end if;
					else
						if (Integers()!(Norm(cl-(2-cardF))) mod p eq 0) then 
							ruledOutBeta := false;
							break;
						end if;
					end if;

				end if;
			
			end for;
		
			/* If we have successfully ruled out a value of beta, we remove it.*/
			if ruledOutBeta then
				removedBeta := removedBeta join {beta};
			end if;
		
		end for;
		
		alphaMod2P := alphaMod2P diff removedBeta;
						
		/* If there are no more values of alpha mod 2p, we conclude the algorithm. */
		if alphaMod2P eq {} then
			return true, {};
		end if;
		
	end for;

	/* If, after finishing the iteration, there are still values of alpha mod 2p, we 
	   fail. We return the corresponding values of alpha. */
	return false, alphaMod2P;

end function;

/******************************************************
** Name: ruleOutThueMahler
** Description: Given the three coefficients C1, q, p of the
**              generalised Lebesgue-Ramanujan-Nagell equation
**              C1x^2 + q^alpha = y^p, along with the parity of
**              alpha and a newform from which the solution arises
**              modulo p, this function aims to prove that the system
**              of Thue-Mahler equations given by:
**
**              f2(X, Y) = rhs2*x;
**              f3(X, Y) = rhs3*q^k;
**
**              does not have any solutions which give rise to solutions
**              of the Lebesgue-Ramanujan-Nagell equation. It does this
**              by working modulo l for as many primes l as specified 
**              by the argument.
**
** Arguments: C1, q -> Coefficients of the equation as above.
**            p -> Fixed exponent.
**            alphaOdd -> Boolean value indicating if alpha is odd or not.
**            nPrimes -> Maximum number of primes l to try.
**            newform -> Newform from which the solution arises modulo p. If modular
**                       is set to false, this is irrelevant.
**            f2, f3, rhs2 -> Coefficients of the Thue equation as above.
**
** Parameters: quadraticTwists -> Boolean value indicating whether we want to rule out
**                             all quadratic twists of the newform f simultaneously.
**
** Output: true if the method is successful (and hence the Thue equation does not
**              give rise to any solution). 
**         false if not.
******************************************************/
function ruleOutThueMahler(C1, q, p, alphaOdd, nPrimes, newform, f2, rhs2, f3, rhs3 : quadraticTwists := true) 
	
	/* We check the level of the newform and whether it is rational or not.
       If it is rational, we compute the elliptic curve E that is associated
       with f.	   */
	N := Level(newform);
	rational := Degree(Parent(Coefficient(newform, 1))) eq 1;
	
	if rational then
		E := EllipticCurve(newform);
	end if;
	
	/* This is the case where p does not divide alpha. 
	   In this situation, the symplectic method is applicable
	   (if f is rational) and provides information on alpha. */
	if (N mod q) eq 0 then
		alphaModP := symplecticMethod(p, newform, C1, q);
	/* This is the case where p divides alpha. The only 
       possibility modulo p is alpha = 0.	*/
	else
		alphaModP := {0};
	end if;
	
	/* We combine the extra information on alpha in order to 
	   build the set of possible values of alpha modulo 2p. */
	if alphaOdd then
		alphaMod2P := {a+((a+1) mod 2)*p : a in alphaModP};
	else
		alphaMod2P := {a+(a mod 2)*p : a in alphaModP};
	end if;
	
	/* We apply Kraus's method, trying to find a prime l ruling 
	   out the existence of solutions. */
	l := 1;
				
	/* We try as many primes l as specified in the argument */
	for i in [1..nPrimes] do
		
		/* We try the next suitable prime of the for l = 2kp+1.  */
		l := nextValue(l, p);
		
		/* Here, we check if l is a prime not dividing the level N
		   and different from q. */
		suitable := (not ((N*q mod l) eq 0));
		
		/* We iterate until we find a suitable prime, with the same conditions as above. */
		while not suitable do
			l := nextValue(l, p);
			
			/* If the prime l is too large, this is computationally unfeasible, so
			   we quit. */
			if ((l-1) div p) gt 1e3 then
				return false, {-1};
			end if;
					
			suitable := (not ((N*q mod l) eq 0));
		
		end while;
		
		/* precomputations -> We will use these quantities extensively, 
           so we precompute them to speed up the process.*/
		   
		/* Roots of unity relevant in our case. */
		roots := rootsOfUnity((l-1) div p, l);
		
		/* We precompute all traces of Frobenius. */
		if rational then 
			cl := FrobeniusTraceDirect(E, l);
		else
			cl := Coefficient(newform, l);
		end if;
			
		/* We will use these quantities to define the Frey curve */
		c1inv := InverseMod(C1, l);
		inv4 := InverseMod(4, l);
		inv64 := InverseMod(64, l);
		
		/* If -1 is a quadratic residue mod l, we can avoid some computations. The 
           same is true if q is a quadratic residue mod. l.		*/
		leg := LegendreSymbol(-1, l);
		legQ := LegendreSymbol(q, l);
		
		/* If the newform is rational, it is useful to precompute #E. */
		if rational then 
			cardinalityE := l+1-cl;
		end if;
		
		/* We will store the beta which we can rule out in this set. */
		removedBeta := {};
				
		/* As opposed to Kraus's method, we need to keep track of the 
		   values of w for each beta. We will do so in the associative
		   array pairs. */
		pairs := AssociativeArray();

		for beta in alphaMod2P do
		
			ruledOutBeta := true;
			qbeta := Modexp(q, beta, l);
			
			/* Here, we take into account the possibility that l | y. If this is possible, we simply
               add the two possible values of x mod l.			*/
			if ((LegendreSymbol(-qbeta*C1, l) eq 1) and (Integers()!(Norm(cl^2-4)) mod p) eq 0) then
				w := Modsqrt(-qbeta*c1inv, l);
				ruledOutBeta := false;
				
				/* We recover v differently depending on the parity of alpha. */
				if alphaOdd then
					v := (beta - 1) div 2;
				else
					v := beta div 2;
				end if;
				
				pairs[v] := [];
				
				Append(~pairs[v], w);
				Append(~pairs[v], l-w);
			end if;
		
			/* Case l does not divide y -> We iterate for each root of unity. */
			for r in roots do
			
				/* If there is no solution to the equation 
				   C1w^2 + q^beta = r (mod l), we don't have 
				   anything to do. */
				if not(LegendreSymbol((r-qbeta)*c1inv, l) eq -1) then 
				
					/* If there is a solution, we recover it. Note that 
					   the other solution would be l-w, and the corresponding 
					   elliptic curve is just a twist by -1 over Fl. */
					w := Modsqrt((r-qbeta)*c1inv, l);
					
					/* We define the elliptic curve Fbeta, w. */
					F := EllipticCurve([FiniteField(l)! 1, inv4*(C1*w-1), 0, inv64*(C1^2*w^2+C1*qbeta), 0]);
					
					/* SHORTCUT to avoid computing #F unless strictly necessary. If n is large enough and 
                       f is rational, then we must have that #E(Fl) = #F(Fl), so for any point P on F(fl), we 
                       must have that #E(Fl)*P = 0. We check this here.	
					   
					   NB: In this method, we expect n to be reasonably small, so it is unlikely that this 
                           shortcut is ever used. */
					
					if rational and p^2 gt 4*l then 
						randomPoint := Random(F);
						if not(cardinalityE*randomPoint eq Identity(F)) and not((2*l+2-cardinalityE)*randomPoint eq Identity(F)) then 
							continue;
						end if;
					end if;
					
					/* Computation of the quantities l+1-#F. If they satisfy
					   the relevant condition, we store the corresponding value of v (which
					   is the congruence class of k modulo p) and w. */
					   
					frobeniusF := 2-#F;
					
					/* In this case, we have to add at least one of w and l-w to 
					   the possible values. */
			     	if (Integers()!(Norm(cl^2-frobeniusF^2)) mod p) eq 0 then
						
						/* We recover v differently depending on the parity of alpha. */
						if alphaOdd then
							v := (beta - 1) div 2;
						else
							v := beta div 2;
						end if;
							
						/* In the first instance, we initialise the array. */
						if ruledOutBeta then
							ruledOutBeta := false;
							pairs[v] := [];
						end if;
							
						/* If the Legendre symbol (q/l) = -1, then we need to 
						   add both q and l-w, since we just know that the 
						   Frey curve is a quadratic twist of our considered
						   curve modulo l. If we want to rule out all quadratic 
						   twists simultaneously, we also need to do this. */
						if quadraticTwists or LegendreSymbol(q, l) eq -1 then 
							Append(~pairs[v], w);
							
							if not (w eq 0) then
								Append(~pairs[v], l-w);
							end if;
						
						/* In the other situation, we know that we need to add
						   at least one value. We determine which by studying 
                           the different traces of Frobenius.		   */
						else
							if (Integers()!(Norm(cl-frobeniusF)) mod p) eq 0 then
								Append(~pairs[v], w);
								
								if LegendreSymbol(-1, l) eq 1 then 
									Append(~pairs[v], l-w);
								end if;
							end if;
							
							if LegendreSymbol(-1, l) eq -1 and (Integers()!(Norm(cl+frobeniusF)) mod p) eq 0 then
								Append(~pairs[v], w);
							end if;
								
						end if;
							
					end if;
					
				end if;
			end for;
			
			/* If there are no possible values for beta mod 2p, we may
			   remove it from our list of possible values. */
			if ruledOutBeta then
				removedBeta := removedBeta join {beta};
			end if;
		end for;
		
		alphaMod2P := alphaMod2P diff removedBeta;

		/* Here, we look at the pair of Thue-Mahler equations and try to 
		   rule out the existence of a solution. */
		for v in Keys(pairs) do
		
			qv := Modexp(q, v, l);
			
			/* We solve the equation f3(U, V) = rhs3*q^v, mod l. Since we 
			   do not expect l to be too large, we do so simply by
			   inspection. */
			UVValues := [];
					
			for U in [0..l-1] do
				for V in [0..l-1] do
					lhs3 := Evaluate(f3, [U, V]) mod l;
					
					if ((lhs3-rhs3*qv) mod l) eq 0 then
						Append(~UVValues, [U, V]);
					end if;
				end for;
			end for;
		
			/* For each of the pairs (U, V) above, we check if the other
			   equation is satisfied modulo 2p for some of the possible 
			   values of w associated to v. If this is not the case, 
			   we may rule out the possibility of v being a value of k
			   mod p. */
			ruledOutV := true;
		
			for tuple in UVValues do
			
				lhs2 := Evaluate(f2, tuple) mod l;
				
				if ((rhs2 mod l) eq 0) and ((lhs2 mod l) eq 0) then 
					ruledOutV := false;
					break;
				else
					if (lhs2*InverseMod(rhs2, l) mod l) in pairs[v] then
						ruledOutV := false;
						break;
					end if;
				end if;
			end for;
			
			if ruledOutV then
				if alphaOdd then
					Exclude(~alphaMod2P, 2*v+1);
				else
					Exclude(~alphaMod2P, 2*v);
				end if;
			end if;
		
		end for;
		
		/* If there are no values of alphaMod2P, we conclude that there
		   are no solutions. */
		if alphaMod2P eq {} then
			return true, {};
		end if;
			
	end for;

	return false, alphaMod2P;
	
end function;


/******************************************************
** Name: modularThueMahler
** Description: Given a tuple (C1, q, n) for the generalised
**              Lebesgue-Ramanujan-Nagell equation
**                C1x^2+q^alpha = y^n,
**              as well as the parity of alpha, and a newform from arising modulo n 
**              from the Frey curve, this function aims to prove that there are no solutions
**              by showing that the associated Thue-Mahler equation has no solu-
**              tions compatible with the constraints of the modular method.
**
**              This method should only be used when p is small.
**
** Arguments: n -> A fixed exponent, which is assumed to be a prime > 5.
**            newform -> Newform arising mod p from F. It can be rational or irrational.
**            nPrimes -> Maximum number of primes to try in order to show that there
**                       are no solutions.
**            C1, q -> Coefficients C1, q in the generalised LRN equation as above
**            alphaOdd -> Boolean value indicating whether alpha is odd or not.
** Parameters: quadraticTwists -> Boolean value indicating whether we want to rule out
**                             all quadratic twists of the newform f simultaneously.
**
** Output: true if the modular Thue method guarantees that there are no solutions.
**         false if it fails to guarantee the non-existence of solutions.
******************************************************/
function modularThueMahler(C1, q, alphaOdd, n, newform, nPrimes : quadraticTwists := true)

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
	P<U,V> := PolynomialRing(Integers(), 2);
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

				/* We build the two polynomials that we need to work with. */
				fReal := 0;
				fImaginary := 0;
				
				for i in [0..n] do
					fReal := fReal + coeffsReal[i+1]*X^(n-i)*Y^(i);
					fImaginary := fImaginary + coeffsImaginary[i+1]*X^(n-i)*Y^(i);
				end for;
				
				fReal := P!fReal;
				fImaginary := P!fImaginary;
				
				/* We try to rule out the existence of a solution by showing that the system:
					fReal = C1*denominatorReal,
					fImaginary = denominatorImaginary*q^k,
				   has no solutions compatible with solutions to the Lebesgue-Ramanujan-Nagell
				   equation. */
				ret, ret2 := ruleOutThueMahler(C1, q, n, alphaOdd, nPrimes, newform, fReal, denominatorReal*C1, fImaginary, denominatorImaginary : quadraticTwists := quadraticTwists);

				if ret eq false then 
					return false;
				end if;
				
			end if;
			
		end for;
		
	end for;

	return true;

end function;

/**********************************************************
** Name:krausBiggerExponents
** Description: This function aims to prove that there are
**              no solutions to the generalised LRN equation:
**
**                C1x^2 + q^alpha = y^p,
**
**              by exploiting certain identities modulo L,
**              where L is one of the two primes above certain
**              rational prime l. This method is reasonably 
**              efficient but fails often for small values of 
**              p, so p should be reasonably big.
**
** Arguments: C1, q, p -> Coefficients of the equation, as above.
**            alphaOdd -> Boolean value indicating whether alpha is odd or not.
**            E -> Elliptic curve whose mod-p Galois representation is 
**                 isomorphic to the Frey curve.
**            tries -> Maximum number of primes to try before declaring failure.
**
** Output: true if the equation can be proved not to have any solutions.
**         false if not.
************************************************************/

function krausBiggerExponents(C1, q, alphaOdd, E, p, tries)

	
	/* We will work in K = Q(-c), and the value of c is different
	depending on the parity of alpha. */
	if alphaOdd then
		c := C1*q;
	else
		c := C1;
	end if;
	
	/* We construct the field of interest K = Q(sqrt(-c)) and
	   the associated ring of integers. We will also need 
	   its class number.*/
	K<a> := QuadraticField(-c);
	O := MaximalOrder(K);
	hK := ClassNumber(O);
	
	/* Error control */
	assert IsSquarefree(C1) and IsPrime(q) and Gcd(C1, q) eq 1;
	assert IsPrime(p) and p gt 5;
	
	/* We precompute the conductor of E. */
	N := Conductor(E);
	
	/* Preparation: The aim of this code is to determine i, j such that:
	    0 <= i, j <= hK-1,
		
		q*p2^j is principal (where q is the product of all ideals over C1,
		                     and p2 is an ideal over 2),
							 
		-2-pi-j is congruent to 0 modulo hk. */
		
	/* We construct the ideal q as above */
	fact := Factorisation(C1*O);
	
	qIdeal := 1*O;
	
	for el in fact do
		qIdeal := qIdeal*el[1];
	end for;
	
		
	/* We need to consider both ideals over 2, so we loop 
       over the two possibilities.	*/
	fact := Factorisation(2*O);
	
	for ideal in fact do 
	
		p2 := ideal[1];
		
		/* We determine j such that q*p2^j is principal and 
           the corresponding value of omega such that 
		   q*p2^j = <omega>. */
		for ii in [0..hK] do
			qp2Principal, qp2generator := IsPrincipal(qIdeal*p2^ii);
		
			if qp2Principal then 
				j := ii;
				omega := qp2generator;
				break;
			end if;
			
		end for;
		
		/* We determine i and, with it, the value of n*
		   that we need. */
		i := ((-2-j)*InverseMod(p, hK)) mod hK;
		
		n := (-2-j-p*i) div hK;
		
		/* We let p2^hK = <beta> */
		a, beta := IsPrincipal(p2^hK);
	
		/* We begin looking for primes l which will allow us
		   to show that there are no solutions. We look for as many 
		   primes as specified in the argument tries. */
		l := 1;
	
		for i in [0..tries-1] do
	
			/* We try the next suitable prime of the for l = tp+1.  */
			l := nextValue(l, p);
			
			/* Here, we check if l is a prime not dividing the level N,
               such that -c is a square modulo l, so that the prime 
			   l splits in Q(-c).*/
			suitable := (not ((N mod l) eq 0)) and LegendreSymbol(-c, l) eq 1;
			
			/* If this is the case, we also want l not to divide y. */
			if suitable then 
				cl := FrobeniusTraceDirect(E, l);
				suitable := suitable and not ((Integers()!(cl^2-4) mod p) eq 0);
			end if;
			
			/* We keep on looking until we find one prime with the three conditions
			   above. */
			while not suitable do
				l := nextValue(l, p);
				suitable := (not ((N mod l) eq 0)) and LegendreSymbol(-c, l) eq 1;
			
				/* If the prime l is too large, this is computationally unfeasible, so
			   we quit. */
				if ((l-1) div p) gt 1e3 then
					return false;
				end if;
				
				if suitable then 
					cl := FrobeniusTraceDirect(E, l);
					suitable := suitable and not ((Integers()!(cl^2-4) mod p) eq 0);
				end if;
			
			end while;
			
			/* We need to work on O/ll, where ll is one of the
			   two primes over l. We can choose any of them, so 
               we just consider the first one.			   */
			factL := Factorisation(l*O);
			Fl, pi := ResidueClassField(O, factL[1,1]);
			
			/* We build a generator of the multiplicative group,
			   as well as a generator of the p-powers. */
			g := PrimitiveElement(Fl);
			h := g^p;
			
			/* We know that the p-powers will be multiplied 
			   by (\overline(omega)/omega)*(\overline(beta)/beta)^(n*), 
			   so we build precisely that element. */
			betatilde := pi(Conjugate(beta))*pi(beta)^(-1);
			betatilden := betatilde^n;
			
			L := [];
			mult := betatilden*pi(Conjugate(omega))*pi(omega)^(-1);
			
			/* We iterate t times, where l = tp + 1. Then,
               we build the corresponding set.		*/
			t := (l-1) div p;
						
			for ii in [0..t-1] do
				Append(~L, mult);
				mult *:= h;
			end for;
			
			/* The last step is checking whether the square 
			   of the two traces of Frobenius are congruent 
			   modulo p. If this does not happen for any of
			   the values we just computed, there will be 
			   no solutions. */
			found := true;
			
			cl2 := Modexp(cl, 2, p);
			P<x> := PolynomialRing(Fl);
			
			for nu in L do 
				
				if nu eq 1 then 
					continue;
				end if;
				
				F := EllipticCurve(x*(x+1)*(x+nu));
				
				if (((2-#F)^2-cl2) mod p) eq 0 then
					found := false;
					break;
				end if;
			end for;
			
			/* If we have found a prime l showing that 
			   there are no solutions, we are finished 
			   with the prime p2, so we exit the loop. */
			if found then
				break;
			end if;
		
		end for;
	
		/* If the loop has finished, but we have been unable to find
		   a prime l, we fail. */
		if not found then
			return false;
		end if;
	
	end for;
	
	return true;
	
end function;

/*

function bruteForceCheck(C1, p)

	solutions := {};
	for y in [x: x in [0..1000] | IsEven(x)] do
		for alpha in [1..10] do
			for n in [7..100] do 
				x2 := (y^n-p^alpha)/C1; 
				
				x := Sqrt(x2);
			
				if IsIntegral(x) then
					x := Integers()!x;
					if C1*x^2+p^alpha eq y^n and Gcd(C1*x, y) eq 1 and Gcd(C1*x, p) eq 1 and Gcd(y, p) eq 1 and IsPrime(n) then
						solutions := solutions join {[Integers()!C1, Integers()!p, Integers()!x, Integers()!y, Integers()!alpha, n]};
					end if;
				end if;
			
			
			end for;

		end for;
	end for;

	return solutions;

end function;

solutions := {};

for C1 in [1..20] do
	for q in [1..20] do
		if IsSquarefree(C1) and IsPrime(q) and Gcd(C1, q) eq 1 then 
			solutions := solutions join bruteForceCheck(C1, q);
		end if;
	end for;
end for;

solutions;

*/

