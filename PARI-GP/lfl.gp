/*************************************************
** MODULE NAME: lfl.gp
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module is based on the code 
**              associated to the paper "A kit on linear
**              forms in three logarithms", by M. Mignotte
**              and Paul Voutier (https://arxiv.org/abs/2205.08899).
**
**              The functions here aim to bound the exponent n in 
**              the generalised Lebesgue-Ramanujan-Nagell equation
**                 C1x^2 + q^alpha = y^n,
**              where C1 is squarefree and q is a prime. 
**************************************************/

/******************************************************************
  How to use?
  
  First of all, set up the parameters corresponding to your pair in the 
  function primepowers_search_general(.). Then, you can proceed to do
  one of two things.
  
  If you want to check the validity of the upper bounds, use the functions
  primepowers_check_itX. Please replace the parameters by the ones in the
  Tables 9 and 10 and run it. They should be run sequentially (so 
  primepowers_check_it1 first, then primepowers_check_it2, and so on).
  
  If you want to look for your own bounds, change the parameters as you 
  want in the functions primepowers_search_itX. First, you should run 
  primepowers_search_it1 and the bound that you find can then be used 
  for the subsequent functions (primepowers_search_it2, which will refine 
  the bound, and the obtained upper bound can be used for primepowers_search_it3.
  
******************************************************************/

/* It is necessary to use Mignotte and Voutier's code for this to work!
   Download it if you do not have it in your computer. */
read("lfl3\\kit-alpha1Variable.gp");

/******************************************************
** Name: primepowers_check_itX
** Description: This function checks whether the parameters provided
**              yield the desired bound. This can be used to check the 
**              validity of Tables 9 and 10 in the paper.
**
** Arguments: None, but replace the input parameters as desired.
**
** Output: If the parameters yield the desired bound, more information
**         is printed. If not, an error occurs.
******************************************************/
primepowers_check_it1()={
	my(bigL,chi,m,mu,rho2Logs,rho3Logs);
	
	/* Input parameters - change as appropiate */
	bigL=112;
	m=15;
	rho2Logs=250;
	rho3Logs=6;
	chi=0.076;
	mu=0.61;
	expMinNUB=1.180969*10^8;
	
	actMinNUB=primepowers_search_general(bigL,bigL,m,m,rho3Logs,rho3Logs,chi,chi,rho2Logs,rho2Logs,mu,mu,,2);
	
	if(abs(actMinNUB/expMinNUB-1)>0.0001,
		printf("FAIL: primepowers_check_it1(), actMinNUB=%9.6e, expMinNUB=%9.6e\n",actMinNUB,expMinNUB);
	);
}

primepowers_check_it2()={
	my(bigL,chi,m,mu,nUB,rho2Logs,rho3Logs);
	
	/* Input parameters - change as appropiate */
	bigL=62;
	m=14.6;
	rho2Logs=200;
	rho3Logs=6.3;
	chi=0.102;
	mu=0.61;
	nUB=1.180969*10^8;
	expMinNUB=4.031551e7;
	
	actMinNUB=primepowers_search_general(bigL,bigL,m,m,rho3Logs,rho3Logs,chi,chi,rho2Logs,rho2Logs,mu,mu,nUB,2);
	
	if(abs(actMinNUB/expMinNUB-1)>0.0001,
		printf("FAIL: primepowers_check_it2(), actMinNUB=%9.6e, expMinNUB=%9.6e\n",actMinNUB,expMinNUB);
	);
}

primepowers_check_it3()={
	my(bigL,chi,m,mu,nUB,rho2Logs,rho3Logs);
	
	/* Input parameters - change as appropiate */
	bigL=62;
	m=15.6;
	rho2Logs=200;
	rho3Logs=5.9;
	chi=0.104;
	mu=0.61;
	nUB=4.031551e7;
	expMinNUB=3.593038e7;

	actMinNUB=primepowers_search_general(bigL,bigL,m,m,rho3Logs,rho3Logs,chi,chi,rho2Logs,rho2Logs,mu,mu,nUB,2);

	if(abs(actMinNUB/expMinNUB-1)>0.0001,
		printf("FAIL: primepowers_check_it3(), actMinNUB=%9.6e, expMinNUB=%9.6e\n",actMinNUB,expMinNUB);
	);
}

/******************************************************
** Name: primepowers_search_itX
** Description: This function performs a search to give the parameters
**              and the best upper bound possible. Note that ideally
**              the results should not be close to the end of the interval.
**              If this is the case, change the intervals and rerun.
**
**				Note that the function primepowers_search_general has to 
**              be configured first.
**
** Arguments: The previous upper bound for it2 and it3. None for it1 (the 
**            corresponding bound is computed using Matveev's theorem).
**
**            Note that the input ranges need to be updated.
**
** Output: The best parameters are printed if they are found.
******************************************************/
primepowers_search_it1(dbg=0)={
	my(bigLLB,bigLUB,chiLB,chiUB,mLB,mUB,rho2LB,rho2UB,rho3LB,rho3UB);

	/* INPUT ranges - change as necessary */
	bigLLB=80;
	bigLUB=140;
	mLB=12;
	mUB=mLB+6;
	rho3LB=3;
	rho3UB=rho3LB+6;
	chiLB=0.05;
	chiUB=chiLB+0.04;
	rho2LB=150;
	rho2UB=rho2LB+100;

	primepowers_search_general(bigLLB,bigLUB,mLB,mUB,rho3LB,rho3UB,chiLB,chiUB,rho2LB,rho2UB,,,,dbg);
}

primepowers_search_it2(nUBInit,dbg=0)={ \\use nUBInit=2.196441e8
	my(bigLLB,bigLUB,chiLB,chiUB,mLB,mUB,rho2LB,rho2UB,rho3LB,rho3UB);

	if(nUBInit<0.00001,
		printf("ERROR: nUBInit=%9.6f must be a positive real number\n",nUBInit);
		return();
	);

	/* INPUT ranges - change as necessary */
	bigLLB=25;
	bigLUB=75;
	mLB=14;
	mUB=mLB+2;
	rho3LB=5;
	rho3UB=rho3LB+2;
	chiLB=0.08;
	chiUB=chiLB+0.04;
	rho2LB=100;
	rho2UB=rho2LB+100;

	primepowers_search_general(bigLLB,bigLUB,mLB,mUB,rho3LB,rho3UB,chiLB,chiUB,rho2LB,rho2UB,,,nUBInit,dbg);
}

primepowers_search_it3(nUBInit,dbg=0)={ \\use nUBInit=8.267981e7
	my(bigLLB,bigLUB,chiLB,chiUB,mLB,mUB,rho2LB,rho2UB,rho3LB,rho3UB);

	if(nUBInit<0.00001,
		printf("ERROR: nUBInit=%9.6f must be a positive real number\n",nUBInit);
		return();
	);
	
	/* INPUT ranges - change as necessary */
	bigLLB=60;
	bigLUB=80;
	mLB=12;
	mUB=mLB+4;
	rho3LB=5;
	rho3UB=rho3LB+2;
	chiLB=0.08;
	chiUB=chiLB+0.04;
	rho2LB=100;
	rho2UB=rho2LB+100;

	primepowers_search_general(bigLLB,bigLUB,mLB,mUB,rho3LB,rho3UB,chiLB,chiUB,rho2LB,rho2UB,,,nUBInit,dbg);
}


/******************************************************
** Name: primepowers_search_general
** Description: The following is a general configuration function that should be 
**              completed before calling primepowers_search_itX with the parameters
**              of our equation.
**
**
** Arguments: The corresponding input parameters should be changed.
**
******************************************************/
primepowers_search_general(bigLLB,bigLUB,mLB,mUB,rho3LB,rho3UB,chiLB,chiUB,rho2LB,rho2UB,muLB=0,muUB=0,nUBInit=0,dbg=0)={
	my(a1,a2,a3,absLogA1,absLogA2,absLogA2a,absLogA2b,absLogA3,al1,al2,al3,areBoundsOK,b1,b2,b3,bigD,chiStep,d,hgtA1,hgtA2,hgtA3,lamUB0,lamUB1,logW,logXLB,matveevChi,minNUB,mStep,nLB,rho3Step,startTime,step3Result);

	startTime=getwalltime();
	
	/* INPUT PARAMETERS common to all iterations of the program - these should 
	   always be like this, so do not change them unless you know what you are doing.
	 */
	
	\\ bigD=[Q(al_1,al_2,al_3):Q] -- used for Matveev's bounds
	bigD=2;
	
	\\ matveevChi=[R(al_1,al_2,al_3):R] -- used for Matveev's bounds
	matveevChi=2;
	
	\\ remember that d=[Q(al_1,al_2,al_3):Q]/[R(al_1,al_2,al_3):R]
	d=bigD/matveevChi; \\ d is the "degree" value used in the kit

	/*************************************************************************************/
	/* INPUT parameters -> This are the parameters that should 
	   be changed depending on the pair (C1, q) that we are dealing
	   with */
	/*************************************************************************************/
	   
	/* This is the smallest integer such that the ideal p2^(2s) is principal. */
	s = 1;
	
	/* This is the generator of p2^(2s) divided by its conjugate. Note that, by 
	   our convention, you should choose the element with positive real part. 
	   If this is not the case, use -beta*/
	beta = (7-sqrt(-15))/8;

	/* The following numbers are chosen as an upper bound for |\Lambda|, so that 
	   |\Lambda| < lamUB1*p + lamUB0. Note that lambUB1 may depend on logX. */
	lamUB1 = -0.493799353652084*logX;
	lamUB2 = 399.535232550159*logX+2.164025100551105;
	
	/*************************************************************************************/
	/* END OF INPUT PARAMETERS */
	/*************************************************************************************/

	/* Here we define our linear form
		nlog(alpha) + log(beta) + jlog(-1), as well as the height for alpha, beta and -1
		and upper bounds on n and j.
		All the details can be found in Section 8 in the paper 
	*/
	al1=x; \\ this is just a placeholder so that al1=alpha_1 is considered to be a polynomial
	hgtA1=s*logX/2; \\ this must be correct though and consistent with logX(=log(y)) usages that follow
	absLogA1=Pi;

	al2=beta;
	hgtA2=s*log(2);
	absLogA2=abs(log(al2));
	
	al3=-1;
	hgtA3=0;
	absLogA3=Pi;

	b1=n;
	b2=1;
	b3=n; \\ since b3=j with |j|<=p
	
	nLB=10^7;
	logXLB=log(4*nLB-4*sqrt(2*nLB)+2);

	if(nUBInit==0,
		\\print("bigD=",bigD,", matveevChi=",matveevChi,", al1=",al1,", absLogA1=",absLogA1,", hgtA1=",hgtA1,", al2=",al2);
		\\print("absLogA2=",absLogA2,", hgtA2=",hgtA2,", al3=",al3,", absLogA3=",absLogA3,", hgtA3=",hgtA3);
		\\print("b1=",b1,", b2=",b2,b3,", logXLB=",logXLB,", nLB=",nLB,", lamUB1=",lamUB1,", lamUB0=",lamUB0,", dbg=",dbg);
		nUBInit=get_matveev_ubnd(bigD,matveevChi,al1,absLogA1,hgtA1,al2,absLogA2,hgtA2,al3,absLogA3,hgtA3,b1,b2,b3,logXLB,nLB,lamUB1,lamUB0,dbg);
		printf("nUBInit=%9.6e\n",nUBInit);
		printf("primepowers_search_general(): calculated nUBInit=%9.6e\n",nUBInit);
	);
	minNUB=nUBInit;
	printf("used nUBInit=%9.6e\n",nUBInit);

	areBoundsOK=check_bounds(bigLLB,bigLUB,mLB,mUB,rho3LB,rho3UB,chiLB,chiUB,rho2LB,rho2UB);
	if(areBoundsOK==0,
		return();
	);
	chiStep=get_step(chiLB,chiUB);
	mStep=get_step(mLB,mUB);
	rho3Step=get_step(rho3LB,rho3UB);

	\\ need chi as the outer loop, as we need to get step 3 and step 4 values for each chi
	forstep(chi=chiLB,chiUB,chiStep,
		\\ step3Result=[minBigK, minBigL, minM, minRho, minChi, minBigR1, minBigR2, minBigS1, minBigT1, minBigT2, minNonDegenNUB]
		step3Result=[0,0,0,0,0,0,0,0,0,0,minNUB];
		\\printf("chi=%9.6f\n",chi);
		for(bigL=bigLLB,bigLUB, \\ L=5 is the lower bound in Theorem 4.1
			\\if(bigL%10==0,print("L=",bigL));
			forstep(m=mLB,mUB,mStep,
				forstep(rho3=rho3LB,rho3UB,rho3Step,
					a1=rho3*absLogA1+2*hgtA1;
					a2=rho3*absLogA2+2*hgtA2;
					a3=rho3*absLogA3+2*hgtA3;
					step3Result=alpha1_do_step3(step3Result,d,al1,a1,absLogA1,hgtA1,al2,a2,absLogA2,hgtA2,al3,a3,absLogA3,hgtA3,b1,b2,b3,chi,bigL,m,rho3,nUBInit,logXLB,nLB,lamUB1,lamUB0,dbg);
				);
			);
		);
		if(length(step3Result)>0 && step3Result[11]<minNUB,
			printf("\nfor chi=%9.6f, minNonDegenNUB=%9.6e\n",chi,step3Result[11]);
			minNUB=alpha1_do_step4(step3Result,minNUB,d,al1,absLogA1,hgtA1,al2,absLogA2,hgtA2,al3,absLogA3,hgtA3,chi,rho2LB,rho2UB,muLB,muUB,logXLB,nLB,lamUB1,lamUB0,dbg);
		);
	);
	print("time taken=",(getwalltime()-startTime));	
	return(minNUB);
}