# Differences between perfect and prime powers
 In this repository, we include all the code necessary for the computations in the paper.
 If you detect any bugs, or have any questions or comments, feel free to contact me in
	pedro-jose.cazorlagarcia@manchester.ac.uk
	
 Note that this code uses existing code from other papers, namely the following:
    
	(1) A. Gherga and S. Siksek, "Efficient resolution of Thue-Mahler equations", 
	    https://arxiv.org/abs/2207.14492. The code is in Gherga's GitHub repository:
		https://github.com/adelagherga/ThueMahler/tree/master/Code/TMSolver.
		
	(2) M. Mignotte and P. Voutier, "A kit on linear forms in three logarithms", 
		https://arxiv.org/abs/2205.08899. The code is in Voutier's GitHub repository:
		https://github.com/PV-314/lfl3-kit.
	
 We briefly detail all existing folders and their contents. 
 
 -> MAGMA: This involves all computations for most of the papers (Sections 2-7).
 
     -> exponents3And4.m: This resolves the equation for n=3 and 4 by finding
	                      S-integral point on elliptic curves (Section 2).
						  
	 -> yOdd.m: This code adapts the computational methodology in Section 3, 
	            including the use of Lehmer sequences and the computational 
				improvements to avoid solving Thue-Mahler equations.
				
				IMPORTANT: It is necessary to include (1) for this to work.
				
	 -> thueMahler.m: This includes the resolution of Thue-Mahler equation in 
	                  Section 4. In order for this to work, n should be relatively
					  small (n < 17).
					  
					  IMPORTANT: It is necessary to include (1) for this to work.
					  
	 -> boundExponent.m: This includes all the techniques that we develop in Section 
	                     6 in order to bound the exponent p. 
						 
	 -> specificExponents.m: This includes all the techniques that we present in 
	                         Section 7 in order to show that there are no exponents for
							 a fixed value of p.
	 
  	 -> classGroups.m: This includes an elementary script to check the validity of 
                           our work in Section 7.3. In particular, we show that all the 
			   class groups that we consider are cyclic.
							 
 -> PARI-GP: This includes the computations on linear forms in logarithms in Section 8.
             We note that this code is an adaptation of (2), and it is required to 
	     work in conjunction with it. Numbers should be modified inside the code in 
	     order for this to work.
      
     -> lfl.gp: Module including the functions and quantities relevant to our problem. 

 -> Heegner Points: For the curious reader! This includes the generators for the 
                    infinite part of the two elliptic curves in section 2 which
		    needed the Heegner point methodology. Points are very big!
      
