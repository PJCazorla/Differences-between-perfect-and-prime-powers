/*************************************************
** MODULE NAME: classGroups.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: Universidad Pontificia Comillas, Spain
** Description: This module computes the class number for
**              all pairs under consideration (which vary
**              depending on the parity of alpha) and 
**              checks that they are all cyclic. This is 
**              used in Section 7.3 in the paper.
**************************************************/

/********************************************
*** Computation for alpha odd  **************
********************************************/

/* These are the pairs in Table 5 in the article, 
   corresponding to alpha odd. */
pairs := [[1,7], [1,23], [3,5], [3,13], [5,3], [5,11],
		   [11,5], [13,3], [13,11]];
		 
print "Computing class groups for alpha odd";
 
for pair in pairs do 

	C1 := pair[1];
	q := pair[2];
	
	/* For alpha odd, c = C1q */
	c := C1*q;
	
	G := ClassGroup(QuadraticField(-c));
	
	print "Pair (C1, q) = (" , C1, ", ", q, "), class number = ", #G, " Is the group cyclic? ", IsCyclic(G); 

end for;

/********************************************
*** Computation for alpha even  **************
********************************************/

/* These are the pairs in Table 6 in the article, 
   corresponding to alpha even. */
pairs := [[7,3], [7,5], [7,11], [7,13], 
		   [7,23], [15,7], [15,11], [15, 17]];
		 
print "Computing class groups for alpha even";
 
for pair in pairs do 

	C1 := pair[1];
	q := pair[2];
	
	c := C1;
	
	G := ClassGroup(QuadraticField(-c));
	
	print "Pair (C1, q) = (" , C1, ", ", q, "), class number = ", #G, " Is the group cyclic? ", IsCyclic(G); 

end for;
