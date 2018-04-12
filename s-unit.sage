# -*- coding: latin-1 -*-

########################################################################
#
# Let S be a finite set of rational primes.
# This code computes all solutions to the S-unit equation
#
#    x + y = 1, where x, y are S-units.
#
# Writing x = a/c and y = b/c, this S-unit equation is equivalent to
#
#    a + b = c, where a,b,c are non-zero coprime integers with all its 
#               prime divisors in S, and we may assume 0 < a <= b < c.
#
# The corresponding main methods are:
#
# - SUE_solve(S)
# - SUE_findAllSolutionsUpToAGivenRadical(maxRadical)
#
# Authors: Rafael von K\"anel, Benjamin Matschke
# Licence: Creative commons BY-NC.
#
# The code is mostly explained in the authors' paper
# "Solving S-unit and Mordell equations via Shimura-Taniyama conjecture",
# https://arxiv.org/abs/1605.06079.
#
########################################################################

########################################################################
### Global variables ###################################################
########################################################################

numCPUs = min(1,sage.parallel.ncpus.ncpus());
#numCPUs = 1;
#solutions = Set([]);
solutions = set([]);
qualityBound = 1.4; #abc-triples with quality larger than this bound will be printed in some functions.
aLotOutput = False;
#FinckePohstVersion = 'pari'; #uses floating point operations, gives an error message for large inputs
FinckePohstVersion = 'mine'; #a numerically robust version
LogMessages = [];

########################################################################
### Utilities ##########################################################
########################################################################

def addLogMessage(message):
	'''
	Appends 'message' to the global list 'LogMessages' and prints it.	
	'''
	global LogMessages;
	print message;
	LogMessages.append(message);

def quality(a,b,c):
	'''
	Computes the quality of an abc-tripe.
	'''
	return N(log(max(a,b,c))/log(myRadical(a*b*c)));
    
def myFactor(n):
	'''
	Returns a string of factorization of n, which also works if n=0.
	'''
	if n==0:
		return "0";
	return str(factor(n));

def myRadical(n):
	'''
	Returns the product of all prime factors of n if n is non-zero, 
	and zero otherwise.
	'''
	if n==0:
		return 0;
	return radical(n);

def myListToStr(list,comma=", "):
	'''
	Converts a list to a string, with 'comma' as separator between
	list entries.
	'''
	result = "";
	firstElement = True;
	for l in list:
		if not firstElement:
			result = result + comma;
		else:
			firstElement = False;
		result = result + str(l);
	return result;

def factorizationToString(E):
	'''
	Input:
		E - list of elements of the form [p,a]

	Output:
		A string of the form "... * p^a * ...".
	'''

	result = "";
	for i in range(len(E)):
		[p,a] = E[i];
		result = result + str(p) + "^" + str(a);
		if i<len(E)-1:
			result = result + " * ";
	return result;

########################################################################
### Teske's Minimize() (computing minimal relations) ###################
########################################################################

def exponentOfXmodPtoTheN(x,p,n):
	'''
	INPUT:
		Integers x and n>=1, and a prime p.

	OUTPUT:
		The smallest integer k = p^e*r greater than 1 such that x^k = 1 mod p^n.
	'''
	
	# phi = p^(n-1)*(p-1) is the order of (ZZ/(p^n))^*
	R = IntegerModRing(p^n);
	X = R.coerce(x); # die Restklasse von x
	# Wollen zuerst den Exponenten bzgl. p finden:
	Y = X^(p-1); # Rechnung sollte in R stattfinden
	Zero = R.coerce(1);
	expp = n-1;
	while expp>=1 and Y^(p^(expp-1))==Zero:
		expp = expp-1;
	Z = X^(p^expp);
	rest = 1;
	while Z^rest != Zero:
		rest = rest+1;
	#return [expp,rest];
	return p^expp*rest;

def teskeMinimizeAtJ(S, B, j, R, primesPossiblyDividingGroupOrder):
	'''
	INPUT:
		S - a list of generators of the subgroup
		B - a list of relations (lower triangular), the j-1 first of which are minimal
		j - an integer between 0 and #S-1
		R - the underlying ring, isomorphic to ZZ/N for some N.
		primesPossiblyDividingGroupOrder - any upper bound for the maximal prime divisor in phi(R) = phi(N).

	OUTPUT:
		B', same as B, except that the j'th relation is replaced by a j'th-minimal one.
	'''

	def findX(k,S,B,j,R,x,c,gcdP0Bkk,p0,m):
		if k==-1:
			#check whether the x-vector is a relation:
				
			StoX = R.coerce(1);
			for i in range(j+1):
				StoX = StoX * R.coerce(S[i])^x[i];
			return StoX == R.coerce(1);
				
		else:
			if gcdP0Bkk[k]==0:
				print "Some error occured. Parameters k,S,j,R,x,c,gcdP0Bkk:",k,S,j,R,x,c,gcdPoBkk;
			
			#try all possible values for x[k] and go deeper into the recursion:
			
			#m = range(j);
			#for i in range(j-1,k,-1):     #i=j-1...k+1
			#    m[i] = B[j][i] - p0*x[i];
			#    for n in range(i+1,j):
			#        m[i] = m[i] - m[n]*B[n][k];    # Important: I think here B[n][k] must be replaced by B[n][i]! (I think Teske's paper has a typo here.)
			#    m[i] = ZZ(m[i] / B[i][i]);
			
			L = B[j][k];
			for i in range(k+1,j):
				L = L - m[i]*B[i][k];

			if not (L in ZZ):
				print "Some error occured. Parameters p0,L,m,k,S,B,j,R,x,c,gcdP0Bkk:",p0,L,m,k,S,B,j,R,x,c,gcdPoBkk;

			if L%gcdP0Bkk[k] != 0:
				return False;
			L = ZZ(L / gcdP0Bkk[k]) % B[k][k];
			Rt = ZZ(B[k][k]/gcdP0Bkk[k]);
			
			for rk in range(0,gcdP0Bkk[k]):
				x[k] = (L*c[k] + Rt*rk) % B[k][k];
				if not(x[k].is_integral()):
					print "Error!";
				m[k] = B[j][k]-p0*x[k];
				for n in range(k+1,j):
					m[k] = m[k] - m[n]*B[n][k];
				m[k] = ZZ(m[k] / B[k][k]);
				
				if findX(k-1,S,B,j,R,x,c,gcdP0Bkk,p0,m):
					return True;
			
			return false;
		
	#The following takes way too long for large primes in S:
	#P = [];        #primes that may reduce b_{jj}
	#for i in prime_range(maxP+1):
	#    if B[j][j]%i == 0:
	#        P.append(i);

	#So let's do it quicker using more knowledge about the underlying group:
	P = []; #primes that may reduce b_{jj}
	for p in primesPossiblyDividingGroupOrder:
		if B[j][j]%p == 0:
			P.append(p);    

	#print S,j,primesPossiblyDividingGroupOrder, P;
		
	while True:
		#Reduce j'th relation by all previous ones:
		for k in range(j-1,-1,-1):             #k=j-1,...,0
			f = round(B[j][k]/B[k][k]);
			if f != 0:
				for i in range(j+1):
					B[j][i] = B[j][i] - f*B[k][i];

		if len(P) == 0:        #no primes left for reduction
			return B;
		p0 = P[0];
		
		c = range(j);
		for k in range(j):
			c[k] = xgcd(p0,B[k][k])[1];    #a number ck such that gcd(p0,Bkk) = p*ck + Bkk*ak
		
		gcdP0Bkk = range(j);
		for k in range(j):
			gcdP0Bkk[k] = gcd(p0,B[k][k]);        
		
		x = range(j+1);
		x[j] = ZZ(B[j][j]/p0);
		
		if findX(j-1,S,B,j,R,x,c,gcdP0Bkk,p0,range(j)):
			#smaller relation x has been found:
			for i in range(j+1):
				B[j][i] = x[i];
			if x[j]%p0 != 0:
				P.remove(p0);
		else:
			#reducing with respect to p0 is impossible:
			P.remove(p0);
			
	return B;
        
def teskeMinimize(S, B, R, primesPossiblyDividingGroupOrder):
	'''
	INPUT:
		S - a list of generators of a subgroup of R
		B - a list of |S| relations (lower triangular)
		R - the underlying ring, isomorphic to ZZ/N for some N.
		primesPossiblyDividingGroupOrder - any upper bound for the
			maximal prime divisor in phi(R) = phi(N).

	OUTPUT:
		B', same as B, except that for each j, the j'th relation is
			replaced by a j'th-minimal one.
	'''
	
	for j in range(len(B)):
		B = teskeMinimizeAtJ(S, B, j, R, primesPossiblyDividingGroupOrder);
	return B;

#Actually not needed anymore, can use Teske directly instead:
def findMinimalRelations(S,p,n):
	'''
	Input:
		S - list of primes (or arbitrary integers)
		p - a prime (if p in S, then we remove p from S)
		n - an integer
	
	Output:
		B - a list of minimal relations
	'''
	
	#print "phi(p^n) =",p^(n-1)*(p-1);
	
	if S.count(p)>0:
		S.remove(p);
	l = len(S);
	B = range(l);
	for i in range(l):
		B[i] = zero_vector(l).list();
		B[i][i] = exponentOfXmodPtoTheN(S[i],p,n);
	R = IntegerModRing(p^n);
	#print B[0][0];
	#print R.coerce(1);

	primesPossiblyDividingGroupOrder = primes_divide(R.unit_group_order());
		
	return teskeMinimize(S,B,R,primesPossiblyDividingGroupOrder);    

########################################################################
### Lattice point algorithms ###########################################
########################################################################

def paris_finckePohst_viaLattice(L,boundForNormSquared,numSolutions):
	'''
	Fincke-Pohst algorithm from pari/GP.
	INPUT:
		L - a matrix whose columns determine a lattice over ZZ.
		boundForNormSquared - determines which vectors will be returned.
		numSolutions - Returns at most numSolutions many vectors.
	'''
	G = L.transpose() * L;
	return pari(G.change_ring(ZZ)).qfminim(boundForNormSquared,max=numSolutions,flag=0).python();

def paris_finckePohst_viaGramMatrix(G,boundForNormSquared,numSolutions):
	'''
	Fincke-Pohst algorithm from pari/GP.
	INPUT:
		G - a square matrix that represents a quadratic form.
		boundForNormSquared - determines which vectors will be returned.
		numSolutions - Returns at most numSolutions many vectors.
	'''
	return pari(G.change_ring(RR)).qfminim(boundForNormSquared,max=numSolutions,flag=2).python();

def quadraticFormToFPForm(A):
	'''
	We compute a symmetric matrix Q such that for any vector x,
	x^t*A*x = \sum_{i=1}^n q_{ii} * (x_i + \sum_{j=i+1}^n q_{ij}*x_j)^2
	Everything is done over QQ
	'''
	
	(n,m) = A.dimensions();
	Q = matrix(QQ,n,n);
	
	#Following Fincke-Pohst's paper:
	#Q = copy(A);
	#Q = Q.change_ring(QQ);
	#for i in range(n):
	#    for j in range(i+1,n):
	#        Q[j,i] = Q[i,j]; #used just as a temporary buffer
	#        Q[i,j] = Q[i,j] / Q[i,i];
	#for i in range(n):
	#    for k in range(i+1,n):
	#        for l in range(k,n):
	#            Q[k,l] = Q[k,l] - Q[k,i]*Q[i,l];
	#for i in range(n):
	#    for j in range(i):
	#        Q[i,j] = 0; #the lower diagonal is redundant now
	
	for i in range(n):
		for k in range(i+1):
			s = 0;
			for j in range(k):
				s = s + Q[j,i]*Q[j,k]*Q[j,j];
			if i==k:
				Q[i,i] = A[i,i]-s;
			else:
				Q[k,i] = (A[k,i]-s)/Q[k,k];
	
	return Q;
	
def my_finckePohst_viaLattice(L,boundForNormSquared,solutionList=None,maxNumSolutions=None,callback=None,callbackArgs=None):
	'''
	Input:
		L - an integral matrix whose columns are a basis of a lattice
		boundForNormSquared - a non-negative integer
		maxNumSolutions - a non-negative integer

	Output:
		[bufferWasBigEnough,solutions], where
			bufferWasBigEnough - true iff number of solutions is at most maxNumSolutions
			solutions - a matrix whose columns are the non-zero integral vectors x with
				||Lx||_2 = x^t*L^t*L*x <= boundForNormSquared
	
	We assume that all input is integral, such that there are no numerical issues at all.
	This one uses the LLL-algorithm!!!
	'''
	
	global aLotOutput;
	#if aLotOutput:
	#    print "L =",L;    
	
	L = L.change_ring(ZZ);
	L1 = L.transpose().LLL().transpose(); #LLL reduction of columns
	#L1 = L;
	#print L1;
	U = L.inverse()*L1;
	
	return my_finckePohst_viaGramMatrix(L1.transpose()*L1, boundForNormSquared, solutionList=solutionList, maxNumSolutions=maxNumSolutions, finalTransformation=U, callback=callback, callbackArgs=callbackArgs);

def my_finckePohst_viaGramMatrix(A,boundForNormSquared,solutionList=None,maxNumSolutions=None,finalTransformation=None,callback=None,callbackArgs=None):
	'''
	Input:
		A - a positive definite matrix with integer coefficients
		boundForNormSquared - a non-negative integer
		maxNumSolutions - a non-negative integer, or None if this should not be bounded.
		solutionList - either None or [], depending on whether it shall be filled with solutions or not
			
	Output:
		If callback function appears as a parameter:
		[notTooManySolutions,numSolutions], where
			notTooManySolutions - true iff number of solutions is at most maxNumSolutions or maxNumSolutions==None
			numSolutions - number of solutions that have been traversed

		Furthermore, for each solution:
			if solutionList != None, then the solution will be appended to solutionList, and
			if callback != None, then callback(solution,callbackArgs) will be called.
	'''
	
	def traverseShortVectors(Q,n,k,x,shortVectors,RemainingBoundForNormSquared,numSolutionsList,maxNumSolutions,xIsZeroSoFar,finalTransformation,callback,callbackArgs):
		#Fills shortVectors or calls callback()
		#Returns [bufferBigEnoughSoFar,newNumSolutionsSoFar]
		if k==-1:
			if not xIsZeroSoFar: 
				if maxNumSolutions!=None and numSolutionsList[0]>=maxNumSolutions:
					return False;
				else:
					numSolutionsList[0] = numSolutionsList[0]+1;
					y = vector(x);
					if finalTransformation != None:
						y = finalTransformation * y;
					if shortVectors != None:
						shortVectors.append(y);
					if callback != None:
						callback(y,callbackArgs);
			return True;
		u = 0;
		for j in range(k+1,n):
			u = u + Q[k,j] * x[j];
		xk0 = -floor(u);
		x[k] = xk0;
		t = Q[k,k] * (x[k] + u)^2;
		while t<=RemainingBoundForNormSquared:
			#print k,x[k],t;
			if not traverseShortVectors(Q,n,k-1,x,shortVectors,RemainingBoundForNormSquared-t,numSolutionsList,maxNumSolutions,xIsZeroSoFar and x[k]==0, finalTransformation,callback,callbackArgs):
				return False; #too many solution found
			x[k] = x[k] + 1;            
			t = Q[k,k] * (x[k] + u)^2;
	
		if not xIsZeroSoFar: #break antipodal symmetry: if x was so far 0, then u is zero here, and we iterate only over x[k]>=0.
			x[k] = xk0-1;
			t = Q[k,k] * (x[k] + u)^2;
			while t<=RemainingBoundForNormSquared:
				if not traverseShortVectors(Q,n,k-1,x,shortVectors,RemainingBoundForNormSquared-t,numSolutionsList,maxNumSolutions,False, finalTransformation,callback,callbackArgs):
					return False; #too many solutions found
				x[k] = x[k] - 1;            
				t = Q[k,k] * (x[k] + u)^2;
			
		return True; #prescribed bufferSize (maxNumSolutions) was enough
		
	global aLotOutput;
	#if aLotOutput:
	#    print "A =",A;
	
	(n,m) = A.dimensions();
	Q = quadraticFormToFPForm(A);
	#print "Q =", Q;
	x = range(n);
	numSolutionsList = [0];
	bufferWasBigEnough = traverseShortVectors(Q,n,n-1,x,solutionList,boundForNormSquared,numSolutionsList,maxNumSolutions,True, finalTransformation,callback,callbackArgs);
		
	#return [bufferWasBigEnough,matrix(shortVectors).transpose()];
	return [bufferWasBigEnough,numSolutionsList[0]];
	
#The following was only a test. It works, but it's slow, since LLL is not used!    
def my_finckePohst_viaUpperTriangularLattice(L,boundForNormSquared,maxNumSolutions):
	'''
	Input:
		L - an upper triangular matrix with integer coefficients whose columns are a basis of the lattice
		boundForNormSquared - a non-negative integer
		maxNumSolutions - a non-negative integer

    Output:
		[bufferWasBigEnough,solutions], where
		bufferWasBigEnough - true iff number of solutions is at most maxNumSolutions
		solutions - a matrix whose columns are the non-zero integral vectors x with
			||Lx||_2 = x^t*L^t*L*x <= boundForNormSquared
	'''
	def traverseShortVectors(Q,n,k,x,shortVectors,RemainingBoundForNormSquared,maxNumSolutions,xIsZeroSoFar):
		#Fills shortVectors, returns true/false depending on whether buffer was big enough.
		if k==-1:
			if not xIsZeroSoFar: 
				if len(shortVectors)>=maxNumSolutions:
					return False;
				else:
					shortVectors.append(copy(x));
			return True;
		u = 0;
		for j in range(k+1,n):
			u = u + Q[k,j] * x[j];
		xk0 = -floor(u);
		x[k] = xk0;
		t = Q[k,k] * (x[k] + u)^2;
		while t<=RemainingBoundForNormSquared:
			#print k,x[k],t;
			if not traverseShortVectors(Q,n,k-1,x,shortVectors,RemainingBoundForNormSquared-t,maxNumSolutions,xIsZeroSoFar and x[k]==0):
				return False; #too many solution found
			x[k] = x[k] + 1;            
			t = Q[k,k] * (x[k] + u)^2;
	
		if not xIsZeroSoFar: #break antipodal symmetry
			x[k] = xk0-1;
			t = Q[k,k] * (x[k] + u)^2;
			while t<=RemainingBoundForNormSquared:
				if not traverseShortVectors(Q,n,k-1,x,shortVectors,RemainingBoundForNormSquared-t,maxNumSolutions,False):
					return False; #too many solutions found
				x[k] = x[k] - 1;            
				t = Q[k,k] * (x[k] + u)^2;
			
		return True; #prescribed bufferSize (maxNumSolutions) was enough
		
	global aLotOutput;
	
	(n,m) = L.dimensions();
	Q = matrix(QQ,n,n);
	for i in range(n):
		Q[i,i] = L[i,i]^2;
		for j in range(i+1,n):
			Q[i,j] = L[i,j]/L[i,i];
	#print "Q =", Q;
	shortVectors = [];
	x = range(n);
	bufferWasBigEnough = traverseShortVectors(Q,n,n-1,x,shortVectors,boundForNormSquared,maxNumSolutions,True);
		
	return [bufferWasBigEnough,matrix(shortVectors).transpose()];
	
#The following was only a test. It works, but it's slow, since LLL is not used!    
def my_finckePohst_viaUpperTriangularLattice2(L,boundForNormSquared,maxNumSolutions):
	'''
	Input:
		L - an upper triangular matrix with integer coefficients whose columns are a basis of the lattice
		boundForNormSquared - a non-negative integer
		maxNumSolutions - a non-negative integer

    Output:
		[bufferWasBigEnough,solutions], where
		bufferWasBigEnough - true iff number of solutions is at most maxNumSolutions
		solutions - a matrix whose columns are the non-zero integral vectors x with
			||Lx||_2 = x^t*L^t*L*x <= boundForNormSquared
	'''
	
	def traverseShortVectors(L,n,k,x,shortVectors,RemainingBoundForNormSquared,maxNumSolutions,xIsZeroSoFar):
		#Fills shortVectors, returns true/false depending on whether buffer was big enough.
		if k==-1:
			if not xIsZeroSoFar: 
				if len(shortVectors)>=maxNumSolutions:
					return False;
				else:
					shortVectors.append(copy(x));
			return True;
		u = 0;
		for j in range(k+1,n):
			u = u + L[k,j] * x[j];
		xk0 = -floor(u/L[k,k]);
		x[k] = xk0;
		t = (L[k,k] * x[k] + u)^2;
		while t<=RemainingBoundForNormSquared:
			#print k,x[k],t;
			if not traverseShortVectors(L,n,k-1,x,shortVectors,RemainingBoundForNormSquared-t,maxNumSolutions,xIsZeroSoFar and x[k]==0):
				return False; #too many solution found
			x[k] = x[k] + 1;            
			t = (L[k,k] * x[k] + u)^2;

		if not xIsZeroSoFar: #break antipodal symmetry
			x[k] = xk0-1;
			t = (L[k,k] * x[k] + u)^2;
			while t<=RemainingBoundForNormSquared:
				if not traverseShortVectors(L,n,k-1,x,shortVectors,RemainingBoundForNormSquared-t,maxNumSolutions,False):
					return False; #too many solutions found
				x[k] = x[k] - 1;            
				t = (L[k,k] * x[k] + u)^2;
	
		return True; #prescribed bufferSize (maxNumSolutions) was enough
		
	global aLotOutput;
	(n,m) = L.dimensions();
	shortVectors = [];
	x = range(n);
	bufferWasBigEnough = traverseShortVectors(L,n,n-1,x,shortVectors,boundForNormSquared,maxNumSolutions,True);
		
	return [bufferWasBigEnough,matrix(shortVectors).transpose()];

def normSquared(v):
	'''
	Returns the square of the l_2-norm of the vector (or list) 'v'.
	'''
	return sum([x^2 for x in v]);

def my_ShortestVector_viaLattice(L,verbose=False):
	'''
	INPUT:
	- "L" - an integral matrix whose columns determine a full lattice in ZZ^n
	OUTPUT:
	A shortest non-zero vector (and only one, even if it is not unique).
	The coordinates are the one from the ambient ZZ^n, not the one wrt. L!
	'''
	L = L.change_ring(ZZ);
	L1 = L.transpose().LLL().transpose(); #LLL reduction of columns
	#L1 = L;
	#print L1;
	#U = L.inverse()*L1;
	U = L1;
	A = L1.transpose()*L1; #associated quadratic form wrt. the new basis

	if verbose:
		print "L =",L;
		print "L1 =",L1;
		sys.stdout.flush();


	#As L1 has LLL reduced columns, we obtain an elementary lower bound for the shortest vector's norm:
	lowerBoundForShortestVectorSquared = normSquared(L1.column(0)) / 2^(L1.nrows()-1);

	boundForNormSquared = lowerBoundForShortestVectorSquared;
	solutionList = [];
	while solutionList==[]:
		boundForNormSquared *= 4;
		if verbose:
			print "boundForNormSquared =",boundForNormSquared;
			sys.stdout.flush();
		[bufferWasBigEnough,numSolutions] = my_finckePohst_viaGramMatrix(A, boundForNormSquared, solutionList=solutionList, maxNumSolutions=None, finalTransformation=U, callback=None, callbackArgs=None);
		#bufferWasBigEnough is always true here, as we don't bound the buffer (i.e. we put maxNumSolutions=None).

	return min(solutionList,key=normSquared);	

########################################################################
### Parts of algorithm solving S-unit equations ########################
########################################################################

class SData:
	'''
	This is a container for data associated to the finite set of primes S
	that is needed again and again.
	'''
	
	def __init__(self,S):
		self.S = S; #A list of primes
		self.primesDividingGroupOrderOfZmodPtoTheNstar = dict(zip(S,[set(prime_divisors(euler_phi(p^2))) for p in S]));

def SUE_addSolution(a,b,c,solutions):
	'''
	Breaks symmetry of the solution, i.e. chooses a canonical representative modulo the
	natural 12-fold symmetry group (6 permutations, 2 signs), and adds it
	to the set solutions.
	'''
	
	a = abs(a);
	b = abs(b);
	c = abs(c);
	if a>b:
		a,b = b,a;
	if b>c:
		b,c = c,b;
	if a>b:
		a,b = b,a;
	s = (a,b,c);
	#solutions = solutions.union(Set([s])); #we should maybe use a better data structure, e.g. a hash
	solutions.add(s); #we should maybe use a better data structure, e.g. a hash

def SUE_checkSolution(solution,SwoPs,listOfPrimesWithMinExponent,solutions):
	'''	
    Input:
		SwoPs - list of primes without the primes in the list listOfPrimesWithMinExponent
		listOfPrimesWithMinExponent - a list with entries [p,minExponentOfP], where p is a prime not in SwoP and minExponentOfP a positive integer
		solution - a list of positive integers a_q, one for any q in SwoP, such that
					prod_(q in SwoP) q^(2a_q) = 1 mod prod p^minExponentOfP.
		solutions - list of solutions, to which this candidate is added in case it's a solution.

	Determines the corresponding tuples (a,b,c) with a+b+c=0, 
	where a comes from the positive exponents in solution, b from the negative ones, 
	and c divides p^minExponentOfP.
	'''
	
	#PtoE = p^minExponentOfP;
	prodPtoE = 1;
	PrimesInModulus = []
	for [p,m] in listOfPrimesWithMinExponent:
		prodPtoE = prodPtoE * p^m;
		PrimesInModulus.append(p);
	R = IntegerModRing(prodPtoE);
	
	a = R.coerce(1);
	b = R.coerce(1);
	for i in range(len(SwoPs)):
		e = solution[i];
		if e>0:
			a = a * R.coerce(SwoPs[i])^e;
		elif e<0:
			b = b * R.coerce(SwoPs[i])^(-e);
	
	sign = +1;
	if a+b != R.coerce(0):
		b = -b;
		sign = -1;
	if a+b != R.coerce(0):
		#print "Candidtate gives no solution.";
		
		#Sanity check:
		if a^2-b^2 != R.coerce(0):
			raise Exception("Error in the program?");
	else:
		a = 1;
		b = sign;
		Sc = copy(PrimesInModulus);
		ExpA = [];
		ExpB = [];
		ExpC = [];
		radical = 1; #prod(Sc);
		for i in range(len(SwoPs)):
			e = solution[i];
			if e>0:
				a = a * SwoPs[i]^e;
				ExpA.append([SwoPs[i],e]);
				radical = radical * SwoPs[i];
			elif e<0:
				b = b * SwoPs[i]^(-e);
				ExpB.append([SwoPs[i],-e]);
				radical = radical * SwoPs[i];
			else:
				Sc.append(SwoPs[i]);
		c = a + b;
		
		#Still have to check whether rad(rest)|NS.
		#But maybe we should also output all (a,b,c) where rest is small, in the sense that the quality of this (a,b,c) is large?
		
		rest = c/prodPtoE;
		for q in Sc:
			e = 0;
			while rest % q == 0:
				rest = rest/q;
				e = e+1;
			for [p,m] in listOfPrimesWithMinExponent:
				if q == p:
					e = e + m;
			if e>0:
				radical = radical * q;
				ExpC.append([q,e]);
		
		loga = N(log(a));
		logb = N(log(abs(b)));
		logc = N(log(abs(c)));
		logRest = N(log(abs(rest)));
		
		height = max(loga,logb,logc);
		
		logEstimatedRadical = log(radical) + logRest;
		
		estimatedQuality = N(height/logEstimatedRadical);
		
		size = N(height/log(10));
		
		if estimatedQuality>1:
			estimatedMerit = N((estimatedQuality-1)^2 * logEstimatedRadical * log(logEstimatedRadical));
		else:
			estimatedMerit = 0;
		
		#print [a,b];   
		
		if abs(rest) == 1:
			if aLotOutput:
				print "Solution found:";
				print "Estimated quality =",estimatedQuality, "| Size =", size, "| Merit =", estimatedMerit;        
				print factorizationToString(ExpA),"|",sign,factorizationToString(ExpB),"|",factorizationToString(ExpC);
			SUE_addSolution(a,b,c,solutions);        
		#elif estimatedQuality > qualityBound:
		#    print "High quality triple found:";
		#    print "Estimated quality =",estimatedQuality, "| Size =", size, "| Merit =", estimatedMerit;        
		#    print factorizationToString(ExpA),"|",sign,factorizationToString(ExpB),"|",factorizationToString(ExpC),rest;
		
	return;

def SUE_enumerateTinySolutions(S,Bounds,solutions,parallelIterator='fork'):

	def weight(A,weights):
		result = 1;
		for p in A:
			result = result * (1+weights[p]);
		return result;
	
	def weight0(A,weights):
		result = 1;
		for p in A:
			result = result * weights[p];
		return result;
		
	def fillFactorsA1(factorsA1,A1,k,a1,factorsSoFar,vBounds,numBoundKGotExeeded):
		if k==len(A1):
			#factors1 = copy(factorsSoFar);
			#factors1.insert(0,[-1,0]);
			##factors1.insert(0,pairBoundExeededSoFar);
			#factorsA1[a1] = factors1;
			factorsA1[a1] = True; #The value actually doesn't matter at all for us.
			#factors2 = copy(factorsSoFar);
			#factors2.insert(0,[-1,1]);
			##factors2.insert(0,pairBoundExeededSoFar);
			#factorsA1[-a1] = factors2;
			factorsA1[-a1] = True; #The value actually doesn't matter at all for us.
		else:
			p = A1[k];
			for alpha in range(vBounds[p,0]+1):
				Kmin = len(numBoundKGotExeeded);
				boundsNotExceededTooOften = True;
				for K in range(len(numBoundKGotExeeded)-1,-1,-1):
					if alpha > vBounds[p,K]:
						numBoundKGotExeeded[K] = numBoundKGotExeeded[K] + 1;
						Kmin = K;
						if numBoundKGotExeeded[K] > K:
							boundsNotExceededTooOften = False;
							break;
					else:
						break;
				if boundsNotExceededTooOften:
					fillFactorsA1(factorsA1,A1,k+1,a1*p^alpha,factorsSoFar,vBounds,numBoundKGotExeeded);                
				for K in range(Kmin,len(numBoundKGotExeeded)):
					numBoundKGotExeeded[K] = numBoundKGotExeeded[K] - 1;
				#factorsSoFar.pop();

	def traverseAllBs_thenCs_thenA2s(k,b,A1,A2,B,C,factorsA1,setA1,vBounds,numBoundKGotExeeded,solutions):
		if k==len(B):
			traverseAllCs_thenA2s(0,b,1,A1,A2,B,C,factorsA1,setA1,vBounds,[0 for i in numBoundKGotExeeded],solutions);
		else:
			p = B[k];
			for alpha in range(1,vBounds[p,0]+1): #we allow alpha=0 only at primes in A = A1\cup A2
				Kmin = len(numBoundKGotExeeded);
				boundsNotExceededTooOften = True;
				for K in range(len(numBoundKGotExeeded)-1,-1,-1):
					if alpha > vBounds[p,K]:
						numBoundKGotExeeded[K] = numBoundKGotExeeded[K] + 1;
						Kmin = K;
						if numBoundKGotExeeded[K] > K:
							boundsNotExceededTooOften = False;
							break;
					else:
						break;
				if boundsNotExceededTooOften:
					traverseAllBs_thenCs_thenA2s(k+1,b*p^alpha,A1,A2,B,C,factorsA1,setA1,vBounds,numBoundKGotExeeded,solutions);
				for K in range(Kmin,len(numBoundKGotExeeded)):
					numBoundKGotExeeded[K] = numBoundKGotExeeded[K] - 1;
		
	def traverseAllCs_thenA2s(k,b,c,A1,A2,B,C,factorsA1,setA1,vBounds,numBoundKGotExeeded,solutions):
		if k==len(C):
			traverseAllA2s(0,1,b,c,b+c,A1,A2,B,C,factorsA1,setA1,vBounds,[0 for i in numBoundKGotExeeded],solutions);
			traverseAllA2s(0,1,b,-c,b-c,A1,A2,B,C,factorsA1,setA1,vBounds,[0 for i in numBoundKGotExeeded],solutions);
		else:
			p = C[k];
			for alpha in range(1,vBounds[p,0]+1): #we allow alpha=0 only at primes in A = A1\cup A2
				Kmin = len(numBoundKGotExeeded);
				boundsNotExceededTooOften = True;
				for K in range(len(numBoundKGotExeeded)-1,-1,-1):
					if alpha > vBounds[p,K]:
						numBoundKGotExeeded[K] = numBoundKGotExeeded[K] + 1;
						Kmin = K;
						if numBoundKGotExeeded[K] > K:
							boundsNotExceededTooOften = False;
							break;
					else:
						break;
				if boundsNotExceededTooOften:
					traverseAllCs_thenA2s(k+1,b,c*p^alpha,A1,A2,B,C,factorsA1,setA1,vBounds,numBoundKGotExeeded,solutions);
				for K in range(Kmin,len(numBoundKGotExeeded)):
					numBoundKGotExeeded[K] = numBoundKGotExeeded[K] - 1;

	def traverseAllA2s(k,a2,b,c,b_plus_c_over_a2,A1,A2,B,C,factorsA1,setA1,vBounds,numBoundKGotExeeded,solutions):
		if k==len(A2):
			#Test whether some a1 equals (b+c)/a2:
			if b_plus_c_over_a2 in setA1:
				#print "Solution:",A1,A2,B,C,":",b_plus_c_over_a2,"*",a2,"=",b,"+",c;                            
				SUE_addSolution(b_plus_c_over_a2*a2,b,c,solutions);
		else:
			p = A2[k];
			alpha = 0;
			#a2local = copy(a2); #This was a test, but we would have to do the same with b_plus_c_over_a2...
			a2local = a2;
			for alpha in range(0,vBounds[p,0]+1): #we allow alpha=0 only at primes in A = A1\cup A2
				Kmin = len(numBoundKGotExeeded);
				boundsNotExceededTooOften = True;
				for K in range(len(numBoundKGotExeeded)-1,-1,-1):
					if alpha > vBounds[p,K]:
						numBoundKGotExeeded[K] = numBoundKGotExeeded[K] + 1;
						Kmin = K;
						if numBoundKGotExeeded[K] > K:
							boundsNotExceededTooOften = False;
							break;
					else:
						break;
				if boundsNotExceededTooOften:
					traverseAllA2s(k+1,a2local,b,c,b_plus_c_over_a2,A1,A2,B,C,factorsA1,setA1,vBounds,numBoundKGotExeeded,solutions);
				for K in range(Kmin,len(numBoundKGotExeeded)):
					numBoundKGotExeeded[K] = numBoundKGotExeeded[K] - 1; 
				if b_plus_c_over_a2 % p != 0:
					return;
				alpha = alpha+1;
				a2local = a2local * p;
				b_plus_c_over_a2 = b_plus_c_over_a2 / p;

	global numCPUs;

	@parallel(p_iter=parallelIterator,ncpus=numCPUs)
	def findSolutionsForFixedA0(A0,S0,S,vBounds,vBounds0):
		#Output: Returns set of solutiuons for all A \subset S, for which A\cap S0 = A0.
		
		solutions = set([]);
		
		Srest = [];
		for p in S:
			if p not in S0:
				Srest.append(p);

		for setArest in Subsets(Srest):
			A = copy(A0);
			for a in setArest:
				A.append(a);
			weightOfA = weight(A,vBounds0);
			if weightOfA^3 < weightOfS:
				continue;
			A.sort();

			BC = copy(S);
			for p in A:
				BC.remove(p);    
			
			#If weight of A is very large then we split A further up into A1 and A2:
			A1 = copy(A);
			A2 = [];
			#while weight(A1,vBounds0)^2 > weight(S,vBounds0) * 2^(len(S)-len(A)-1): #this was the first heuristik
			while A1!=[] and weight(A1,vBounds0) > weight0(BC,vBounds0) * 2^(len(BC)-1): #we ignore here A2 on the RHS, but that should be reasonable
				A2.insert(0,A1.pop()); #Add last element of A1 at the first place of A2.
			
			#if aLotOutput:
			#    print A, A1, A2;
				
				
			factorsA1 = {}; #a dictionary: The keys are all possible integers that appear as a1, and their value is the corresponding factorization
			fillFactorsA1(factorsA1,A1,0,1,[],vBounds,[0 for i in Bounds]);
			setA1 = Set(factorsA1.keys());
			#print factorsA1;
			#print setA1;
	
			for setB in Subsets(BC):
				B = setB.list();
				weightOfB = weight(B,vBounds0);
				if weightOfB > weightOfA:
					continue;
				if weightOfB == weightOfA:
					if A!=[] and B!=[] and min(A)>min(B): 
						continue;
				B.sort();       
				
				C = copy(BC);
				for p in B:
					C.remove(p);
				weightOfC = weight(C,vBounds0);
	
				if weightOfC > weightOfB:
					continue;
				if weightOfC == weightOfB:
					if C!=[]:
						if B==[]:
							continue;
						if min(B)>min(C):
							continue;
						
				#if aLotOutput:
				#    print A, A1, A2, setA1, B, C;
				traverseAllBs_thenCs_thenA2s(0,1,A1,A2,B,C,factorsA1,setA1,vBounds,[0 for i in Bounds],solutions);
		
		return solutions;                

	#In case S is actually an instance of my SData class:
	if S.__class__.__name__ != 'list':
		S = S.S; 
			
	vBounds = {};
	vBounds0 = {};
	for p in S:
		for k in range(len(Bounds)):
			vBounds[p,k] = N(Bounds[k]/log(p)).floor();
		vBounds0[p] = vBounds[p,0];
		
	#print vBounds;
	#print vBounds0;
		
	weightOfS = weight(S,vBounds0);
	
	#print len(Bounds);
	
	parameters = [];
	
	#First, we iterate over the set of primes that appear in a:
	#In the following loop we only do this for primes in S0:
	S0 = [];
	for i in range(8): # This means that we will run at most 2^10=1024 parallel instances of findSolutionsForFixedA0 below.
		if i<len(S):
			S0.append(S[i]);
	
	for setA0 in Subsets(S0):
		A0 = setA0.list();
		#We only iterate over those A\dot\cup B\dot\cup C = S for which A has the biggest weight:
		#However this cannot be tested so far:
		#if weight(A0,vBounds0)^3 < weightOfS:
		#    continue;
		A0.sort();
		parameters.append((copy(A0),S0,S,vBounds,vBounds0));
		
	#Setup parallel computing:
	gen = findSolutionsForFixedA0(parameters);
	
	for x in gen:
		solutions.update(x[1]);

	return;

def SUE_tryDeWegersReduction(S,OldBound,NewBound,makeALog=True,keepOldLogMessages=True,parallelIterator='fork'):
	'''
	Returns True if we could reduce OldBound to NewBound successfully.

	More precisely:
	Associate to any solution (a,b,c) a number m(a,b,c), which is defined as
	m(a,b,c) := max(log(p)*ord_p(x): p in S, x in {a,b,c}).
	This method returns True if we can prove that there exists no primitive solution (a,b,c)
	with NewBound < m(a,b,c) <= OldBound.
	'''

	global numCPUs;

	def deWegerGamma(p,S,vNewBound,star=False):
		#Compute lattice Gamma_m or Gamma_m^star, in de Weger's notation.
		#Assumption: len(S) >= 2.
		#Returns None if VNewBound is too small!

		SwoP = copy(S);
		SwoP.remove(p);

		#m + m0 = vNewBound-1
		#prec = m + m0

		#Determine m0, the smallest order of log(q) for q in S\p.
		smallPrec = 2;
		while True:
			K = Qp(p,smallPrec);
			m0 = +Infinity;
			someLogIsNonzero = False;
			for q in SwoP:
				qlogp = K(q).log();
				if not qlogp.is_zero():
					someLogIsNonzero = True;
				qordp = qlogp.ordp();
				#print p, q, qordp, qlogp;
				if m0 > qordp:
					m0 = qordp;
					q0 = q;
			if someLogIsNonzero:
				break; #m0 is determined
			else:
				#All logs were zero, need to restart with larger precision:
				smallPrec += 2;
				continue;
		#print q0, qordp;
		
		m = vNewBound-1-m0;
		if m<=0:
			return None;
		prec = m+m0;
		K = Qp(p,prec=prec);
		
		s = len(S);
		L = identity_matrix(s-1);
		L[-1,-1] = p^m;
		logs = {}
		for q in SwoP:
			logs[q] = K(q).log();
		SwoPwoQ0 = copy(SwoP);
		SwoPwoQ0.remove(q0);

		for i in range(s-2):
			q = SwoPwoQ0[i];
			theta = -logs[q]/logs[q0];
			L[-1,i] = theta.lift() % p^m;

		if not star:
			return L;
		else:
			raise NotImplementedError("Error: Gamma_m^star is not implemented yet!");

		#Now we compute a sublattice Gamma_m^star, as in [de Weger, Sect. 5.B.]
		#It's columns give a basis for the set of all vectors alpha in Z^{S\p}
		# such that prod_{q in S\p} p^{alpha_q} = +-1 mod q^{vNewBound+1}
		
		if p in [2,3]:
			return L;

		Fp = FiniteField(p);
		zeta = Fp.zeta();

		def kOfX(x,SwoPwoQ0,q0,Fp,zeta):
			product = Fp(1);
			for i in range(len(SwoPwoQ0)):
				product *= Fp(SwoPwoQ0[i])^x[i];
			product *= Fp(q0)^x[-1];
			return product.log(zeta);

		k = gcd([kOfX(x,SwoPwoQ0,q0,Fp,zeta) for x in L.columns()]);

		#phi = 
		#... to do!

		raise NotImplementedError();
	
	@parallel(p_iter=parallelIterator,ncpus=numCPUs)
	def deWegerReduceBound(p,S,OldBound,NewBound):
		#Returns whether we can prove here that all solutions for which
		#p appears with exponent at most OldBound actually appears with
		#exponent at most NewBound.

		vNewBound = (RIF(NewBound)/RIF(p).log()).lower().floor();
		vOldBound = (RIF(OldBound)/RIF(p).log()).upper().floor();

		#print vOldBound, vNewBound;

		if S==[]:
			return vNewBound>=0;
		if len(S)==1:
			if 2 in S:
				return vNewBound>=1;
			else:
				return vNewBound>=0;

		L = deWegerGamma(p,S,vNewBound);
		if L == None:
			#this means that vNewBound is too small
			return False;
		
		v = my_ShortestVector_viaLattice(L);
		vNormSq = sum([x^2 for x in v]);
		if vNormSq > (len(S)-1)*vOldBound^2:
			return True;
		else:
			return False;	

	global LogMessages;

	t00 = walltime();    

	#In case S is actually an instance of my SData class:
	if S.__class__.__name__ != 'list':
		S = S.S; 

	if makeALog and (not keepOldLogMessages):
		LogMessages = [];

	'''
	for p in S:
		if not deWegerReduceBound(p,S,OldBound,b0,solutions):
			reductionFailed = True;
			break;
	'''
	#Setup parallel computing:
	parameters = [];
	for p in S:
		parameters.append((p,S,OldBound,NewBound));    
	gen = deWegerReduceBound(parameters);
	for x in gen:
		if not x[1]: #reduction failed
			return False;

	return True;

def SUE_deWegerReducedBound(S,OldBound,makeALog=True,keepOldLogMessages=True,parallelIterator='fork'):
	'''
	#Computes a de Weger reduced bound from the given OldBound.
	#Note: We use a slightly simplified version, namely we use the bigger
	#lattice Gamma_m instead of Gamma_m^* (in de Weger's notation from [deW87, Sect. 5.B].
	'''

	global LogMessages;

	t00 = walltime();    

	#In case S is actually an instance of my SData class:
	if S.__class__.__name__ != 'list':
		S = S.S; 

	if makeALog and (not keepOldLogMessages):
		LogMessages = [];

	t0 = walltime();
	b0 = 10;
	if b0>=OldBound:
		return OldBound;
	while True:
		if makeALog:
			addLogMessage("Try "+str(b0));

		reductionSucceeded = SUE_tryDeWegersReduction(S,OldBound,b0,makeALog=makeALog,keepOldLogMessages=True,parallelIterator=parallelIterator);

		if reductionSucceeded:
			break; #New bound bo worked!
		else:
			b0 = (1.3*b0).floor();
			continue;
		
	if makeALog:
		addLogMessage("Reduced bound: "+str(b0)+", time used: "+str(walltime(t0)));    

	return b0;

def SUE_decreaseBounds(S,BoundsOld,BoundsNew,maxFinckePohstSolutions=None,solutions=None,parallelIterator='fork'):
	'''
	Input:
		S - list of primes or an instance of SData
		BoundsOld - list of bounds [b1,b2,...], with the following meaning:
			We only look for solutions (a,b,c) such that for each x in {a,b,c}, and each k, and each k pw. distinct primes p_1..p_k in S,
			min(|x|_p1,...,|x|_pk) <= bk.
		BoundsNew - list of bounds [b1,b2,...], with the following meaning:
			We omit solutions (a,b,c) such that for each x in {a,b,c}, and each k, and each k pw. distinct primes p_1..p_k in S,
			min(|x|_p1,...,|x|_pk) <= bk.

	All solutoins (a,b,c) "between" these two bounds will be added via SUE_addSolutions(a,b,c,solutions),
	except possibly for (1,1,2)!
	
	Output:
		A boolean - depending on whether maxFinckePohstSolutions was chosen big enough.
	'''
	
	def finckePohst_callback(vecSolution,args):
		Ps = args[0];
		SwoPs = args[1];
		numBounds = args[2];
		vBoundsOld = args[3];
		vBoundsNew = args[4];
		L = args[5];
		solutions = args[6];
		
		k = len(Ps)-1;
		
		FPsolution = (L * vecSolution).list();
		
		
		#Check whether some exponent exceeds the old bound:
		tooBig = false;
		for i in range(len(FPsolution)):
			if abs(FPsolution[i]) > vBoundsOld[SwoPs[i],0]:
				tooBig = true;

		if not tooBig:
			#Check whether the (k+1)-wise minima of the POSITIVE exponents are not too big:
			numBoundKGotExeeded = [0 for i in range(numBounds)];
			for i in range(len(FPsolution)):
				for K in range(numBounds-1,0,-1):
					 if FPsolution[i] > vBoundsOld[SwoPs[i],K]:
						 numBoundKGotExeeded[K] = numBoundKGotExeeded[K] + 1;
						 if numBoundKGotExeeded[K] > K:
							 tooBig = True;
							 break;
					 else:
						 break;
				if tooBig:
					break;

		if not tooBig:
			#Check whether the (k+1)-wise minima of the NEGATIVE exponents are not too big:
			numBoundKGotExeeded = [0 for i in range(numBounds)];
			for i in range(len(FPsolution)):
				for K in range(numBounds-1,0,-1):
					 if -FPsolution[i] > vBoundsOld[SwoPs[i],K]:
						 numBoundKGotExeeded[K] = numBoundKGotExeeded[K] + 1;
						 if numBoundKGotExeeded[K] > K:
							 tooBig = True;
							 break;
					 else:
						 break;
				if tooBig:
					break;
		
				
		#tooBig = False;
		
		if not tooBig:
			primeExponentList = [];
			for p in Ps:
				primeExponentList.append([p,vBoundsNew[p,k]+1]);
			SUE_checkSolution(FPsolution,SwoPs,primeExponentList,solutions);
		
	global numCPUs;
		
	@parallel(p_iter=parallelIterator,ncpus=numCPUs)
	def findSolutionsForFixedPs(Sdata,listOfPs,vBoundsOld,vBoundsNew,BoundsOld,BoundsNew,maxFinckePohstSolutions):
		#Output: Refurns (FPmaxSolutionsNotExceeded,solutions), where 
		#        FPmaxSolutionsNotExceeded - false iff some Fincke-Pohst call returns more than maxFinckePohstSolutions solutions
		#        solutions - set of all solutions that have been found in this instance.

		S = Sdata.S;

		solutions = set([]);
		
		numBounds = len(BoundsOld);

		for Ps in listOfPs:
			k = len(Ps)-1;
			
			
			BoundsCurrent = copy(BoundsOld);
			#Assume that the new bounds have been already established for k' < k:
			for l in range(k):
				for j in range(l,numBounds):
					if BoundsCurrent[j] > BoundsNew[l]:
						BoundsCurrent[j] = BoundsNew[l];

			#print "Ps =",Ps;
			#print vBoundsOld;
			#print vBoundsNew;
		
			SwoPs = [];
			for q in S:
				if (q not in Ps) and vBoundsOld[q,0]>0:
					SwoPs.append(q);
			SwoPsSquared = [];
			for q in SwoPs:
				SwoPsSquared.append(q^2);
			
			#Now we assume that each p in Ps appears with exponent at least vBoundsNew[p,k]+1 in c:

			B = range(len(SwoPs));
			n = 1;
			phi = 1;
			for p in Ps:
				n = n * p^(vBoundsNew[p,k]+1);
				phi = phi * p^vBoundsNew[p,k] * (p-1);
			for i in range(len(SwoPs)):
				B[i] = zero_vector(len(SwoPs)).list();
				B[i][i] = phi;
			R = IntegerModRing(n);

			#print "Start Teske...", Ps, n
			primesPossiblyDividingGroupOrder = set([]);
			for p in Ps:
				primesPossiblyDividingGroupOrder.update(Sdata.primesDividingGroupOrderOfZmodPtoTheNstar[p]);
			L = matrix(teskeMinimize(SwoPsSquared,B,R,primesPossiblyDividingGroupOrder)).transpose();
			#print L
			#print "... Teske done."
		
			scaleRows = [];
			normSquaredBound = 0;
			factor = 100;
			for q in SwoPs:
				scaleRows.append(N(factor*log(q)).floor());
			normSquaredBound = 0;
				
			m = BoundsOld[0];
			for i in range(len(SwoPs)):
				normSquaredBound = normSquaredBound + (BoundsCurrent[min((i/2).floor(),len(BoundsCurrent)-1)])^2;
			normSquaredBound = normSquaredBound * factor^2;
				
		   
			L2 = matrix.diagonal(scaleRows) * L;
			#print L;
			#print scaleRows;
			#print L2;
			
			FPargs = (Ps,SwoPs,numBounds,vBoundsOld,vBoundsNew,L,solutions);
		
			[notTooManySolutions,numSolutions] = my_finckePohst_viaLattice(L2,normSquaredBound, \
												 solutionList=None,maxNumSolutions=maxFinckePohstSolutions,callback=finckePohst_callback,callbackArgs=FPargs);
								
			if not notTooManySolutions:
				if aLotOutput:
					print "Not all solutions got checked, numSolutions =", numSolutions;
				return (false,solutions);
					
			
			if aLotOutput:
				print numSolutions;
				
			#Fincke-Pohst omits the zero vector (on purpose).
			#We omit it as well, since it gives only solutions with a and b in {1,-1} (i.e. only 1+1=2), and it has to be checked every single time.
			#Thus the following is commented out:
			#solutions.append(zero_vector(len(SwoP))); 
			
		return (true,solutions);

	#In case S is not yet an instance of my SData class:
	if S.__class__.__name__ == 'list':
		Sdata = SData(S);
	else:
		Sdata = S;
		S = Sdata.S; 

	numBounds = max(len(BoundsOld),len(BoundsNew));

	while len(BoundsOld)<numBounds:
		BoundsOld.append(BoundsOld[len(BoundsOld)-1]);
	while len(BoundsNew)<numBounds:
		BoundsNew.append(BoundsNew[len(BoundsNew)-1]);
	for i in range(1,numBounds):
		if BoundsOld[i] > BoundsOld[i-1]:
			BoundsOld[i] = BoundsOld[i-1];
		if BoundsNew[i] > BoundsNew[i-1]:
			BoundsNew[i] = BoundsNew[i-1];

	vBoundsOld = {};
	vBoundsNew = {};

	listOfPs = [];
	   
	for k in range(numBounds):
		for p in S:
			vBoundsOld[p,k] = N(BoundsOld[k]/log(p)).floor();
			vBoundsNew[p,k] = N(BoundsNew[k]/log(p)).floor();
			
	#print vBoundsOld;        
	#print vBoundsNew;        

	for k in range(numBounds):

		if BoundsOld[k]<=BoundsNew[k]: #nothing to do
			continue;
		
		#Assume that for k' = k-1 the new bound is already established, and now check whether this already implies the bound for k:
		if k>=1 and BoundsNew[k-1] == BoundsNew[k]:
			continue;

		#print "k =",k;

		for setPs in Subsets(S,k+1): #subsets of S of size k+1
			Ps = setPs.list();
			Ps.sort();
			
			#Check whether bounds are already implicit from the old bound, or the newly obtained one from smaller k:
			boundsImplicitFromOldBounds = True;
			for p in Ps:
				if vBoundsOld[p,k]>vBoundsNew[p,k]:
					boundsImplicitFromOldBounds = False;
					break;
			if boundsImplicitFromOldBounds:
				#print "Ps =",Ps,"-> bound already implicit from old bounds";
				continue;
				
			boundsImplicitFromSmallerK = False;    
			for Ps1 in Subsets(Ps):
				k1 = len(Ps1)-1;
				if k1>=0 and k1<k:
					boundsImplicitByThisPs1 = True;
					for p1 in Ps1:
						if vBoundsNew[p1,k1]>vBoundsNew[p1,k]:
							boundsImplicitByThisPs1 = False;
							break;
					if boundsImplicitByThisPs1:
						#print "Ps =",Ps,"-> bound already implicit from",Ps1;
						boundsImplicitFromSmallerK = True;
						break;
			if boundsImplicitFromSmallerK:
				continue;
			
			listOfPs.append(copy(Ps));    
			#parameters.append((S,Ps,vBoundsOld,vBoundsNew,BoundsOld,BoundsNew,maxFinckePohstSolutions));    

	if listOfPs == []:
		return True;

	#Cut listOfPs into at most maxNumProcesses many pieces:
	parameters = [];
	maxNumProcesses = max(1,len(listOfPs)); #1024; #The problem here with 1024 is that sometimes several Ps that take the longest time will end up in the same process, and thus essentially only one process is running for most of the time.
	parametersPerProcess = max(1,floor(len(listOfPs)/maxNumProcesses));
	PsIndex = 0;
	while PsIndex < len(listOfPs):
		PsForCurrentProcess = [];
		for i in range(parametersPerProcess):
			if PsIndex < len(listOfPs):
				PsForCurrentProcess.append(listOfPs[PsIndex]);
				PsIndex = PsIndex + 1;
		parameters.append((Sdata,PsForCurrentProcess,vBoundsOld,vBoundsNew,BoundsOld,BoundsNew,maxFinckePohstSolutions));    

	#Setup parallel computing:
	gen = findSolutionsForFixedPs(parameters);
	for x in gen:
		solutions.update(x[1][1]);
		if not x[1][0]: #the Fincke-Pohst maxSolutions was exceeded
			#print "maxFinckePohstSolutions got exceeded!";
			#print x
			return False;

	return True;

def SUE_innitialHeightBound(S,precision=RR.prec()):
	'''
	Input:
		S - a finite set of primes

	Output:
		An upper bound for log(max(|a|,|b|,|c|)) valid for all solutions (a,b,c) of the S-unit equation.

	Reference:
		[vKM16], Prop. 10.7.
	'''

	#A first simple bound from [vKM15] is
	#HeightBound = (NS/5*(12*log(R(NS))+8*log(max(1,log(log(R(NS)))))+35)+46);
	#Instead we use an improved but a bit more complicated bound:

	R = RealIntervalField(precision);
	NS = prod(S);
	Sand2 = copy(S);
	if 2 not in S:
		Sand2 += [2];	
	N = 2^4 * NS; #Note that e from the paper is bounded by 4.
	#Now we compute alphaBar(N):
	s0N = R(N);
	sInfinityN = R(1);
	d = R(N);
	l = R(N/6);
	lStar = R(N/6);
	for p in Sand2:
		#compute exponent n of p in N:
		if p==2:
			n = 5;
		else:
			n = 1;
		if n>=2:
			s0N *= 1-1/p^2;
			sInfinityN *= (p-1)*p^floor(n/2-1);
		d *= 1+1/p;
		l *= p+1;
		lStar *= 1+1/p;

	gUpperBound = 1+d/12; #Upper bound for the genus of the corresponding modular curve.
	M = R(s0N/12 - sInfinityN/2 + 1/3 + 1/4); #Rounding up and this minus sign is indeed no problem here.
	betaBar = R(1/2*M*log(M)+5/8*M*(18+log(l)));
	betaPrime = R(M*(1/2*log(M) + 3/4*log(l) + log(R(8.5))));
	betaBarStar = R(1/2*gUpperBound*log(gUpperBound*lStar)+1/2*lStar*log(4+4*log(lStar)));
	alphaBar = min(betaBar, betaBarStar, betaPrime);
	alpha = alphaBar; #The actual alpha is actually slightly smaller, but more difficult to compute.

	HeightBound = 6/5 * alphaBar + 28;

	#print "Optimized HeightBound:",HeightBound;
	#print "Simple bound used before:", (NS/5*(12*log(R(NS))+8*log(max(1,log(log(R(NS)))))+35)+46);
	#print "Simple bound from Prop. 10.2.:", 12/5*NS*log(R(NS)) + 9/10*NS*log(max(1,log(log(16*R(NS))))) + R(8.26)*NS + 28;

	return HeightBound.upper();	

########################################################################
### Main methods #######################################################
########################################################################

def SUE_solve(S,saveToFile=False,solutions=None,keepOldLogMessages=False,makeALog=False,parallelIterator='fork'):
	'''
	Input:
		S - list of rational primes or an instance of SData
		saveToFile - if true the solutions will be saved to two files (one text-file and one sobj-file)
		solutions - either None, or a set: If it's a set, then the solution set will be added to it.

	Output:
		solutions - the set of solutions (together with what the parameter 'solutions' contained when calling this function).
	'''

	def boundsForTinySolutions(b,numBounds):
		result = [];
		for i in range(numBounds):
			result.append((b/(i+1)).floor());
		return result;
		
	global LogMessages;

	t00 = walltime();

	#In case S is not yet an instance of my SData class:
	if S.__class__.__name__ == 'list':
		Sdata = SData(S);
	else:
		Sdata = S;
		S = Sdata.S; 

	if solutions == None:
		solutions = set([]);
	if makeALog and (not keepOldLogMessages):
		LogMessages = [];
	if makeALog:
		addLogMessage("Number of available CPUs: "+str(sage.parallel.ncpus.ncpus()));
		addLogMessage("Number of CPUs we use: "+str(numCPUs));

	#From our vKM-paper:
	#In particular we have that each p^alpha appearing the prime factorization of a, b, and c satisfies:
	#      alpha*log(p) <= HeightBound
	NS = prod(S);
	HeightBound = SUE_innitialHeightBound(S);
	if makeALog:
		print "S =", S;
		print "NS =",NS;
		print "Height bound from paper:",HeightBound;

	#print "S =",S; #debug

	b = HeightBound;

	#de Weger reduction:
	if makeALog:
		addLogMessage("Use simplified version of de Weger reduction to reduce it to some reasonable bound (probably smaller than 1000):");
	for i in range(1): 
		bNew = SUE_deWegerReducedBound(S,b,makeALog=makeALog,keepOldLogMessages=True,parallelIterator=parallelIterator);
		if bNew < b:
			b = bNew;
			continue;
		else:
			break;

	#Now reduce b by a factor using de Weger:
	if makeALog:
		addLogMessage("Now reduction by a factor using de Weger:");
	while b>=10:
		t0 = walltime();
		bNew = (b/1.3).floor();
		oldNumSolutions = len(solutions);
		if SUE_tryDeWegersReduction(S,b,bNew,makeALog=makeALog,keepOldLogMessages=True,parallelIterator=parallelIterator):
			b = bNew;
			if makeALog:
				logMessage = "New bound: "+str(b)+", time used: "+str(walltime(t0));
				#logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
		else:
			if makeALog:
				logMessage = "Quick reduction to: "+str(bNew)+" was not possible, time used: "+str(walltime(t0));
				#logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
			break;


	#Now reduce b0 stepwise using de Weger:
	if makeALog:
		addLogMessage("Now stepwise reduction using de Weger:");
	while b>=1:
		t0 = walltime();
		bNew = b-1;
		oldNumSolutions = len(solutions);
		if SUE_tryDeWegersReduction(S,b,bNew,makeALog=makeALog,keepOldLogMessages=True,parallelIterator=parallelIterator):
			b = bNew;
			if makeALog:
				logMessage = "New bound: "+str(b)+", time used: "+str(walltime(t0));
				#logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
		else:
			if makeALog:
				logMessage = "Quick reduction to: "+str(bNew)+" was not possible, time used: "+str(walltime(t0));
				#logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
			break;


	#Now reduce b by a factor using Teske:
	if makeALog:
		addLogMessage("Now reduction by a factor using Teske:");
	while b>=1:
		t0 = walltime();
		bNew = (b/1.3).floor();
		oldNumSolutions = len(solutions);
		if SUE_decreaseBounds(Sdata,[b],[bNew],0,solutions=solutions,parallelIterator=parallelIterator):
			b = bNew;
			if makeALog:
				logMessage = "New bound: "+str(b)+", time used: "+str(walltime(t0));
				logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
		else:
			if makeALog:
				logMessage = "Quick reduction to: "+str(bNew)+" was not possible, time used: "+str(walltime(t0));
				logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
			break;

	if b==0:
		if (1,1,2) not in solutions:
			logMessage = "Forgot to add (1,1,2) (on purpose), do this now."
			#Here the purpose is that in SUE_decreaseBounds we don't want FP to return the origin all the time. This misses only the solution (1,1,2), because only here a and b can be both invertible.
			addLogMessage(logMessage);
			SUE_addSolution(1,1,2,solutions);
			

	'''
	#Now reduce b0 stepwise using Teske:
	if makeALog:
		addLogMessage("Now stepwise reduction using Teske:");
	while b>=1:
		t0 = walltime();
		bNew = b-1;
		oldNumSolutions = len(solutions);
		if SUE_decreaseBounds(Sdata,[b],[bNew],1000,solutions,parallelIterator):
			b = bNew;
			if makeALog:
				logMessage = "New bound: "+str(b)+", time used: "+str(walltime(t0));
				logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
		else:
			if makeALog:
				logMessage = "Quick reduction to: "+str(bNew)+" was not possible, time used: "+str(walltime(t0));
				logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
			break;
	'''

	'''
	#Now reduce b0 quickly using Teske:
	while b>=3:
		t0 = walltime();
		bNew = floor(b/1.3);
		oldNumSolutions = len(solutions);
		if SUE_decreaseBounds(Sdata,[b],[bNew],1000,solutions,parallelIterator):
			b = bNew;
			if makeALog:
				logMessage = "New bound: "+str(b)+", time used: "+str(walltime(t0));
				logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
		else:
			if makeALog:
				logMessage = "Quick reduction to: "+str(bNew)+" was not possible, time used: "+str(walltime(t0));
				logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
			break;
	#if b==1:
	#    SUE_addSolution(1,1,2);
	#    return;
	'''
			
	#Now reduce b slowly:
	if makeALog:
		addLogMessage("Now we reduce the bound slowly and simultaneously enumerate tiny solutions:");

	numBounds = max((len(S)/3).floor(),1); #This is obtained from a heuristic, it makes sense to take numBounds between 1 and s/3.

	maxTimeToDecreaseBounds = 0.0;

	bEnumeratedSoFar = 0;
	maxTimeToEnumerateTinySolutions = 0.001; #we want to start with decreasing Bound.

	OldBounds = [b];
			
	while b>bEnumeratedSoFar:
		#Either we decrease the bounds using Fincke-Pohst, or we enumerate more tiny solutions, depending on what took less time previously:
		if b>=2 and maxTimeToDecreaseBounds <= maxTimeToEnumerateTinySolutions:
			#Decrease Bounds:
			t0 = walltime();
			bNew = b-1;
			NewBounds = boundsForTinySolutions(bNew,numBounds);
			oldNumSolutions = len(solutions);
			if SUE_decreaseBounds(Sdata,OldBounds,NewBounds,maxFinckePohstSolutions=None,solutions=solutions,parallelIterator=parallelIterator): 
				b = bNew;
				#print "New bound:",NewBounds;
			else:
				print "We must enumerate the rest!"; #or enlarge the 5000000. This might indeed make sense for large S!
				SUE_enumerateTinySolutions(S,OldBounds,solutions);
				break;
			timeToDecreaseBounds = walltime(t0);
			maxTimeToDecreaseBounds = max(maxTimeToDecreaseBounds,timeToDecreaseBounds);
			if makeALog:
				logMessage = "New bound: "+str(NewBounds);
				logMessage = logMessage + ", timeToDecreaseBounds: "+str(timeToDecreaseBounds);
				logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);
			OldBounds = copy(NewBounds);
		else:
			t0 = walltime();
			if b-bEnumeratedSoFar >= 4:
				bEnumeratedSoFar = bEnumeratedSoFar + 2;
			else:
				bEnumeratedSoFar = bEnumeratedSoFar + 1; #should we increase the increment?
			Bounds = boundsForTinySolutions(bEnumeratedSoFar,numBounds);
			oldNumSolutions = len(solutions);
			SUE_enumerateTinySolutions(S,Bounds,solutions,parallelIterator=parallelIterator);
			timeToEnumerateTinySolutions = walltime(t0);
			maxTimeToEnumerateTinySolutions = max(maxTimeToEnumerateTinySolutions,timeToEnumerateTinySolutions);
			if makeALog:
				logMessage = "New bound for tiny solutions: "+str(Bounds);
				logMessage = logMessage + ", timeToEnumerateTinySolutions: "+str(timeToEnumerateTinySolutions);
				logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
				addLogMessage(logMessage);

	totalTime = walltime(t00);
	if makeALog:
		addLogMessage("Finished! Total time: "+str(totalTime));
		addLogMessage("Number of solutions: "+str(len(solutions)));

	if saveToFile:
		#First save the sage object 'solutions':
		save(solutions,"solutions_"+myListToStr(S,'_'));
		
		#Furthermore save the solutions to a text file:
		solutionsList = [(myRadical(a*b*c),a,b,c,quality(a,b,c)) for (a,b,c) in solutions];
		solutionsList.sort();
		out = file("solutions_"+myListToStr(S,'_')+'.txt','w')
		#out.write("###\n");
		out.write("# List of all triples (a,b,c) satisfying\n");
		out.write("#  - a+b=c,\n");
		out.write("#  - 0<a<=b<c, and\n");
		out.write("#  - rad(abc) | "+myListToStr(S,"*")+".\n");
		out.write("# It contains "+str(len(solutions))+" triples in total.\n");
		out.write('# Format: "r: a + b = c (q)", where r=rad(abc) is the radical and q=log(c)/log(r) is the quality.\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2014.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		#out.write("###\n");
		out.write("#\n");
		for (r,a,b,c,q) in solutionsList:
			#out.write(str(r)+": "+str(a)+" + "+str(b)+" = "+str(c)+" ("+str(q)+")\n");
			out.write("%d: %d + %d = %d (%.4f)\n" % (r,a,b,c,q));
		out.close();
		
		#Furthermore save log:
		if makeALog:
			out = file("log_"+myListToStr(S,'_')+'.txt','w');
			for msg in LogMessages:
				out.write(msg+"\n");
			out.close();

	return solutions;

def SUE_findAllSolutionsUpToAGivenRadical(maxRadical,saveToFile=False):
	'''
	Input:
		maxRadical - a positve integer
		saveToFile - if true the solutions will be saved to two files
		             (one text-file and one sobj-file)

	Output:
		solutions - the set of solutions (a,b,c) to the S-unit equation
		            (up to symmetry) with bounded radical:
		              rad(abc) <= maxRadical
	'''

	global solutions;
	global LogMessages;
	global numCPUs;
		
	@parallel(p_iter='fork',ncpus=numCPUs)
	def solutionsForGivenS(S):
		t0 = walltime();
		result = set([]);
		#print S;
		SUE_solve(S,saveToFile=False,solutions=result,keepOldLogMessages=True,makeALog=False,parallelIterator='reference');
		t = walltime(t0);
		return (result,t);

		
	solutions = set([]);

	LogMessages = [];
	t00 = walltime();

	t0 = walltime();
	P = prime_range(maxRadical+1); #set of all primes <= maxRadical
	P.append(maxRadical+1);
	addLogMessage("Computed primes <= %d, time used: %f." % (maxRadical,walltime(t0)));

	numRadicals = 0;

	##Old non-parallel code:
	#for r in range(2,maxRadical+1,2):
	#    f = factor(r);
	#    squarefree = true;
	#    S = [];
	#    for (p,alpha) in f:
	#        if alpha>=2:
	#            squarefree = false;
	#        S.append(p);
	#    if squarefree:    
	#        Q = P.difference(set(S));
	#        if len(Q)==0 or min(Q)*r>maxRadical:
	#            #r is a maximal squarefree number <= maxRadical with respect to integer multiples.
	#            addLogMessage("######################## New r = "+str(r)+" ########################");
	#            addLogMessage("S = "+str(S));
	#            numRadicals = numRadicals + 1;
	#            numSolutionsSoFar = len(solutions);
	#            SUE_solve(S,saveToFile=False,solutions=solutions,keepOldLogMessages=True,makeALog=False,parallelIterator='reference');
	#            addLogMessage("#new solutions = "+str(len(solutions)-numSolutionsSoFar));

	t0 = walltime();
	parameters = [];
	for r in range(2,maxRadical+1,4):
		f = factor(r);
		squarefree = true;
		S = [];
		for (p,alpha) in f:
			if alpha>=2:
				squarefree = false;
			S.append(p);
		if squarefree:    
			minPrimeNotInS = 0;
			for p in P:
				if p not in S:
					minPrimeNotInS = p;
					break;
			if minPrimeNotInS*r>maxRadical:
				#r is a maximal squarefree number <= maxRadical with respect to integer multiples.
				parameters.append(S);
				numRadicals = numRadicals + 1;

	#addLogMessage(str(parameters));
	addLogMessage("Computed all %d relevant sets S, time used: %f." % (len(parameters),walltime(t0)));
				
	#Do parallel computing:
	gen = solutionsForGivenS(parameters);
	for x in gen:
		numSolutionsSoFar = len(solutions);
		solutions.update(x[1][0]);
		S = x[0][0][0];
		r = prod(S);
		timeThisProcessTook = x[1][1];
		addLogMessage("#sol. = %d, r = %d, S = %s, time = %.2f" % (len(solutions)-numSolutionsSoFar,r,str(S),timeThisProcessTook));
		
		#str(len(solutions)-numSolutionsSoFar)+" new solutions for r = "+str(r)+", S = "+str(S)+". Time used: "+timeThisProcessTook);
	 
	totalTime = walltime(t00);
	addLogMessage("########################################################################");
	addLogMessage("Finished. Total time: "+str(totalTime)+". Number of maximal radicals: "+str(numRadicals)+". Number of solutions: "+str(len(solutions)));


	if saveToFile:
		#First save the sage object 'solutions':
		save(solutions,"solutions_uptoRadical_"+str(maxRadical));
		
		#Furthermore save the solutions to a text file:
		solutionsList = [(myRadical(a*b*c),a,b,c,quality(a,b,c)) for (a,b,c) in solutions];
		solutionsList.sort();
		out = file("solutions_uptoRadical_"+str(maxRadical)+'.txt','w')
		#out.write("###\n");
		out.write("# List of all triples (a,b,c) satisfying\n");
		out.write("#  - a+b=c,\n");
		out.write("#  - 0<a<=b<c, and\n");
		out.write("#  - rad(abc) <= "+str(maxRadical)+".\n");
		out.write("# It contains "+str(len(solutions))+" triples in total.\n");
		out.write('# Format: "r: a + b = c (q)", where r=rad(abc) is the radical and q=log(c)/log(r) is the quality.\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2014.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		#out.write("###\n");
		out.write("#\n");
		for (r,a,b,c,q) in solutionsList:
			#out.write(str(r)+": "+str(a)+" + "+str(b)+" = "+str(c)+" ("+str(q)+")\n");
			out.write("%d: %d + %d = %d (%.4f)\n" % (r,a,b,c,q));
		out.close();
		
		#Furthermore save log:
		out = file("log_uptoRadical_"+str(maxRadical)+'.txt','w');
		for msg in LogMessages:
			out.write(msg+"\n");
		out.close();
	return solutions;

########################################################################
### Tests ##############################################################
########################################################################

#aLotOutput = True;
FinckePohstVersion = 'mine'; #the numerically robust version

def SUE_searchForLargeSolutions(S,solutions=None):
	'''
	Input:
		S - list of primes
		saveToFile - if true the solutions will be saved to two files (one text-file and one sobj-file)
		solutions - either none, or a set: If it's a set, then the solution set will be added to it.
    '''
	
	def boundsForTinySolutions(b,numBounds):
		result = [];
		for i in range(numBounds):
			result.append((b/(i+1)).floor());
		return result;
		
	global LogMessages;
	
	t00 = walltime();    
	
	if solutions == None:
		solutions = set([]);
	LogMessages = [];
	
	addLogMessage("Number of available CPUs: "+str(sage.parallel.ncpus.ncpus()));
	addLogMessage("Number of CPUs we use: "+str(numCPUs));

	print "S =", S;
	NS = prod(S);
	print "NS =",NS;

	#From our vKM-paper:
	#In particular we have that each p^alpha appearing the prime factorization of a, b, and c satisfies:
	#      alpha*log(p) <= HeightBound
	HeightBound = SUE_innitialHeightBound(S);
	print "Height bound from paper:",HeightBound;
	
	b0 = 5*ceil(3/2*(len(S)-1)*log(len(S)));   
	
	addLogMessage("We already start with a relatively small bound b0: "+str(b0));
	
	#Now reduce b0 quickly:
		
	b = b0;
	
	while b>=3 and len(solutions)==0:
		t0 = walltime();
		bNew = floor(b/1.3);
		oldNumSolutions = len(solutions);
		if SUE_decreaseBounds(S,[b],[bNew],1000,solutions):
			b = bNew;
			logMessage = "New bound: "+str(b)+", time used: "+str(walltime(t0));
			logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
			addLogMessage(logMessage);
		else:
			logMessage = "Quick reduction to: "+str(bNew)+" was not possible, time used: "+str(walltime(t0));
			logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
			addLogMessage(logMessage);
			break;
	#if b==1:
	#    SUE_addSolution(1,1,2);
	#    return;
			
	#Now reduce b slowly:
	if len(solutions)==0:
		addLogMessage("Now we reduce the bound slowly:");
	
	numBounds = min(3,max((len(S)/3).floor(),1)); #This is obtained from a heuristic, it makes sense to take numBounds between 1 and s/3.
	
	maxTimeToDecreaseBounds = 0.0;

	bEnumeratedSoFar = 0;
	maxTimeToEnumerateTinySolutions = 0.001; #we want to start with decreasing Bound.

	OldBounds = [b];
			
	while b>bEnumeratedSoFar and len(solutions)==0:
		#Either we decrease the bounds using Fincke-Pohst, or we enumerate more tiny solutions, depending on what took less time previously:
		if b>=2 :
			#Decrease Bounds:
			t0 = walltime();
			bNew = b-1;
			NewBounds = boundsForTinySolutions(bNew,numBounds);
			oldNumSolutions = len(solutions);
			if SUE_decreaseBounds(S,OldBounds,NewBounds,maxFinckePohstSolutions=None,solutions=solutions): 
				b = bNew;
				#print "New bound:",NewBounds;
			else:
				print "We must enumerate the rest!"; #or enlarge the 5000000. This might indeed make sense for large S!
				SUE_enumerateTinySolutions(S,OldBounds,solutions);
				break;
			timeToDecreaseBounds = walltime(t0);
			maxTimeToDecreaseBounds = max(maxTimeToDecreaseBounds,timeToDecreaseBounds);
			logMessage = "New bound: "+str(NewBounds);
			logMessage = logMessage + ", timeToDecreaseBounds: "+str(timeToDecreaseBounds);
			logMessage = logMessage + ", #new solutions: "+str(len(solutions)-oldNumSolutions);
			addLogMessage(logMessage);
			OldBounds = copy(NewBounds);
		else:
			break;
	
	totalTime = walltime(t00);
	addLogMessage("Finished! Total time: "+str(totalTime));
	addLogMessage("Number of large solutions: "+str(len(solutions)));
	
	#for s in solutions:
	#	print s;

	return solutions;

#time SUE_searchForLargeSolutions(prime_range(10));

#SUE_findAllSolutionsUpToAGivenRadical(100); #0.55 sec       
#SUE_findAllSolutionsUpToAGivenRadical(1000); #4.4 sec       
#SUE_findAllSolutionsUpToAGivenRadical(10000); #44 sec
#SUE_findAllSolutionsUpToAGivenRadical(20000); #91 sec       
#SUE_findAllSolutionsUpToAGivenRadical(100000); #7.5 min, de Weger red. made it 2.5 times faster
#SUE_findAllSolutionsUpToAGivenRadical(1000000); #
#SUE_findAllSolutionsUpToAGivenRadical(3000000); #4.58h, de Weger red. made it 7.1 times faster
#SUE_findAllSolutionsUpToAGivenRadical(10000000); #
#SUE_findAllSolutionsUpToAGivenRadical(100000000); #

#time SUE_solve(primes_first_n(1)) #0 sec, 1 solutions
#time SUE_solve(primes_first_n(2)) #0 sec, 4 solutions
#time SUE_solve(primes_first_n(3)) #0 sec, 17 solutions
#time SUE_solve(primes_first_n(4)) #1 sec, 63 solutions
#time SUE_solve(primes_first_n(5)) #7 sec, 190 solutions
#time SUE_solve(primes_first_n(6)) #11 sec, 545 solutions
#time SUE_solve(primes_first_n(7)) #32 sec, 1433 solutions
#time SUE_solve(primes_first_n(8)) #127 sec, 3649 solutions #parallel: 183 sec
#time SUE_solve(primes_first_n(9)) #581 sec, 8828 solutions 
#time SUE_solve(primes_first_n(10)) # sec, 20015 solutions #16 cpus: 180 sec
#time SUE_solve(primes_first_n(11)) #14858 sec, 44641 solutions (4.127 hours)
#time SUE_solve(primes_first_n(12)) #ca 65600 sec, 95358 solutions (18.22 hours)
#time SUE_solve(primes_first_n(13)) #199081 solutions 
#time SUE_solve(primes_first_n(14)) #412791 solutions #parallel: 331210 sec = 92 h (allerdings mit Unterbrechungen)
