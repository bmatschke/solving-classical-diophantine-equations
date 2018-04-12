# -*- coding: latin-1 -*-

########################################################################
#
# This code computes S-integral solutions of rational elliptic curves,
# in particular Mordell curves.
# Furthermore several other related diophantine equations and problems
# can be solved: Thue and Thue-Mahler equations of degree three,
# generalized Ramanujan-Nagell equations, sums of unit equations,
# and computing all rational elliptic curves with given places
# of bad reduction.
# The corresponding main methods are:
#
# - computeSIntegralPoints(E,S,...)
# - solveThueEquation(a,b,c,d,m,S,...)
# - solveThueMahlerEquation(a,b,c,d,m,S,...)
# - solveRamanujanNagellEquation_XY(b,c,S,...)
# - solveRamanujanNagellEquation_XN(b,c,d,...)
# - computeAllRationalEllipticCurvesWithGoodReductionOutsideS(S,...)
# - solveSumsOfUnitsBeingASquare(S,...)
# - solveSumsOfUnitsBeingACube(S,...)
#
# Authors: Rafael von Kaenel, Benjamin Matschke
# Licence: Creative commons BY-NC.
#
# The code is mostly explained in the authors' paper
# "Solving S-unit and Mordell equations via Shimura-Taniyama conjecture".
#
########################################################################

#
# Some major differences in the notation:
# - The height pairing matrix for the rational lower approximation h_k
#   of the Neron-Tate height h is here denoted by Qhk/Qf^2, where
#   Qhk is an integral matrix and Qf a rational number.
# - The height bound M_0 in the paper is here denoted by Mmax0/Qf^2.
#

########################################################################
### Global variables: ##################################################
########################################################################

parallelIterator = "fork"
numCPUs = min(64,sage.parallel.ncpus.ncpus());
#numCPUs = min(100,sage.parallel.ncpus.ncpus());
#numCPUs = min(128,sage.parallel.ncpus.ncpus());

#parallelIterator = "reference"
#numCPUs = 1;

pathData = "data/";
#pathMordellWeil = pathData; 
pathMordellWeil = "mordell-weil-bases/"; 

########################################################################
### Parallel computing utility: ########################################
########################################################################

def my_run_in_parallel(params,fct,print_param=False,print_result=True,return_param_index=True,returnPartialResultsIfInterrupted=False,ignoreTimeouts=False,ignoreNODATAoutputs=False,timeout=0):
	'''
	Calls fct(*p) for each p in params.
	The global variables parallelIterator and numCPUs determine,
	in which parallel way this is done.
		
	OUTPUT:
	 a list of tuples (i,param,result) where
	   i is either
	     - the index in range(len(params)) of the i'th element in the iterable params,
	       if return_param_index==True, or
	     - the i'th element of the iterable params,
	       if return_param_index==False.
	   result is the output of fuction(param);
	
	Example:
	 x = my_run_in_parallel([(n,n+3) for n in range(3)],max);
	
	During the computation, CTRL-C can be pressed to restart the computation
	of fct(*p) for those parameters p in params for which the computation
	has not yet finished (or not even started).
	To interrupt the whole computation, press CTRL-C twice within one second. 
	'''

	global parallelIterator, numCPUs;

	@parallel(p_iter=parallelIterator,ncpus=numCPUs,timeout=timeout)
	def call_function(i,param,fct):
		#print "i =",i;
		return (i,fct(*param));

	params_ex = [];
	i = 0;
	for param in params:
		params_ex.append((copy(i),param,fct));
		i += 1;

	results = [];

	while True:
		print "Remaining parameter indices:",[i for (i,p,fct) in params_ex];
		gen = call_function(params_ex);
		try:
			for x in gen:
				print "x:",x;
				print "x[1]:",x[1];
				param = x[0][0][1];

				if x[1] == "NO DATA (timed out)":
					succeeded = False;
					i = x[0][0][0];
					if print_param:
						print "Timed out for",param,"with index",i,".";
					else:
						print "Timed out for parameter with index",i,".";
					if not ignoreTimeouts:
						raise ValueError;			
				elif x[1] == "NO DATA":
					succeeded = False;
					i = x[0][0][0];
					if print_param:
						print "NO DATA for",param,"with index",i,".";
					else:
						print "NO DATA for parameter with index",i,".";
					if not ignoreNODATAoutputs:
						raise ValueError;			
				else:
					succeeded = True;
					i,output_for_i = x[1];
					if print_param:
						if print_result:
							print "Output for",param,"with index",i,"is",output_for_i;
						else:
							print "Computation for parameter",param,"with index",i,"finished.";
					else:
						if print_result:
							print "Output for parameter with index",i,"is",output_for_i;
						else:
							print "Computation with index",i,"finished.";
				params_ex_new = [(i0,p,fct) for (i0,p,fct) in params_ex if i!=i0];
				if succeeded and len(params_ex_new) < len(params_ex):
					if return_param_index:
						results.append((i,output_for_i));
					else:
						results.append((param,output_for_i));
				params_ex = params_ex_new;
					
		except KeyboardInterrupt:
			gen.close();
			print "Keyboard-Interrupt. If you want to cancel the code, press it again within the next second.";
			try:
				sleep(1);
			except KeyboardInterrupt:
				if returnPartialResultsIfInterrupted:
					return results;
				else:
					return None;
			print "Restart parallel computation.";
			continue;

		print "Finished computation!";
		break;

	return results;

########################################################################
### Repetitively used data of elliptic curve E: ########################
########################################################################

class E_Cache:
	'''
	A class that contains all additional information of the
	rational elliptic curve E that are used over and over again.
	It handles in particular the elliptic logarithms.
	'''

	def __init__(self,E,S,mwBasis,Qhk,Qf,lamdaMinQhk,timer,regularPrecision=RR.prec(),verbose=False,debugParam={}):
		#verbose = True; #DEBUG

		self.timer = timer;
		self.E = E;
		self.S = S;
		self.Sstar = copy(S);
		self.Sstar.append(Infinity);
		self.logNS = sum([log(RIF(p)) for p in S]);
		self.mwBasis = mwBasis;
		self.r = len(mwBasis);
		#Qhk/Qf^2 is a good lower bound for the height pairing matrix of E
		#with respect to the given MW base. Here, Qhk is integral, and Qf rational.
		self.Qhk = Qhk;
		self.Qf = Qf;
		self.lamdaMinQhk = lamdaMinQhk; #a lower bound on the smallest eigenvalue of Qhk.
		self.torsionPoints = E.torsion_points();
		self.torsionOrder = len(self.torsionPoints);
		self.torsionExponent = E.torsion_subgroup().exponent();
		self.ordersOfTorsionPoints = [self.torsionPoints[i].order() for i in range(self.torsionOrder)];
		self.maxSizeOfSiContainingInfinity = 1;
		self.maxSizeOfSiContaining2 = 1;
		self.refinedSieveWeights = ["placeholder",RIF(1),RIF(0.6),RIF(0.4),RIF(0.3),RIF(0.25),RIF(0.2),RIF(0.16),RIF(0.14)];
		self.cacheIsActive = bool(self.r >= 2); #For r=1, one may choose very large S, however in this case memory becomes a serious issue when caching the p-adic logs.
		if verbose:
			print "cacheIsActive =",self.cacheIsActive;
		self.logs = {};
		self.Cw1 = {};
		#[vkM]: \hat{h}(P) <= h(x(P))/2 + mu, where \hat{h} the Tate normalized height (as in Silverman).
		if E.b2() != 0:
			twoStar = 2;
		else:
			twoStar = 1;
		self.muE = 1/12*max(RIF(0),log(abs(RIF(E.j_invariant())))) + 1/12*myRRtoRIF(E.discriminant().global_height()) + 1/2*max(0,log(abs(RIF(E.b2())/12))) + 1/2*log(RIF(twoStar))
		self.mu = self.muE + myRRtoRIF(1.07);
		#We have inequalities: -mu <= h^(P) - 1/2 * h(x(P)) <= mu, see Silverman [1990]
		self.safetyBitsForRounding = 6;
		self.cKappa, self.x0 = computeX0andCKappa(self,kappa=None,verbose=verbose);
		#The following methods for the height-logarithm-sieve are explained in heightLogarithmSieve():
		self.heightLogSieve_Methods = ["NoTest","WeakHeightLogSieve","StrongHeightLogSieve","Automatic_Weak_or_NoTest","Automatic_Strong_or_NoTest"];
		if debugParam.has_key("heightLogSieve_Method"):
			self.heightLogSieve_Method = debugParam["heightLogSieve_Method"];
		else:
			self.heightLogSieve_Method = "Automatic_Weak_or_NoTest"; #Shall use this always (also the rank=1 case is dealt with reasonably).
		#self.heightLogSieve_Method = "NoTest"; #for debugging...
		#self.heightLogSieve_Method = "StrongHeightLogSieve"; #for debugging...
		self.heightLogSieve_Log = {};
		self.heightLogSieve_Prec = {};
		self.heightLogSieve_W1 = {};

		#We need to compute w1 with a certain absolute precision.
		#In Pari we can prescribe only the relative precision,
		#so we first need to estimate the order of w1.
		self.w1, self.w2 = E.period_lattice().basis(prec=regularPrecision);
		self.orderOfW1 = (log(abs(myRRtoRIF(self.w1)))/log(RIF(2))).upper().ceil();
		if verbose:
			print "Real period w1 =",self.w1;
			print "Number of bits before dot of real period w1:",self.orderOfW1;

		if verbose:
			print "Compute orders of p-adic logs..."
		self.timer.startTimer("Computing orders of p-adic logs");
		self.m = {}; #m[p] will be a positive integer such that the p-adic log of m*P will be defined (and computed) for each P in mwBasis.
		self.m[Infinity] = lcm(self.torsionExponent,E.real_components());
		self.P0 = {}; #This dict stores (for each p in S) the point of the MW basis whose p-adic log has minimal order.
		self.ordAlphaP0 = {}; #And that's the corresponding order.

		debug = False;
		
		loop = 0;
		for p in S:
			if verbose:
				print p,;
			sys.stdout.flush();

			if debug:
				print "debug 1"

			#Determine m, such that m*torsion = 0, and m*P in E^1(Qp) for each P in mwBasis:
			t = E.local_data(p).bad_reduction_type();
			#print "debug: bad reduction type:", t;
			if t is None:
				#print E.has_good_reduction(p);
				#print E.reduction(p);
				#print E.reduction(p).abelian_group();
				ep = E.reduction(p).abelian_group().exponent();
				#print ep;
			else:
				#The following is the group order and not the exponent of the group E_{ns},
				#i.e. it is an integer multiple of what is actually needed.
				#This makes computation of the p-adic logs slightly slower, but
				#the gain is that we don't need to compute the exponent of E_{ns}:
				ep = p - t; 
			self.m[p] = lcm(self.torsionExponent,E.tamagawa_exponent(p)*ep);

			if debug:
				print "t =",t;
				print "ep =",ep;
				print "m =",self.m[p];
			
			smallPrec = 4;
			while True:
				ordAlphaP0 = +Infinity;
				someLogIsNonzero = False;

				#Compute p-adic logs of m*P for each P in the MW basis:
				mwBasisLog = [self.log(P,p,smallPrec) for P in self.mwBasis];
				
				for P in self.mwBasis:
					#if debug:
					#	print "P =",P;
					#try:
					#	alphaP = P.padic_elliptic_logarithm(p,absprec=smallPrec);
					#except ValueError:
					#	smallPrec += 2;
					#	continue;
					alphaP = mwBasisLog[self.mwBasis.index(P)];
					if alphaP.is_zero()==False and alphaP.valuation()<smallPrec:
						someLogIsNonzero = True;
					ordAlphaP = alphaP.ordp();
					#print p, P, alphaP, ordAlphaP;
					if ordAlphaP0 > ordAlphaP:
						ordAlphaP0 = ordAlphaP;
						P0 = P;
				if someLogIsNonzero:
					break; #ordAlphaP0 is determined
				else:
					#All logs were zero, need to restart with larger precision:
					smallPrec += 4;
					if debug:
						print "restart with smallPrec =",smallPrec;
					continue;
			if self.r>=2:
				self.P0[p] = P0; #A point in mwBasis whose p-adic log has minimal order.
			self.ordAlphaP0[p] = ordAlphaP0; #its order
			
			loop += 1;
			if loop % 10000 == 0:
				if verbose:
					print "gc.collect()",;
				while gc.collect()>0:
					if verbose:
						print ".",;
			
			#debug:
			#if p==5:
			#	print "For p=5:";
			#	print "m =",m;
			#	print "mwBasisLogs:",mwBasisLog;
			#	return;			
			
		self.timer.endTimer("Computing orders of p-adic logs",verbose=verbose);

		if self.heightLogSieve_Method in ["StrongHeightLogSieve","Automatic_Strong_or_NoTest"]:

			self.primes_at_which_reduction_is_considered = set([]);

			if self.r == 1:
				if verbose:
					print "Compute orders of reductions of P0 at good places...";
				self.timer.startTimer("Computing orders of reductions of P0 at good places");
				self.orderOfMWBasisRed = {};
				P = self.mwBasis[0];
				loop = 0;
				for p in S:
					if self.E.has_good_reduction(p):
						self.orderOfMWBasisRed[p] = E.reduction(p)(P).order();				
						self.primes_at_which_reduction_is_considered.add(p);
					loop += 1;
					if loop % 10000 == 0:
						if verbose:
							print "gc.collect():",gc.collect();
				self.timer.endTimer("Computing orders of reductions of P0 at good places");
			else:
				
				if verbose:
					print "Compute reductions at good places...";
				self.timer.startTimer("Computing reductions at good places");
				self.discriminant = E.discriminant();
				#self.Ered = {}; Reduction of E at p ---> we don't need this in the memory
				self.mwBasisRed = {}; #Coordinate vectors of reduction of mwBasis mod p 
				self.torsionRed = {}; #Coordinate vectors of reduction of torsion points mod p 
				#self.torsionRedSet = {}; same as torsionRed, but as a set ---> as vectors are not hashable, we don't use this (tuples would be an alternative, but the addition of vectors is convenient...)
				self.EredGeneratorOrders = {};
				loop = 0;
				for p in S:
					if self.discriminant % p != 0:
						if verbose:
							print p,;
						sys.stdout.flush();
						Ered = E.reduction(p);
						#self.Ered[p] = Ered;
						Gred = Ered.abelian_group();
						self.mwBasisRed[p] = [Gred.coordinate_vector(Ered(P)) for P in self.mwBasis];
						self.torsionRed[p] = [Gred.coordinate_vector(Ered(P)) for P in self.torsionPoints];
						#self.torsionRedSet[p] = set(self.torsionRed[p]);
						self.EredGeneratorOrders[p] = Gred.generator_orders();
						self.primes_at_which_reduction_is_considered.add(p);
						if verbose:
							print "p =",p,;
							print "mwBasisRed[p] =",self.mwBasisRed[p],;
							print "torsionRed[p] =",self.torsionRed[p],;
							print "EredGeneratorOrders[p] =",self.EredGeneratorOrders[p],;
							print "len of EredGeneratorOrders[p] =",len(self.EredGeneratorOrders[p]);
						loop += 1;
						if loop % 10000 == 0:
							if verbose:
								print "gc.collect():",gc.collect();

				self.timer.endTimer("Computing reductions at good places",verbose=verbose);
			
	def log(self,P,p,prec,verbose=False):
		'''
		Computes p-adic log of m[p]*P (!!!), where p is allowed to be Infinity.
		prec is absolute precision if p is finite.
		prec is relative precision if p is infinite.
		'''
		
		if self.logs.has_key((P,p)):
			logPp = self.logs[(P,p)];
			if p == Infinity:
				if logPp.precision()>=prec:
					#print "Log was previously computed for p = infty and prec =",prec;
					return logPp.numerical_approx(prec);
				#else:
				#	print "Log computed already but not up to sufficient precision"
			else: #p = finite:
				if logPp.precision_absolute()>=prec:
					#print "Log of certain point was previously computed for p =",p,"and prec =",prec;
					return logPp.add_bigoh(prec);
				#else:
				#	print "Log computed already but not up to sufficient precision"

		m = self.m[p];
				
		if p == Infinity:
			result = (m*P).elliptic_logarithm(precision=prec); #The complex part will be zero anyway.
			#print "type of ell log at infty:",type(result);
			#if result not in RR:
			if result.__class__.__name__.startswith("Complex"):
				result = result.real();
		else:
			result = my_padic_elliptic_logarithm(m,P,p,absPrec=prec);
		if self.cacheIsActive:
			self.logs[(P,p)] = result;
		if verbose:
			print "Computed elliptic log at p =",p,"with precision",prec;
			if p == Infinity:
				print "... obtained prec =",result.prec();
			else:
				print "... obtained prec =",result.precision_absolute();
		return result;

	def roundedCtimesOmega1_preciseC_highPrecision(self,C,verbose=False,precAbs="default"):
		'''
		For the (refined) sieve at p=Infinity we first need to compute:
		- an integer close to C*omega_1 (up to an additive error of 1/2+1/2^precAbs)
		- a high precision copy of C (i.e. put some zeros at the end of C, after the comma)
		- to which precision the elliptic logs need to be computed.
		'''

		debug = False;
		#debug = True;

		if debug:
			verbose = True;
			print "C =",C;
			print "precAbs =",precAbs;

		if precAbs == "default":
			precAbs = self.safetyBitsForRounding;
			if debug:
				print "default precAbs =",precAbs;
		if self.Cw1.has_key((C,precAbs)):
			return self.Cw1[(C,precAbs)];
		#Need to compute C*w1 up to absolute precision 1/2^precAbs:
		orderOfC = max(0,RR(log(abs(C.upper()))/log(2)).ceil());
		highPrecision = max(0,orderOfC + self.orderOfW1) + 3 + precAbs;
		#Here, we use 3 bit safety (1 is necessary because of the conversion between absolute and relative precision)
		#          + precAbs bits such that we know the number up to +- 1/2^6, such that later we can round to an integer of distance at most 1/2 + 1/2^6 from this number.
		if verbose:
			print "highPrecision =",highPrecision;
			sys.stdout.flush();
		Rprec = RealField(highPrecision);
		Cprec = Rprec(C.upper());
		w1Prec = self.E.period_lattice().real_period(prec=highPrecision);
		if verbose:
			print "w1Prec =",w1Prec;
			sys.stdout.flush();
		result = ((Cprec*w1Prec).round(),Cprec,highPrecision);
		if self.cacheIsActive:
			self.Cw1[(C,precAbs)] = result;
		return result;
	
########################################################################
### Elliptic curve basics: #############################################
########################################################################

def mordellCurve(a):
	'''
	Returns the Mordell curve with Weierstrass equation y^2 = x^3 + a.
	'''
	return EllipticCurve([0,0,0,0,a]);

def ellipticCurveSMinimalModel(E,S):
	'''
	Computes S-minimal model of E, via a transformation (u,r,s,t) with
	u being an S-unit.

	INPUT:

	"E" - An elliptic curve with _integral_ coefficients.

	"S" - A finite set of (rational) primes.
	'''
	
	#Important: This works so far only if E has _integral_ Weierstrass equation.
	
	if S==[]:
		return E;
	#The problem with the following first algorithm is that it sometimes
	#minimizes too much, which would force us to enlarge the set S in general;
	#and thus we rather take a more naive algorithm below.
	#
	#Delta = E.discriminant();
	#ESmin = E;
	#for p in prime_factors(Delta):
	#	if p in S:
	#		ESmin = ESmin.local_minimal_model(p);
	#return ESmin;		

	#Naive but functional algorithm:
	#print "E =",E
	Emin = E.minimal_model();
	#print "Emin =",Emin
	iso = E.isomorphism_to(Emin);
	#print "iso from E to Emin:",iso.tuple();
	#We'll remove all primes not in S from the u-part of the transformation:
	u = iso.u;
	#print "u = ",u;
	#uS = 1;
	#for p in S:
	#	uS *= p^u.ord(p);
	uS = prod([p^u.ord(p) for p in S]);
	uWoS = u/uS;
	
	#print "u =", iso.u,", uS =", uS;
	transformation = [uS,iso.r,iso.s,iso.t];
	ESmin = E.change_weierstrass_model(transformation);
	return ESmin;

def my_padic_elliptic_logarithm(m, P, p, absPrec=20, verbose=False):
	'''
	Computes the p-adic elliptic logarithm of m*P, where
	m is some given positive integer such that m*P lies in E^1(Q_p).

	INPUT:

	"m" - An integer, such that m*P is in E^1(Q_p).

	"P" - A rational point on some rational elliptic curve.

	"p" - A prime.

	"absPrec" - An integer (default: 20). The result will be an
	element of Qp(prec) with prec>=absPrec.

	OUTPUT:

	phi - the p-adic elliptic logarithm of m*P with precision ''absPrec''.

	ALGORITHM:

	We take the ''log()'' function from the formal groups module and
	evaluate it at `-x/y`.      
	This implementation is a modification of the
	"padic_elliptic_logarithm" algorithm by Tobias Nagel,
	Michael Mardaus, and John Cremona.
	'''

	def nextPrec(prec,absPrec):
		return prec+4;

	if not p.is_prime():
		raise ValueError('p must be prime');
	debug = False;
	#debug = True;
	if debug:
		verbose = True;
	if debug:
		print "P=", P, "; p=", p, " with precision ", absPrec;
	E = P.curve()
	prec = absPrec+8; 
	if P.has_finite_order():
		return Qp(p,prec)(0);
	numLoops = 0;
	while True: #We might repeat the computation with higher precision "prec".
		numLoops += 1;
		Q_p = Qp(p, prec);
		try:
			Ep = E.change_ring(Q_p);
			mPp = m * Ep(P); #Computing m*Pp is _much_ faster than computing m*P (for large m).
			x, y = mPp.xy();
		#except (ArithmeticError, ZeroDivisionError):
		except (sage.rings.padics.precision_error.PrecisionError, ArithmeticError, ZeroDivisionError):
			if verbose:
				print " some error when computing mPp, thus restart";
			prec = nextPrec(prec,absPrec);
			continue;
		#if debug:
		#	print "x, y =", (x, y);
		vx = x.valuation();
		vy = y.valuation();
		v = vx-vy;
		if not (v > 0 and vx == -2*v and vy == -3*v):
			prec = nextPrec(prec,absPrec);
			if verbose or debug:
				print "v,vx,vy =",v,vx,vy,"thus restart...";
			continue;
		#if prec < v*absPrec:
		#	if verbose:
		#		print " prec =",prec,"< v*absPrec =",v,"*",absPrec,"=",v*absPrec,", thus restart";
		#	prec = v*absPrec;
		#	continue;
		try:
			t = -x/y;
		#except (ZeroDivisionError):
		except (ZeroDivisionError, sage.rings.padics.precision_error.PrecisionError):
			if verbose:
				print " t=-x/y is not well-defined, as y is zero mod precision, thus restart";
			prec = nextPrec(prec,absPrec);
			continue;
		if debug:
			print "t=", t, ", with valuation ", v;
		#phi = Ep.formal().log(prec=1+prec//v);
		phi = Ep.formal().log(prec=1+prec);
		phiT = phi(t);
		if phiT.precision_absolute()<absPrec:
			if verbose:
				print " phiT.prec =",phiT.precision_absolute(),"< absPrec =",absPrec,", thus restart";
			prec += v*(absPrec-phiT.precision_absolute());
			continue;
		if debug:
			print "Abs.precs.:",x.precision_absolute(),y.precision_absolute(),t.precision_absolute(),phiT.precision_absolute();
			print "Rel.precs.:",x.precision_relative(),y.precision_relative(),t.precision_relative(),phiT.precision_relative();
			print "Valuations:",x.valuation(), y.valuation(), t.valuation(), phiT.valuation();
		break; #Succeeded!

	if verbose:
		print p,"adic log computed, numLoops =",numLoops,", absPrec =",absPrec,", obtained prec =",phiT.precision_absolute();

	return phiT;

########################################################################
### MW bases of some frequently used Mordell curves: ###################
########################################################################

#Here are the smallest positive and largest negative KNOWN k for with a given rank<=12:
#(For rank<=6, these k are indeed optimal.)
kPosOfRank = [1,2,15,113,2089,66265,1358556,47550317,1632201497,185418133372,68513487607153,35470887868736225,176415071705787247056];
kNegOfRank = [-1,-2,-11,-174,-2351,-28279,-975379,-56877643,-2520963512,-463066403167,-56736325657288,-46111487743732324,-6533891544658786928];

#Mordell curves studied by [GPZ96] with S = first 8 primes:
ksGPZ96 = [-92712,-43847,-28279,32977,54225,66265,81077,92025,94636];
#Mordell curves studied by [GPZ97] with S = first 3 primes: (They actually looked at all |a|<=10000, but the following were mentioned in detail with all solutions:)
ksGPZ97 = [108,225,1025,2089];

#Mordell-Weil bases: (which are of course fully saturated)
my_mwBasis_for_mordellCurves = {};
#my_mwBasis_for_mordellCurves = dict(load("mwBases10000.sobj"));
my_mwBasis_for_mordellCurves[kPosOfRank[1]] = [(-1,1)];
my_mwBasis_for_mordellCurves[kPosOfRank[2]] = [(1,4), (109,1138)]
my_mwBasis_for_mordellCurves[kPosOfRank[3]] = [(-4,7), (2,11), (8,25)];
my_mwBasis_for_mordellCurves[kPosOfRank[4]] = [(-12,19), (-10,33), (-4,45), (3,46)];
my_mwBasis_for_mordellCurves[kPosOfRank[5]] = [(-24,229), (-9,256), (-6,257), (24,283), (51, 446)];
my_mwBasis_for_mordellCurves[kPosOfRank[6]] = [(-110,166), (-86,850), (-83,887), (-47/4,9319/8), (-11,1165), (10,1166)];
my_mwBasis_for_mordellCurves[kPosOfRank[7]] = [(-1399/4,17467/8), (-277,5128), (-121,6766), (-37,6892), (67/9,186184/27), (2047/9,207946/27), (359,9686)];
my_mwBasis_for_mordellCurves[kPosOfRank[8]] = [(-1177,1292), (-1132,13477), (-1088,18555), (-982,26177), (-656,36741), (-557,38202), (-538,38425), (34,40401)];
my_mwBasis_for_mordellCurves[kNegOfRank[1]] = [(3,5)];
my_mwBasis_for_mordellCurves[kNegOfRank[2]] = [(3,4), (15,58)];
my_mwBasis_for_mordellCurves[kNegOfRank[3]] = [(7,13), (457/16,9733/64), (799,22585)];
my_mwBasis_for_mordellCurves[kNegOfRank[4]] = [(15,32), (18,59), (30,157), (378,7349)];
my_mwBasis_for_mordellCurves[kNegOfRank[5]] = [(32,67), (34,105), (40,189), (50,311), (67,522)];
my_mwBasis_for_mordellCurves[kNegOfRank[6]] = [(2143/9,95554/27), (953/4,28339/8), (347,6388), (359,6730), (28025/64,4664243/512), (875,25864)];
my_mwBasis_for_mordellCurves[kNegOfRank[7]] = [(1553/4,10265/8), (403,2928), (1697/4,35311/8), (1363,49752), (2063,93398), (2707,140640), (129986057/44944,1480246437659/9528128)];
my_mwBasis_for_mordellCurves[kNegOfRank[8]] = [(1361,213), (1433,20535), (1662,45496), (2126,84192), (10313/4,967227/8), (2802,139564), (587417/16,450203331/64), (364857/4,220385645/8)];
my_mwBasis_for_mordellCurves[7823] = [(2263582143321421502100209233517777/143560497706190989485475151904721, 186398152584623305624837551485596770028144776655756/1720094998106353355821008525938727950159777043481)];
#For Thue equation:
#my_mwBasis_for_mordellCurves[19607184] = [];
#my_mwBasis_for_mordellCurves[39237696] = [(232,7192)];
#my_mwBasis_for_mordellCurves[40602384] = [];
#For Thue-Mahler equation:
#my_mwBasis_for_mordellCurves[1417766490000] = [];
#my_mwBasis_for_mordellCurves[5671065960000] = [(14896,-2996056)]; #actually sage can do it!
#my_mwBasis_for_mordellCurves[22684263840000] = [(50544,-12321072)];
#my_mwBasis_for_mordellCurves[332120306881440000] = [(447700,649503800), (753300,871543800)];

#Full rank sublattice of Mordell-Weil lattice: (POSSIBLY NOT fully saturated!)
my_mwSublatticeBasis_for_mordellCurves = {};
my_mwSublatticeBasis_for_mordellCurves[kPosOfRank[9]] = [(-21663/4,1304081/8), (521/4,3444837/8), (258,430622), (1037,431895), (12900097753/5645376,-5958783853959907/13413413376), (2762,454410), (1215323297/394384,-114756101613681/247673152), (34497/4,7274591/8), (891273/4,841433435/8)]; #obtained via E.gens()
my_mwSublatticeBasis_for_mordellCurves[kPosOfRank[10]] = [(-4765488/121,3626593669/1331), (-524192758/14161,7108112097309/1685159), (9612,8330759), (654297/16,748824931/64,), (356367775372/4968441,-231648511146959269/11074654989), (2891777/16,4945983489/64), (25155130798449/136656100,-126856327763081836457/1597509809000), (176075673/484,2338071687773/10648), (183570128/169,2487222424077/2197), (440399288,9242084017305)]; #obtained via E.gens()
my_mwSublatticeBasis_for_mordellCurves[kPosOfRank[11]] = [(-324124,37677551), (-315269,64302954), (-307690,79629835), (-1225591/4,655140677/8), (-295670,98097885), (-1007215/4,1117289255/8), (-251336,139978737), (-249040,141510415), (-225224,155068401), (-201580,165165935), (-674551/4,1401143557/8)]; #obtained via rat_points()
my_mwSublatticeBasis_for_mordellCurves[kPosOfRank[12]] = [(79934520107549361/365497924,22599832488886738003499415/6987589311032), (-5375180,4594818916), (-18260087/4,72125512741/8), (-4358148,9676713708), (-4136060,10279081916), (-3749636,11121872660), (-2985468,12239507268), (-2726468,12495900268), (-2418036,12738801420), (-2281628,12827209852), (-1545260,13142498084), (-2520519/4,106181691885/8)]; #obtained via rat_points()
my_mwSublatticeBasis_for_mordellCurves[kNegOfRank[9]] = [(31393/4,1141137/8), (32369/4,2068439/8), (8326,337803), (8632,424401), (9932,718799), (10096,752337), (10706,874093), (12322,1186509), (23966,3647227)]; #obtained via rat_points()
my_mwSublatticeBasis_for_mordellCurves[kNegOfRank[10]] = [(153857/4,3312769/8), (39398,2101748), (41234,3656704), (46649,6691631), (55817,10824215), (56338,11048928), (255497/4,114225179/8), (71618,17623912), (94342,27981180), (173074,71607456)]; #obtained via rat_points()
my_mwSublatticeBasis_for_mordellCurves[kNegOfRank[11]] = [(366362,55335598), (439442,196847242), (446522,207163982), (594074,404414930), (4533425/4,9498397417/8), (6314345/4,15773643083/8), (2067050,2964078974), (3511010,6575315974), (3786122,7363890718), (8751770,25889812526), (13453637,49346396773)]; #obtained via rat_points()
my_mwSublatticeBasis_for_mordellCurves[kNegOfRank[12]] = [(7674321/4,5814777113/8), (1919184,731420524), (2109824,1690470036), (2540288,3139864212), (2609513,3351975363), (2902808,4233913428), (3078848,4759353708), (3112049,4858583439), (3565313,6227875287), (14530881/4,51477914143/8), (3842768,7086024852), (5677104,13282935956)];
#Quer's Mordell curves of rank 12:
my_mwSublatticeBasis_for_mordellCurves[-16*408368221541174183] = [(2109824,1690470036),(2540288,3139864212),(2902808,4233913428),(3078848,4759353708),(3842768,7086024852),(1919184,731420524),(3529728,6119061868),(4108584,7925964076),(5677104,13282935956),(7544664,20565094996),(3565313,6227875287),(16444368,66635626348)]; #from Quer's paper
my_mwSublatticeBasis_for_mordellCurves[-16*3082320147153282331] = [(3676420,611232948),(3724780,1536366948),(3936388,3417279924),(4596988,6915764676),(9423508,28062679404),(4248668,5232241156),(6012116,12961251860),(14675908,55781837004),(9950060,30590449052),(4976465,8598025823),(51151540,365769963948),(5483753,10751177309)]; #from Quer's paper
my_mwSublatticeBasis_for_mordellCurves[-16*3161659186633662283] = [(3706924,592751364),(3757612,1571499780),(4407988,5921337588),(7746412,20353172100),(3708212,635978740),(4729604,7430389844),(4840604,7926904156),(5290748,9874823908),(13874212,51187036140),(15914524,63088176036),(23686412,115059040700),(17378609,72097380751)]; #from Quer's paper, with one typo corrected.

def pointViaMagmasFourDescent(a,height_limit="auto"):
	E = mordellCurve(a);

	'''
	ME = magma(E);
	T = ME.TwoDescent(RemoveTorsion=True);
	print "TwoDescent:",T;
	S = T[1].FourDescent(RemoveTorsion=True);
	print "FourDescent:",S;
	for height_limit in range(100):
		print "Find points with height_limit =",height_limit;
		points = S[1].PointsQI(2^height_limit);
		if len(points)>0:
			break;
	ME2, map = S[1].AssociatedEllipticCurve(nvals=2);

	E2 = ME2.sage();
	print "TODO...";	
	b, m2 = ME2.IsIsomorphic(ME,nvals=2);
	'''

	magmaCode = "" + \
		"E := EllipticCurve([0,0,0,0,"+str(a)+"]);" + \
		"T:=TwoDescent(E : RemoveTorsion); T;" + \
		"S:=FourDescent(T[1] : RemoveTorsion); S;";
	if height_limit=="auto":
		magmaCode += "" + \
			"creg := ConjecturalRegulator(E);" + \
			"r:=creg/8/Log(2);";
	else:
		magmaCode += "r:="+str(height_limit)+";";
	magmaCode += "" + \
		"pts:=PointsQI(S[1],Ceiling(2^r));" + \
		"EE,mp:=AssociatedEllipticCurve(S[1] : E := E);" + \
		"mp(pts[1]);";

	MP = magma.eval(magmaCode);
	print "Magma returns point:",MP;
	xyz = tuple([QQ(x) for x in str(MP).replace("(","").replace(")","").split(":")]);
	P = E(xyz);
	print "Converting to sage:",P;
	if P.is_finite_order():
		print "but it's a torsion point!!!";
		return None;
	P = E.saturation([P])[0][0];
	print "Saturated point:",P;	
	return P;

def load_full_mwBasisCache_as_list(cacheFileName=None):
	#If cacheFileName==None, then all known cache files will be loaded.
	global pathMordellWeil;
	cacheFileNames = [];
	if cacheFileName == None:
		#pass;
		cacheFileNames.append("mwAll.sobj");
		cacheFileNames.append("mwCache.sobj");
		cacheFileNames.append("mwMordell.sobj");
		cacheFileNames.append("mwMordell10000.sobj");
		cacheFileNames.append("mwThue.sobj");
		cacheFileNames.append("mwThueMahlerN2.sobj");
		cacheFileNames.append("mwThueMahlerN3.sobj");
		cacheFileNames.append("mwThueMahlerN4.sobj");
		cacheFileNames.append("mwThueMahlerN5.sobj");
		cacheFileNames.append("mwThueMahlerN6.sobj");
		cacheFileNames.append("mwRamanujanNagellXN.sobj");
		cacheFileNames.append("mwRamanujanNagellXY_N2.sobj");
		cacheFileNames.append("mwRamanujanNagellXY_N3.sobj");
		cacheFileNames.append("mwRamanujanNagellXY_N4.sobj");
		cacheFileNames.append("mwRamanujanNagellXY_N5.sobj");
		cacheFileNames.append("mwRamanujanNagellXY_N6.sobj");
		cacheFileNames.append("mwMordellS.sobj");
		cacheFileNames.append("mwMordellS6.sobj");
	else:
		cacheFileNames.append(cacheFileName);
	mwCacheList = []
	for cacheFileName in cacheFileNames:
		filename = pathMordellWeil + cacheFileName;
		try:
			mwCacheList0 = load(filename);
			mwCacheList += mwCacheList0;
		except IOError:
			pass;
	return mwCacheList;

def load_full_mwBasisCache_as_dict(cacheFileName=None):
	return dict(load_full_mwBasisCache_as_list(cacheFileName=cacheFileName));

def sixthPowerFreeK(k):
	return sign(k)*prod([p^(e % 6) for (p,e) in factor(k)]);

def load_mwBasis_from_cache(k,mwCacheDict=None,cacheFileName=None):
	#if mwCacheDict==None then it gets loaded.
	if mwCacheDict == None:
		mwCacheDict = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
	if mwCacheDict.has_key(k):
		mwBasis = mwCacheDict[k];
		E = mordellCurve(k);
		mwBasis = [E(P) for P in mwBasis];
	k6 = sixthPowerFreeK(k);
	if mwCacheDict.has_key(k6):
		mwBasis6 = mwCacheDict[k6];
		E = mordellCurve(k);
		E6 = mordellCurve(k6);
		h_E6_to_E = E6.isomorphism_to(E);
		mwBasis = [h_E6_to_E(E6(P6)) for P6 in mwBasis6];
		return mwBasis;

	if (k6/27) in ZZ:
		k27 = ZZ(-k6/27);
	else:
		k27 = -27*k6;
	if mwCacheDict.has_key(k27):
		print "k27 is in cache!";
		mwBasis27 = mwCacheDict[k27];
		E = mordellCurve(k);
		E27 = mordellCurve(k27);
		E27iso = None;
		for isogeny in E27.isogenies_prime_degree(3):
			if isogeny.codomain().is_isomorphic(E):
				isogeny_27_to_27iso = isogeny;
				E27iso = isogeny_27_to_27iso.codomain();
				h_E27iso_to_E = E27iso.isomorphism_to(E);
				break;
		if E27iso == None:
			print "Error, no isogeny was found between E and E27!";
			return None;		
		mwSubbasis = [h_E27iso_to_E(isogeny_27_to_27iso(E27(P27))) for P27 in mwBasis27];
		print "Saturate subbasis coming from basis for E27.";
		mwBasis = E.saturation(mwSubbasis)[0];
		return mwBasis;
	return None;

def save_mwBases_to_cache(pairsOfTuples_k_mwBasis,cacheFileName=None,saturateFirst=False):
	#If cacheFileName==None, then the basis is saved to the standard cache file.
	global pathMordellWeil;
	mwCacheList = load_full_mwBasisCache_as_list(cacheFileName=cacheFileName);
	mwCache = dict(mwCacheList);
	if cacheFileName==None:
		cacheFileName = "mwAll.sobj";
	filename = pathMordellWeil + cacheFileName;
	cacheChanged = False;
	for k, mwBasis in pairsOfTuples_k_mwBasis:
		k6 = sixthPowerFreeK(k);
		if not mwCache.has_key(k6):
			#mwBasis is not yet in cache, thus save it there:
			E = mordellCurve(k);
			E6 = mordellCurve(k6);
			h_E_to_E6 = E.isomorphism_to(E6);
			mwBasis6 = [h_E_to_E6(E(P)) for P in mwBasis];
			if saturateFirst:
				mwBasis6 = E.saturation(mwBasis6)[0];
			mwBasis6Formatted = [P.xy() for P in mwBasis6];
			mwBasis6Formatted.sort();
			#mwCacheList.append((k6,mwBasis6Formatted));
			#save(mwCacheList,filename);
			mwCache[k6] = mwBasis6Formatted;
			cacheChanged = True;
	if cacheChanged:
		mwCacheList = mwCache.items();
		save(mwCacheList,filename);

def save_mwBasis_to_cache(k,mwBasis,cacheFileName=None,saturateFirst=False):
	save_mwBases_to_cache([(k,mwBasis)],cacheFileName=cacheFileName,saturateFirst=saturateFirst);

def mwBasisViaCacheMagmaOrSage(k,mwBasesDict={},mwSubbasesDict={},loadFromCacheIfPossible=True,saveMWToCache=True,cacheFileName=None,inMagmaUseHeegnerPointIfRank1=False,inSageUseTwoDescentInCaseOfFailure=True,useMagma=True,useSageRankBound=False,useSageRank=False,useParisHeegnerPoint=True):
	if loadFromCacheIfPossible:
		mwBasis = load_mwBasis_from_cache(k,mwCacheDict=mwBasesDict,cacheFileName=cacheFileName);
	else:
		mwBasis = None;
	if mwBasis != None:
		print "Obtained basis from cache";
		return mwBasis;
		
	global my_mwBasis_for_mordellCurves;
	if loadFromCacheIfPossible and my_mwBasis_for_mordellCurves.has_key(k):
		print "Can use MW basis from database.";
		mwBasis = my_mwBasis_for_mordellCurves[k];
		if saveMWToCache:
			save_mwBasis_to_cache(k,mwBasis,cacheFileName=cacheFileName);
		return mwBasis;

	E = mordellCurve(k);
	an_rank = E.analytic_rank();
	print "Analytic rank:",an_rank;

	if an_rank <= 1:
		#The following idea was taken from E.rank() source code:
		#
		# Try zero sum rank bound first; if this is 0 or 1 it's the
		# true rank
		an_rank_upper_bound = E.analytic_rank_upper_bound();
		
		if an_rank_upper_bound <= 1:
			#We know here that rank = an_rank_upper_bound.
			if an_rank_upper_bound==1 and useParisHeegnerPoint:
				print "Try to find Heegner point using pari...";
				Ep = gp(E);
				succeeded = False;
				try:
					Pp = gp.ellheegner(Ep);
					P = E(Pp[1],Pp[2]);
					succeeded = True;
				except (TypeError,KeyboardInterrupt) as exception:
					print "Either pari's ellheegner() didn't succeed or KeyboardInterrupt came.";

				if succeeded:
					if P.has_finite_order():
						print "Heegner point has finite order (should not happen), and thus cannot be used.";
					else:
						print "Heegner point found:",P;
						mwBasis = [P];
						mwBasis = E.saturation(mwBasis)[0];
					if saveMWToCache:
						save_mwBasis_to_cache(k,mwBasis,cacheFileName=cacheFileName);
					return mwBasis;
			if an_rank_upper_bound==0:
				mwBasis = [];
				if saveMWToCache:
					save_mwBasis_to_cache(k,mwBasis,cacheFileName=cacheFileName);
				return mwBasis;

	if useMagma:
		try:
			#magma.SetVerbose("TwoDescent",1);
			#magma.SetVerbose("FourDescent",1);
			#magma.SetVerbose("EightDescent",1);
			#magma.SetVerbose("ThreeDescent",1);
			#magma.SetVerbose("Selmer",1);
			
			magmaSucceeded = False;
			ME = magma(E);
			if useSageRankBound:
				print "Compute rank bound via sage:";
				#bound1 = E.rank_bound();
				bound1 = E.rank_bounds()[1];
			elif useSageRank:
				print "Compute rank via sage:"
				bound1 = E.rank(only_use_mwrank=False);
			else:
				print "Compute rank bound via magma:";
				#The following was WRONG, as this yields a lower bound for the rank!
				#bound1, exactRank = ME.RankBound(nvals=2);
				#exactRank = exactRank.sage();
				#bound1 = bound1.sage();

				bound0,bound1 = ME.RankBounds(nvals=2);
				bound0 = bound0.sage(); #Lower bound for the rank
				bound1 = bound1.sage();	#Upper bound for the rank	
			print "Rank bound1:",bound1;

			mwSubbasis = load_mwBasis_from_cache(k,mwCacheDict=mwSubbasesDict,cacheFileName=cacheFileName);
			print "loaded subbasis:",mwSubbasis;
			if mwSubbasis == None:
				mwSubbasis = [];
			if len(mwSubbasis) >= bound1:
				print "Cached subbasis has promising cardinality. May need to saturate it...";
				print E.saturation(mwSubbasis);
				mwBasis = E.saturation(mwSubbasis)[0];
				print "Saturated subbasis:",mwBasis;
				if len(mwBasis) == bound1:
					print "Also saturated subbasis has correct rank, so this is a MW basis.";
					if saveMWToCache:
						save_mwBasis_to_cache(k,mwBasis,cacheFileName=cacheFileName);
					return mwBasis;

			
			#OLD: First Heegner-Points if possible:
			HPsucceeded = False;
			if bound1 == 1 and inMagmaUseHeegnerPointIfRank1:
				print "First Heegner discriminant:",E.heegner_discriminants_list(1);
				HPsucceeded, heegnerPoint = ME.HeegnerPoint(nvals=2);
				HPsucceeded = HPsucceeded.sage();
				print "HeegnerPoint successful:",HPsucceeded;
				print "heegnerPoint:",heegnerPoint;
				if HPsucceeded:
					gens = [heegnerPoint];
					needsSaturation = True;
					magmaSucceeded = True;
				
			if not HPsucceeded:
				print "Use magma with effort 2...";
				bounds,gens,sha = ME.MordellWeilShaInformation(nvals=3,Silent=True,Effort=2);
				magmaSucceeded = bool(len(gens) == bounds[2]);
				needsSaturation = True;

			print "Generators from magma:",gens;

			if magmaSucceeded:
				mwBasis = [];
				for MP in gens:
					xyz = tuple([QQ(x) for x in str(MP).replace("(","").replace(")","").split(":")]);
					P = E(xyz);
					if not P.is_finite_order():
						mwBasis.append(P);
				print "mwBasis before saturation:",mwBasis;
				if needsSaturation:
					mwBasis = E.saturation(mwBasis)[0];
				if saveMWToCache:
					save_mwBasis_to_cache(k,mwBasis,cacheFileName=cacheFileName);
				return mwBasis;

		except (TypeError,KeyboardInterrupt):
			print "Either magma didn't work or KeyboardInterrupt came. Thus use pari/sage instead to find MW basis.";

	try:
		mwBasis = E.gens();
	except (RuntimeError,KeyboardInterrupt) as exception:
		if inSageUseTwoDescentInCaseOfFailure:
			second_limit = 13;
			while True:
				print "Try two-descent with second_limit =",second_limit;
				if E.two_descent(second_limit=second_limit):
					break;
				second_limit += 2;
			mwBasis = E.gens();
			mwBasis = E.saturation(mwBasis)[0];
		else:
			raise exception;					
	print "Computed basis via Sage.";
	if saveMWToCache:
		save_mwBasis_to_cache(k,mwBasis,cacheFileName=cacheFileName);
	return mwBasis;

def checkBasisWithMagma(k,mwBasis):
	#Returns True if it is certain that the Basis is correct.
	print "k =",k," and mw =",mwBasis;
	E = mordellCurve(k);
	mwBasis = [E(P) for P in mwBasis];
	ME = magma(E);
	#Check rank:
	#print "Check rank...";
	bound0, bound1 = ME.RankBounds(nvals=2);
	bound1 = bound1.sage();
	if len(mwBasis) < bound1:
		print "Rank possibly larger than given basis!";
		return False;
	if bound1 == 0:
		if mwBasis == []:
			return True;
		else:
			print "Rank is 0 but mwBasis is non-empty!";
			return False;
	#Check saturation:
	#print "Check saturation...";
	mwSat, index, regulator = E.saturation(mwBasis);
	if len(mwSat) != len(mwBasis):
		print "Basis was not linearly independent!";
		return False;
	if index != 1:
		print "Basis may not be saturated!";
		return False;
	return True;

def checkBasesWithMagma(mwCacheList):
	#Returns the same dictionary but with the bases removed for which
	#their corrected could not be proved.
	print "Check MW-Bases in the database with",len(mwCacheList),"entries:";
	positive_mwCacheDict = {};
	
	'''
	params = [];
	for (k,mw) in mwCacheList:
		params.append((k,mw));
	fct = checkBasisWithMagma;
	
	results = my_run_in_parallel(params,fct,print_param=True,print_result=True,return_param_index=False,returnPartialResultsIfInterrupted=True);

	print "results:",results;

	for ((k,mw),checkPassed) in results:
		if checkPassed:
			positive_mwCacheDict[k] = mw;
	
	'''
	#for k, mw in mwCacheDict.iteritems():
	for (k,mw) in mwCacheList: 
		if k in [587908125]:
			print "We omit k =",k,"as it took too long previously.";
			continue;
		if checkBasisWithMagma(k,mw):
			positive_mwCacheDict[k] = mw;
		#else:
		#	print "May be wrong!";
	
	
	return positive_mwCacheDict;
		
#positive_mwCacheDict = checkBasesWithMagma(load_full_mwBasisCache_as_list());

def checkRanks(cacheFileName="mwMordell10000.sobj",startWithK=None,onlyRank=None,minK=0):
	mwCacheList = load_full_mwBasisCache_as_list(cacheFileName=cacheFileName);
	potentiallyBadKsAndLenMWs = [];

	onlyConsiderTheseKs = None;

	print "Bound ranks using magma:";

	maxRank = max([len(mw) for (k,mw) in mwCacheList]);
	print "maxRank =",maxRank;
	
	for (k,mw) in mwCacheList:
		if startWithK != None:
			if startWithK != k:
				continue;
			startWithK = None;

		if abs(k) < minK:
			continue;

		if onlyRank != None:
			if onlyRank != len(mw):
				continue;
		
		if onlyConsiderTheseKs!=None:
			if k not in onlyConsiderTheseKs:
				continue;
		print "================================== k =",k;
		E = mordellCurve(k);
		analyticRank = E.analytic_rank();
		#analyticRank = 1000;
		print "analyticRank:",analyticRank;
		if k in [587908125,115229992500,-1584660000,-418567500,-433147500,-130156875]:
			bound1 = E.rank_bounds()[1];
			print "   -  ,bound1,|mw|,analyticRank:","-",bound1,len(mw),analyticRank;
		elif analyticRank == 0 or k in [-17467275,-36829839375]:
			bound1 = E.rank(only_use_mwrank=False);
			print "   -  ,bound1,|mw|,analyticRank:","-",bound1,len(mw),analyticRank;
		elif False: #analyticRank == 1:
			bound1 = E.rank_bound();
			print "   -  ,bound1,|mw|,analyticRank:","-",bound1,len(mw),analyticRank;
		else:
			ME = magma(E);
			#print "debug0";
			bound0, bound1 = ME.RankBounds(nvals=2);
			#print type(bound0),type(bound1);
			#print "debug0.5";
			#print bound0,bound1;
			#print "debug1";
			bound0 = bound0.sage();
			#print "debug2";
			bound1 = bound1.sage();
			print "bound0,bound1,|mw|,analyticRank:",bound0,bound1,len(mw),analyticRank;
		if len(mw) < bound1:
			print "len(mw) < bound1, so compute rank with sage:";	
			if E.rank(only_use_mwrank=false) > len(mw):
				print "POSSIBLE PROBLEM!!!";
				potentiallyBadKsAndLenMWs.append((k,len(mw)));
		print "potentiallyBadKsAndLenMWs:",potentiallyBadKsAndLenMWs;
	print "potentiallyBadKsAndLenMWs:",potentiallyBadKsAndLenMWs;

	print "Check now sage's rank():";
	for k,lenMW in potentiallyBadKsAndLenMWs:
			print "================================== k =",k;
			E = mordellCurve(k);
			sageRank = E.rank(only_use_mwrank=False);
			print "sageRank,|mw|:",sageRank,lenMW;
			if sageRank != lenMW:
				print "Seems to be a serious PROBLEM!";

	print "DONE";

	#Successfully checked:
	# mwMordell10000
	# mwMordell
	# mwThue
	# mwThueMahlerN2
	# mwThueMahlerN3 up to two possible wrong bases, see below.
	# mwThueMahlerN4
	# mwThueMahlerN5
	# mwThueMahlerN6

	#Problems with
	# mwThueMahlerN3:
	#  [(-447727500, 0), (-520627500, 0)]

	#---------------------------------------------- delta = -857
	#exponents: 212
	#a = -33320160000 = -1 * 2^8 * 3^5 * 5^4 * 857
	#E.analytic_rank(): 1
	#Obtained basis from cache
	#mwBasis: []
	#RANK = 0
	#
	# Sieht nach einem Fehler aus, der von magma's Generator(E) kommt!
	# Es gibt zwei Booleans zurueck, aber was bedeuten diese?
	# Magmas Dokumentation scheint nicht zu stimmen!
		
	return;

def manyMWBasesViaCacheMagmaOrSage(Ks,mwBasesDict={},mwSubbasesDict={},loadFromCacheIfPossible=True,saveMWToCacheAtTheEnd=True,saveMWToCacheSeparately=True,cacheFileName=None,inMagmaUseHeegnerPointIfRank1=False,inSageUseTwoDescentInCaseOfFailure=True,useMagma=True,useSageRankBound=False,useSageRank=False,in_parallel=True,timeout=0,randomOrder=False,useParisHeegnerPoint=True,onlyAnalyticRanks="all",skipTheFirstXRemainingKs=0):

	t00 = walltime();

	print "debug-1";
	
	if mwBasesDict==None:
		if loadFromCacheIfPossible:
			mwBasesDict = load_full_mwBasisCache_as_dict();
		else:
			mwBasesDict = {};

	if loadFromCacheIfPossible:
		print "debug0"
		mwCache = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
		print "debug1"
		global my_mwBasis_for_mordellCurves;
		print "debug2"
		mwCache.update(my_mwBasis_for_mordellCurves);
		print "debug3"
		mwCache.update(mwBasesDict);
		print "debug4"
	else:
		mwCache = mwBasesDict;
	
	newBases = [];

	parameters = [];
	if randomOrder:
		randForK = dict([(k,randint(1,100000)) for k in Ks]);
		Ks.sort(key = lambda x: randForK[x]);
		#Ks.sort(key = lambda x: randint(1,100000));
	for k in Ks:
		mwBasesDict_local = {};
		if mwCache.has_key(k):
			mwBasesDict_local[k] = mwCache[k];
			print "k =",k,"already in cache";
			continue;
		if mwCache.has_key(sixthPowerFreeK(k)):
			print "k =",k,"up to some u^6 already in cache.";
			continue;
		if mwCache.has_key(sixthPowerFreeK(-27*k)):
			print "k =",k,"up to some -27 * u^6 already in cache.";
			continue;
		mwSubbasesDict_local = {};
		if mwSubbasesDict.has_key(k):
			mwSubbasesDict_local[k] = mwSubbasesDict[k];
		loadFromCacheIfPossible_local = False;

		if in_parallel:
			saveMWToCache_local = saveMWToCacheSeparately;
		else:
			saveMWToCache_local = False;
		cacheFileName_local = cacheFileName;
		inMagmaUseHeegnerPointIfRank1_local = inMagmaUseHeegnerPointIfRank1;
		inSageUseTwoDescentInCaseOfFailure_local = inSageUseTwoDescentInCaseOfFailure;
		useMagma_local = useMagma;
		useSageRankBound_local = useSageRankBound;
		useSageRank_local = useSageRank;
		useParisHeegnerPoint_local = useParisHeegnerPoint;
		param = (k,mwBasesDict_local,mwSubbasesDict_local,loadFromCacheIfPossible_local,saveMWToCache_local,cacheFileName_local,inMagmaUseHeegnerPointIfRank1_local,inSageUseTwoDescentInCaseOfFailure_local,useMagma_local,useSageRankBound_local,useSageRank_local,useParisHeegnerPoint_local);
		parameters.append(param);

	if skipTheFirstXRemainingKs != 0:
		parameters = [parameters[i] for i in range(skipTheFirstXRemainingKs,len(parameters))];
	
	print "Remaining parameters:"
	for i in range(len(parameters)):
		#print i,":",parameters[i];
		k = parameters[i][0];
		print i,":",factor(k);
		#print "debug: sage rank:",mordellCurve(k).rank(only_use_mwrank=False);
		#print "debug: conductor:",mordellCurve(k).conductor();

	print "Number of remaining k's:",len(parameters);

	if in_parallel:
		results = my_run_in_parallel(parameters,mwBasisViaCacheMagmaOrSage,returnPartialResultsIfInterrupted=True,ignoreNODATAoutputs=True,ignoreTimeouts=True,print_param=False,print_result=True,return_param_index=True,timeout=timeout);
		#print "results:",results;
		for i, basis_for_k in results:
			param = parameters[i];
			k = param[0];
			basis_for_k = list(basis_for_k);
			basis_for_k.sort();
			newBases.append((k,basis_for_k));
	else:
		for param in parameters:
			k = param[0];
			print "k =",k,"=",factor(k);
			if onlyAnalyticRanks!="all":
				E = mordellCurve(k);
				if not E.analytic_rank() in onlyAnalyticRanks:
					print "analyticRank =",E.analytic_rank(),"thus omit this curve.";
					continue;
			basis_for_k = mwBasisViaCacheMagmaOrSage(param[0],param[1],param[2],param[3],param[4],param[5],param[6],param[7],param[8],param[9],param[10]);
			basis_for_k = list(basis_for_k);
			basis_for_k.sort();
			newBases.append((k,basis_for_k));
			if saveMWToCacheSeparately:
				save_mwBases_to_cache(newBases,cacheFileName=cacheFileName);

	totalTime = walltime(t00);
	newBases.sort(key=lambda (k,sol): k);
	
	#print "new Bases:",newBases;
	print "len(newBases):",len(newBases),"versus len(parameters):",len(parameters),"versus len(Ks):",len(Ks);

	if saveMWToCacheAtTheEnd:
		print "Saving to cache...";
		save_mwBases_to_cache(newBases,cacheFileName=cacheFileName);
		print "done!";

	return newBases;

def checkBases(oldCacheFileName="mwAll.sobj",newCacheFileName=None,checkSaturation=True,checkRank=False,checkAnalyticRank=True):
	mwList = load_full_mwBasisCache_as_list(oldCacheFileName);
	print "len(mwList):",len(mwList);
	problematicKs = [];
	notRescuableKs = [];
	loop = 0;
	mwListNew = [];
	for k,mw in mwList:
		problems = [];
		E = mordellCurve(k);
		mwBasis = [E(P) for P in mw];

		if checkRank:
			if E.rank() != len(mwBasis):
				print "Rank is incorrect for k =",k;
				problems.append("wrongRank");

		if checkAnalyticRank:
			if E.analytic_rank() != len(mwBasis):
				print "Analytic rank is different from len(mwBasis) for k =",k;
				print "analytic rank:",E.analytic_rank();
				print "len(mwBasis):",len(mwBasis);
				problems.append("differentAnalyticRank");
		
		if checkSaturation:
			#Check saturation:
			#print "Check saturation...";
			mwSat, index, regulator = E.saturation(mwBasis);
			if len(mwSat) != len(mwBasis):
				print "Basis was not linearly independent for k =",k;
				print "len(mwSat) =",len(mwSat),"vs len(mw) =",len(mw);
				problems.append("notIndependent");
			if len(mwSat)>=1 and index != 1:
				print "Basis may not be saturated for k =",k;
				print "index:",index;
				problems.append("notSaturated");

		if problems != []:
			problematicKs.append((k,mw));
		print ".",;
		sys.stdout.flush();
		loop += 1;
		if loop % 1000 == 0:
			print "loop:",loop;

		if problems == ["notSaturated"]:
			problems = [];
			mwBasis = mwSat;

		if problems == []:
			mwBasisFormatted = [E(P).xy() for P in mwBasis];
			mwBasisFormatted.sort();
			mwListNew.append((k,mwBasisFormatted));		
		else:
			print "For this k =",k,"the basis was not rescuable, so it will not appear in the new file!";
			notRescuableKs.append((k,mw));

			
	print "Done!"

	
	print "Problematic Ks and mwBases:",problematicKs;

	print "Not rescuable Ks and mwBases:",notRescuableKs;

	global pathMordellWeil;
	if newCacheFileName != None:
		save(mwListNew,pathMordellWeil+newCacheFileName);

	return problematicKs,notRescuableKs;

def checkMyMWDatabase():
	cacheFileNames = [];
	cacheFileNames.append("mwAll.sobj");
	cacheFileNames.append("mwThue.sobj");
	cacheFileNames.append("mwThueMahlerN2.sobj");
	cacheFileNames.append("mwThueMahlerN3.sobj");
	cacheFileNames.append("mwThueMahlerN4.sobj");
	cacheFileNames.append("mwThueMahlerN5.sobj");
	cacheFileNames.append("mwThueMahlerN6.sobj");
	cacheFileNames.append("mwRamanujanNagellXN.sobj");
	cacheFileNames.append("mwRamanujanNagellXY_N2.sobj");
	cacheFileNames.append("mwRamanujanNagellXY_N3.sobj");
	cacheFileNames.append("mwRamanujanNagellXY_N4.sobj");
	cacheFileNames.append("mwRamanujanNagellXY_N5.sobj");
	cacheFileNames.append("mwRamanujanNagellXY_N6.sobj");
	cacheFileNames.append("mwMordellS.sobj");
	cacheFileNames.append("mwMordell.sobj");
	cacheFileNames.append("mwMordell10000.sobj");

	problematicKs = {};
	notRescuableKs = {};
	for cacheFileName in cacheFileNames:
		#First round:
		#oldFilename = "OLD" + cacheFileName;
		#newFilename = "TMP" + cacheFileName;

		#Second round (for safty):
		oldFilename = "TMP" + cacheFileName;
		newFilename = "" + cacheFileName;

		print "oldFilename:",oldFilename;
		problematicKs[cacheFileName], notRescuableKs[cacheFileName] = checkBases(oldCacheFileName=oldFilename,newCacheFileName=newFilename,checkSaturation=True,checkRank=False,checkAnalyticRank=True);

	print "Problematic Ks and mwBases:",problematicKs;
	print "Not rescuable Ks and mwBases:",notRescuableKs;

def add_all_bases_of_E27_to_cache(cacheFileName):
	mwDictOld = load_full_mwBasisCache_as_dict(cacheFileName);
	mwDictNew = {};
	for k,basis in mwDictOld.iteritems():
		print factor(k), basis;
		mwDictNew[k] = basis;
		k27 = sixthPowerFreeK(-27*k);
		if not mwDictOld.has_key(k27):
			basis27 = load_mwBasis_from_cache(k27,mwCacheDict={k:basis});
			print "E27's basis:",basis27;
			mwDictNew[k27] = basis27;
	if cacheFileName==None:
		cacheFileName="mwAll.sobj";
	save_mwBases_to_cache(mwDictNew.items(),cacheFileName=cacheFileName);

def analyzeMWBases(cacheFileName=None):
	mwDict = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
	print "Number of bases:",len(mwDict);

	highestPoint = {};
	highestRegulator = {};
	for k,MW in mwDict.iteritems():
		E = mordellCurve(k);
		mw = [E(P) for P in MW];
		r = len(mw);
		
		if highestPoint.has_key(r) == False:
			highestPoint[r] = (-Infinity,0);
		for P in mw:
			heightP = P.height();
			if highestPoint[r][0] < heightP:
				highestPoint[r] = (heightP,P,k);

		if highestRegulator.has_key(r) == False:
			highestRegulator[r] = (-Infinity,0);
		regMW = E.regulator_of_points(mw);
		if highestRegulator[r][0] < regMW:
			highestRegulator[r] = (regMW,k);
		

	print "highestPoint:",highestPoint;
	print "highestRegulators:",highestRegulator;	

def isogenyOfPrimeDegree(E2,E1,degree=3):
	#Returns a tuple (g,h), where g circ h: E2 to E1 is an isogeny of degree degree.
	
	E2iso = None;
	for isogeny in E2.isogenies_prime_degree(degree):
		if isogeny.codomain().is_isomorphic(E1):
			isogeny_2_to_2iso = isogeny;
			E2iso = isogeny_2_to_2iso.codomain();
			h_E2iso_to_E1 = E2iso.isomorphism_to(E1);
			break;
	if E2iso == None:
		print "Error, no isogeny was found between E and E27!";
		return None;
	else:
		print "Isogeny found.";

	return (h_E2iso_to_E1,isogeny_2_to_2iso);

def testMWofRank2curve(a,Xs=[],Xs3=[],checkRegulators=True):
	E = mordellCurve(a);
	E3 = mordellCurve(-27*a);
	mw = [E.lift_x(x) for x in Xs];
	mw3 = [E3.lift_x(x3) for x3 in Xs3];

	print "Initial mw:",mw;
	print "Initial mw3:",mw3;

	print "Isogeny-graph:",E.isogeny_graph();

	i_toE3,j_toE3 = isogenyOfPrimeDegree(E,E3,3);
	i_toE,j_toE = isogenyOfPrimeDegree(E3,E,3);

	mwex = mw + [E(i_toE(j_toE(P3))) for P3 in mw3];
	mwex3 = mw3 + [E3(i_toE3(j_toE3(P))) for P in mw];

	print "mw with added points:",mwex;
	print "mw3 with added points:",mwex3;

	mwex_sat = E.saturation(mwex)[0];
	mwex3_sat = E3.saturation(mwex3)[0];

	print "Independent points on E:",mwex_sat;
	print "Their heights:",[P.height() for P in mwex_sat];
	print "Independent points on E3:",mwex3_sat;
	print "Their heights:",[P.height() for P in mwex3_sat];
	
	if checkRegulators:
		ME = magma(E);
		ME3 = magma(E);
		reg = magma.ConjecturalRegulator(E);
		print "Regulator of E:",reg;
		reg3 = magma.ConjecturalRegulator(E3);
		print "Regulator of E3:",reg3;
	
########################################################################
### Numerics: ##########################################################
########################################################################

def myRRtoRIF(x,precisionLoss = 2):
	'''
	Turns an element of some RealField into an element in the
	  RealIntervalField of the same precision.
	We assume that at most the last precisionLoss number of bits of x are wrong.
	More precisely we assume that x lies in the following interval:
	'''
	return RealIntervalField(x.precision())(x-x*2^(precisionLoss-x.precision()),x+x*2^(precisionLoss-x.precision()));

def myRRtoRIF_matrix(M,precisionLoss = 2):
	'''
	Turns a matrix with RR entries to a matrix with RIF entries using myRRtoRIF().
	'''
	prec = M.base_ring().precision();
	Mi = matrix(RealIntervalField(prec),nrows=M.nrows(),ncols=M.ncols());
	for i in range(M.nrows()):
		for j in range(M.ncols()):
			Mi[i,j] = myRRtoRIF(M[i,j],precisionLoss=precisionLoss);
	return Mi;
	
def lowerAndUpperBoundsForSmallestAndLargestEigenvalueOfSelfadjointRealMatrix(M,verbose=False):
	'''
	INPUT:
	A self-adjoint matrix M with RR or RIF entries.

	OUTPUT:
	A tuple (lamdaMin,lamdaMax) consisting of
	- a lower bound lamdaMin for the smallest eigenvalue of M and
	- an upper bound lamdaMax for the largest eigenvalue of M.
	
	We assume that M.base_ring() is RealField(prec) or RIF(prec) for some natural number prec.
	The result will be an element in RR(prec), where prec is the precision of the base ring of M.
	The obtained bounds are correct (without numerical errors!).
	However they may not be optimal (although they are quite good).
	'''
	
	#Convert matrix elements into real intervals:
	prec = M.base_ring().precision();
	if M.base_ring().name().startswith('IntervalRealIntervalField'):
		Mi = M;
	elif M.base_ring().name().startswith('RealField'):
		Mi = myRRtoRIF_matrix(M);
	else:
		print "Error: M.base_ring() is neither RR nor RIF.";
		return;

	#Do Newton algorithm for the minimal polynomial of M, starting left of all roots.
	#This works so easily because all roots are real!
	Q = Mi.charpoly();
	Qd = Q.derivative();
	cauchyBoundForRoots = 1 + max([abs(c) for c in Q.coefficients()]);
	lamdaMinQ = -cauchyBoundForRoots;
	lamdaMaxQ = +cauchyBoundForRoots;
	if verbose:
		print "lamdaMinQ obtained from Cauchy bound:",lamdaMinQ;
		print "lamdaMaxQ obtained from Cauchy bound:",lamdaMaxQ;

	while True:
		lamdaMinQNew = lamdaMinQ - Q(lamdaMinQ)/Qd(lamdaMinQ);
		lamdaMinQNew = RIF(lamdaMinQNew.lower()); #If we don't do this, then sometimes the error (diameter of the real interval) would explode exponentially, and adjusting the precision slightly will not help.
		if verbose:
			print "New lamdaMinQNew:",lamdaMinQNew;
		if lamdaMinQNew.lower()<=lamdaMinQ.lower():
			break;
		else:
			lamdaMinQ = lamdaMinQNew;

	while True:
		lamdaMaxQNew = lamdaMaxQ - Q(lamdaMaxQ)/Qd(lamdaMaxQ);
		lamdaMaxQNew = RIF(lamdaMaxQNew.upper()); #If we don't do this, then sometimes the error (diameter of the real interval) would explode exponentially, and adjusting the precision slightly will not help.
		if verbose:
			print "New lamdaMaxQNew:",lamdaMaxQNew;
		if lamdaMaxQNew.upper()>=lamdaMaxQ.upper():
			break;
		else:
			lamdaMaxQ = lamdaMaxQNew;

	#If M is the exact height pairing matrix, and M' the above machine approximation,
	#and assuming we can compute the smallest eigenvalue of M' precisely within the machine precision,
	#this is the same as the smallest eigenvalue of M up to an error which is bounded by
	#the spectral radius of the matrix M-M', by a theorem of Ronn ["Bounds on Eigenvalues of Interval Matrices"].
	#This spectral radius is trivially bounded by the maximal absolute value of an entry of M-M' times the dimension of M.

	lamdaError = Mi.nrows()*max([x.absolute_diameter() for x in Mi.list()]); 
	#Now we replace the computed lamda by a lower bound of it:
	lamdaMinQ -= lamdaError;
	lamdaMaxQ += lamdaError;
	return (lamdaMinQ.lower(),lamdaMaxQ.upper());

def integralLowerAndUpperApproximationOfQuadraticForm(Q,precAim=20):
	'''
	INPUT
	A positive definite form Q with entries in some RR or RIF.

	OUTPUT
	A tuple (Qlow,Qup,factor,delta), where Qint is self-adjoint with ZZ entries,
	and factor is a rational number such that Qlow and Qup is roughly Q*factor^2.
	Moreover, for any vector v, we have
				||v||_Qup >= factor^2*||v||_Q >= ||v||_Qlow.
	Finally, Qlow <= Qup <= Qlow + delta*Id, where delta is an integer.
	Note: Qlow might not be positive definite! If this is needed, but
	not fullfilled, adjust the precision of Q and precAim.
	'''

	debug = False;
	if debug:
		print Q, precAim;
	
	#Convert matrix elements into real intervals:
	prec = Q.base_ring().precision();
	if precAim > prec-3:
		precAim = prec-3;
	if Q.base_ring().name().startswith('IntervalRealIntervalField'):
		Qi = Q;
	elif Q.base_ring().name().startswith('RealField'):
		Qi = myRRtoRIF_matrix(Q);
	else:
		print "Error: Q.base_ring() is neither RR nor RIF.";
		return;

	R = Qi.base_ring();
	n = Q.ncols();
	maxEntry = R(max([abs(x) for x in Qi.list()]).upper());
	#maxEntryRat = continued_fraction(maxEntry.upper(),bits=prec).value();
	factorSq = 2^precAim/maxEntry; #In the paper, factorSq is called $f$, and precAim plays the role of $k$.

	#In Sage version 6.4.1:
	#while True:
	#	contFrac = continued_fraction(sqrt(factorSq).upper(),bits=precAim+1);
	#	if len(contFrac)>0:
	#		break;
	#	if debug:
	#		print "Need to increase precision for continued fractions!"
	#	precAim += 1;
	#factor = contFrac.value();

	#In Sage version 6.5:
	while True:
		factorRR = sqrt(factorSq).upper();
		factor = factorRR.numerical_approx(prec = precAim+1).simplest_rational();
		if factor>0:
			break;
		if debug:
			print "Need to increase precision for continued fractions!"
		precAim += 1;
	
	factorSq = factor^2;
	#print factor.relative_diameter();
	Qlow = matrix(ZZ,n);
	error = R(0.5);
	for i in range(n):
		for j in range(n):
			x = Qi[i,j]*factorSq;
			Qlow[i,j] = x.upper().round();
			if (x.absolute_diameter()+R(0.5)).upper()>error:
				error = x.absolute_diameter()+R(0.5);
	Qup = copy(Qlow);
	deltaHalf = (n*error).upper().ceil();
	for i in range(n):
		Qlow[i,i] -= deltaHalf;
		Qup[i,i] += deltaHalf;

	return (Qlow,Qup,factor,2*deltaHalf);

########################################################################
### Basis utilities: ###################################################
########################################################################

class MyTimer:
	'''
	A simple class that keeps track of several running times.
	Call startTimer("X") and later endTimer("X"), then this class saves
	how long the process "X" took.
	'''

	def __init__(self):
		self.timers = {};
		self.startTimer("CPU time at start");		
	
	def startTimer(self,timerName):
		self.timers[timerName] = cputime();

	def endTimer(self,timerName,verbose = False):
		self.timers[timerName] = cputime(self.timers[timerName]);
		if verbose:
			print "Time taken for "+timerName+":",self.timers[timerName];
		return self.timers[timerName];

	def totalTime(self):
		return cputime(self.timers["CPU time at start"]);

	def toString(self,linePrefix = ""):
		result = "";
		for timerName, t in self.timers.iteritems():
			if timerName != "CPU time at start":
				result += linePrefix+timerName+": "+str(t)+"\n";
		result += linePrefix+"Total time: "+str(self.totalTime());
		return result;

def myListToStr(list,comma=", "):
	'''
	Turns a list into a string using the parameter 'comma' as a separator.
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

def logStar(x):
	'''
	Returns log(max(x,1)).
	'''
	return log(max(x,1));

def volumeOfBall(dim,radius=1):
	'''
	Returns the volume of a 'dim'-dimensional ball in Euclidean space of radius 'radius'.
	'''
	return RR(pi^(dim/2)*radius^dim/gamma(dim/2+1));

def volumeOfEllipsoid(Qhk,Mmax):
	'''
	Returns the volume of the ellipsoid E = { x | ||x||_Qhk^2 <= Mmax }.
	'''
	#Outputs volume of ellipsoid {x: x^t * Qhk * x <= Mmax}.
	return RR(volumeOfBall(Qhk.nrows(),sqrt(Mmax)) / sqrt(abs(det(Qhk))));

def volumeOfSphere(dim,radius=1):
	'''
	Returns the volume of the 'dim'-dimensional sphere of radius 'radius'.
	Note that this sphere sits naturally inside R^(dim+1).
	'''
	return RR((dim+1)*pi^((dim+1)/2)/gamma((dim+1)/2+1)*radius^dim);

def randomListOfGivenLengthAndSum(length,oneNorm):
	'''
	Returns a list of 'length' non-negative integers that sum up to 'oneNorm'.
	'''
	result = [0 for i in range(length)];
	for i in range(oneNorm):
		j = randint(0,length-1);
		result[j] += 1;
	return result;

def quality(a,b,c):
	'''
	Returns the quality of the given abc-triple (a,b,c).
	'''
	abc = a*b*c;
	if abs(abc) <= 1:
		return 0;
	return N(log(max(a,b,c))/log(radical(abc)));

def randomRealPointOnSphere(dim):
	'''
	Here, dim is the dimension of the sphere.
	The return list has dim+1 elements.
	'''
	v = [normalvariate(0,1) for i in range(dim+1)];
	normSq = normSquared(v);
	if normSq == 0:
		return randomRealPointOnSphere(dim+1);
	norm = sqrt(normSq);
	return vector([vi/norm for vi in v]);

def randomLatticePoint(dim,normSquaredApprox=1.0,Q=None):
	#We assume that Q is already LLL-reduced, or close to it

	if Q == None:
		Q = identity_matrix(ZZ,dim);
	
	#First we find a random direction, and then a lattice point along this direction.
	#In high dimensions it may be reasonable to take "R*direction" instead of "direction", where
	#Q = R^t * R is the LR-decomposition (= Cholesky decomposition).
	#But for our purposes this slightly unnatural distribution should be very sufficient.
	while True:
		direction = randomRealPointOnSphere(dim-1);
		nSq = normSquared(direction,Q);
		if nSq > 0:
			break;
	scalingFactor = sqrt(normSquaredApprox/nSq);
	randomRealPoint = scalingFactor * direction;

	#Need to round randomRealPoint to a suitable lattice point, without changing the norm too much:
	
	##Trivial way to round would be:
	#result = vector([x.round() for x in randomRealPoint]);
	
	#More clever greedy way:
	#Round the entries of randomRealPoint iteratively,
	#starting with the coordinates that heuristically change the norm the most, and
	#such that at each time we round up or down depending on what brings the norm closer to the goal:
	derivative = Q * randomRealPoint;
	coordinates = range(dim);
	coordinates.sort(key = lambda i: -derivative[i].abs());
	result = randomRealPoint;
	for i in coordinates:
		result1 = copy(result);
		result1[i] = result1[i].floor();
		result2 = copy(result);
		result2[i] = result2[i].ceil();
		if abs(normSquared(result1,Q)-normSquaredApprox) < abs(normSquared(result2,Q)-normSquaredApprox):
			result = result1;
		else:
			result = result2;
	
	return result.change_ring(ZZ);
    
########################################################################
### Fincke-Pohst: ######################################################
########################################################################

def quadraticFormToFPForm(A):
    '''
    Computes a symmetric matrix Q such that for any vector x,
     x^t*A*x = \sum_{i=1}^n q_{ii} * (x_i + \sum_{j=i+1}^n q_{ij}*x_j)^2
    Everything is done over QQ
    '''
    
    (n,m) = A.dimensions();
    Q = matrix(QQ,n,n);
    
    #Following Fincke-Pohst's paper: (there must be a typo somewhere...)
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

	#So let's do it correctly:
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
	INPUT:
	L - an integral matrix whose columns are a basis of a lattice
	boundForNormSquared - a non-negative integer
	solutionList - a list to which the solutions are appended.
	maxNumSolutions - a non-negative integer (or None, which means Infinity).
	callback - a function that is called for each solution via 'callback(y,callbackArgs);'.
	callbackArgs - optional arguments at are handed over to the callback function.

	OUTPUT:
	[bufferWasBigEnough,numSolutions], where
	bufferWasBigEnough - true iff number of solutions is at most maxNumSolutions
	numSolutions - the number of non-zero integral vectors x up to +- symmetry with
				||Lx||_2 = x^t*L^t*L*x <= boundForNormSquared

	We assume that all input is integral, such that there are no numerical issues at all.
	The LLL-algorithm is used.
	'''

	global aLotOutput;
	#if aLotOutput:
	#    print "L =",L;    

	L = L.change_ring(ZZ);
	L1 = L.transpose().LLL().transpose(); #LLL reduction of columns
	#L1 = L;
	#print L1;
	U = L.inverse()*L1;

	return my_finckePohst_viaGramMatrix(L1.transpose()*L1, boundForNormSquared, solutionList=solutionList, maxNumSolutions=maxNumSolutions, finalTransformation=U, callback=callback, callbackArgs=callbackArgs,lllReduce=False);
    
def my_finckePohst_viaGramMatrix(A,boundForNormSquared,center=0,solutionList=None,maxNumSolutions=None,finalTransformation=None,callback=None,callbackArgs=None,lllReduce=True,breakSymmetry=True):
	'''
	INPUT:
	A - an integral nxn matrix which is the Gram matrix of some lattice (i.e. it's positive definite).
	boundForNormSquared - a non-negative integer
	center - a rational vector or 0 (default: 0) that is the center of the ellipsoid in Z^n.
	solutionList - a list to which the solutions are appended (if None, then no list will be created).
	maxNumSolutions - a non-negative integer (or None, which means Infinity).
	finalTransformation - a matrix T such that the solution vectors x in Z^n are multiplied by T (to T*x) before it gets appended to solutionsList.
	callback - a function that is called for each solution via 'callback(y,callbackArgs);'.
	callbackArgs - optional arguments at are handed over to the callback function.
	lllReduce - whether A first gets LLL reduced to speed up Fincke-Pohst (default: True).
	breakSymmetry - a boolean: If True and if center.base_ring()==ZZ, then the output will consider only one solution among each pair of antipodal solutions.

	OUTPUT:
	[bufferWasBigEnough,numSolutions], where
	bufferWasBigEnough - true iff number of solutions is at most maxNumSolutions
	numSolutions - the number of non-zero integral vectors x!=center (possibly up to +- symmetry, depending on 'breakSymmetry' and center==0) with
				(x-center)^t * A * (x-center) <= boundForNormSquared

	For each solution:
	    if solutionList != None, then the solution will be appended to solutionList, and
	    if callback != None, then callback(solution,callbackArgs) will be called.
	We assume that all input is integral or rational, such that there are no numerical issues at all.
	'''

	def traverseShortVectors(Q,n,k,x,center,shortVectors,RemainingBoundForNormSquared,numSolutionsList,maxNumSolutions,xIsCenterSoFar,finalTransformation,callback,callbackArgs):
		'''
		This is the Fincke-Pohst recursion.
		Fills shortVectors or calls callback()
		Returns [bufferBigEnoughSoFar,newNumSolutionsSoFar]
		'''
		if k==-1:
			if not xIsCenterSoFar: 
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
		u = -center[k];
		for j in range(k+1,n):
			u = u + Q[k,j] * (x[j]-center[j]);
		xk0 = -floor(u);
		x[k] = xk0;
		#print k,u,x[k]
		while True:
			t = Q[k,k] * (x[k] + u)^2;
			#print "t =",t;
			if t>RemainingBoundForNormSquared:
				break;
			#print k,x[k],t;
			if not traverseShortVectors(Q,n,k-1,x,center,shortVectors,RemainingBoundForNormSquared-t,numSolutionsList,maxNumSolutions,xIsCenterSoFar and x[k]==center[k], finalTransformation,callback,callbackArgs):
				return False; #too many solution found
			x[k] = x[k] + 1;            

		if not xIsCenterSoFar: #break antipodal symmetry: if x was so far center, then u is zero here, and we iterate only over x[k]>=0.
			x[k] = xk0-1;
			while True:
				t = Q[k,k] * (x[k] + u)^2;
				if t>RemainingBoundForNormSquared:
					break;
				if not traverseShortVectors(Q,n,k-1,x,center,shortVectors,RemainingBoundForNormSquared-t,numSolutionsList,maxNumSolutions,False, finalTransformation,callback,callbackArgs):
					return False; #too many solutions found
				x[k] = x[k] - 1;            
			
		return True; #prescribed bufferSize (maxNumSolutions) was enough
		
	global aLotOutput;
	#if aLotOutput:
	#    print "A =",A;    

	(n,m) = A.dimensions();

	if center==0:
		center = zero_vector(n);

	if center.base_ring() != ZZ: #We check this here, as after multiplication with U, center.base_ring() might become QQ! (even though U's base_ring is ZZ as well...)
		breakSymmetry = False;

	if lllReduce:
		U = A.LLL_gram();
		A = U.transpose() * A * U;
		if finalTransformation != None:
			finalTransformation = finalTransformation * U;
		else:
			finalTransformation = U;
		if not center.is_zero():
			center = U.inverse() * center;

	Q = quadraticFormToFPForm(A);
	#print "center =",center;
	#print "Q =\n", Q;

	x = range(n);
	numSolutionsList = [0];
	bufferWasBigEnough = traverseShortVectors(Q,n,n-1,x,center,solutionList,boundForNormSquared,numSolutionsList,maxNumSolutions,breakSymmetry,finalTransformation,callback,callbackArgs);
		
	#return [bufferWasBigEnough,matrix(shortVectors).transpose()];
	return [bufferWasBigEnough,numSolutionsList[0]];

def normSquared(v,Q=None):
	'''
	INPUT
	* v - a vector
	* Q - a quadratic form, Q=None stands for the standard
	      Euclidean quadratic form (i.e. identity matrix).
	OUTPUT
	<v,v>_Q = v*Q*v
	'''
	if Q == None:
		return sum([x^2 for x in v]);
	else:
		v = vector(v);
		return v * Q * v;

def my_shortestVector_viaLattice(L,Q=None,exactLLL=True,verbose=True):
	'''
	INPUT:
	- "L" - an integral matrix whose columns determine a full lattice in ZZ^n
	- "Q" - a quadratic form on the ambient space ZZ^n; Q=None means standard form.
	        It is assumed that Q is rather close to being LLL reduced,
	        otherwise the running time might unreasonably big.
	- "exactLLL" - boolean, whether a lot of time should be used for LLL'ing L.
	        Check yourself what makes the method faster for your input.
	        Either way the algorithm gives an exact result.
	OUTPUT:
	A shortest non-zero vector (and only one, even if it is not unique).
	The coordinates are the one from the ambient ZZ^n, not the one wrt. L!
	The algorithm is exact.
	'''

	if Q==None:
		Q = identity_matrix(ZZ,L.nrows());

	if verbose:
		print "Do LLL...",;
		sys.stdout.flush();
	L = L.change_ring(ZZ);
	if exactLLL:
		L1 = L.transpose().LLL().transpose(); #LLL reduction of columns
	else:
		L1 = L.transpose().LLL(algorithm="fpLLL:fast").transpose(); #LLL reduction of columns
		
	if verbose:
		print "done.";
		sys.stdout.flush();		

	#U = L.inverse()*L1;
	U = L1;
	A = L1.transpose()*Q*L1; #associated quadratic form wrt. the new basis

	if verbose:
		print "L =",L;
		print "L1 =",L1;
		sys.stdout.flush();


	#As L1 has LLL reduced columns, we obtain an elementary lower bound for the shortest vector's norm:
	#lowerBoundForShortestVectorSquared = ceil(normSquared(L1.column(0),Q) / 2^(L1.nrows()-1));
	lowerBoundForShortestVectorSquared = ceil(normSquared(L1.column(0),Q) / 2^(L1.nrows()+30));

	boundForNormSquared = lowerBoundForShortestVectorSquared;
	solutionList = [];
	while solutionList==[]:
		boundForNormSquared *= 4;
		if verbose:
			print "boundForNormSquared =",RR(boundForNormSquared);
			sys.stdout.flush();
		[bufferWasBigEnough,numSolutions] = my_finckePohst_viaGramMatrix(A, boundForNormSquared, solutionList=solutionList, maxNumSolutions=None, finalTransformation=U, callback=None, callbackArgs=None);
		#bufferWasBigEnough is always true here, as we don't bound the buffer (i.e. we put maxNumSolutions=None).

	return min(solutionList,key=lambda v: normSquared(v,Q));	

def my_closestVector_viaLattice(L,v,Q=None,verbose=True):
	'''
	INPUT:
	- "L" - an integral matrix whose columns determine a full lattice in ZZ^n
	- "v" - an integral or rational vector
	- "Q" - a quadratic form on the ambient space ZZ^n; Q=None means standard form.
	        It is assumed that Q is rather close to being orthogonal (or LLL reduced),
	        otherwise the running time might be unreasonably big.
	OUTPUT:
	A vector in L\{v} that is closest to v (and only one, even if it is not unique).

	Remark: We assume that has not too large coordinates with respect to
	the LLL reduction of L. In this way we can calculate the coordinates of v with
	respect to this reduced matrix quite well with an floating point inverse of this matrix.
	Calculating the precise inverse is extremely expensive.
	'''

	def approxIntegralCoordinatesWrtL1(L1,v):
		L1approx = L1.change_ring(RealField((50+1.45*logStar(max(L1.list()))+0.73*logStar(normSquared(v))).round()));
		v0real = L1approx.inverse() * v; #approx. coordinates of v wrt. L1
		v0 = vector([x.round() for x in v0real]);
		return v0;		

	if verbose:
		print "Start computing closest vector...";
		sys.stdout.flush();

	if Q==None:
		Q = identity_matrix(ZZ,L.nrows());

	L = L.change_ring(ZZ);
	L1 = L.transpose().LLL().transpose(); #LLL reduction of columns

	if verbose:
		print "... LLL done...";
		sys.stdout.flush();

	#Linv = L.inverse(); #This is extremely costly! We should avoid that!
	#if verbose:
	#	print "... Linv done...";
	#	sys.stdout.flush();

	'''
	L1inv = L1.inverse(); #This is extremely costly! We should avoid that!
	if verbose:
		print "... L1inv done...";
		sys.stdout.flush();

	v0 = L1inv*v; #coordinates of v wrt. basis L1
	v0Round = vector([x.round() for x in v0]);
	v0red = v0-v0Round;
	#Check whether v already lies in L,
	#in which case we reduce to shortest vector problem:
	if v0red.is_zero():
		return v + my_shortestVector_viaLattice(L);
	vRound = L1*v0Round;
	vRed = v - vRound; #=L1*v0red
	'''

	v0Round = approxIntegralCoordinatesWrtL1(L1,v);
	vRound = L1*v0Round;
	vRed = v - vRound;
	if vRed.is_zero():
		return v + my_shortestVector_viaLattice(L1,Q,verbose=verbose);

	#U = Linv*L1;
	U = L1;
	A = L1.transpose()*Q*L1; #associated quadratic form wrt. the new basis

	if verbose:
		#print "L =",L;
		#print "L1 =",L1;
		sys.stdout.flush();

	#In the following we compute all lattice points that have norm at most
	#twice the norm of vRed.
	#This list contains the lattice point that is closest to vRed.
	boundForNormSquared = 4*normSquared(vRed,Q);
	solutionList = [];
	if verbose:
		print "bound For Norm Squared =",RR(boundForNormSquared);
		sys.stdout.flush();
	if verbose:
		print "... invoking Fincke-Pohst...";
		sys.stdout.flush();
	[bufferWasBigEnough,numSolutions] = my_finckePohst_viaGramMatrix(A, boundForNormSquared, solutionList=solutionList, maxNumSolutions=None, finalTransformation=U, callback=None, callbackArgs=None);
	#bufferWasBigEnough is always true here, as we don't bound the buffer (i.e. we put maxNumSolutions=None).

	#Determine closest lattice point to vRed:
	closestPoint = zero_vector(len(vRed));
	distanceSquared = normSquared(vRed,Q);
	for w in solutionList:
		nSq = normSquared(w-vRed,Q);
		if nSq < distanceSquared and nSq!=0:
			closestPoint = w;
			distanceSquared = nSq;

	if distanceSquared==0:
		return v + my_shortestVector_viaLattice(L1,Q,verbose=verbose);

	if verbose:
		print "... closest vector found.";
		sys.stdout.flush();

	return vRound + closestPoint;

########################################################################
### Innitial height bounds and conversion of bounds: ###################
########################################################################

def general_initialBounds_Mmax0_and_N0(E,S,mwBasis,lamdaMinQhk,Qf,precision=RR.prec(),method="PZGH99",verbose=True):
	'''
	Computes
	 - the initial bound Mmax0 for the Neron-Tate height and
	 - the initial bound N0 for the maximal Mordell-Weil coefficient
	of the S-integral points on the Mordell curve E, which is
	minimal at all primes in S.
	The 'method' can be
	- "PZGH99": The bound comes from [Peth"o-Zimmer-Gebel-Herrmann '99, "Computing all S-integral points on elliptic curves"]
	- TODO: "HKK14": The bound comes from [Hirata-Kohno--Kovacs '14, "Computing S-integral points on elliptic curves of rank at least 3"]
	'''

	debug = False;
	#debug = True;
	
	R = RealIntervalField(precision);

	if method=="PZGH99":
		#Bound from [Peth"o-Zimmer-Gebel-Herrmann '99, "Computing all S-integral points on elliptic curves"]:
		Delta1 = R(-2^2*3^9*(E.c4()^3-E.c6()^2));
		sStar = R(len(S)+1);
		q = R(max(S + [2]));
		k2 = log(max(abs(R(E.b2())),abs(R(E.b4()))^(1/2),abs(R(E.b6()))^(1/3),abs(R(E.b8()))^(1/4)));
		k3 = R(32/3 * abs(Delta1).sqrt() * (8 + 1/2*log(abs(Delta1)))^4);
		k4 = R(20^4 * max(3^6*R(E.c4())^2,16*abs(Delta1)^(3/2)));
		k1 = R(7*10^(38*sStar+49)*sStar^(20*sStar+15)*q^24*max(1,log(q))^(4*sStar-2)*k3*log(k3)^2*((20*sStar-19)*k3+1+log(k4)) + 2*log(2*abs(R(E.b2()))+6));
		Mmax0 = R(k1/2+k2); #Upper bound for Neron-Tate height.
		N0 = R(Mmax0/R(lamdaMinQhk)*R(Qf)^2).sqrt();

		if debug:
			print "Delta1 =",Delta1;
			print "sStar =",sStar;
			print "q =",q;
			print "k2 =",k2;
			print "k3 =",k3;
			print "k4 =",k4;
			print "k1 =",k1;
			print "Mmax0 =",Mmax0;
			print "N0 =",N0;

	elif method=="HKK14":
		#TODO: Need that a1=a2=a3=0!!!
		Eab = E.short_weierstrass_model(compete_cube=True);
		a = E.a4();
		b = E.a6();

		
		r = len(mwBasis);
		w1 = myRRtoRIF(E.period_lattice().real_period(prec=precision));
		g = E.torsion_order();
		j = E.j_invariant();
		j1 = R(j.numerator());
		j2 = R(j.denominator());
		h = log(max(4*abs(R(a)*j2),4*abs(R(b)*j2),abs(j1),abs(j2)));
		s = R(len(S)+1);
		lamda1 = R(lamdaMinQhk)/R(Qf)^2;
		c1 = TODO;
		c2 = exp(c1/s);
		c3 = lamda1/s;
		c4 = R(2.9)*R(10)^R(6*r+6)*R(4)^R(2*r^2)*R(r+1)^R(2*r^2+9*r+R(12.3));
		raise NotImplementedError("TODO...");

	else:
		raise ValueError("method '"+method+"' not known");
		
	return (R(Mmax0.upper()), R(N0.upper()));

def initialBounds_Mmax0_and_N0(a,S,lamdaMinQhk,lamdaMaxQhk,Qf,Qdelta,r,mwBase,precision=RR.prec(),method="vKM15",verbose=False):
	'''
	Computes
	 - the initial bound Mmax0 for the Neron-Tate height and
	 - the initial bound N0 for the maximal Mordell-Weil coefficient
	of the S-integral points on the Mordell curve y^2 = x^3 + a,
	where a is an S-integer.
	The 'method' can be
	- "vKM15": The bound comes from [vkM15].
	- "PZGH99": The bound comes from [Peth"o-Zimmer-Gebel-Herrmann '99, "Computing all S-integral points on elliptic curves"]
	- "ST94": The bound comes from [Stroeker-Tzanakis 94 "Solving elliptic diophantine equations by estimating linear forms in elliptic logarithms"].

	WARNING:
	Only the "vKM15"- and "PZGH99"-bounds are implemented correctly!
	The other bound "ST94" is strictly stronger than the ones that were
	proved there; they are implemented only for comparision.
	TODO: Implement the correct ST94 bound (if needed...).
	'''

	#R = RealField(rnd="RNDU"); #Real field with standard precision, where we always round up.
	R = RealIntervalField(precision);

	if method=="vKM15":

		if a in ZZ:
			m = 1;
		else:
			m = 12;
		#The NT-height of P is bounded by 1/2*height(x) + m/6*height(a) + 1.58.

		if verbose:
			print "Compute aS...";
			sys.stdout.flush()
		#aS = R_up(1728);
		aS = R(1728);
		for p in S:
			aS *= p^2;
		#primesInAS = copy(S);
		exponentsInAs = {2: 0, 3: 0};
		for p in S:
			exponentsInAs[p] = 2;
		exponentsInAs[2] += 1728.ord(2);
		exponentsInAs[3] += 1728.ord(3);
		for (p,n) in factor(abs(a)):
			if not (p in S):
				aS *= p^min(2,n);
				if p in exponentsInAs.keys():
					exponentsInAs[p] += min(2,n);
				else:
					exponentsInAs[p] = min(2,n);
		#if 2 not in primesInAS:
		#	primesInAS.append(2);
		#if 3 not in primesInAS:
		#	primesInAS.append(3);
		if verbose:
			print "Done. aS =",aS;
			sys.stdout.flush()


		N = aS;
		s0N = R(N);
		sInfinityN = R(1);
		d = R(N);
		l = R(N/6);
		lStar = R(N/6);
		for p in exponentsInAs.keys():
			n = exponentsInAs[p];
			if n>=2:
				s0N *= 1-1/p^2;
				sInfinityN *= (p-1)*p^floor(n/2-1);
			d *= 1+1/p;
			l *= p+1;
			lStar *= 1+1/p;

		gUpperBound = 1+d/12; #Upper bound for the genus of the corresponding modular curve.
		M = R(s0N/12 - sInfinityN/2 + 1/3 + 1/4); #Rounding up and this minus sign is indeed no problem here.
		betaBar = R(1/2*M*log(M)+5/8*M*(18+log(l)));
		betaBarStar = R(1/2*gUpperBound*log(gUpperBound*lStar)+1/2*lStar*log(4+4*log(lStar)));
		alphaBar = min(betaBar, betaBarStar);
		alpha = alphaBar; #The actual alpha is actually slightly smaller, but more difficult to compute.
		kappa = R(4*pi+log(163/pi));
		
		if verbose:
			print "s0N =",s0N;
			print "sInfN =",sInfinityN;
			print "l =", l;
			print "l* =", lStar;
			print "N =",N;
			print "Upper bound for g:",gUpperBound;
			print "M =",M;
		#print betaBar, betaBarStar, alpha;

		#Bound for NT-height of P:
		heightBoundForX = 1/3*a.global_height()+4*alpha + 2*log(alpha+kappa)+35+4*kappa;
		NTheightBoundForP = 0.5*heightBoundForX + m/6*a.global_height()+1.58;
		#This is a bound for the largest coefficent (which we don't need anymore):

		#N0 (the MW-coefficient bound) is depreciated, we use Mmax0 instead, the bound for the approximated Neron-Tate height.
		N0 = sqrt(NTheightBoundForP/lamdaMinQhk*Qf^2); #Here the rounding procedure for the numerator is used, i.e. rounding up.
		Mmax0 = NTheightBoundForP;

		if verbose:
			print "height bound for x coordinate:",heightBoundForX;
			print "Neron-Tate height bound for P:",NTheightBoundForP;
			print "Lower bound for spectral gap:",lamdaMinQhk/Qf^2;
			print "Innitial upper bound Mmax0 =",Mmax0;
			print "Innitial upper bound N0 =",N0;

	elif method=="PZGH99":
		#Bound from [Peth"o-Zimmer-Gebel-Herrmann '99, "Computing all S-integral points on elliptic curves"]:
		delta0 = R(27 * abs(R(a))^2);
		k3 = 32/3 * delta0^(1/2) * (8+R(1/2)*log(delta0))^4;
		k4 = 10^4 * 256 * delta0^(3/2);
		s = R(len(S));
		q = R(max(S + [2]));
		kappa1 = R(7/2 * 10^(38*s + 87) * (s+1)^(20*s+35) * q^24 * max(1,log(q))^(4*s+2) * k3 * log(k3)^2 * (k3+20*s*k3+log(myRRtoRIF(RR(exp(1)))*k4)));
		Mmax0 = R(kappa1 + 1/3*log(abs(R(4*6^3*a)))); #Upper bound for Neron-Tate height.
		N0 = R(Mmax0/lamdaMinQhk*Qf^2).sqrt();

	elif method=="ST94":
		#slightly stronger bound than the one by [Stroeker-Tzanakis 94 "Solving elliptic diophantine equations by estimating linear forms in elliptic logarithms"]:
		#(up to possibly numerical errors, which make the bound slightly larger again...)
		lamda = RIF(lamdaMinQhk/Qf^2); #lower bound on smallest eigenvalue of height-pairing matrix
		q = R(max(S + [1]));
		N0 = lamda^(-1/2) * 10^(3*r+2) * 4^((r+1)^2) * (r+2)^((r^2+13*r+R(23.3))/2) * prod([max((myRRtoRIF(mwBase[i].height())/R(2))^(1/2),log(R(4*abs(a)))) for i in range(r)]) * q^r;
		Mmax0 = R(r)*(R(lamdaMaxQhk)+Qdelta)*N0^2 / Qf^2;

	else:
		raise ValueError("method '"+method+"' not known");
		
	return (R(Mmax0.upper()), R(N0.upper()));

def computeX0andCKappa(ECache,kappa=None,verbose=False):
	'''
	INPUT
	A rational number kappa>=1 (or a RIF), e.g. take kappa=20.
	If kappa=None then we compute one that is nearly optimal wrt. to some heuristic (see [vKM15]).

	OUTPUT:
	A tuple (cKappa,x0) with the following meaning:

	For each S-integral solution P=(x,y) such that
	|x|_v <= |x| for all v in S,
	we have either
	- |x| <= x0, or
	- |sum ni*alpha_i + k*w1| <= m*cKappa / |x|.

	Here, cKappa is decreasing with kappa, and x0 is roughtly linear in kappa.
	alpha_i = log(m*Pi)  
	'''

	debug = False;
	
	E = ECache.E;

	g2 = E.c4()/12;
	g3 = E.c6()/216;

	t = var("t");
	f(t) = 4*t^3 - g2*t - g3;
	roots = f.roots(t,multiplicities=False); #result is a symbolic expression over Q(i) containing second and third roots.
	if debug:
		print "f:",f;
		print "roots of f:",roots;
		sys.stdout.flush();

	maxRootAbs = max([RIF(CIF(xi).abs().upper()) for xi in roots]);
	if debug:
		print "maxRoot:", maxRootAbs;
		sys.stdout.flush();

	tmp = E.b2().abs()/12 + maxRootAbs;
	
	if kappa != None:
		x0 = (kappa+1)*tmp;
		cKappa = ((kappa+1)/kappa)^2;
	else:
		#take a reasonably small kappa>=1, according to the heuristic in the heightLogSieve:
		b_aim = 10; #will be radius for extra search
		kappa = RIF(1.0);
		tMax = 4; #Must be >=1. This is just a heuristic for the largest t that appears in the refined sieve, and here it has not much of an effect.
		while True:
			newKappa = kappa * RIF(1.1);
			x0 = (newKappa+1)*tmp;
			b = heightBound_for_extraSearch(ECache,tMax,x0=x0);
			if debug: #verbose:
				print "try kappa:",newKappa,"--> b =",b;
			if b.upper()>b_aim:
				break;
			kappa = newKappa;
		cKappa = ((kappa+1)/kappa)^2; #a factor that appears in the equalities for the elliptic logarithms.
		x0 = (kappa+1)*tmp;
	if verbose:
		print "|max root of f| =",maxRootAbs;
		print "tmp =",tmp;
		print "kappa:", kappa;
		print "cKappa:", cKappa;
		print "x0:", x0;
		sys.stdout.flush();
	return (cKappa,x0);

def heightBound_for_extraSearch(ECache,tMax,x0=None):
	if x0 == None:
		x0 = ECache.x0;
	#Compute how far the extra search has to go:
	tStar = min(tMax,max(ECache.maxSizeOfSiContainingInfinity,ECache.maxSizeOfSiContaining2));
	w_tStar = ECache.refinedSieveWeights[tStar];
	s_tStar = len([p for p in ECache.S if not RIF(p)^(2*w_tStar) > max(x0,4)]);
	return ECache.mu + 1/(2*w_tStar) * (1+s_tStar) * log(RIF(max(x0,4)));

def convert_MmaxQhk_to_MmaxQ(MmaxQhk,Qf,Qdelta):
	'''
	Determine a bound Mmax for ||q||_Q <= MmaxQ from a 
	given bound Mmax for h_k(P) = ||q||_Qhk <= MmaxQhk.
	'''
	MmaxQ = ((RIF(MmaxQhk)+Qdelta) / Qf^2).upper();
	return MmaxQ;

########################################################################
### Height logarithm sieve: ############################################
########################################################################

def heightLogarithmSieve(n,Mmax,ECache,testMethod=None,normSqQhk=None,verbose=True):
	'''
	INPUT:
	n - the coefficient vector for the MW base of the candidate point
		(all possible torsion has to be considered).
	Mmax - DEPRECIATED: it gets set to Infinity automatically now.
	ECache - an instance of E_Cache storing additional data of the given elliptic curve E.
	testMethod - one of the methods in ECache.heightLogSieve_Methods, see below.
	normSqQhk - the norm of sum n_i * P_i w.r.t. Qhk, if it has been computed already.

	OUTPUT:
	Set of coefficient vectors of all candidates that pass the heightLogSieve;
	now there is an additional coordinate for the torsion point index
	that is added to the linear combination of MW base points.

	REMARK:
	The parameter ''testMethod'' can be one of the following:
	- "NoTest": Any candidate n passes the test.
	- "WeakHeightLogSieve": For each torsion point, test the weak heigh-log-inequality,
		which does not involve the reductions of E mod p.
	- "StrongHeightLogSieve": For each torsion point, test the weak heigh-log-inequality,
		which does involve the reductions of E mod p at the places != 2 of good reduction.
	- "Automatic_Weak_or_NoTest": Do "NoTest" or "WeakHeightLogSieve" depending on how
		the norm of P = sum n_i*P_i compares to ECache.minHeightForHeightLogSieveTest.
	- "Automatic_STrong_or_NoTest": Do "NoTest" or "StrongHeightLogSieve" depending on how
		the norm of P = sum n_i*P_i compares to ECache.minHeightForHeightLogSieveTest.
	'''


	if testMethod == None:
		testMethod = ECache.heightLogSieve_Method;

	if testMethod in ["Automatic_Weak_or_NoTest","Automatic_Strong_or_NoTest"]:
		if normSqQhk == None:
			normSqQhk = normSquared(n,Q=ECache.Qhk);
		if normSqQhk < ECache.minHeightForHeightLogSieveTest:
			testMethod = "NoTest";
		else:
			if testMethod == "Automatic_Weak_or_NoTest":
				testMethod = "WeakHeightLogSieve";
			else:
				testMethod = "StrongHeightLogSieve";

	if testMethod == "NoTest":
		return set([n + tuple([t]) for t in range(ECache.torsionOrder)]);

	#At this point, testMethod is either "WeakHeightLogSieve" or "StrongHeightLogSieve".
	
	E = ECache.E;
	Sstar = ECache.Sstar;
	mwBasis = ECache.mwBasis;
	Qhk = ECache.Qhk;
	Qf = ECache.Qf;
	r = len(mwBasis);
	torsionOrder = ECache.torsionOrder;

	if verbose:
		print "Do HeightLogSieve for candidate n =",n;

	#Avoid too many different Mmaxes, such that logs are not computed every single time:
	#Mmax = exp(log(Mmax).ceil());
	#basicPrecision = ((Mmax/Qf^2 + ECache.mu + 1/24*E.j_invariant().global_height())/len(Sstar)*(1+log(len(Sstar)))).ceil();

	Mmax = Infinity; #Use the same test for all Mmax! (It turned out that adjusting the log precisions according to the size (say Mmax.log().floor()) doesn't bring much of an advantage...)
	#basicPrecision = 100;
	basicPrecision = 30; #on RVK's request
	
	soFarUnsufficientTorsionIndices = range(torsionOrder); #These are the indices of the torsion points in the list torsionPoints that still may fail the height-log inequality (which we want such that we can sieve them out).
	successfulTorsionIndices = []; #This will be the complement of soFarUnsufficientTorsionIndices.

	if ECache.heightLogSieve_Log.has_key(Mmax):
		heightLogSieve_Log = ECache.heightLogSieve_Log[Mmax];
		heightLogSieve_Prec = ECache.heightLogSieve_Prec[Mmax];
		heightLogSieve_W1 = ECache.heightLogSieve_W1[Mmax];
	else:
		if verbose:
			print "Basic precision for heightLogSieve:",basicPrecision;
		heightLogSieve_Log = {};
		heightLogSieve_Prec = {};
		heightLogSieve_W1 = None;
		for p in Sstar:
			m = ECache.m[p];
			if p == Infinity:
				heightLogSieve_Prec[Infinity] = RR(m + 2 + ECache.orderOfW1 + basicPrecision/log(2)).ceil();
				heightLogSieve_W1 = myRRtoRIF(E.period_lattice().real_period(prec=heightLogSieve_Prec[Infinity]));
				if verbose:
					print "type(heightLogSieve_W1):",type(heightLogSieve_W1);
					print "heightLogSieve_W1 =",heightLogSieve_W1;
				for i in range(r):
					logarithm = ECache.log(mwBasis[i],Infinity,prec=heightLogSieve_Prec[Infinity]) #This is the elliptic log of m[Infinity]*P !
					if logarithm.__class__.__name__.startswith("Complex"):
						logarithm = logarithm.real();
					heightLogSieve_Log[(Infinity,i)] = myRRtoRIF(logarithm);
					if verbose:
						print "type(heightLogSieve_Log[(Infinity,i)]):",type(heightLogSieve_Log[(Infinity,i)]);
						print "heightLogSieve_Log[(Infinity,i)] =", heightLogSieve_Log[(Infinity,i)];
			else: # p == finite:
				if r>=2:
					#C = ((1/RIF(sigma)*(RIF(Mmin)/Qf^2-ECache.mu))/RIF(p).log()-ordAlphaP0+m.ord(p)).upper().ceil();
					heightLogSieve_Prec[p] = (m.ord(p) + basicPrecision/log(RIF(p))).upper().ceil();
					
					#Sometimes, this heightLogSieve_Prec[p] is larger than the precision that was needed in the first reduction step at p!
					#This is obviously too large. Thus:
					#print "ECache.logs:",ECache.logs;
					heightLogSieve_Prec[p] = min(min([ECache.logs[(P,p)].precision_absolute() for P in mwBasis]),heightLogSieve_Prec[p]); #Here we assume that the first reduction step at p was already done!
				
					for i in range(r):
						P = mwBasis[i];
						pAdicLog = ECache.log(P,p,prec=heightLogSieve_Prec[p]); #Note that this computes the p-adic log of m[p]*P !
						heightLogSieve_Log[(p,i)] = pAdicLog;
			#if verbose:
			#	print "heightLogSieve_Prec at p =",p,": ",heightLogSieve_Prec[p];
		ECache.heightLogSieve_Log[Mmax] = heightLogSieve_Log;
		ECache.heightLogSieve_Prec[Mmax] = heightLogSieve_Prec;
		ECache.heightLogSieve_W1[Mmax] = heightLogSieve_W1;

	if normSqQhk == None:
		normSqQhk = normSquared(n,Q=ECache.Qhk);
	normSq = RIF(normSqQhk)/Qf^2;
	LHS =  normSq - ECache.mu;
	RHSs = [RIF(0) for t in range(torsionOrder)];
	for p in Sstar:
		#print "Do p =",p;
		if p == Infinity:
			#RIFp = RealIntervalField(heightLogSieve_Prec[Infinity]);		
			lpRepr = abs(sum([n[i]*heightLogSieve_Log[(Infinity,i)] for i in range(r)]));
			l = (lpRepr/heightLogSieve_W1).floor();
			lp1 = lpRepr - l*heightLogSieve_W1;
			if lp1.lower()<=0:
				if verbose:
					print "Candidate tested successfully due to lack of precision' at p =",p;
				lp = RIF(Infinity);
			else:
				lp2 = lpRepr - (l+1)*heightLogSieve_W1;
				if lp2.upper()>=0:
					if verbose:
						print "Candidate tested successfully due to lack of precision'' at p =",p;
					lp = RIF(Infinity);
				else:
					lp = -min(log(lp1),log(-lp2));
					lp += log(RIF(ECache.m[Infinity]*ECache.cKappa))
					if verbose:
						print "lInfty and lInftyMin:",lp, 1/2*log(RIF(ECache.x0));
					lp = max(lp,1/2*log(RIF(ECache.x0)));
			relevantTorsionIndicesAtP = copy(soFarUnsufficientTorsionIndices);
		else: #p = finite:
			if testMethod != "StrongHeightLogSieve" or p==2 or (p not in ECache.primes_at_which_reduction_is_considered):
				relevantTorsionIndicesAtP = copy(soFarUnsufficientTorsionIndices);
			else:
				#E has good reduction at p and p!=2 and we use StrongHeightLogSieve.
				#Thus if the point P does NOT go to zero in E(F_p), then we may take the summand lp=0.
				if r==1:
					#print "debug",p;
					relevantTorsionIndicesAtP = [];
					for i in soFarUnsufficientTorsionIndices:
						if (n[0]*ECache.ordersOfTorsionPoints[i]) % ECache.orderOfMWBasisRed[p] == 0:
							relevantTorsionIndicesAtP.append(i);
				else:
					mwBasisRed = ECache.mwBasisRed[p];
					#torsionRedSet = ECache.torsionRedSet[p];
					torsionRed = ECache.torsionRed[p];
					EredGeneratorOrders = ECache.EredGeneratorOrders[p];
					nRed = -sum([n[i]*mwBasisRed[i] for i in range(r)]);
					#print "nRed =",nRed
					#print "EredGeneratorOrders =",EredGeneratorOrders
					#print "mwBasisRed =",mwBasisRed
					nRed = vector([nRed[i] % EredGeneratorOrders[i] for i in range(len(EredGeneratorOrders))]);
					#print "debug"
					relevantTorsionIndicesAtP = [t for t in soFarUnsufficientTorsionIndices if nRed == torsionRed[t]];

			if relevantTorsionIndicesAtP != []:
				#Need to compute local summand lp:
				if r==1:
					ordp_sumNiAi = Integer(n[0]).ord(p) + ECache.ordAlphaP0[p];
					
				else: #r>=2:
					sumNiAi = sum([n[i]*heightLogSieve_Log[(p,i)] for i in range(r)]);
					if sumNiAi.is_zero():
						#Precision was not enough to determine the order of sumNiAi.
						#If precisionw as chosen high enough this means anyways that
						#this test will not be able to remove this candidate.
						#if verbose:
						#	print "Candidate tested successfully due to lack of precision at p =",p;
						
						#lp = RIF(Infinity);
						ordp_sumNiAi = RIF(Infinity);
					else:
						ordp_sumNiAi = sumNiAi.ordp();
				lp = log(RIF(p)) * RIF(ordp_sumNiAi - ECache.m[p].ord(p));
				if p == 2:
					lp = max(lp,log(RIF(2)));
				else:
					lp = max(lp,0);

		for t in relevantTorsionIndicesAtP:
			RHSs[t] += lp;
			if LHS.lower() <= RHSs[t].upper():
				#Torsion index t passed the heightLogarithmSieve:
				soFarUnsufficientTorsionIndices.remove(t);
				successfulTorsionIndices.append(t);
		if soFarUnsufficientTorsionIndices == []:
			#All torsion indices passed the heightLogarithmSieve:
			break;

		#print "Finished with p =",p,"and soFarUnsufficientTorsionIndices =",soFarUnsufficientTorsionIndices;
		#print "Summand at",p,":",lp;

	#successfulTorsionIndices = [t for t in range(torsionOrder) if t not in soFarUnsufficientTorsionIndices];
	#print "At the end of quick reduction: soFarUnsufficientTorsionIndices =",soFarUnsufficientTorsionIndices;
	#print "successfulTorsionIndices =",successfulTorsionIndices;

	if verbose:
		print "Candidate",n,"satisfies LHS =",LHS,"and RHSs =",RHSs,"for torsion points with indices in",successfulTorsionIndices;
	return set([n + tuple([t]) for t in successfulTorsionIndices]);

########################################################################
### Refined sieve: #####################################################
########################################################################

def bottomRowOfLatticeA(p,C,ECache,verbose=True):
	'''
	Computes the non-trivial rows in the matrices A for the refinedSieveAtT()
	consisting of the elliptic or p-adic logarithms.
	'''

	E = ECache.E;
	mwBasis = ECache.mwBasis;

	if p==Infinity: #At Infinity:

		#print "debug13434: C:",C;
		
		C = RIF(C);
		#|sum ni*alpha_i + k*w1| <= m * cKappa * exp(-1/sigma * (||n||_Q^2 - mu)).
		#with alpha_i = log(m*P_i)
		#sigma = len(S)+1 bzw. alpha*tau
		
		Cw1, Cprec, highPrecision = ECache.roundedCtimesOmega1_preciseC_highPrecision(C);
		mwBasisLogPrec = [ECache.log(P,Infinity,highPrecision) for P in mwBasis]; #Note: These are the elliptic logs of m[Infinity]*P !

		if verbose:
			#print "Computed elliptic logs with precision ",highPrecision;
			print "High precision =",highPrecision,"(p=Infty)";
			#print "mwBasisLog =",mwBasisLogPrec;
			sys.stdout.flush();

		bottomRow = [(Cprec*l).round() for l in mwBasisLogPrec];
		bottomRow.append(Cw1);

	else: #At finite p:
		
		#Determine ordAlphaP0, the smallest order of ord_p(alphaP), where alphaP = padic-ell-log of MW basis elements.


		#P0 = ECache.P0[p]; #DEPRECIATED: Not needed anymore.
		ordAlphaP0 = ECache.ordAlphaP0[p];
		m = ECache.m[p];
			
		#if verbose:
		#	print P0, ordAlphaP0, m;

		#mwBasisWoP0 = copy(mwBasis);
		#mwBasisWoP0.remove(P0);

		pC = p^C;
		r = len(mwBasis);

		if r==1:
			bottomRow = [1,pC];
			#The first entry here is actually log(alpha_0)/p^ord(alpha_0), alpha_0 being the p-adic log of P0, but it is only important that this number is integral and not divisible by p.
			#Any such number does the job. Note in particular, that we only need to know the order of alpha_0, nothing else. This is very particular for rank r=1.

		if r>=2:
			highPrecision = C + ordAlphaP0; #In the paper, ordAlphaP0 is called $ord_p(\alpha_{i^*})$.
			if verbose:
				print "High precision =",highPrecision,"(p=",p,")";
				sys.stdout.flush();

			#Compute p-adic logs of m*P for each P in the MW basis:

			#print "Compute logs..."
			mwBasisLog = [ECache.log(P,p,prec=highPrecision) for P in mwBasis]; #Note that these are the p-adic logs of m*P!
			if verbose:
				#print "done.";
				sys.stdout.flush();

			#bottomRow = [l.lift() % pC for l in mwBasisLog];
			bottomRow = [(l/p^ordAlphaP0).add_bigoh(C).lift() % pC for l in mwBasisLog]; #The entries of this list are called $\beta_i$ in the paper.
			bottomRow.append(pC);

	return bottomRow;

def refinedSieveAtT(T,Mmin,Mmax,sigma,ECache,maxCandidates=None,diligentAndSlow=True,verbose=True):
	'''
	Do the refined sieve at T (see the paper or refinedSieve() for what this does).

	INPUT:
	Mmin, Mmax - as in refinedSieve().
	diligentAndSlow - a boolean: There are two algorithms for the refinedSieveAtT.
				If diligentAndSlow == True then less candidates are found in general,
				however it may take slightly longer.
	maxCandidates - the buffer size for the candidate set, as in refinedSieve().
	ECache - an instance of E_Cache (caching some data associated to the elliptic curve E).
	sigma - a positive rational number, see the paper. For the ordinary sieve (i.e. tau=1),
				one takes sigma = |Sstar|. In the refined sieve for larger tau, one may
				choose a smaller (and hence better) sigma.

	OUTPUT:
	[bufferWasBigEnough,candidateSet], where
	 - bufferWasBigEnough is a boolean saying whether result will be complete and
	 - candidateSet is a set of candidates found.
	'''
	
	#It is important that if Infinity is in T, then it's the last element.
	#Output: [bufferWasBigEnough,listOfCandidates]

	debug = True;
	debug = False;
	if debug:
		verbose = True; #debug

	E = ECache.E;
	mwBasis = ECache.mwBasis;
	r = len(mwBasis);
	Qhk = ECache.Qhk;
	Qf = ECache.Qf;
	
	solutions = set([]);
	if verbose:
		print "========================================================";
		print "T =",T,", Mmax =",Mmax, ", sigma =",sigma;
		sys.stdout.flush();			

	#Compute bottom rows for A at finite places:
	bottomRowsFinite = [];
	for p in T:
		if p!=Infinity:
			if verbose:
				print "p =",p,": -----------------"
			#P0 = ECache.P0[p]; #DEPRICIATED: Not needed anymore
			ordAlphaP0 = ECache.ordAlphaP0[p];
			m = ECache.m[p];
			C = ((1/RIF(sigma)*(RIF(Mmin)/Qf^2-ECache.mu))/RIF(p).log()-ordAlphaP0+m.ord(p)).lower().ceil();
			if verbose:
				print "Mmax = ",Mmax,", Mmin =",Mmin,", Qf =",Qf;
				print "Original C =",C;
				sys.stdout.flush();
			C = max(C,0);
			if verbose:
				print "m =",m,", p =",p,", C = ",C,", sigma =",sigma;
				sys.stdout.flush();			
			bottomRowsFinite.append(bottomRowOfLatticeA(p,C,ECache,verbose=verbose));
		
	if verbose:
		print "bottomRowsFinite:";
		print bottomRowsFinite;
		sys.stdout.flush();			

	for i in range(len(bottomRowsFinite)):
		for j in range(i):
			bottomRowsFinite[i].insert(-1,0);
		for j in range(i+1,len(bottomRowsFinite)):
			bottomRowsFinite[i].append(0);

	#Compute bottom row for A at infinite place:
	if Infinity in T:
		if verbose:
			print "p = infty : -----------------"
			sys.stdout.flush();	
		#Choose C according to heuristic such that both terms coming from C, M' respecitvely are equally large (roughly):

		#First we bound the abs of the last coordinate in the lattice
		#given by the columns of A. This bound is delta=delta1 + delta2,
		#where delta1 comes from the rounding errors,
		#and delta2=C*delta2overC comes from C and M'.
		m = ECache.m[Infinity];
		delta1 = 2*(1/2 + 2^(-ECache.safetyBitsForRounding))*(m+(r*RIF(Mmax)/RIF(ECache.lamdaMinQhk)).sqrt());
		delta2overC = m*RIF(ECache.cKappa)*exp(-1/sigma*(RIF(Mmin)/Qf^2-ECache.mu));

		#choose C such that delta1 and delta2 become roughly equal:
		Cinf = delta1 / delta2overC;
		#Cinf *= 2^20
		if diligentAndSlow:
			Cinf *= 2^10;
		Cinf = Cinf.upper();

		delta = delta1 + Cinf*delta2overC;

		if verbose:
			print "m =",m;
			print "mu =",ECache.mu;
			print "Mmax/Qf^2 =",Mmax/Qf^2;
			print "Mmin/Qf^2/sigma =",RIF(Mmin)/Qf^2/sigma;
			print "cKappa =",ECache.cKappa;
			print "delta1 =",delta1;
			print "delta2 ohne C:",delta2overC;
			print "delta =",delta;
			print "C =",Cinf;
			sys.stdout.flush();	
					
		bottomRowInfty = bottomRowOfLatticeA(Infinity,Cinf,ECache,verbose=verbose);

		if verbose:
			print "bottomRowInfty:",bottomRowInfty;
			sys.stdout.flush();	

	#Setting up lattice for Fincke-Pohst:

	if Infinity in T:
		lastEntryOfQnumerator = RIF((RIF(Mmax)/delta^2).lower()); 
		lastEntryOfQdenominator = 1;
		while lastEntryOfQnumerator.lower()<2^10: #It may make sense to increase this number (implies longer running time for Fincke-Pohst, but yields less false candidates)
			lastEntryOfQnumerator *= 2;
			lastEntryOfQdenominator *= 2;
		lastEntryOfQnumerator = lastEntryOfQnumerator.lower().floor();
		#lastEntryOfQnumerator = lastEntryOfQnumerator.lower().floor()/2^i;
		if verbose:
			print "lastEntryOfQ =",lastEntryOfQnumerator,"/",lastEntryOfQdenominator;
			sys.stdout.flush();	

	if debug:
		print "diligentAndSlow:",diligentAndSlow;

	if diligentAndSlow: #In the paper we always use this option diligentAndSlow=True.
		#In this version of the sieve we compute first the sublattice
		#of all candidate vectors for which the coordinates
		#corresponding to the finite places in T vanish exactly:
		M = matrix(ZZ,bottomRowsFinite);
		#K = M.right_kernel().matrix();
		Kernel = M.transpose().integer_kernel().matrix();
		if T==[Infinity]:
			K = identity_matrix(ZZ,r);
		else:
			K = Kernel.matrix_from_columns(range(r)).transpose();
			K = matrix(ZZ,K);

		if verbose:
			print "type M:",type(M),"M=\n",M;
			print "Kernel of M =\n", Kernel;
			print "type K:",type(K),"K=\n", K;
			sys.stdout.flush();			

		#TODO: Bad notation: Q is used in two different ways (1. as height pairing matrix/2, and 2. as quadratic form defining the ellipsoid for Fincke--Pohst):
		#We should rename the latter one!

		if Infinity not in T:
			A = K;
			Q = Qhk;
			normSqBound = RIF(Mmax).upper().floor();
		else:
		
			Kx = block_diagonal_matrix(K,matrix(ZZ,[[1]]));
			A = identity_matrix(ZZ,r+1);
			for i in range(r+1):
				A[r,i] = bottomRowInfty[i];
			#print "dims A, Kx, K:",A.dimensions(),Kx.dimensions(), K.dimensions();
			#print "T:",T;
			A = A * Kx;

			#DEPRECIATED: Old weights for the blocks of the quadratic form:
			#Q = block_diagonal_matrix(lastEntryOfQdenominator*Qhk,matrix([[lastEntryOfQnumerator]]));
			#Q = matrix(Q,ZZ);
			#normSqBound = (RIF(2)*Mmax*lastEntryOfQdenominator).upper().floor(); #The floor comes from the fact that Q is an integral matrix.

			#New, more optimal weights:
			Q = block_diagonal_matrix(r*lastEntryOfQdenominator*Qhk,matrix(ZZ,[[lastEntryOfQnumerator]]));
			#Q = matrix(ZZ,Q);
			normSqBound = (RIF(r+1)*Mmax*lastEntryOfQdenominator).upper().floor(); #The floor comes from the fact that Q is an integral matrix.
	else:
		#This is the faster(?) but more sloppy version:
		#Instead of computing that sublattice where the coordinates
		#corresponding to the finite places are zero we simply bound
		#these by 1.
		#
		#In the paper we never use this option diligentAndSlow=False.

		A = identity_matrix(ZZ,r+len(T));
		for i in range(len(bottomRowsFinite)):
			row = bottomRowsFinite[i];
			for j in range(r+len(bottomRowsFinite)):
				A[r+i,j] = row[j];
		if Infinity in T:
			for j in range(r):
				A[-1,j] = bottomRowInfty[j];
			A[-1,-1] = bottomRowInfty[r];
		if verbose:
			print "A =\n",A;
			sys.stdout.flush();

		Q = block_diagonal_matrix(Qhk,diagonal_matrix(ZZ,[RIF(Mmax).upper().floor() for k in range(len(T))]));
		if Infinity in T:
			Q = lastEntryOfQdenominator * Q;
			Q[-1,-1] = lastEntryOfQnumerator;
			normSqBound = (RIF(2)*Mmax*lastEntryOfQdenominator).upper().floor();
		else:
			normSqBound = RIF(Mmax).upper().floor();
		#Q = matrix(ZZ,Q);

	#Do Fincke-Pohsting:

	GramMatrix = A.transpose() * Q * A;
	if verbose:
		print "type A:",type(A),"A=\n", A;
		print "type Q:",type(Q),"Q=\n", Q;
		print "GramMatrix =\n", GramMatrix;
		print "det(GramMatrix) =",det(GramMatrix);
		sys.stdout.flush();		

	#return [False,set([])]; #debugging...

	candidatesModSign = [];
	[bufferWasBigEnough,numSolutions] = my_finckePohst_viaGramMatrix(GramMatrix,normSqBound,center=0,solutionList=candidatesModSign,maxNumSolutions=maxCandidates,finalTransformation=None,callback=None,callbackArgs=None,lllReduce=True,breakSymmetry=True);

	if debug:
		print "Fincke-Pohst returns candidatesModSign:";
		#for c in candidatesModSign:
		#	print c;

	if bufferWasBigEnough == False:
		return [False,set([])];


	candidates = [];
	for c in candidatesModSign:
		cTuple = tuple(c.list_from_positions(range(r))); #only the first r components!

		if debug:
			c1 = (0, -1, 0, -1, 0, -1, 0, 1);
			mc1 = (0, 1, 0, 1, 0, 1, 0, -1);
			c2 = (1, 0, 0, 1, 0, 1, 1, 0);
			mc2 = (-1, 0, 0, -1, 0, -1, -1, 0);
			debugInfo = False;
			if c1==cTuple or mc1==cTuple:
				print "c1 was found in FinckePohst output";
				debugInfo = True;
			if c2==cTuple or mc2==cTuple:
				print "c2 was found in FinckePohst output";
				debugInfo = True;
		normSq = normSquared(cTuple,Q=Qhk);
		if Mmin >= normSq:
			if debug and debugInfo:
				print "normSq below Mmin for candidate",c;
			continue;
		if normSq > Mmax:
			if debug and debugInfo:
				print "normSq above Mmax for candidate",c;
			continue;
		if Infinity in T:
			#Check whether c lies in the appropriate cylinder
			#(Fincke-Pohst gave all lattice vectors in the smallest
			#ellipsoid containing this cylinder, which is of course too big):
			#print "last row of A:",A.row(-1),", c =",c;
			d = abs(A.row(-1) * c);
			if d > delta:
				if debug and debugInfo:
					print "last coordinate too large for candidate",c;
				continue;
			#More precise check:
			#Adjust delta1 and delta2 to the candidate c:
			m = ECache.m[Infinity];
			delta1c = RIF(2)*(1/2 + 2^(-ECache.safetyBitsForRounding))*(m+sum([abs(ni) for ni in cTuple]));
			delta2c = Cinf*m*RIF(ECache.cKappa)*exp(-1/sigma*(RIF(normSq)/Qf^2-ECache.mu));
			if d > delta1c+delta2c:
				if debug and debugInfo:
					print "last coordinate slightly too large for candidate",c;
					print "--> here, delta1c =",delta1c,", delta2c =",delta2c,", and delta1c+delta2c =",delta1c+delta2c;
					sys.stdout.flush();
				continue;
			else:
				if debug and debugInfo:
					print "Remaining candidate:",c[r],delta1c,delta2c,normSq;
					print "heightLogarithmSieve output:",heightLogarithmSieve(E,cTuple,ECache.Sstar,Qhk,Qf,Mmax,mwBasis,ECache,verbose=True);
					print "Candidate without torsion is S-integral:",sum([c[i]*mwBasis[i] for i in range(r)])[0].is_S_integral(ECache.S);
					sys.stdout.flush();
			#|sum ni*alpha_i + k*w1| <= m * cKappa * exp(-1/sigma * (||n||_Q^2 - mu)).

		candidates.append(cTuple);
		#cmTuple = tuple((-c).list_from_positions(range(r)));
		#candidates.append(cmTuple);
		
	if verbose:
		print "Num candidates:",len(candidates);
		#print "Candidates:",candidates;
		sys.stdout.flush();		
		
	return [True,set(candidates)];

def refinedSieve(Mmin,Mmax,maxPartSize,maxTupleSize,regularPrecision,ECache,maxCandidates=None,diligentAndSlow=True,verbose=True,parallelIterator='reference'):
	'''
	We determine all points P on E (up to a few technical special cases
	to be covered separately later in the algorithm) with
	 P = sum_i n_i*P_i + T,
	 Mmin < ||n||_Qhk <= Mmax.

	INPUT:
	Mmin, Mmax - as explained above.
	maxPartSize - Sstar gets partitioned into parts of size at most
					maxPartSize (denoted n in the paper).
	maxTupleSize - We consider for each part in the partition of Sstar
					all subsets T of size <= maxTupleSize (denoted tau
					in the paper).
	ECache - an instance of E_Cache.
	maxCandidates - return [False,candidateSet] if more than maxCandidates
					candidates are found.
	diligentAndSlow - see refinedSieveAtT's docstring.
	parallelIterator - determines whether and how the local refinedSieveAtT's
					are	called in parallel.

	OUTPUT:
	[bufferWasBigEnough,candidateSet], where
	 - bufferWasBigEnough is a boolean saying whether result will be complete and
	 - candidateSet is a set of candidates found.	
	'''

	@parallel(p_iter=parallelIterator,ncpus=numCPUs)
	def call_refinedSieveAtT(T,Mmin,Mmax,sigma,ECache,maxCandidates=None,diligentAndSlow=True,verbose=True):
		return refinedSieveAtT(T,Mmin,Mmax,sigma,ECache,maxCandidates=maxCandidates,diligentAndSlow=diligentAndSlow,verbose=verbose);

	debug = False;

	E = ECache.E;
	S = ECache.S;
	Swo2 = copy(S);
	Scontains2 = 2 in S;
	if Scontains2:
		Swo2.remove(2);
	Sstar = ECache.Sstar;
	Qhk = ECache.Qhk;
	Qf = ECache.Qf;
	mwBasis = ECache.mwBasis;
	torsionPoints = ECache.torsionPoints;	
	mu = ECache.mu;

	#The following splits S into parts Si of size at most maxPartSize.
	#There are constraints:
	#The part containing 2 must have at most ECache.maxSizeOfSiContaining2 elements.
	#The part containing Infinity must have at most ECache.maxSizeOfSiContainingInfinity elements.
	#All other parts should have roughly the same size (a difference of 1 element is allowed).

	partSizeGeneral = min(maxPartSize,len(Sstar));
	partSizeInf = min(partSizeGeneral,ECache.maxSizeOfSiContainingInfinity);
	if 2 in S:
		partSize2 = min(partSizeGeneral,ECache.maxSizeOfSiContaining2);
	else:
		partSize2 = Infinity;
	put2AndInfTogether = (not Scontains2) or ((partSize2>=2) and (partSizeInf>=2));
	if put2AndInfTogether:
		partSize2 = min(partSize2,partSizeInf);
		partSizeInf = min(partSize2,partSizeInf);
		numPrimesNotInPartsWith2orInf = max(0,len(Sstar)-partSizeInf);
	else:
		numPrimesNotInPartsWith2orInf = max(0,len(Sstar)-partSize2-partSizeInf);
	numPartsWo2AndInf = (numPrimesNotInPartsWith2orInf/partSizeGeneral).ceil();
	if numPartsWo2AndInf > 0:
		partSizeGeneral = (numPrimesNotInPartsWith2orInf/numPartsWo2AndInf).ceil();
	if put2AndInfTogether:
		numParts = numPartsWo2AndInf + 1;
	else:
		numParts = numPartsWo2AndInf + 2;

	n = partSizeGeneral;
	tau = min(maxTupleSize,max(partSizeGeneral,partSize2,partSizeInf));

	Sis = [[] for i in range(numParts)]; #In the paper, Si is called $S_j$.
	iInf = 0; #index of part Si containing Infinity
	i2 = 0 if put2AndInfTogether else 1; #index of part Si containing 2
	
	Sis[iInf].append(Infinity);
	if Scontains2:
		Sis[i2].append(2);

	iNext = i2 + 1;
	for p in Swo2:
		if iNext >= numParts:
			iNext = 0;
		if iNext == iInf and len(Sis[iInf])>=partSizeInf:
			iNext += 1;
		if Scontains2 and iNext == i2 and len(Sis[i2])>=partSize2:
			iNext += 1;
		Sis[iNext].append(p);
		iNext += 1;
			
	if debug:
		print "Partition of S:",Sis;

	weights = ECache.refinedSieveWeights;
	alpha = sum([sum([weights[min(j,tau)] for j in range(1,len(Si)+1)]) for Si in Sis]); #In the paper, alpha is called $\omega = \sum \omega(j)$.
	z = (Mmin/Qf^2-mu)/alpha;

	#In order to enumerate all candidates P=sum ni Pi + T
	#with Mmin < ||n||_Qhk <= Mmax,
	#we run through all T\subset Si for some Si in Sis with |T|<=tau
	#and find for each such T the set of P with
	#log |x(P)|_v >= z*weight(|T|) for each v in T.

	parameters = [];
	for t in range(1,tau+1): #t = 1..tau:
		for Si in Sis:
			for Tset in Subsets(Si,t):
				T = Tset.list();
				T.sort();

				#We may assume here, that the sieve was applied already
				#for all T'\subset Si' with |T'|<|T| or with
				#|T'|=|T| and i'<i.
				if t == 1:
					newMmax = Mmax;
				else:
					alphaTilda = sum([sum([weights[min(j,t if Sis.index(Sk) < Sis.index(Si) else t-1)] for j in range(1,len(Sk)+1)]) for Sk in Sis]); #In the paper, this is $\omega^*$.
					newMmax = min(Mmax,Qf^2*(alphaTilda*z+mu));

				#Debug: Just for comparison of running times, choose the trivial Mmax for each T:
				newMmax = Mmax; #debug

				#sigma = RIF(alpha)*t;
				sigma = RIF(alpha)/weights[t]; #In the paper, this is called $\sigma_t$.

				#Trivial sigma for test purposes:
				#sigma = len(S)+1
					
				param = (T,Mmin,newMmax,sigma,ECache,maxCandidates,diligentAndSlow,verbose);
				#print param;
				#print "T =",T," newMmax =",newMmax;
				parameters.append(param);

	if verbose:
		print "========================================================";

	candidateSet = set([]);
		
	gen = call_refinedSieveAtT(parameters);
	for x in gen:
		if verbose:
			print "T:",x[0][0][1];

		[bufferWasBigEnough,candidatesFromT] = x[1];

		if verbose:
			print "Buffer was big enough:",bufferWasBigEnough;
			print "Num candidates:",len(candidatesFromT);
			print "========================================================";
		
		if not bufferWasBigEnough:
			return [False,candidateSet];

		candidateSet.update(candidatesFromT);

		#print x[1];
		#if not x[1]:
		#	return False;

	#print ECache.m;
	
	return [True,candidateSet];	

########################################################################
### Main program: ######################################################
########################################################################

@parallel(p_iter=parallelIterator,ncpus=numCPUs)
def computeSIntegralPoints(E,S=[],mwBasis=None,Mmax0=None,verbose=True,bothSigns=False,saveToFile=False,saveToPath=pathData,debugParam={}):
	'''
	Computes the S-integral points of a rational elliptic curve E.

	INPUT:

	- ''E'' - a rational elliptic curve. 

	- ''S'' -  a list of primes, possibly empty.

	- ''mwBasis'' - list of points on E generating the
	  Mordell-Weil group of E (default: None - calls 'E.gens()').

	- ''Mmax0'' - an upper bound for the Neron-Tate height of
	  the points of E in the search space. (Here we use the standard definition
	  as in Silverman's book! Sage uses twice this height.)
	  If Mmax=None, all points are considered.

	- ''bothSigns'' - True/False (default False): if True the
	  output contains both P and -P, otherwise only one of each
	  pair. Note: If the Weierstrass equation is not integral,
	  then only one of P,-P might be S-integral, so we automatically
	  change bothSigns to True!

	- ''verbose'' - True/False (default False): if True, some
	  details of the computation are output.

	OUTPUT:

	A sorted list of all the S-integral points on E (up to sign
	unless both_signs is True).
	'''

	timer = MyTimer();
	debug = False;
	if debug:
		print E,S,mwBasis,Mmax0,verbose,bothSigns,saveToFile;

	####################################################################
	# Check input:
	####################################################################

	##If no Mmax is given, below we will be able to compute one only if E is a Mordell curve, where a is an S-integer!
	#if Mmax0 == None:
	#	if E.c4() != 0:
	#		print "E is no Mordell curve (i.e. j(E) is non-zero), so you need to provide an Mmax0.";
	#		print "There is a bound coming from linear forms in logarithms, see e.g. Gebel-Petho-Zimmer, but it is not implemented yet."
	#		return False;
	#	#if not (54*E.c6()).is_S_integral():
	#	#	print

	if verbose:
		print "Input:",E;
		print "len(S) =",len(S);
		sys.stdout.flush();

	if FractionField(E.base_ring()) != QQ:
		print "INPUT ERROR: Given Weierstrass equation is not rational!";
		return False;
	
	if bothSigns==False:
		#Depreciated: The following criterion was a bit too restrictive:
		#if not E.is_integral():
		#	print "WARNING: Given Weierstrass equation is not integral, and bothSigns=False. As there may exist S-integral points P on E such that -P is not S-integral, we set bothSigns=True!";
		#	bothSigns = True;
		
		#For P=(x,y), -P=(x,-a_1*x-a_3-y).
		#Thus if a1 and a3 are S-integral, then for any S-integral P, -P is also S-integral.
		if not (E.a1().is_S_integral(S) and E.a3().is_S_integral):
			print "WARNING: In the given Weierstrass equation, at least one of a1 and a3 is not S-integral. Thus we change the given parameter bothSigns=False into bothSigns=True, as a priori the S-integrality of points on E may depend on the sign!";
			bothSigns = True;

	#We'll use some standard precision for usual computations, unless
	#it turns out to be non-sufficient, in which case we increase it and do computations again.
	regularPrecision = RR.prec();
	#regularPrecision = 10; #debug
	RIF = RealIntervalField(regularPrecision);

	Eoriginal = E;

	Mmax0original = Mmax0;

	#Make coefficients of E integral:
	#commonDenominator = lcm([ai.denominator() for ai in E.a_invariants()]);
	#u = 1/commonDenominator;
	#E = E.change_weierstrass_model([u,0,0,0]);
	E = E.global_integral_model();
	if verbose:
		#print "common denominator of a-invariants:",commonDenominator;
		print "Integral model of E:",E;
		sys.stdout.flush();
	
	#Make E minimal at all primes in S:
	E = ellipticCurveSMinimalModel(E,S); #In the paper, the S-minimal model is called W.
	isoToOriginalCurve = E.isomorphism_to(Eoriginal); #In the paper, this is called $\varphi$ (assuming that the given Weierstrass equation is integral).
	isoFromOriginalCurve = Eoriginal.isomorphism_to(E);
	if verbose:
		print "S-minimal model of E:", E;
		sys.stdout.flush();
	#return; #debug
		
	####################################################################
	# Compute Mordell-Weil basis:
	####################################################################

	if mwBasis == None:
		if verbose:
			print "Computing MW basis...";
			sys.stdout.flush();
		timer.startTimer("MW base computation");		
		mwBasis = E.gens(proof=True);
		mwOriginal = [isoToOriginalCurve(P) for P in mwBasis];
		timer.endTimer("MW base computation",verbose=verbose);
	else:
		#Need to possibly transform the given mwBasis to the new coordinates:
		mwOriginal = [Eoriginal(P) for P in mwBasis];
		mwBasis = [isoFromOriginalCurve(P) for P in mwOriginal];		
	r = len(mwBasis);
	torsionPoints = E.torsion_points(); #In the paper, the torsion exponent is called $e_t$.
	torsionOrder = len(torsionPoints);
	if verbose:
		print "MW basis: ",mwBasis;
		print "rank =",r;
		print "torsion order =",torsionOrder;
		sys.stdout.flush();


	if r == 0:
		#If rank is zero, consider all S-integral torsion points:
		xSolutions = set([P[0] for P in torsionPoints if not P.is_zero() and P[0].is_S_integral(S)]);
	else:
		####################################################################
		# rank >= 1: (the main case)
		####################################################################
		
		#The following step is only done for numerical purposes (and in practise not really needed as we deal with ellipsoids instead of the infinity-norm of the coefficient vectors):
		#Optimize the choice of the MW basis by LLL reducing it with respect to the Neron-Tate height:
		#(The following takes indeed the canonical Neron-Tate heights!
		#...with the smaller of the two conventions, because of the factor 2.)
		M = E.height_pairing_matrix(mwBasis)/2; #In the paper, this is called $(\hat{h}_{ij})$.
		if verbose:
			lamdaApprox = min(M.charpoly(algorithm="hessenberg").roots(multiplicities = False))
			print 'Initial approximated lambda before LLL reduction:',lamdaApprox;
			sys.stdout.flush()
		mwBasis, U = E.lll_reduce(mwBasis,M);
		M = U.transpose()*M*U;
		if verbose:
			lamdaApprox = min(M.charpoly(algorithm="hessenberg").roots(multiplicities = False))
			print 'Approximated lambda after LLL reduction:',lamdaApprox;
			#print "New height pairing matrix:"
			#print M;
			sys.stdout.flush();
		
		####################################################################
		# Computation of lower eigenvalue bound of the height_pairing_matrix, 
		# and of initial bound N0 for the coefficients w.r.t. the MW basis, and and Mmax0:
		####################################################################

		while True:
			R = RealField(regularPrecision);
			#Compute the height pairing matrix, but with the other "smaller" convention,
			#which is also used e.g. in Silverman's books:
			M = E.height_pairing_matrix(mwBasis,precision=regularPrecision)/R(2);
			Q = myRRtoRIF_matrix(M);
			#Qhk, Qup, Qf, Qdelta = integralLowerAndUpperApproximationOfQuadraticForm(Q,precAim=regularPrecision//5+2*r);
			#Qhk, Qup, Qf, Qdelta = integralLowerAndUpperApproximationOfQuadraticForm(Q,precAim=regularPrecision//10);
			Qhk, Qup, Qf, Qdelta = integralLowerAndUpperApproximationOfQuadraticForm(Q,precAim=regularPrecision//5);

			#Note: Qup and Qdelta are actually not needed.
			#TODO: Notation mit Paper vereinheitlichen! (Mit all den Q...'s)

			#Here, Qint is a quadratic Form, Qf a rational number, such that
			#the matrix Q - Qint/Qf^2 is positive semidefinite.

			if verbose:
				#print "Qhk: ",Qhk.base_extend(R);
				print "Qhk: ",Qhk;

			#Among the following lambdas, only lamdaMinQhk is needed:
			lamdaMinQ, lamdaMaxQ = lowerAndUpperBoundsForSmallestAndLargestEigenvalueOfSelfadjointRealMatrix(M);
			lamdaMinQhk, lamdaMaxQhk = lowerAndUpperBoundsForSmallestAndLargestEigenvalueOfSelfadjointRealMatrix(Qhk.base_extend(R));
			#lamdaMinQhk is a lower bound for $\lambda$ in the paper (and in practise almost equal).
			#lamdaMaxQhk is an upper bound for $\lambda'$ in the paper (and in practise almost equal).

			if lamdaMinQhk<=0: #will probably not happen too often, but rather be safe...
				#regularPrecision += 10;
				regularPrecision *= 2;
				if verbose:
					print "lamdaMinQhk was negative:",lamdaMinQhk;
					print "New regular precision:",regularPrecision;
				continue; #Computation will be redone with increased precision
				
			#We want that lamdaMinQhk is almost the smallest eigenvalue of Qf^2 * M, up to a 1% multiplicative error:
			if 0.01 * lamdaMinQhk <= Qdelta:
				regularPrecision += 10;
				if verbose:
					print "lamdaMinQhk/Qf^2 =",lamdaMinQhk / Qf^2;
					print "Qdelta/Qf^2 =",N(Qdelta/Qf^2);
					print "lamdaMinQhk is possibly not close enough to the smallest eigenvalue of Qf^2 * M.";
					print "New regular precision:",regularPrecision;
				continue; #Computation will be redone with increased precision
		
		
			if Mmax0 == None:
				if E.c4() != 0:
					#E is not a Mordell curve, take PZGH99 bound:
					Mmax0, N0 = general_initialBounds_Mmax0_and_N0(E,S,mwBasis,lamdaMinQhk,Qf,precision=regularPrecision,method="PZGH99",verbose=verbose);
				else:
					#E is a Mordell curve, take vkM15 bound:
					#We transform E into the form E_mordell: y^2=x^3 - 27c4*x - 54c6.
					a = -54*E.c6();
					#We need that S-integral solutions for the Weierstrass eq E
					#are sent to S-integral solutions for E_mordell. In general
					#this holds only if 2 and 3 are in S. Otherwise we need to:
					if 2 not in S:
						a *= 2^6;
					if 3 not in S:
						a *= 3^6;

					#Our new height bound:
					initialBounds_method = "vKM15";
					if debugParam.has_key("initialBoundMethod"):
						if debugParam["initialBoundMethod"]=="PZGH99":
							initialBounds_method = "PZGH99";
						elif debugParam["initialBoundMethod"]=="ST94":
							initialBounds_method = "ST94";					
					Mmax0, N0 = initialBounds_Mmax0_and_N0(a,S,lamdaMinQhk,lamdaMaxQhk,Qf,Qdelta,r,mwBasis,precision=regularPrecision,method=initialBounds_method,verbose=verbose);

					
					if Mmax0.relative_diameter()>2^(-20):
						#Computation will be redone with increased precision,
						#as we might get a considerably better N0.
						regularPrecision += 10;
						if verbose:
							print "Mmax0's relative diameter not enough:",Mmax0.relative_diameter();
							print "New regular precision:",regularPrecision;
						Mmax0=None;
						continue;
					if verbose:
						print "Mmax's relative diameter:",Mmax0.relative_diameter();
						print "a =",a;

					#Mmax0 is wrt Q
					#Mmax is wrt Qhk

			Mmax = Mmax0 * Qf^2;
			
			break; #Computation of lamda and Mmax0 finished with enough precision.

		if verbose:
			#if N0 != None:
			#	print "N0 =",N0;
			print "Mmax0 =",Mmax0;
			print "Mmax =",Mmax;
			print "Optimized MW basis: ",mwBasis;
			print 'torsion order:',torsionOrder;
			print 'optimized lamdaMinQ',lamdaMinQ
			print "comparison: lamdaMinQ(Q) =",lamdaMinQ,", lamdaMinQhk/Qf^2:",lamdaMinQhk/Qf^2;
			print 'optimized lamdaMaxQ',lamdaMaxQ
			print "comparison: lamdaMaxQ(Q) =",lamdaMaxQ,", lamdaMaxQhk/Qf^2:",lamdaMaxQhk/Qf^2;
			print "Qhk:"
			print Qhk, Qf;
			sys.stdout.flush();

		####################################################################
		####################################################################
		####################################################################
		# The main part of the algorithm:
		####################################################################
		####################################################################
		####################################################################

		ECache = E_Cache(E,S,mwBasis,Qhk,Qf,lamdaMinQhk,timer,regularPrecision=regularPrecision,verbose=verbose,debugParam=debugParam);
		Sstar = ECache.Sstar;
	
		####################################################################
		####################################################################
		# First reductions of Mmax:
		####################################################################
		####################################################################

		timer.startTimer("First reductions");
		
		#Mmax = RIF(10^90000) #debug

		Mmaxes = {};
		for p in Sstar:
			Mmaxes[p] = Mmax;

		#return;

		stepSize = ceil(Qf^2);
		stepSizeMult = 0.99;

		for p in Sstar:
			if verbose:
				if debug:
					print "=========================================================";
				if verbose:
					print "Starting initial reduction at p =",p,;
				sys.stdout.flush();
				
			if r==1 and p!=Infinity:
				#For rank r=1 we can speed up the first reduction considerably, as we only need to know the order of the p-adic log of P0, and not even Fincke-Pohst:
				sigma = len(Sstar);
				#print "debug0";
				hk_P0 = RIF(normSquared(vector([1]),Q=Qhk)/Qf^2);
				#print "debug"
				#This first reduction cannot yield a better bound than:
				bestPossibleMmax_p = max(RIF(0), ECache.mu + sigma*log(RIF(p))*(ECache.ordAlphaP0[p]-ECache.m[p].ord(p)));
				#print "debug: bestPossible Mmax_p =",bestPossibleMmax_p;
				#print "debug:",ECache.ordAlphaP0[p],ECache.m[p];
				while True:
					oldMmax_p = Mmaxes[p];
					newMmax_p = Qf^2 * (sigma/2*(log(RIF(oldMmax_p)/Qf^2)-log(hk_P0)) + sigma*log(RIF(p)) * (ECache.ordAlphaP0[p]-ECache.m[p].ord(p)) + ECache.mu);
					#print "newMmax_p =",newMmax_p;
					#print "debug: newMmax_p =",newMmax_p;
					newMmax_p = min(oldMmax_p,max(RIF(0),newMmax_p)).upper();
					Mmaxes[p] = newMmax_p;
					if (not newMmax_p < 0.98 * oldMmax_p) or newMmax_p<=0:
						break;
				if verbose or debug:
					print "obtained a new bound Mmax =",Mmaxes[p],"at p =",p;			
					sys.stdout.flush();
				
			else: #r>=2 or p==Infinity:	
				
				Mmin = ceil(Qf^2); #TODO: We could save some milliseconds if we start here from the extra search height bound.
				while True:
					if verbose or debug:
						print "Try with Mmin =",Mmin,"...";
					diligentAndSlow = True;
					sigma = len(Sstar);
					#sigma = 10001; #debug!!!!!!!!!!!!!!!!!!!!!
					[bufferWasBigEnough,newCandidates] = refinedSieveAtT([p],Mmin,Mmaxes[p],sigma,ECache,maxCandidates=0,diligentAndSlow=diligentAndSlow,verbose=False);
					if bufferWasBigEnough:
						Mmaxes[p] = Mmin;
						if verbose or debug:
							print "obtained a new bound Mmax =",Mmaxes[p],"at p =",p;
							sys.stdout.flush();
						break;
					else:
						Mmin *= 2;
						if Mmin >= Mmaxes[p]: #Will usually not happen when Mmax is large
							if verbose:
								print "Couldn't easily reduce Mmax at p =",p;
							break;
						continue;

				#factors = [0.5,0.75,0.9,0.95,0.98,0.995,1];
				factors = [0.5,0.75,0.9,0.95,0.98];
				iFactor = 0;
				while True:
					Mmin = floor(Mmaxes[p]*factors[iFactor]);
					if Mmin > Mmaxes[p]-stepSize:
						Mmin = Mmaxes[p]-stepSize;
					if Mmin < 0:
						Mmin = 0;
					if debug:
						print "Try to reduce Mmax quickly at p =",p,"to Mmin =",Mmin;
						sys.stdout.flush();
					diligentAndSlow = True;
					sigma = len(Sstar);
					#sigma = 10001; #debug!!!!!!!!!!!!!!
					[bufferWasBigEnough,newCandidates] = refinedSieveAtT([p],Mmin,Mmaxes[p],sigma,ECache,maxCandidates=0,diligentAndSlow=diligentAndSlow,verbose=False);
					if bufferWasBigEnough:
						Mmaxes[p] = Mmin;
						if verbose or debug:
							#print "obtained a new bound MmaxQ =",RR(Mmaxes[p]/Qf^2),"at p =",p;
							sys.stdout.flush();
						if Mmin==0:
							break;
						continue;
					iFactor += 1;
					if iFactor<len(factors):
						continue;
					break;

		if verbose:
			#if debug:
			print "Mmaxes:",Mmaxes;
			print "Qf^2 roughly",N(Qf^2);


		Mmax = max(Mmaxes.values());

		#Sort Sstar according to Mmaxes:
		#This is done such that in the partition of Sstar, all parts
		#become roughly equally difficult. This is of course just a heuristic.
		Sstar.sort(key = lambda x: Mmaxes[x]);
		#print Sstar;

		t1 = timer.endTimer("First reductions",verbose=False);
		
		if verbose:
			print "First reduction steps finished, time taken:",t1;
			print "Obtained overall new Mmax =",Mmax;
			print "Remaining volume:",volumeOfEllipsoid(Qhk,Mmax);
			print "=> Remaining height bound: MmaxQ =",convert_MmaxQhk_to_MmaxQ(Mmax,Qf,Qdelta);
			print "Would yield bound for infinity-norm of coefficient vector:", N(floor(sqrt(convert_MmaxQhk_to_MmaxQ(Mmax,Qf,Qdelta)  /  (lamdaMinQhk/Qf^2))));
			print "=========================================================";

		if debugParam.has_key("initialBoundMethod"): #with value in ["vKM15","PZGH99","ST94"]:
			print timer.toString();
			return;

		MmaxQ_AfterFirstReductions = convert_MmaxQhk_to_MmaxQ(Mmax,Qf,Qdelta);
		
		####################################################################
		####################################################################
		# Check from which time on, heightLogSieve is stronger than directly checking S-integrality of x(P):
		####################################################################
		####################################################################

		#Initialize WeakHeightLogSieve for Mmax:
		if verbose:
			print "Initialize heightLogSieve...";

		#Mmax = 100000000*Qf^2; #for debug purposes only
		timer.startTimer("Initialization of heightLogSieve");
		heightLogarithmSieve(tuple(range(r)),Mmax,ECache,testMethod="NoTest" if ECache.heightLogSieve_Method=="NoTest" else "WeakHeightLogSieve",verbose=False);
		timer.endTimer("Initialization of heightLogSieve",verbose=verbose);

		if verbose:
			print "We will use the following heightLogSieve method:",ECache.heightLogSieve_Method;
			print ECache.heightLogSieve_Method in ["WeakHeightLogSieve","StrongHeightLogSieve"];

		P = mwBasis[0];
		if ECache.heightLogSieve_Method == "NoTest":
			minHeightForHeightLogSieveTest = Mmax + 1;
		elif ECache.heightLogSieve_Method in ["WeakHeightLogSieve","StrongHeightLogSieve"]:
			minHeightForHeightLogSieveTest = -Infinity;
		else: #"Automatic_Weak_or_NoTest" or "Automatic_Strong_or_NoTest"
			if verbose:
				print "Check from which time on the heightLogSieve becomes faster than the direct test for S-integrality...";
			
			meanNormSqOfMWBasis = sum([Qhk[(k,k)] for k in range(r)])/r;
			k = 1;
			loops = r^2;
			if ECache.heightLogSieve_Method == "Automatic_Weak_or_NoTest":
				testMethod = "WeakHeightLogSieve";
			else:
				testMethod = "StrongHeightLogSieve";

			minHeightForHeightLogSieveTest = 0;

			while minHeightForHeightLogSieveTest < Mmax:

				timeForHeightLogSieveTest0 = walltime();
				#Old choice of random n's, which is not very well distributed, as it uses essentially a 1-norm instead of a 2-norm:
				#ns = [tuple(randomListOfGivenLengthAndSum(r,k)) for i in range(loops)];
				#So instead we use random n's which have all roughly the same height:
				ns = [tuple(randomLatticePoint(r,normSquaredApprox=k^2*meanNormSqOfMWBasis,Q=Qhk)) for i in range(loops)];
				candidates = set([]);
				for i in range(loops):
					n = ns[i];
					candidates.update(heightLogarithmSieve(n,Mmax,ECache,testMethod=testMethod,verbose=False));
					if len(candidates) > 0:
						break;
				timeForHeightLogSieveTest = walltime(timeForHeightLogSieveTest0);

				#If no candidate remained, it makes sure that the heightLogSieve went through all primes:
				if len(candidates) == 0:

					timeForDirectTest0 = walltime();
					for i in range(loops):
						n = ns[i];
						#OLD and bad: P = sum([k*mwBasis[j] for j in range(r)]);
						P = sum([n[j]*mwBasis[j] for j in range(r)]);
						for T in torsionPoints:
							dummy = (P+T)[0].is_S_integral(S);
					timeForDirectTest = torsionOrder * walltime(timeForDirectTest0);

					if verbose:
						print "For k =",k,", the times are",timeForHeightLogSieveTest,"(heightLogarithmSieve) and",timeForDirectTest,"(direct test) "; #///",timeForDirectTest/P.height()^2;
					if timeForHeightLogSieveTest < timeForDirectTest:
						if verbose:
							print testMethod,"is faster than direct S-integrality check for k =",k;
						break;

				minHeightForHeightLogSieveTest = sum([normSquared(n,Q=Qhk) for n in ns])/loops;
				k = RR(k*2^(1/RR(r)/4)).ceil();
				
			if verbose:
				print "Quick test will be used from the following height on:", N(minHeightForHeightLogSieveTest/Qf^2);
				
			ECache.minHeightForHeightLogSieveTest = minHeightForHeightLogSieveTest;
		
		####################################################################
		####################################################################
		# Apply refined sieves and refined enumerations:
		####################################################################
		####################################################################

		if verbose:
			print "Now turn to refined sieve and refined enumeration:";

		timer.startTimer("Refined sieves and refined enumerations");

		xSolutions = set([]);
		
		#Depreciated: Not needed anymore:
		#Extra search of solutions that might have been missed during sieves at p=2:
		#if 2 in S:
		#	for x in [-1/4,1/4,-1/2,1/2,-3/4,3/4]:
		#		if E.is_x_coord(x):
		#			xSolutions.add(x);

		def update_xSolutions(candidatesWithTorsion,xSolutions,ECache):
			#Check whether c in candidatesWithTorsion have S-integral x coordinates.
			#If so, add these x coordinates to xSolutions.
			for c in candidatesWithTorsion:
				P = ECache.E(0);
				r = ECache.r;
				for i in range(r):
					P += c[i] * ECache.mwBasis[i];
				P += ECache.torsionPoints[c[r]];
				#print "P =",P,", c =",c;
				if P!=ECache.E(0):
					#xCoordinateCandidates.add(P[0]);
					x = P[0];
					if x.is_S_integral(S):
						xSolutions.add(x);
					if debug:
						c0 = vector([c[i] for i in range(r)]);
						print "Solution:",P,"for c =",c,"with h^(P) = ||c||_Q^2 =",P.height()/2 #,", or approx. =",normSquared(c0,Q);
						print "and ||c||_Qhk / Qf^2 =",N(normSquared(c0,ECache.Qhk)/ECache.Qf^2);
			
		#First of all, add all torsion candidates:
		candidatesWithTorsion = heightLogarithmSieve(tuple(zero_vector(r)),Mmax,ECache,verbose=False);
		if verbose:
			print "Torsion candidates:",candidatesWithTorsion;
		update_xSolutions(candidatesWithTorsion,xSolutions,ECache);


		enumerationMethods = [];
		enumerationMethods.append({"name":"refinedEnumeration", "averageCost":-Infinity, "preferedMethods": copy([])});
		maxBufferSize = min(10^r,10^7);
		#maxBufferSize = 10; #debug
		if not debugParam.has_key("tMax") or debugParam["tMax"]>=1:
			enumerationMethods.append({"name":"refinedSieve", "averageCost":0, "n":len(Sstar), "t":1, "mc":maxBufferSize, "preferedMethods": copy([])});
		if len(S) >= 3 and r >= 2:
			if not debugParam.has_key("tMax") or debugParam["tMax"]>=2:
				enumerationMethods.append({"name":"refinedSieve", "averageCost":0, "n":10, "t":2, "mc":maxBufferSize, "preferedMethods": copy([])});
		if len(S) >= 4 and r >= 3:
			if not debugParam.has_key("tMax") or debugParam["tMax"]>=3:
				enumerationMethods.append({"name":"refinedSieve", "averageCost":0, "n":10, "t":3, "mc":maxBufferSize, "preferedMethods": copy([])});
		if len(S) >= 5 and r >= 4:
			if not debugParam.has_key("tMax") or debugParam["tMax"]>=4:
				enumerationMethods.append({"name":"refinedSieve", "averageCost":0, "n":10, "t":4, "mc":maxBufferSize, "preferedMethods": copy([])});
		#Here:
		# - averageCost: the estimated time the method took per lattice point during the last step it was used.
		# - n: the maximal size of the parts in the partition of S in the refined sieve.
		# - t: see refined sieve
		# - mc: maximal number of candidates (i.e. buffer size) in the refined sieve. Method fails if more buffer is needed.
		# - preferedMethods: list of methods that are probably faster.

		
		#Compute how far the extra search has to go:
		tMax = max([1]+[method["t"] for method in enumerationMethods if method["name"]=="refinedSieve"]);
		Mmax_extraSearch = heightBound_for_extraSearch(ECache,tMax);
		Mmax_extraSearch = (Qf^2 * Mmax_extraSearch).upper();
		if verbose:
			print "Need to do extra search up to Mmax_extraSearch/Qf^2 =",Mmax_extraSearch/Qf^2;

		remainingRangeMin = 0;
		remainingRangeMax = max(Mmax,Mmax_extraSearch);

		refinedEnumerationWasDoneUpToMmax = 0; #only for output, will be updated later.

		def FinckePohst_callback(vecSolution,args):
			#print vecSolution;
			#print args;
			#sleep(1)
			E = args[0];
			Sstar = args[1];
			Qhk = args[2];
			Qf = args[3];
			Mmin = args[4];
			Mmax = args[5];
			mwBasis = args[6];
			ECache = args[7];
			xSolutions = args[8];
			c = tuple(vecSolution);
			cminus = tuple([vecSolution[i] for i in range(len(c))]);
			if False: #debug:
				c1 = (0, 0, -1, 1, 0, 1, 0, 0); #An example giving rise to a bug
				#c1 = (0, 0, 0, 1, 0, 0, 0, 0); #should be found easily, just as a test.
				if c1==c or c1==cminus:
					print "c1 was found!"
			normSqQhk = normSquared(c,Q=Qhk);			
			if not normSqQhk > Mmin:
				return;
			refinedEnumerationCandidatesWithTorsion = heightLogarithmSieve(c,Mmax,ECache,testMethod=ECache.heightLogSieve_Method,normSqQhk=normSqQhk,verbose=False);
			update_xSolutions(refinedEnumerationCandidatesWithTorsion,xSolutions,ECache);
		
		while True:
			#Select the method with previous least average cost amoong all methods that do not prefer another method:
			method = min([m for m in enumerationMethods if m["preferedMethods"]==[]],key=lambda method: method["averageCost"]);
			if verbose:
				print "- Use method",method,;
				sys.stdout.flush();
			t0 = walltime();
			if method["name"] == "refinedSieve":
				Mmax = remainingRangeMax;
				Mmin = max(remainingRangeMin,Mmax_extraSearch,min(Mmax - stepSize,(Mmax * stepSizeMult).floor()));

				maxPartSize = method["n"];
				maxTupleSize = method["t"];
				maxCandidates = method["mc"];
				diligentAndSlow = True;
				#diligentAndSlow = False;
				[bufferWasBigEnough,newCandidates] = refinedSieve(Mmin,Mmax,maxPartSize,maxTupleSize,regularPrecision,ECache,maxCandidates=maxCandidates,diligentAndSlow=diligentAndSlow,verbose=False);
				if not bufferWasBigEnough:
					#Don't use this method anymore:
					if verbose:
						print "-> required too much buffer and will not be used anymore. Time taken:",walltime(t0);
					#If this method was prefered over another one, make the other one free again:
					for otherMethod in enumerationMethods:
						if otherMethod["preferedMethods"].count(method) >= 1:
							otherMethod["preferedMethods"].remove(method);
							otherMethod["averageCost"] = max(otherMethod["averageCost"],method["averageCost"]);
					method["averageCost"] = Infinity; #the current method will not be used again
					continue;
				numNewCandidatesBeforeQuickTest = len(newCandidates);
				for c in newCandidates:
					candidatesWithTorsion = heightLogarithmSieve(c,Mmax,ECache,testMethod=ECache.heightLogSieve_Method,verbose=False);
					update_xSolutions(candidatesWithTorsion,xSolutions,ECache);
				remainingRangeMax = Mmin;

				if verbose:
					print "New candidates:",len(newCandidates),;
					print ". Num candidates with torsion passing heightLogSieve at this step:",len(candidatesWithTorsion),;
					#print "New Mmax:",Mmax,", remaining volume:",volumeOfEllipsoid(Qhk,Mmax),", remaining height bound MmaxQ =",convert_MmaxQhk_to_MmaxQ(Mmax,Qf,Qdelta);
					

			elif method["name"] == "refinedEnumeration":
				####################################################################
				#Enumerate small candidates without a sieve:

				#The following calls Fincke-Pohst and puts candidates into the memory:
				#refinedEnumerationCandidates = [];
				#[bufferWasBigEnough,numRefinedEnumerationCandidates] = my_finckePohst_viaGramMatrix(Qhk,Mmax,center=0,solutionList=refinedEnumerationCandidates,maxNumSolutions=None,finalTransformation=None,callback=None,callbackArgs=None,lllReduce=True,breakSymmetry=False);

				#The following calls Fincke-Pohst and heightLogSieve candidates immediately.
				#Only the candidates that survive the heightLogSieve are stored in the memory:

				#Do roughly twice as many candidates as before:
				firstRefinedEnumeration = remainingRangeMin<=0;
				Mmin = remainingRangeMin;
				
				if firstRefinedEnumeration:
					Mmax = Mmin+stepSize;
				else:
					Mmax = min(remainingRangeMax,max(stepSize,remainingRangeMin+stepSize,ceil(remainingRangeMin*2^(1/r))));
					#Go at least as far as the extra search:
					Mmax = max(Mmax,Mmax_extraSearch); 
					#And don't leave a tiny rest:
					if Mmax*2^(1/(2*r)) > remainingRangeMax:
						Mmax = remainingRangeMax; 
					
					#if verbose and Mmax == Mmax_extraSearch:
					#	print "This time the refined enumeration IS the extra search!";
				#print "Mmax =",Mmax;
				#print "Mmax_extraSearch =",Mmax_extraSearch;

				FPargs = (E,Sstar,Qhk,Qf,Mmin,Mmax,mwBasis,ECache,xSolutions);
				[bufferWasBigEnough,numRefinedEnumerationCandidates] = my_finckePohst_viaGramMatrix(Qhk,Mmax,center=0,solutionList=None,maxNumSolutions=None,finalTransformation=None,callback=FinckePohst_callback,callbackArgs=FPargs,lllReduce=True,breakSymmetry=True);
				remainingRangeMin = Mmax;

				refinedEnumerationWasDoneUpToMmax = Mmax;
	
	
			timeForThisStep = walltime(t0);
			volumeForThisStep = volumeOfEllipsoid(Qhk,Mmax) - volumeOfEllipsoid(Qhk,max(0,Mmin));
			if volumeForThisStep > 0:
				method["averageCost"] = timeForThisStep / volumeForThisStep;
			else:
				method["averageCost"] = Infinity;
			if verbose:
				print "AvgCost for this step:",method["averageCost"],". New remaining height range: [",RR(remainingRangeMin/Qf^2),",",RR(remainingRangeMax/Qf^2),"].";

			if method["name"] == "refinedSieve":
				#If refined sieve didn't sieve much, don't use it anymore:
				if 0.9*volumeForThisStep <= len(newCandidates):
					if verbose:
						print "Heuristically, from now on the sieve doesn't sieve away more than 10 percent of the candidate anymore, so we stop it.";
					method["averageCost"] = Infinity; #these sieve parameters will not be used again
				#If this refined sieve for t was faster than some previous refined sieve with smaller t, don't use the previous one anymore:
				for otherMethod in enumerationMethods:
					if otherMethod["name"] == "refinedSieve":
						if otherMethod["t"] < method["t"]:
							if otherMethod["n"] == method["n"] or otherMethod["t"] == 1:
								if otherMethod["averageCost"] > method["averageCost"]:
									if otherMethod["averageCost"] < Infinity:
										if otherMethod["preferedMethods"].count(method) == 0:
											#otherMethod["averageCost"] = Infinity;
											otherMethod["preferedMethods"].append(method);
											if verbose:
												print "######### This refined sieve went faster than the same method with t =",otherMethod["t"],"and thus from now on we prefer the former method.";
												print "";
			elif method["name"] == "refinedEnumeration":
				if firstRefinedEnumeration:
					#The first time it take unusually long, in particular because
					#the data behind the heightLogSieve has to be set up. 
					#This biases the heuristic in a bad way, so:
					method["averageCost"] = -Infinity;
					#We put it to -Infinity such that the refined enumeration gets run again immediately,
					#this second time doing the extra search up to
					continue;

			if remainingRangeMin >= remainingRangeMax:
				if verbose:
					print "Search for candidates surviving quick-test is finished, num candidates with torsion:",len(candidatesWithTorsion);
					print "log(NS):",ECache.logNS;
				break;

		timer.endTimer("Refined sieves and refined enumerations",verbose=verbose);
		
	if debug:
		print "xCoordinates to check:",xCoordinateCandidates;

	solutions = set([]);
	for x in xSolutions:
		bothLifts = E.lift_x(x,all=True)
		bothLifts.sort();
		if bothSigns:
			solutions.update(set(bothLifts));
		else:
			#Take the last lift of the two. Note that sometimes there is only one such lift.
			solutions.add(bothLifts[-1]);

	solutions = [isoToOriginalCurve(P) for P in solutions];
	solutions = [P for P in solutions if P[0].is_S_integral(S) and P[1].is_S_integral(S)]; #This is needed only when the given Weierstrass equation is not integral.

	#solutions.sort(key=lambda (x,y): x.global_height());
	solutions.sort(key=lambda P: P.height());
	
	if verbose:
		print "Solutions:\n",solutions;
		print "E:",E;
		print "rank(E) =",r;
		if len(S) <= 10:
			print "S =",S;
		else:
			print "len(S) =",len(S);
		print "Number of solutions:",len(solutions);

		if r>=1:
			if debugParam.has_key("tMax"):
				print "Bounded t by tMax =",debugParam["tMax"];
			print "Used height log sieve method:",ECache.heightLogSieve_Method;
			
			if ECache.heightLogSieve_Method == "Automatic_Weak_or_NoTest":
				print "Weak-HeightLogSieve was used from the following height on:", N(minHeightForHeightLogSieveTest/Qf^2);
			if ECache.heightLogSieve_Method == "Automatic_Strong_or_NoTest":
				print "Strong-HeightLogSieve was used from the following height on:", N(minHeightForHeightLogSieveTest/Qf^2);
			print "Height bound MmaxQ after first reductions:",MmaxQ_AfterFirstReductions;
			print "Refined sieve ended and refined enumeration started at height:",N(refinedEnumerationWasDoneUpToMmax/Qf^2);
			print "Height bound for extra search:",Mmax_extraSearch/Qf^2;

	totalTime = timer.totalTime();
	if verbose:
		print "Time that was used:";
		print timer.toString();

	####################################################################
	# Save to file
	####################################################################

	if saveToFile:
		Eoriginal_is_Mordell = Eoriginal.a1()==0 and Eoriginal.a2()==0 and Eoriginal.a3()==0 and Eoriginal.a4()==0;
		solutionsAsTuplesXY = [(P[0],P[1]) for P in solutions];
		#First save the sage object 'solutionsAsTuplesXY':
		if Eoriginal_is_Mordell:
			a = Eoriginal.a6();
			signA = "+" if a>=0 else "-";
			filename = "mordell_a_"+str(a);
		else:
			filename = "E_"+myListToStr(E.a_invariants(),"_");
		if S==primes_first_n(len(S)):
			filename += "_n_"+str(len(S));
		else:
			filename += "_S_"+myListToStr(S,'_');
		if Mmax0original != None:
			filename += "_upToMmax0";
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutionsAsTuplesXY,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		if Eoriginal_is_Mordell:
			out.write("# List of S-integral points (x,y) on the Mordell curve\n");
			out.write("# y^2 = x^3 "+signA+" "+str(abs(a))+", of rank "+str(r)+", where\n");
		else:
			curve = str(E).split("by ")[1].split(" over")[0];
			out.write("# List of S-integral points (x,y) on the elliptic curve\n");
			out.write("# "+curve+", where\n");
		if Mmax0original != None:
			out.write("# we consider only points of height <= Mmax0 = "+str(RR(Mmax0original))+",\n");
		if S==primes_first_n(len(S)):
			out.write("# S is the set of the first "+str(len(S))+" primes.\n");
		else:
			out.write("# S = {"+myListToStr(S,',')+"}.\n");
		out.write("# It contains "+str(len(solutions))+" points in total.\n");
		if bothSigns==False:
			out.write("# For each point P, only one of +P, -P is listed.\n");
		out.write('# Format: "(P(x),P(y))".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		#out.write("###\n");
		out.write("#\n");
		for (x,y) in solutionsAsTuplesXY:
			#out.write(str(r)+": "+str(a)+" + "+str(b)+" = "+str(c)+" ("+str(q)+")\n");
			out.write("(%s,%s)\n" % (str(x),str(y)));
		out.close();
		
		#Furthermore save log:
		#out = file("log_"+filename+'.txt','w');
		#for msg in LogMessages:
		#	out.write(msg+"\n");
		#out.close();

	####################################################################
	# Finished computing S-integral points!
	####################################################################

	if debugParam.has_key("compareWithSagesImplementation") and debugParam["compareWithSagesImplementation"]:
		solutionsViaSage_E = E.S_integral_points(S,mw_base=mwBasis,both_signs=bothSigns,verbose=False,proof=True);
		solutionsViaSage = [isoToOriginalCurve(P) for P in solutionsViaSage_E if P[0].is_S_integral(S)];
		if len(solutionsViaSage) != len(solutions):
			print "ERROR:";
			print "Found",len(solutions),"solutions, whereas sage yields",len(solutionsViaSage),"solutions!!!";
			return;

	return solutions;

@parallel(p_iter=parallelIterator,ncpus=numCPUs)
def solveThueEquation(a,b,c,d,m=1,S=[],modOutSymmetry=False,checkRelevantAbcTriples=False,verbose=True,mwBasesDict=None):
	'''
	INPUT:
	- S a finite set of rational primes.
	- m a non-zero rational number.
	- a,b,c,d rational coefficients of the binary quartic
		homogeneous polynomial F(x,y) = ax^3 + bx^2y + cxy^2 + d y^3,
		such that the discriminant D(F) is non-zero.

	OUTPUT:
	The set of all S-integral solutions of the Thue equation F(x,y) = m
	(possibly up to symmetry (x,y)<->(y,x), if modOutSymmetry=True and a=d and b=c).
		
	WARNING:
	During tests, the call I.variety() sometimes never returns (this is
	based on Singular). This is like a Poisson process, which seems
	independent of I. If this happens, we rerun I.variety() a few times.
	But it may still fail in some cases.
	In this case, try to run the program again. 
	'''

	#debug = True;
	debug = False;

	a,b,c,d,m = QQ(a),QQ(b),QQ(c),QQ(d),QQ(m);

	#Make coefficients a,b,c,d of F S-integral:
	denom = lcm([a.denominator(),b.denominator(),c.denominator(),d.denominator(),m.denominator()]);
	for p in S:
		denom /= p^denom.valuation(p);
	a,b,c,d,m = (a*denom,b*denom,c*denom,d*denom,m*denom);
	
	R.<x,y> = PolynomialRing(QQ,["x","y"]);

	F = a*x^3 + b*x^2*y + c*x*y^2 + d*y^3;

	F_is_symmetric = (a==d) and (b==c);
	modOutSymmetry = modOutSymmetry and F_is_symmetric; #can mod out by (x,y) ~ (y,x) only if F(x,y)=F(y,x).

	#Discriminant of F:
	D = 27*a^2*d^2 + 4*a*c^3 - 18*a*b*c*d + 4*b^3*d - b^2*c^2;

	#Covariant polynomials of degrees 2 and 3:
	H = (3*a*c-b^2)*x^2 + (9*a*d-b*c)*x*y + (3*b*d-c^2)*y^2;
	J = (27*a^2*d-9*a*b*c+2*b^3)*x^3 - 3*(6*a*c^2-b^2*c-9*a*b*d)*x^2*y + 3*(6*b^2*d-b*c^2-9*a*c*d)*x*y^2 - (27*a*d^2-9*b*c*d+2*c^3)*y^3;
		
	#The associated Mordell curve:
	k = 432*m^2*D;
	E = mordellCurve(k);

	if verbose or debug:
		print "F(x,y)=m:",F,"=",m;
		print "|S| =",len(S);
		print "D =",str(D)+",",;
		print "k =",k,"=",factor(k);
	#if debug:
	#	print "for x=-73/35, y=81/35, we have:"
	#	print "  F(x,y) =",F(x=-73/35,y=81/35);
	#	print "  -4*H(x,y) =",-4*H(x=-73/35,y=81/35);
	#	print "  4*J(x,y) =",4*J(x=-73/35,y=81/35);
	#	return;

	'''
	mwBase = load_mwBasis_from_cache(k);
	if mwBase == None:
		global my_mwBasis_for_mordellCurves;
		if my_mwBasis_for_mordellCurves.has_key(k):
			#if verbose:
			#	print "Can use MW basis from database.";
			mwBase = my_mwBasis_for_mordellCurves[k];
		else:
			#Try to use magma:
			try:
				mwBase = mwBaseViaMagma(E);
			except TypeError:
				if verbose:
					print "Problem with using magma, use sage instead for MW base computation."
				mwBase = E.gens();
		save_mwBasis_to_cache(k,mwBase);
	'''

	mwBase = mwBasisViaCacheMagmaOrSage(k,mwBasesDict=mwBasesDict,loadFromCacheIfPossible=True,saveMWToCache=True,inMagmaUseHeegnerPointIfRank1=True,inSageUseTwoDescentInCaseOfFailure=True);

	r = len(mwBase);
	
	if verbose:
		#print "E.rank() =",r;
		print "MW basis:",mwBase;

	#S-integral solution of Thue equation F(x,y) = m yields S-integral point (u,v) on E:
	#u = -4*H(x,y) #u in the paper
	#v = 4*J(x,y) #v in the paper
	#So for any (u,v) on E we compute all (x,y) that satisfy these two equations:

	solutions = set([]);

	S_integral_points_on_E = computeSIntegralPoints(E,S=S,mwBasis=mwBase,verbose=debug,bothSigns=True);
	if debug:
		print "S_integral_points_on_E:",S_integral_points_on_E;
	for (u,v,w) in S_integral_points_on_E:
		if debug:
			print "("+str(u)+","+str(v)+")",;
			sys.stdout.flush();
		u = u/w;
		v = v/w;
		w = 1;
		if debug:
			print "u,v:",u,v;
		I = Ideal([4*H+u,4*J-v]);
		#We could also take instead the possibly larger ideal:
		#I = Ideal([4*J+u,F-m]);

		#for i in range(100): #Just force errors with more likelyhood! :)
		#The following computation calling I.variety() is unstable, sometimes it works, sometimes not.
		#That's why we give it some time, and if it doesn't finish, we rerun it.
		#We abort if it doesn't work within a few tries.
		numTries = 1;
		Z = None;
		while Z==None and numTries<=10:
			alarm(numTries^2); #give it 'numTries'^2 seconds of time...
			try:
				Z = I.variety();
			except (AlarmInterrupt, KeyboardInterrupt, sage.interfaces.singular.SingularError):
				print "Problem with 'I.variety()' at u,v:",u,v,". Restart computation...";
				Z = None;
			cancel_alarm(); #stop alarm
			numTries += 1;
		if Z==None:
			print "Error, couldn't determine I.variety()!";
			return None;
		if debug:
			print "Z:",Z;
				
		for s in Z:
			if s[x].is_S_integral(S) and s[y].is_S_integral(S):
				if F(s[x],s[y])==m:
					if modOutSymmetry and s[x]<s[y]:
						continue; #don't output this solutions, as (s[y],s[x]) will also be found.
					solutions.add((s[x],s[y]));
	if verbose:
		print "Thue equation has",len(solutions),;
		if modOutSymmetry:
			print "ordered solutions:",;
		else:
			print "solutions:",;
		print solutions;

		if checkRelevantAbcTriples:
			#Check relevance for ABC:
			relevant_abc_triples = [];
			for (x,y) in solutions:
				denom = lcm(x.denominator(),y.denominator());
				a = (x*denom)^3;
				b = (y*denom)^3;
				c = m*denom^3;
				g = gcd([a,b,c]);
				a /= g;
				b /= g;
				c /= g;
				if quality(a,b,c)>1:
					relevant_abc_triples.append((a,b,c));
			if relevant_abc_triples != []:
				print "Relevant abc triples:";
				for a,b,c in relevant_abc_triples:
					print str(factor(a))+" + "+str(factor(b))+" = "+str(factor(c))+" has quality "+str(quality(a,b,c));
	
	return solutions;

def solveThueMahlerEquation(a,b,c,d,m=1,S=[],modOutSymmetry=False,verbose=True,saveToFile=True,saveToPath=pathData,makeLog=True,mwBasesDict=None):
	'''
	INPUT:
	- S a finite set of rational primes.
	- m a non-zero rational number.
	- a,b,c,d rational coefficients of the binary quartic
		homogeneous polynomial F(x,y) = ax^3 + bx^2y + cxy^2 + d y^3,
		such that the discriminant of F is non-zero.

	OUTPUT:
	The set of all primitive integral solutions (x,y,z) of the Thue-Mahler equation
		F(x,y) = m * z, with z = prod_{p\in S} p^{\alpha_p}.
	Note: The solutions of F(x,y) = m*(-z) (and z as before) are not returned,
	because they correspond bijectively to the solutions of F(x,y)=mz via (x,y) <-> (-x,-y).

	NOTE:
	This algorithm relies on the computation of Mordell-Weil bases for
	many (3^|S|) elliptic curves. Thus it is NOT very practical, in
	particular for large S.
	'''

	'''
	if makeLog:
		logName = "thueMahler_a"+str(a)+"_b"+str(b)+"_c"+str(c)+"_d"+str(d)+"_m"+str(m)+"_";
		if S == primes_first_n(len(S)):
			logName += "n"+str(len(S));
		else:
			logName += "S_"+myListToStr(S,"_");
		logName += ".txt";
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			logName = saveToPath + logName;
			if not os.path.exists(os.path.dirname(logName)):
				os.makedirs(os.path.dirname(logName))
		#TODO!
	'''

	t00 = walltime();
	
	s = len(S);
	solutions = set([]);
	F_is_symmetric = (a==d) and (b==c);
	modOutSymmetry = modOutSymmetry and F_is_symmetric; #can mod out by (x,y) ~ (y,x) only if F(x,y)=F(y,x).

	if verbose:
		print "Solve Thue-Mahler equation %dxxx + %dxxy + %dxyy + %dyyy = %d over S-integers." % (a,b,c,d,m);
		print "|S| =",s;

	if mwBasesDict == None:
		mwBasesDict = load_full_mwBasisCache_as_dict();
	
	for exponents in Words([0,1,2],s):
		if verbose:
			print "----------------------------------------------";
			print "exponents:",exponents;
		z = prod([S[i]^exponents[i] for i in range(s)])
		M = m * z; #in the apper, z is called w.
		solutions_for_M = solveThueEquation(a,b,c,d,m=M,S=S,modOutSymmetry=modOutSymmetry,verbose=verbose,mwBasesDict=mwBasesDict);
		for (x,y) in solutions_for_M:
			#Replace (x,y,z) by primitive solution:
			#The following is actually the same as multiplying x and y with the lcm of the denominators of x and y.
			for p in S:
				vx = x.ord(p);
				vy = y.ord(p);
				#vz = z.ord(p); #which is 0, 1, or 2
				v = min([vx,vy,0]);
				x /= p^v;
				y /= p^v;
				z /= p^(3*v);
			x = ZZ(x);
			y = ZZ(y);
			z = ZZ(z);
			solutions.add((x,y));

	totalTime = walltime(t00);
			
	if verbose:
		print "==============================================";
		print "Thue-Mahler equation has",len(solutions),;
		if modOutSymmetry:
			print "ordered primitive solutions:",;
		else:
			print "primitive solutions:",;
		print solutions;

	if saveToFile:
		solutionsList = list(solutions);
		solutionsList.sort();
		
		filename = "thueMahler_"+myListToStr([a,b,c,d],"_");
		filename += "_m"+str(m);
		if S==primes_first_n(len(S)):
			filename += "_n"+str(len(S));
		else:
			filename += "_S_"+myListToStr(S,'_');
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutionsList,filename);
	
		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all primitive integral solutions of the Thue-Mahler equation\n");
		out.write("# "+str(a)+"x^3 + "+str(b)+"x^2y + "+str(c)+"xy^2 + "+str(d)+"y^3 = "+str(m)+"z,\n");
		out.write("# such that the only primes dividing z are among ");
		if S==primes_first_n(len(S)):
			out.write("the first "+str(len(S))+" primes.\n");
		else:
			out.write("S = {"+myListToStr(S,',')+"}.\n");
		if modOutSymmetry:
			out.write("# For each solution (x,y), only one of (x,y), (-x,-y) is listed.\n");
		out.write("# It contains "+str(len(solutionsList))+" pairs in total.\n");
		out.write('# Format: "(x, y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for (x,y) in solutionsList:
			out.write("(%s, %s)\n" % (str(x),str(y)));
		out.close();

	return solutions;

def solveRamanujanNagellEquation_XY(b,c=1,S=[],mwBasesDict={},verbose=True,saveMWToCache=True,saveToFile=True,saveToPath=pathData,reverseExponents=False):
	'''
	INPUT:
	- b - a non-zero S-integer,
	- c - a non-zero S-integer,
	- S - a finite set of rational primes.

	OUTPUT:
	A list of all solutions (x,y) of the (more general) Ramanujan-Nagell equation
	  x^2 + b = c*y,
	where b and c are the given parameters, x>=0 is an S-integer, and y an S-unit.
	'''

	t00 = walltime();
	t_MW = 0;
	t_Main = 0;

	if b==0 or not QQ(b).is_S_integral(S):
		raise ValueError("The parameter b needs to be a non-zero S-integer.");
	if c==0 or not QQ(c).is_S_integral(S):
		raise ValueError("The parameter c needs to be a non-zero S-integer.");	
	
	s = len(S);
	solutions = set([]);

	if verbose:
		print "Solve generalized Ramanujan-Nagell equation x^2 + %d = %d*y with S-integer x and S-units y." % (b,c);
		print "|S| =",s;

	if mwBasesDict == None:
		mwBasesDict = load_full_mwBasisCache_as_dict();

	Exponents = [w for w in Words([0,1,2],s)];
	if reverseExponents:
		Exponents.reverse();			
	for exponents in Exponents:
		if verbose:
			print "----------------------------------------------";
			print "exponents:",exponents;
		eps = prod([S[i]^exponents[i] for i in range(s)])
		a = -b*(eps*c)^2;
		E = mordellCurve(a);
		print "a =",a;
		t0_mw = walltime();
		mwBasis = mwBasisViaCacheMagmaOrSage(a,mwBasesDict=mwBasesDict,saveMWToCache=saveMWToCache);
		t_MW += walltime(t0_mw);
		if verbose:
			print "mwBasis:",mwBasis;
		t0_main = walltime();
		solutions_for_a = computeSIntegralPoints(E,S=S,mwBasis=mwBasis,bothSigns=False,saveToFile=False,verbose=False);
		t_Main += walltime(t0_main);
		print "solutions_for_a:",solutions_for_a;
		for P in solutions_for_a:
			(u,v) = P.xy();
			x = (v/(eps*c)).abs();
			y = u^3/(eps^2*c^3);
			if x.is_S_integral(S) and y.is_S_unit(S):
				solutions.add((x,y));

	solutions = list(solutions);
	solutions.sort();

	totalTime = walltime(t00);
			
	if verbose:
		print "==============================================";
		print "Generalized Ramanujan-Nagell equation has",len(solutions),"solutions (up to x <---> -x symmetry).";
		print solutions;
		print "time for MW:",t_MW;
		print "time for searching S-integral points:",t_Main;

	if saveToFile:
		filename = "ramanujanNagellXY"; #+myListToStr([a,b,c,d],"_");
		filename += "_b"+str(b);
		filename += "_c"+str(c);
		if S==primes_first_n(len(S)):
			filename += "_n"+str(len(S));
		else:
			filename += "_S_"+myListToStr(S,'_');
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all solutions (x,y) of the generalized Ramanujan-Nagell equation\n");
		out.write("# x^2 + "+str(b)+" = "+str(c)+" * y, where\n");
		out.write("# x >= 0 is an S-integer and y an S-unit, and\n");
		if S==primes_first_n(len(S)):
			out.write("# S is the set of the first "+str(len(S))+" primes.\n");
		else:
			out.write("# S = {"+myListToStr(S,',')+"}.\n");
		#if modOutSymmetry:
		#	out.write("# For each solution (x,y), only one of (x,y), (-x,-y) is listed.\n");
		out.write("# It contains "+str(len(solutions))+" pairs in total.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for x,y in solutions:
			out.write("(%s,%s)\n" % (str(x),str(y)));
		out.close();

	return solutions;	

def solveRamanujanNagellEquation_XN(b,c=1,d=2,mwBasesDict={},verbose=True,saveMWToCache=True,saveToFile=True,saveToPath=pathData):
	'''
	INPUT:
	- b - a non-zero integer,
	- c - a non-zero integer,
	- d - an integer with |d| >= 2.

	OUTPUT:
	A list of all solutions (x,n) of the (more special) Ramanujan-Nagell equation
	  x^2 + b = c * d^n,
	where b, c, and d are the given parameters, and x and n are non-negative integers.
	'''

	t00 = walltime();

	t_MW = 0;
	t_Main = 0;

	if b==0 or not b in ZZ:
		raise ValueError("The parameter b needs to be a non-zero integer.");
	if c==0 or not b in ZZ:
		raise ValueError("The parameter c needs to be a non-zero integer.");	
	if d in [0,1,-1] or not b in ZZ:
		raise ValueError("The parameter d needs to be an integer with |d|>=2.");	

	solutions = set([]);

	if not Mod(-b,c*d).is_square():
		#This is a trivial case:
		#Equation x^2 + b = c*d^n has no solutions for n>=1.
		#Check if n = 0 gives a solution:
		
		xSq = c - b;
		if xSq.is_square():
			x = ZZ(sqrt(c-b));
			solutions.add((x,0));
	else:
		#Regular algorithm:
		S = [p for (p,e) in factor(d)];
		s = len(S);

		if verbose:
			print "Solve generalized Ramanujan-Nagell equation x^2 + %d = %d * %d^n with non-negative integers x and n." % (b,c,d);
			print "S =",S;
		
		for n0 in [0,1,2]:
			if verbose:
				print "----------------------------------------------";
				print "n0:",n0;
			eps = d^n0;
			a = -b*(eps*c)^2;
			E = mordellCurve(a);
			print "a =",a;
			t0_mw = walltime();
			mwBasis = mwBasisViaCacheMagmaOrSage(a,mwBasesDict=mwBasesDict,saveMWToCache=saveMWToCache);
			t_MW += walltime(t0_mw);
			if verbose:
				print "mwBasis:",mwBasis;
			t0_main = walltime();
			solutions_for_a = computeSIntegralPoints(E,S=S,mwBasis=mwBasis,bothSigns=False,saveToFile=False,verbose=False);
			t_Main += walltime(t0_main);
			print "solutions_for_a:",solutions_for_a;
			for P in solutions_for_a:
				(u,v) = P.xy();
				x = (v/(eps*c)).abs();
				if not x in ZZ:
					continue;
				y = u^3/(eps^2*c^3);
				n = 0;
				while abs(y)>1:
					y /= d;
					n += 1;
				if y != 1:
					continue;
				solutions.add((x,n));

	solutions = list(solutions);
	solutions.sort();

	totalTime = walltime(t00);
			
	if verbose:
		print "==============================================";
		print "Generalized Ramanujan-Nagell equation has",len(solutions),"solutions (up to x <---> -x symmetry).";
		print solutions;
		print "totalTime:",totalTime;
		print "time for MW:",t_MW;
		print "time for searching S-integral points:",t_Main;

	if saveToFile:
		filename = "ramanujanNagellXN"; #+myListToStr([a,b,c,d],"_");
		filename += "_b"+str(b);
		filename += "_c"+str(c);
		filename += "_d"+str(d);
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all solutions (x,y) of the generalized Ramanujan-Nagell equation\n");
		out.write("# x^2 + "+str(b)+" = "+str(c)+" * "+str(d)+"^n, where\n");
		out.write("# x and n are non-negative integers.\n");
		out.write("# It contains "+str(len(solutions))+" pairs in total.\n");
		out.write('# Format: "(x,n)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for x,n in solutions:
			out.write("(%s,%s)\n" % (str(x),str(n)));
		out.close();

	return solutions;	

########################################################################
########################################################################
### Tests: #############################################################
########################################################################
########################################################################

def listmordellCurves(maxA=100,minA=-100,rank=None):
	'''
	List all Mordell curves in given range with some of their properties.
	'''
	numberOfCurves = 0;
	for a in range(minA,maxA+1):
		if a!=0:
			E = mordellCurve(a);
			r = E.rank(proof=False);
			if rank!=None and r!=rank:
				continue;
			numberOfCurves += 1;
			t = E.torsion_order();
			Wmin = E.minimal_model();
			Delta = E.discriminant();
			N = E.conductor();
			SBadReduction = prime_factors(N);
			rc = E.real_components();
			print "a=%d, rk=%d, tor=%d, bad_red=%s, realcomp=%d" % (a, r, t, str(SBadReduction), rc);
	print "Number of curves:",numberOfCurves;

def testSIntegralityForMultiplesNTimesP(P,S,n):
	'''
	Check is_S_integral()...
	'''
	E = P.scheme();
	print E;
	Q = E(0); # = 0*P
	for i in range(n+1):
		print i, Q[0].is_S_integral(S);
		Q = Q + P;

def rafaelsTest(r):
	'''
	Yet another computation for Rafael...
	'''
	c13 = 2.9 * 10^(6*r+12) * 4^(2*(r+1)^2) * (r+2)^(2*r^2+13*r+23.3) * 10^r;
	C = c13^(r/2);
	return log(C)/log(2);

def test_integralLowerApproximationOfQuadraticForm():
	'''
	Checks the integral/rational lower approximation function for a quadratic form...
	'''
	M = E.height_pairing_matrix();
	Mint, f = integralLowerApproximationOfQuadraticForm(M,20);
	print "f:",f;
	v = vector(range(M.nrows(),0,-1));
	print normSquared(v*f,M);
	print normSquared(v,Mint);

def testParallel():
	'''
	This test checks how much time it takes to run one instance of a function
	with in the parallel decorator. Result: On my laptop it takes 0.033 seconds per instance.
	'''

	@parallel(p_iter="fork",ncpus=1)
	def f(n):
		return n;

	t00 = walltime();
	gen = f(range(100));
	for x in gen:
		print ".",
	print "";
	print "time:",walltime(t00);
	
#testParallel();

def NunosQuestion():
	'''
	Check something for Nuno...
	'''
	G = QuaternionGroup();
	for S in G.subgroups():
		if S.order() == 4:
			print S.is_cyclic(), S.gens_small();

def test():
	'''
	Check the matrices A that appear in the refined sieve...
	'''
	S = primes_first_n(10);
	print "|S| =",len(S),", a =",a;
	E = EllipticCurve([0,0,0,0,a]);
	mwBasis = E.gens();
	ECache = E_Cache(E,mwBasis);

	p = 5;
	C = 5;
	print bottomRowOfLatticeA(E,5,7,mwBasis,ECache,verbose=True)
	print bottomRowOfLatticeA(E,Infinity,2^7,mwBasis,ECache,verbose=True)

def testPadicLog():
	'''
	Check p-adic logs...
	'''
	a = kPosOfRank[2];
	E = mordellCurve(a);
	S = [523];
	P = E.gen(0);
	p = S[0];
	print my_padic_elliptic_logarithm(P, p, absPrec=4);

def computeSIntegralPointsForManymordellCurves(n,rank=None,maxA=None,As=None,verbose=True,saveToOneFile=True,saveToFileSeparately=True,bothSigns=False):
	'''
	Calls computeSIntegralPoints() in parallel for all Mordell curves y^2=x^3+a where:
	- S = first n primes,
	- only the given ranks (if rank!=None),
	- for all nonzero -maxA <= a <= maxA (if maxA!=None),
	- for all a in As (if As!=None).
	We require that the global dictionary my_mwBasis_for_mordellCurves contains all needed MW-bases.
	'''

	global pathData;
	global pathMordellWeil;
	global my_mwBasis_for_mordellCurves;

	t0 = walltime();

	if verbose:
		print "n =",n;
		if rank != None:
			print "rank =",rank;
		if maxA != None:
			print "maxA =",maxA;
		if As != None:
			print "|As| =",len(As);	
	S = primes_first_n(n);
	if verbose:
		print "Load Mordell-Weil bases...";
	mwBases = dict(load(pathMordellWeil+"mwBases10000.sobj"));
	#mwBases = my_mwBasis_for_mordellCurves;
	#mwBases[7823] = [(2263582143321421502100209233517777/143560497706190989485475151904721,\
	#		186398152584623305624837551485596770028144776655756/1720094998106353355821008525938727950159777043481)];
	path = pathData;
	if rank != None:
		path += "rank"+str(rank)+"_";
	path += "n"+str(n);
	if maxA != None:
		path += "_maxA"+str(maxA);
	if As != None:
		path += "_numAs"+str(len(As));
	path += "/";
	if verbose:
		print "Start parallel computing...";
	parameters = [];
	keys = copy(mwBases.keys());
	#keys.sort(key=lambda a: abs(a+4347)); #debug
	keys.sort(key=lambda a: abs(a)); #compare positive and negative a's.
	for a in keys:
		if maxA==None or abs(a)<=maxA:
			if As==None or a in As:
				mwBasis = mwBases[a];
				if rank==None or rank==len(mwBasis):
					E = mordellCurve(a);
					Mmax0 = None;
					verbose2 = False;
					#verbose2 = True;
					saveToFile = saveToFileSeparately;
					saveToPath = path;
					param = (E,S,mwBasis,Mmax0,verbose2,bothSigns,saveToFile,saveToPath);
					parameters.append(param);

	if verbose:
		print "Number of curves:",len(parameters);

	allSolutionsAsTuples = [];

	gen = computeSIntegralPoints(parameters);
	for x in gen:
		a = x[0][0][0].a6();
		solutionsForA = x[1];
		if verbose:
			print "Done for a =",a;
			print "Output: ",solutionsForA;

		if saveToOneFile:
			solutionsAsTuplesXY_forA = [(P[0],P[1]) for P in solutionsForA];
			allSolutionsAsTuples.append((a,solutionsAsTuplesXY_forA));

	totalTime = walltime(t0);

	if saveToOneFile:
		allSolutionsAsTuples.sort(key = lambda t: t[0]);
		
		#First save the sage object 'solutionsAsTuplesXY':
		filename = "allSolutions";
		if rank != None:
			filename += "_r_"+str(rank);
		if maxA != None:
			filename += "_maxA_"+str(maxA);
		#if As != None:
		#	filename += "_As_"+myListToStr(As,'_');
		if As != None:
			filename += "_numAs_"+str(len(As));
		if S==primes_first_n(len(S)):
			filename += "_n_"+str(len(S));
		else:
			filename += "_S_"+myListToStr(S,'_');
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(allSolutionsAsTuples,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# Lists of S-integral points (x,y) on the Mordell curves\n");
		out.write("# y^2 = x^3 + a, with the following constraints:\n");
		if rank != None:
			out.write("# we consider only curves of rank r = "+str(rank)+",\n");
		if maxA != None:
			out.write("# a is bounded by |a| <= "+str(maxA)+",\n");
		if As != None:
			out.write("# a lies in {"+myListToStr(As,", ")+"},\n");
		if S==primes_first_n(len(S)):
			out.write("# S is the set of the first "+str(len(S))+" primes.\n");
		else:
			out.write("# S = {"+myListToStr(S,',')+"}.\n");
		if (rank==None or rank==1) and (maxA==None or maxA>=7823) and (As==None or 7823 in As) and (7823 not in [t[0] for t in allSolutionsAsTuples]):
			out.write("# WARNING: Furthermore a = 7823 is NOT considered here, as we don't know the corresponding Mordell-Weil basis.\n");
		out.write("# It contains "+str(len(allSolutionsAsTuples))+" curves in total.\n");
		out.write("# It contains "+str(sum([len(t[1]) for t in allSolutionsAsTuples]))+" points in total.\n");
		if bothSigns==False:
			out.write("# For each point P, only one of +P, -P is listed.\n");
		out.write('# Format of the points: "(P(x),P(y))".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		#out.write("###\n");
		for a, solutionsAsTuplesXY in allSolutionsAsTuples:
			out.write("#\n");
			out.write("# a = "+str(a)+":\n");
			out.write("#\n");
			for (x,y) in solutionsAsTuplesXY:
				#out.write(str(r)+": "+str(a)+" + "+str(b)+" = "+str(c)+" ("+str(q)+")\n");
				out.write("(%s,%s)\n" % (str(x),str(y)));
		out.close();
		
		#Furthermore save log:
		#out = file("log_"+filename+'.txt','w');
		#for msg in LogMessages:
		#	out.write(msg+"\n");
		#out.close();

	if verbose:
		print "Finished!";

	return allSolutionsAsTuples;

def rafaelsChecks():
	'''
	var("a1 a2 a3 a4 a6 x xprime")
	Egen = EllipticCurve([a1,a2,a3,a4,a6])
	print Egen
	#f = Egen.two_division_polynomial()
	#print "f",f
	#xprime = x + 1/12*Egen.b2();
	#print "x'",xprime;
	#print "f(x')=",f(xprime)
	
	g2 = Egen.c4()/12;
	g3 = Egen.c6()/216;

	t = var("t");
	f2(t) = 4*t^3 - g2*t - g3;
	print "f2",f2
	#print 3 
	#print f2(100)-f(100)

	return;
	'''
	
	E = mordellCurve(80);
	r = E.rank()
	print "rank =",r;
	Emin = E;
	#Emin = E.minimal_model();
	P = Emin.gen(0);
	x = P[0];
	print Emin;
	xprime = x - 1/12*Emin.b2();
	print "xprime =",xprime;
	g2 = Emin.c4()/12;
	g3 = Emin.c6()/216;

	f = 4*t^3 - g2*t - g3;
	rootsF = f.roots(ring=RR,multiplicities=False)
	e1 = max(rootsF);
	#f = Emin.two
	#print f(xprime-1/12*Emin.b2());
	print "f =",f
	#print "integral =",integral_numerical(lambda x: 1/sqrt(f(x)),xprime,Infinity);
	print "integral2 =",integral_numerical(lambda x: 1/sqrt(f(x)),e1,Infinity);
	print "omega1 =",Emin.period_lattice().real_period()
	print "omega1/2 =",Emin.period_lattice().real_period()/2
	print "real log =",(-P).elliptic_logarithm()


	def summe1durchp(n):
		return N(sum([1/p for p in primes_first_n(n)]));

	print (summe1durchp(100)-summe1durchp(50))
	
#rafaelsChecks();

def test_RealComponents():
	'''
	Check number of real components...
	'''
	for a in range(-100,101):
		if a!=0:
			E = mordellCurve(a);
			print "a =", a, ", num real components:",E.real_components();

#test_RealComponents()

def test_Isogenies():
	'''
	Check isogenies...
	'''
	for a in range(1,100) + range(-100,0):
		E = mordellCurve(a);
		print a,"\n", E.isogenies_prime_degree();

#test_Isogenies();

def test_computeReductions():
	'''
	Compute reductions of E wrt. to the first few primes.
	'''
	global E;
	P = E.gen(0);
	for p in primes_first_n(1000):
		if E.has_good_reduction(p):
			Ered = E.reduction(p);
			#print "p =",p,". Reduction:",Ered; #ca. 5 seconds
			#print "p =",p,". Reduction_abelian_group:",Ered.abelian_group(); #30 seconds
			#print "p =",p,". Reduction_exponent:",Ered.abelian_group().exponent(); #27 seconds
			#print "p =",p,". Reduction generator_orders:",Ered.abelian_group().generator_orders(); #33
			#print "p =",p,". order(Pred) =",Ered(P).order(); #14
			print "p =",p,". coordinate_vector(Pred) =",Ered.abelian_group().coordinate_vector(Ered(P)); #sehr lange

#time test_computeReductions();

def duellGame():
	'''
	Alice and Bob play the following game:
	A and B have pistols with n bullet slots.
	First A shoots B with 1 random bullet (i.e. A wins immediately with probability 1/n).
	Then B shoots A with 2 random bullets.
	Then A shoots B with 3 random bullets.
	And so on.
	At the n'th round all n slots contain a bullet, and the game ends here at the latest.
	Who has the higher winning chances (depending on n)?
	What winning chance does Alice have in the limit n ---> infinity?
	For which n>=2 does Alice have the highest winning chances?
	'''
	
	def duell(n):
		n = QQ(n);
		p = {0:0, 1:0};
		for i in range(1,n+1):
			p[i % 2] += i/n * prod([(n-k)/QQ(n) for k in range(1,i)]);
			#print [(n-k)/QQ(n) for k in range(1,i)]
		print "For n =",n,", p =",p;
		print "  that is:",N(p[0]),N(p[1]);
	
	for n in range(1,10+1):
		duell(n);

#duellGame();

def testHighRank():
	t = var("t");
	p = 1/3*(-10826200650935848777 + 164811596583226 * t - 5127792247*t^2 - 6816*t^3);
	print p;
	roots = p.roots(multiplicities=False);
	print roots;
	q = 1/27*(219447198708806169550761710218 - 9503942061991832238562998*t + 69459713496020650440*t^2 + 412911834544636 * t^3 + 1843807527 * t^4 + 243*t^5);
	print q;
	for r in roots:
		print CC(q(t=r));
	
#testHighRank();

def testMWBases():
	global my_mwBasis_for_mordellCurves;
	global my_mwSublatticeBasis_for_mordellCurves;
	#bases = copy(my_mwBasis_for_mordellCurves);
	#bases.update(my_mwSublatticeBasis_for_mordellCurves);
	bases = dict(load("mwBases10000.sobj"));
	for k, mwBase in bases.iteritems():
		#if len(mwBase)<12:
		#	continue;
		if len(mwBase)==0:
			continue;
		if k<=-5249 or k>0:
			continue;
		print "===================";
		E = mordellCurve(k);
		print 
		print E;
		points = [];
		for x,y in mwBase:
			#print E.lift_x(x);
			P = E(x,y);
			print P;
			points.append(P);

		###Check whether points are saturated:
		##sat = E.saturation(points,max_prime=1000);
		#sat = E.saturation(points,max_prime=0);
		#print sat;
		#if (sat[1] != 1) or (len(sat[0]) != len(points)):
		#	print "ERROR: This one is NOT saturated!!! Stop here...";
		#	return;

		#continue;

		###Check whether rank is correct:
		#alarm(10); #give it 10 seconds of time...
		try:
			#if len(points)>1:
			ME = magma(E);
			rankBounds = ME.RankBounds(nvals=2);
			rankUpperBound = rankBounds[1].sage();
			#else:
			#	rankUpperBound = E.rank_bound();
		except (AlarmInterrupt,TypeError,KeyboardInterrupt):
			rankUpperBound = E.rank_bound();
		#cancel_alarm(); #stop alarm
		if rankUpperBound != len(points):
			print "ERROR: Couldn't prove that rank is correct!!! Stop here...";
			return;

def studyMWBases():
	bases = dict(load("mwBases10000.sobj"));
	keys = bases.keys();
	keys.sort();

	def studyTorsion():
		#How many S-integral torsion points are there:
		r = 0;
		S = [2,3,5];
		print "r =",r;
		print "len(S) =",len(S);
		T = [];
		for k in keys:
			basis = bases[k];
			E = mordellCurve(k);
			if len(basis) == r:
				for t in E.torsion_points():
					if t != E(0):
						if t[0].is_S_integral(S):
							if -t not in T:
								T.append(t);
		print "len(T):",len(T);
			
	def studyNumberOfSolutions():
		#How many curves are there with given number of S-integral points:
		r = 2;
		n = 3;
		S = primes_first_n(n);
		print "r =",r;
		print "n =",n;
		
		global pathData;
		path = pathData+"GPZ97/";
		path += "rank"+str(r);
		path += "_n"+str(n);
		path += "_maxA10000";
		path += "/";
		filename = "allSolutions_r_"+str(r);
		filename += "_maxA_10000";
		filename += "_n_"+str(n);
		filename += ".sobj";
		kp = load(path+filename);
		ksWithGivenNumberOfSolutions = {};
		for (k,points) in kp:
			numSols = len(points);
			if not ksWithGivenNumberOfSolutions.has_key(numSols):
				ksWithGivenNumberOfSolutions[numSols] = [];
			ksWithGivenNumberOfSolutions[numSols].append(k);
		nums = ksWithGivenNumberOfSolutions.keys();
		nums.sort();
		for num in nums:
			print "#ks with",num,"solutions:",len(ksWithGivenNumberOfSolutions[num]);
			if num == -4:
				for k in ksWithGivenNumberOfSolutions[num]:
					E = mordellCurve(k);
					if not forall(S,lambda p: E.is_p_minimal(p)):
						print "Non-S-minimal k:",k;
					else:
						print "S-minimal k:",k;
						solSage = E.S_integral_points(S,both_signs=True);
						print " with num solutions (according to sage):",len(solSage);


	#studyTorsion();
	studyNumberOfSolutions();

def test_findMWBasis(k,rank_bound=None,height_limit=10,via_rat_points=True):

	def point_search_mod(E, height_limit, verbose=False, rank_bound=None, max_prime=0, max_prime_end=0):
		'''
		Modified version of E.point_search() from sage.
		The only change is that we allow also 
		'''
		from sage.libs.ratpoints import ratpoints
		from sage.functions.all import exp
		from sage.rings.arith import GCD
		H = exp(float(height_limit)) # max(|p|,|q|) <= H, if x = p/q coprime
		coeffs = [16*E.b6(), 8*E.b4(), E.b2(), 1]
		points = []
		a1 = E.a1()
		a3 = E.a3()
		new_H = H*2 # since we change the x-coord by 2 below
		for X,Y,Z in ratpoints(coeffs, new_H, verbose):
			if Z == 0: continue
			z = 2*Z
			x = X/2
			y = (Y/z - a1*x - a3*z)/2
			d = GCD((x,y,z))
			x = x/d
			if max(x.numerator().abs(), x.denominator().abs()) <= H:
				y = y/d
				z = z/d
				points.append(E((x,y,z)))
				if rank_bound is not None:
					points = E.saturation(points, verbose=verbose, max_prime=max_prime)[0]
					if len(points) == rank_bound:
						break
		if rank_bound is None or max_prime!=max_prime_end:
			points = E.saturation(points, verbose=verbose, max_prime=max_prime_end)[0]
		return points

	E = mordellCurve(k);
	if via_rat_points:
		points = point_search_mod(E,height_limit=height_limit,verbose=True,rank_bound=rank_bound,max_prime=20,max_prime_end=1000);
	else:
		points = E.gens(verbose=True,proof=True);
		points = E.saturation(points,max_prime=0,verbose=True)[0];
	print "Points:";
	for P in points:
		print "("+str(P.xy()[0])+","+str(P.xy()[1])+"),",;
	print "";
	return points;

def test_compareRunningTimeForLogComputationForDifferentHeightBounds():
	global my_mwBasis_for_mordellCurves;
	#global my_mwSublatticeBasis_for_mordellCurves;
	bases = copy(my_mwBasis_for_mordellCurves);
	bases.update(my_mwSublatticeBasis_for_mordellCurves);
	As = bases.keys();
	As.sort(key=abs);
	print "As:",As;
	for a in As:
		if abs(a) <= 0:
			continue;
		print "=============================";
		print "a =",a;
		mwBase = bases[a];
		print "rank =",len(mwBase);
		#for heightBound in ["vKM15","PZGH99","ST94"]:
		#Important: Whenever computations are rerun, the cache needs to be cleared first!!! (E.g. by restarting sage.)
		heightBound = "vKM15";
		#heightBound = "PZGH99";
		#heightBound = "ST94";
		#n = 0;
		n = 1;
		#n = 10;
		#n = 100;
		print "Height bound from:",heightBound;
		print "------ n =",n;
		E = mordellCurve(a);
		computeSIntegralPoints(E=E,S=primes_first_n(n),mwBasis=mwBase,verbose=False,debugParam={"initialBoundMethod":heightBound});

def test_7823(h = 12):
	#Try to find a Mordell-Weil basis for E = mordellCurve(7823)!
	#This is the only Mordell curve with |a|<=10^4 for which the MW-Basis is unknown.
	#It is known that E's rank is 1.

	a = 7823;
	E = mordellCurve(a);
	print "E =",E;

	def try_via_ratpoints():
		from sage.libs.ratpoints import ratpoints;
		#coeffs = [16*E.b6(), 8*E.b4(), E.b2(), 1];
		coeffs = [a,0,0,1];
		#coeffs = [1,0,0,a];
		print "coeffs =",coeffs;
		print "h =",h;
		#H = 2*exp(h); #since we change the x-coord by 2 below
		H = exp(h); #since we change the x-coord by 2 below
		points = ratpoints(coeffs, H, verbose=True, max=1);
		print "points:",points;

	#try_via_ratpoints();

	P = E((2263582143321421502100209233517777/143560497706190989485475151904721,\
			186398152584623305624837551485596770028144776655756/1720094998106353355821008525938727950159777043481));

	print "P =",P;
	print "height(P) =",P.height();
	print "height(P).log() =",P.height().log();
	print "saturation:",E.saturation([P]);

	return E,P;

def test_QuarticCovariants():

	R.<x,A,B,C> = PolynomialRing(QQ,["x","A","B","C"]);
	a = 1;
	b = a*(-A-B-C);
	c = a*(A*B+A*C+B*C);
	d = a*(-A*B*C);

	y = 1;

	H = (3*a*c-b^2)*x^2 + (9*a*d-b*c)*x*y + (3*b*d-c^2)*y^2;
	G = (27*a^2*d-9*a*b*c+2*b^3)*x^3 - 3*(6*a*c^2-b^2*c-9*a*b*d)*x^2*y + 3*(6*b^2*d-b*c^2-9*b*c*d)*x*y^2 - (27*a*d^2-9*b*c*d+2*c^3)*y^3;

	H2 = (x-A)^2*(B-C)^2 + (x-B)^2*(A-C)^2 + (x-C)^2*(A-B)^2;

	#print "G:",G;
	print "H:",H;
	print "H2:",H2;
	print "differenz:",H+H2/2;
	
def estimateNumberOfSolutionsEstimate(S,r,a,torsionOrder=1,regulator=1,bothSigns=False):

	def dickman_neg(u):
		return 1;
	def dickman_0_1(u):
		return 1;
	def dickman_1_2(u):
		return 1-log(u);
	def dickman_2_3(u):
		return 1-(1-log(u-1))*log(u) + dilog(1-u) + pi^2/12;
	def dickman_3_inf(u):
		#return exp(-u*(log(u)+log(u)/log(2)-1+(log(u)/log(2)-1)/log(u)));
		#return u^(-u);
		#return u^(-u);
		return 1/gamma(1+u);

	def Cr(r,x_offset = 0.0, eps=0):
		#int D(t^2)*t^(r-1)dt = int 1/2*D(x)*x^(r/2-1) dx, t^2 = x, dx/dt = 2t, dt = dx/(2x^(1/2)).
		#The following was wrong, as D(x) must read D(x^2):
		#c1 = numerical_integral(dickman_0_1(x)*x^(r-1),0,1)[0];
		#c2 = numerical_integral(dickman_1_2(x)*x^(r-1),1,2)[0];
		#c3 = numerical_integral(dickman_2_3(x)*x^(r-1),2,3)[0];
		#c4 = numerical_integral(dickman_3_inf(x)*x^(r-1),3,Infinity)[0];
		c0 = numerical_integral(1/2*dickman_neg(x)*(x+x_offset)^(r/2-1),-x_offset,0)[0];
		c1 = numerical_integral(1/2*dickman_0_1(x)*(x+x_offset)^(r/2-1),0,1)[0];
		c2 = numerical_integral(1/2*dickman_1_2(x)*(x+x_offset)^(r/2-1),1,2)[0];
		c3 = numerical_integral(1/2*dickman_2_3(x)*(x+x_offset)^(r/2-1),2,3)[0];
		c4 = numerical_integral(1/2*dickman_3_inf(x)*(x+x_offset)^(r/2-1),3,Infinity)[0];
		print c0,c1,c2,c3,c4;
		cr = (c0+c1+c2+c3+c4);
		cr *= volumeOfSphere(r-1);
		cr *= (2+eps)^(r/2); #Actually here we should have (2+eps)^(r/2), but we put eps=0.
		#print "c0 =",c0;
		#print "c1 =",c1;
		#print "c2 =",c2;
		#print "c3 =",c3;
		#print "c4 =",c4;
		return cr;

	#debug = True;
	debug = False;

	if debug:
		g  = plot(dickman_neg,xmin=-1,xmax=0);
		g += plot(dickman_0_1,xmin=0,xmax=1);
		g += plot(dickman_1_2,xmin=1,xmax=2);
		g += plot(dickman_2_3,xmin=2,xmax=3);
		g += plot(dickman_3_inf,xmin=3,xmax=10);
		g.show();

	if debug:
		data = [];
		logdata = [];
		for r in range(1,30,1):
			#print "-----------------------";
			#print "r = ",r;
			cr = Cr(r);
			#print "r =",r,": cr =",cr;
			data.append([r,cr]);
			logdata.append([r,log(cr)]);
		print data;

		var('a, b, c, h, l, r, f');
		#model(x) = (a*x^2)*exp(-l*x^2) * 2^(x/2);
		#fit = find_fit(data, model);
		#fit = [a == 1.8019570126906823, l == 0.0041916584200636904]
		#fit = [a == 2.0, l == 0.0041916584200636904]
		#fit = [a == 2.0, l == 0.004]
		#model(x) = (a*x^2)*exp(-l*x^2);
		#fit = find_fit(data, model);
		logmodel(x) = b*x + c*x^2 + h*x^3 + f*x^4;
		fit = find_fit(logdata,logmodel);
		print "fit:",fit;
		#fitFkt = model;
		fitFkt = exp(logmodel);
		for s in fit:
			fitFkt = fitFkt.subs(s);
		g = plot(fitFkt,xmin=0,xmax=100);
		for p in data:
			g += point(p);
			#break;
		g.show();

		#print data[0];
	

		return;
		
	if r==0:
		estimate = torsionOrder;
	else:
		#debug:
		#for rr in range(11):
		#	print "cr for r=",rr,"is",Cr(rr);

		q = max(S+[1]);


		E = mordellCurve(a);
		twoStar = 1;
		muE = 1/12*max(0,log(abs(E.j_invariant()))) + 1/12*E.discriminant().global_height() + 1/2*max(0,log(abs(E.b2()/12))) + 1/2*log(twoStar);
		mu = muE + 1.07;
		c = RR(log(max(1,log(abs(a))))); #a constant that depends on a and eps, the eps from abc.
		c = RR(10); #a constant that depends on a and eps, the eps from abc.
		c_2 = (c+mu)/2; #(actually 2+eps...)
		x_offset = c_2/log(q);

		cr = Cr(r,x_offset=x_offset);
		#print "cr =",cr;
		
		#logNS = sum([RR(log(p)) for p in S]);
		#y = RR(logNS + log(logNS));
		#n = len(S);
		#y = n*log(RR(n));
		d = log(RR(q));
		#cr = RR(2)*(RR(2*sqrt(pi)))^r/(r+1)/sqrt(RR(pi*r))/(r/RR(exp(1)*2))^(r/2);
		#cr = RR(2)*(RR(2*sqrt(pi)))^r/(r+1)/gamma(r/2+1);
		#print "d =",d;
		#print "cr =",cr;
		#Regulator = RR(1);
		#Regulator = RR(327165);
		estimate = RR(torsionOrder/sqrt(regulator)*d^(r/2)*cr);
	if bothSigns==False:
		estimate = estimate/2;
	return estimate;

#estimateNumberOfSolutionsEstimate(S=[],r=0);

def test_estimateNumberOfSolutions():
	#r = 8;
	#ns = range(31);
	#regulator = 327165;
	#torsionOrder = 1;
	#a = kPosOfRank[r];

	r = 1;
	ns = [10^k for k in range(10)];
	regulator = 1;
	torsionOrder = 1;
	a = kPosOfRank[r];

	for n in ns:
		print "------";
		print "n =",n,"and r =",r,":",;
		print "estimate:",estimateNumberOfSolutionsEstimate(primes_first_n(n),r,a,torsionOrder=torsionOrder,regulator=regulator,bothSigns=False);

#test_estimateNumberOfSolutions();

def computeEllipticCurvesWithGoodReductionOutsideS(S):
	print "S =",S;
	s = len(S);
	solutions = [];
	for exponents in Words([0,1,2,3,4,5],s):
		print "-----",exponents,;
		sys.stdout.flush();
		Delta = prod([S[i]^exponents[i] for i in range(s)]);
		a = -1728*Delta;
		print ", a =",a,",",;
		E = mordellCurve(a);
		sys.stdout.flush();
		
		global my_mwBasis_for_mordellCurves;
		if my_mwBasis_for_mordellCurves.has_key(a):
			mwBase = my_mwBasis_for_mordellCurves[a];
		else:
			#Try to use magma:
			try:
				mwBase = mwBaseViaMagma(E);
			except TypeError:
				if verbose:
					print "Problem with using magma, use sage instead for MW base computation."
				mwBase = E.gens();

		print "r =",len(mwBase);
		sys.stdout.flush();
		#print "mwBase:",mwBase;

		c4c6s = computeSIntegralPoints(E,S=S,mwBasis=mwBase,verbose=False,bothSigns=True,saveToFile=False);
		#print "c4c6s:",c4c6s;
		for P in c4c6s:
			c4,c6 = P.xy();
			Esol = EllipticCurve_from_c4c6(c4,c6).minimal_model();
			solutions.append(Esol);
			print "c4 =",c4,"and c6 =",c6,"yields",Esol;
			sys.stdout.flush();
	print "Number of solutions:",len(solutions);
	sys.stdout.flush();
	#TODO: Determine isomorphism classes:
	#...	
	return solutions;

#curves = computeEllipticCurvesWithGoodReductionOutsideS(S=[2]);
#curves = computeEllipticCurvesWithGoodReductionOutsideS(S=[2,3,5,7]);
#S=[2,3]: 68 solutions
#S=[2,3,5]: 360 solutions

def compareWithBennettGhadermarzi():
	'''
	Bennett--Ghadermarzi [BG15] computed all integral solutions to the
	Mordell equations y^2 = x^3 + k with |k|<=10^7.
	We did this computation in the smaller range |k|<=10^4.
	Here we compare both databases in this smaller range.
	'''

	#Load B-G database:
	f = file("bennettGhadermarzi10000.txt",'r');
	BGnum = {};
	BGpoints = {};
	for s in f:
		s = s.strip(" \t\n\r");
		if s=="":
			continue;
		if s.startswith("#"):
			continue;
		#for blank in ["<(",")>","< (",")",">"]:
		#	s = s.replace(blank,"");
		for comma in ["[","]",","," "]:
			s = s.replace(comma,",");
		t = [x.strip() for x in s.split(",")];
		while "" in t:
			t.remove("");
		if len(t)==0:
			continue;
		a = ZZ(t[0]);
		numSols = ZZ(t[1]);
		points = [(ZZ(t[2*i+2]),ZZ(t[2*i+3])) for i in range(0,len(t)/2-1)];
		BGnum[a] = numSols;
		BGpoints[a] = points;

	print "Number of k's in BG's database up to +-10000:",len(BGnum.keys());

	
	#Load vK-M database:

	global pathData;
	vKMpoints = dict(load(pathData+"n0_maxA10000/"+"allSolutions_maxA_10000_n_0.sobj"));

	#print "BGpoints[-9967]:",BGpoints[-9967];
	#print "vKMpoints[-9967]:",vKMpoints[-9967];

	ks = BGnum.keys();
	ks.sort();
	for k in ks:
		pointsBG = BGpoints[k];
		pointsVKM = vKMpoints[k];
		pointsBG.sort();
		pointsVKM.sort();
		if pointsBG != pointsVKM:
			print "Problem:"
			print "k =",k;
			print "pointsBG:",pointsBG;
			print "pointsVKM:",pointsVKM;
			break;
		#else:
		#	print k,;

	for k in vKMpoints.keys():
		if k not in BGpoints:
			if len(vKMpoints[k])>0:
				if k!=0:
					#if all(e<=5 for (p,e) in factor(k)):
					print "k =",k,"not in BG database although vKM yields solutions:",vKMpoints[k];
	
def testRank0Curves():
	mw = dict(load("mwBases10000.sobj"));
	for (a,basis) in mw.iteritems():
		if len(basis)==0:
			E = mordellCurve(a);
			if E.torsion_order()!=1:
				print a, E.torsion_points();

def test_rank1mordellCurvesWithLargeA():
	#aMin = 10^10;
	aMin = 10^6;

	#As = range(aMin,aMin+100,1);
	As = [randint(aMin,10*aMin) for i in range(100)]

	print "As:",As;

	As_with_rank1 = [];

	for a in As:
		print "a =",a;
		E = mordellCurve(a);

		alarm(10); #give it ... seconds of time...
		try:
			ra = E.analytic_rank();
		except (AlarmInterrupt, sage.interfaces.singular.SingularError):
			print "Took too long, take next a";
			continue;
		cancel_alarm(); #stop alarm

		ra = E.analytic_rank();
		print "ra =",ra;
		if ra == 1:
			rb = E.rank_bound();
			print "rank bound:",rb;
			if rb == 1:
				rbs = E.rank_bounds();
				print "rank bounds:",rbs;
				if rbs == (1,1):
					print "Found a rank 1 curve.";
					As_with_rank1.append(a);

	print "As_with_rank1:",As_with_rank1;

	#found so far:
	#7198032, 3059408, 7168568
	#following ones have non-trivial k^6-factor:
	#8470728, 2410112, 8160768,

	return True;

#time test_rank1mordellCurvesWithLargeA()

def test_rank1mordellCurvesWithLargeA_2():
	x_size = 6;
	RR = RealField(prec=x_size*10);
	As_with_P0 = [];
	#for i in range(10):
	iLoop = 0;
	while len(As_with_P0)<10:
		iLoop += 1;
		print "===========================",iLoop;
		#x = ZZ(randint(10^x_size,10^(x_size+1)));
		#x = randint(10^6,10^7);
		x = (RR.random_element(min=1,max=10)*10^x_size).round();
		print "x =",x;
		x = ZZ(str(x));
		y = ZZ((RR(x)^3).sqrt().round());
		print "y =",y;
		a = y^2 - x^3;
		print "a =",a;
		E = mordellCurve(a);
		#if E.lseries().deriv_at1()[0] != 0:
		#	print "L-series of E has probably simple pole at s=1, so probably rank(E)=1."

		#continue;

		use_alarm = True;
		if use_alarm:
			#signal.alarm(60); #give it ... seconds of time...
			alarm(10); #give it ... seconds of time...
			try:
				time rb = E.rank_bound();
			except (AlarmInterrupt, sage.interfaces.singular.SingularError):
				print "Took too long, take next a";
				#signal.alarm(0); #stop alarm
				#cancel_alarm(); #stop alarm
				continue;
			#signal.alarm(0); #stop alarm
			cancel_alarm(); #stop alarm
		else:
			time rb = E.rank_bound();

		print "rb = ",rb;
		if rb == 1:
			P = E((x,y));
			if not P.is_finite_order():
				print "E has rank 1";
				mwbasis, index, regulator = E.saturation([P]);
				P0 = mwbasis[0];
				print "Generator of E(QQ):",P0;
				print "regulator:",regulator;
				print "("+str(a)+",("+str(P0[0])+","+str(P0[1])+")),";

				As_with_P0.append((a,P0));

	print "As_with_P0:",As_with_P0;

	'''
	(-27862111,(5542546,13048601235)),

	(287085177,(1331379,1536216954)),
	(700506828,(3640926,6947327598)),
	(889197040,(2554209,4082109463)),

	(-1290695886,(4875343,10764844561)),
	(-1546579968,(3273508,5922705112)), #has factor 2^12
	(2781381448,(7262606,19572158592)),
	(4380760029,(9722935,30317687602)),
	(5226678495,(3704509,7130105918)), #has factor 3^7
	(5895338604,(4670638,10094023526)),
	(-6488165816,(7560270,20787676928)),
	(7710452100,(8970640,26867987810)),

	(-21540761276,(8783376,26031081490)),
	(24681450473,(8968652,26859056909)),
	'''
	
	return As_with_P0;
						
#time As_with_P0 = test_rank1mordellCurvesWithLargeA_2();

def test_rank1mordellCurvesWithLargeA_3():
	@parallel(p_iter='fork',ncpus=numCPUs, timeout=60)
	def check_for_rank_1(x,y,a):
		E = mordellCurve(a);
		time rb = E.rank_bound();
		print "rb = ",rb;
		if rb == 1:
			P = E((x,y));
			if not P.is_finite_order():
				return True;
			else:
				return False;
		else:
			return False;
	
	x_size = 7;
	RR = RealField(prec=x_size*10);
	params = [];
	while len(params) < 30000:
		x = (RR.random_element(min=1,max=10)*10^x_size).round();
		x = ZZ(str(x));
		y = ZZ((RR(x)^3).sqrt().round());
		a = y^2 - x^3;
		if abs(a)>=10^10:
			if abs(a) <= 2*10^10:
				params.append((x,y,a));

	print "Number of parameters:",len(params);

	iLoop = 0;
	As_with_P0 = [];
	for input,output in check_for_rank_1(params):
		iLoop += 1;
		print iLoop,":",;
		x,y,a = input[0];
		if type(output)==type(True):
			if output == True:
				E = mordellCurve(a);
				P = E((x,y));
				print "E has rank 1";
				mwbasis, index, regulator = E.saturation([P]);
				P0 = mwbasis[0];
				print "Generator of E(QQ):",P0;
				print "regulator:",regulator;
				print "("+str(a)+",("+str(P0[0])+","+str(P0[1])+")),";
				As_with_P0.append((a,P0));
				#save_mwBasis_to_cache(a,p=[P0]);
			else:
				print "rankbound!=1 or P is torsion";
		else:
			print "timeout";

	print "As_with_P0:",As_with_P0;
	for a,P0 in As_with_P0:
		print "("+str(a)+",("+str(P0[0])+","+str(P0[1])+")),";

	'''
	(11170578176,(5873224,14233602960)),
	(11862783424,(5486820,12852306368)),
	(16231216192,(8976264,26893258456)),
	(-17951011911,(9129978,27587007729)),
	(-21540761276,(8783376,26031081490)),
	(24681450473,(8968652,26859056909)),

	#Neu, noch einzusortieren:

	for a,P in As_with_P0:
		save_mwBasis_to_cache(a,[P]);
	'''
	
	return As_with_P0;

#time As_with_P0 = test_rank1mordellCurvesWithLargeA_3();

def test_rank1mordellCurvesWithLargeA_ComputeSIntegralPoints():
	#The following list of a's with a generator of E_a(Q)/torsion (or rank 1) was computed
	#via test_rank1mordellCurvesWithLargeA_3():
	As_with_P0 = [ \
		(13938443648,(53135116,387322253112)), \
		(11372230143,(31615677,177768058374)), \
		(12639729600,(11020020,36582516240)), \
		(-14431105792,(27337492,142934808264)), \
		(-15233586112,(16276652,65667066736)), \
		(16613557164,(73080198,624740373666)), \
		(17851819520,(11972264,41425182208)), \
		(-16713421568,(21762257,101521003545)), \
		(-16169705216,(27499508,144207346536)), \
		(15619152064,(13234308,48145073776)), \
		(16843036544,(39061868,244134700024)), \
		(-16425740032,(11254736,37757477168)), \
		(16301168128,(15716712,62307817984)), \
		(-16670427904,(86825140,809036729064)), \
		(-11236352768,(14630657,55962324225)), \
		(-12287967232,(15999968,63999808000)), \
		(19660216832,(60121432,466169627520)), \
		(14107897792,(18026244,76534609024)), \
		(-16670419712,(86825108,809036281800)), \
		(-13668734375,(29159975,157463797500)), \
		(18928915456,(11704752,40044541408)), \
		(-15542177536,(51239600,366782491408)), \
		(14045712320,(16050164,64301219792)), \
		(13155981606,(19958139,89162053965)), \
		(-19369351395,(35426331,210857602464)), \
		(10333266112,(17004308,70119440832)), \
		(10379228608,(84251876,773338033728)), \
		(-12618242775,(32263720,183261678515)), \
		(13869134848,(20551632,93168579104)), \
		(-16584790824,(10961577,36291887703)), \
		(-15257798400,(55245076,410620249976)), \
		(18954102464,(10908148,36026870016)), \
		(-18341972424,(75481362,655782151248)), \
		(-12574971648,(78883344,700612641456)), \
		(12815405312,(37805888,232455146128)), \
		(-16593430272,(89888512,852228957616)), \
		(11418006400,(21999084,103182702152)), \
		(-11388835305,(20830069,95068373302)), \
		(12269339730,(13483071,49508894871)), \
		(17203122368,(81287636,732886531232)), \
		(-12470739831,(73460710,629626041487)), \
		(11134817280,(52932496,385108904096)), \
		(14217688448,(26225996,134306795128)), \
		(-12392702720,(16136321,64819665729)), \
		(-12659408896,(65934416,535387522880)), \
		(-19473602040,(80138286,717397855704)), \
		(14172838912,(12251684,42883841304)), \
		(14149983312,(29270124,158356846044)), \
		(17131505832,(20165418,90554668092)), \
		(10724219136,(37763760,232066708944)), \
		(-16310117312,(66284732,539660034816)), \
		(-11386359375,(19084300,83370873625)), \
		(13475662336,(10335512,33227524992)), \
		(-10978950336,(22823980,109040307392)), \
		(16875607878,(23153787,111412277091)), \
		(-11265711104,(58675584,449454912160)), \
		(-14505761792,(75550848,656687901280)), \
		(12598934528,(16499012,67017297016)), \
		(-12025195264,(15657817,61957918557)), \
		(-16826144192,(93842648,909076394760)), \
		(12348502569,(10224711,32694640200)), \
		(-17926314120,(32787049,187738565273)), \
		(-13493737216,(29923273,163686793851)), \
		(14427394785,(35505486,211564693179)), \
		(-19274032896,(10241140,32773472152)), \
		(17292402688,(13700208,50709664960)), \
		(-19019494818,(18800379,81517322511)), \
		(-10647437500,(2200,-750)), \
		(10109526016,(42625392,278293189952)), \
		(10510781888,(18983012,82708031296)), \
		(15557608192,(13928952,51984953840)), \
		(-10071831924,(41447862,266841393498)), \
		(15741610560,(50697864,360981124152)), \
		(-16661194496,(34222193,200198931081)), \
		(11898638592,(81255904,732457431184)), \
		(-19889433792,(16330476,65993059872)), \
		(-19486656243,(80192007,718119342090)), \
		(-16251769044,(66879702,546942276558)), \
		(-16286194432,(21205993,97653524085)), \
		(-14328453447,(11422566,38605173993)), \
		(10002733056,(15775300,62656544584)), \
		(16771534848,(10526512,34152833024)), \
		(11916597952,(39739044,250510608944)), \
		(-14279692288,(74373392,641396201600)), \
		(12391818112,(14744492,56616722040)), \
		(10065736704,(29902948,163520048936)), \
		(10606335488,(51093352,365213307264)), \
		(-14190788992,(74875772,647905952216)), \
		(-18483214784,(10132152,32251695032)), \
		(-11361687040,(13613864,50231033248)), \
		(15902566656,(10147060,32322901784)), \
		(16508508264,(26169030,133869437208)), \
		(18895216576,(23025012,110484103952)), \
		(13227243584,(58333400,445528956328)), \
		(13638937728,(11933788,41225646760)), \
		(-13211236800,(17555676,73557394176)), \
		(17131278080,(26284616,134757347824)), \
		(-11361687040,(13613864,50231033248)), \
		(15295968396,(15239934,59494200030)), \
		(12268159744,(18613368,80304049424)), \
		(18743410944,(17694688,74432801296)), \
		(16043518400,(94264340,915210821680)), \
		(17213658112,(34519088,202809815328)), \
		(18859349888,(27982636,148024272312)), \
		(17708110208,(10901932,35996079576)), \
		(16114816000,(57937776,441004205024)), \
		(-16051355072,(10074888,31978665800)), \
		(18867118912,(25043868,125329154288)), \
		(17497933308,(15998562,63991372194)), \
		(13277760448,(25423812,128192023424)), \
		(15749797140,(10302741,33069617631)), \
		(12936906900,(15159645,59024667195)), \
		(18207956992,(23079984,110880009664)), \
		(-15158926528,(11161244,37287984016)), \
		(-12203894528,(78109712,690331283760)), \
		(-11694168000,(23600620,114652919600)), \
		(-11183659713,(16699933,68245197218)), \
		(-19795365312,(25719592,130435591624)), \
		(-19525940800,(47013524,322354850032)), \
		(-16936259584,(88209680,828465389696)), \
		(19058641408,(21423272,99158215584)), \
		(18186638562,(22526703,106916922567)), \
		(-19447465932,(20007693,89494330275)), \
		(15481340224,(12518220,44290835168)), \
		(13117517824,(61223748,479048924104)), \
		(-18005842944,(10420032,33635940768)), \
		(14454016192,(49161044,344692350624)), \
		(-16185729280,(15407816,60479978096)), \
		(12953104896,(11149432,37228806592)), \
		(-14117888000,(47059620,322829061800)), \
		(11775372736,(15188820,59195140144)), \
		(12706010560,(92714324,892730256528)), \
		(16618192146,(31369095,175692403539)), \
		(11275467264,(17294296,71920770560)), \
		(-15196314096,(15634080,61817081148)), \
		(-18504128256,(29927728,163723349936)), \
		(-17291552679,(46740592,319551832997)), \
		(18904299840,(13671436,50550004736)), \
		(-13518069120,(99755964,996341694168)), \
		(16569119744,(44015440,292016621088)), \
		(-16199641600,(26670440,137735303680)), \
		(-16849805312,(87759408,822130059200)), \
		(-11593585984,(12497444,44180619280)), \
		(-15416197992,(28196073,149721075945)), \
		(-13367484416,(69622320,580928571328)), \
		(-11312860160,(14730276,56534860696)), \
		(16130572480,(11926916,41190042576)), \
		(16325324416,(32670620,186739445304)), \
		(-12989245455,(71185266,600599779371)), \
		(-10008853632,(10635468,34684457640)), \
		(-19238030064,(77214600,678498886044)), \
		(-10508734375,(12935000,46521065125)), \
		(-17324680128,(47272408,325021124072)), \
		(-10844734375,(23790850,116041928625)), \
		(-10030481344,(45119164,303069035040)), \
		(10478548314,(11899863,41049979281)), \
		(-15680991232,(35058752,207584383424)), \
		(-19054837760,(13520976,49717818304)), \
		(-16239933000,(10692945,34966003725)), \
		(17490479872,(23111448,111106824208)), \
		(-11071671875,(23619575,114791073750)), \
		(11441629440,(11884416,40970075856)), \
		(16097959808,(16214732,65292705176)), \
		(-17308276480,(14871136,57347728176)), \
		(18860720896,(29131512,157233303568)), \
		(17703400704,(28044340,148514150552)), \
		(18249221025,(21166650,97381888605)), \
		(-17293314672,(17791488,75044420460)), \
		(19558561600,(13006700,46908407040)), \
		(13970888192,(25141352,126061637120)), \
		(-15924670208,(54418352,401437628400)), \
		(14901660315,(15141181,58916864584)), \
		(10839269888,(28818808,154708444800)), \
		(-18202912758,(33292927,192100266685)), \
		(-18789432624,(43494049,286843332295)), \
	];
	
	As_with_P0 = list(set(As_with_P0));

	for a, P0 in As_with_P0:
		print "a =",factor(a);
	
	print "Number of a's:",len(As_with_P0);
	#print "As_with_P0[0]:",As_with_P0[0];
	
	global my_mwBasis_for_mordellCurves;
	for a,P0 in As_with_P0:
		my_mwBasis_for_mordellCurves[a] = [P0];
	
	#n = 0;
	n = 100;
	#n = 10^5;
	numAs = 100;
	As = [As_with_P0[i][0] for i in range(numAs)];
	As.sort();
	print "len(set(As))=",len(set(As));
		
	computeSIntegralPointsForManymordellCurves(n,rank=None,maxA=None,As=As,verbose=True);
	
#time test_rank1mordellCurvesWithLargeA_ComputeSIntegralPoints();

def test_conjecture_about_Sb():
	for a in range(-10,1+10):
		if a == 0:
			continue;
		E = mordellCurve(a);
		if E.rank() != 1:
			continue;
		print "=====================================================";
		print "E:",E;
		P = E.gens()[0]
		for n in range(1,20):
			print n, factor(ZZ(sqrt((n*P).xy()[0].denominator()))), " - Height:",(n*P).height();

def test_conjecture_about_Sb_2():
	a = 3;
	E = mordellCurve(a);
	print "E:",E;
	P = E.gen(0);
	print "Generator P:",P;
	for n in range(1,1+5):
		print n,"* P =",n*P,"has sage-height:",(n*P).height(),"and the height we use is therefore:",(n*P).height()/2;
	'''
	E: Elliptic Curve defined by y^2 = x^3 + 3 over Rational Field
	1 1  - Height: 0.921919125128010
	2 2^2  - Height: 3.68767650051204
	3 3 * 13  - Height: 8.29727212615209
	4 2^3 * 11  - Height: 14.7507060020482
	5 64951  - Height: 23.0479781282003
	'''
	Sb5 = [2,3,13];
	
	S1 = [2,11];
	S2 = [2,64951];
	S3 = [2,11,64951];

	Ss = [Sb5,S1,S2,S3];
	for S in Ss:
		print "====================================================================";
		print "For S =",S,
		solutions = computeSIntegralPoints(E,S,verbose=False,bothSigns=True);
		print "there are",len(solutions),"S-integral points (bothsigns), namely:";
		print solutions;

def test_conjecture_about_Sb_3():
	E = mordellCurve(3);
	print "E:",E;
	P = E.gen(0);
	print "Generator P:",P;
	for n in range(1,1+5):
		print n,"* P =",n*P,"has sage-height:",(n*P).height();
	
	S = [64951];
	solutions = computeSIntegralPoints(E,S,verbose=True,bothSigns=True);
	print "Number of S-integral points:",len(solutions);
	print "solutions:",solutions;

########################################################################
### Testing some Thue equations: #######################################
########################################################################

def solveManyThueEquations(a,b,c,d,maxM,S,modOutSymmetry=True,saveToFile=True,saveToPath=pathData,in_parallel=True):

	t00 = walltime();

	solutions = [];

	F_is_symmetric = (a==d) and (b==c);
	modOutSymmetry = modOutSymmetry and F_is_symmetric; #can mod out by (x,y) ~ (y,x) only if F(x,y)=F(y,x).

	Ms = range(1,maxM+1);

	if in_parallel:
		parameters = [];
		for m in Ms:
			S=S;
			modOutSymmetry_m=modOutSymmetry;
			checkRelevantAbcTriples=False;
			verbose=True;
			mwBasesDict0=None;
			param = (a,b,c,d,m,S,modOutSymmetry_m,checkRelevantAbcTriples,verbose,mwBasesDict0);
			parameters.append(param);

		results = my_run_in_parallel(parameters,solveThueEquation,print_param=False,print_result=False,return_param_index=True);
		for i,solutions_for_m in results:
			param = parameters[i];
			m = param[4];
			solutions.append([m,solutions_for_m]);
			
	else:
		for m in Ms:
			print "----------------------------------------------";
			solutions_for_m = solveThueEquation(a,b,c,d,m=m,S=S,modOutSymmetry=modOutSymmetry);
			solutions_for_m = list(solutions_for_m);
			solutions_for_m.sort();
			solutions.append([m,solutions_for_m]);

	numSolutions = sum([len(sols) for (m,sols) in solutions]);
	totalTime = walltime(t00);

	solutions.sort(key = lambda (m,sols_m): m);

	if saveToFile:
		filename = "thue_"+myListToStr([a,b,c,d],"_");
		filename += "_maxM"+str(maxM);
		if S==primes_first_n(len(S)):
			filename += "_n"+str(len(S));
		else:
			filename += "_S_"+myListToStr(S,'_');
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);
	

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of pairs of S-integers (x,y) satisfying\n");
		out.write("# "+str(a)+"x^3 + "+str(b)+"x^2y + "+str(c)+"xy^2 + "+str(d)+"y^3 = m, where\n");
		out.write("# m = 1, ..., "+str(maxM)+" and\n");
		if S==primes_first_n(len(S)):
			out.write("# S is the set of the first "+str(len(S))+" primes.\n");
		else:
			out.write("# S = {"+myListToStr(S,',')+"}.\n");
		if modOutSymmetry:
			out.write("# For each solution (x,y), only one of (x,y), (y,x) is listed.\n");
		out.write("# It contains "+str(numSolutions)+" pairs in total.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		#out.write("###\n");
		for m,sols in solutions:
			out.write("#\n");
			out.write("# m = "+str(m)+":\n");
			out.write("#\n");
			for (x,y) in sols:
				out.write("(%s,%s)\n" % (str(x),str(y)));
		out.close();

	print "Number of solutions:",numSolutions;

	return solutions;

def testThue(a=None,b=None,c=None,d=None,S=None):
	'''
	Solve some quartic Thue equations over S-integers.
	'''
	if a==None or b==None or c==None or d==None:
		#a,b,c,d = var("a","b","c","d");
		#a,b,c,d = (1,0,0,1); #not prime
		#a,b,c,d = (1,1,1,1); #not prime
		#a,b,c,d = (1,-1,-1,1); #not prime
		#a,b,c,d = (1,0,0,2); #prime
		a,b,c,d = (1,2,3,4); #prime
	R.<x,y> = QQ[];
	f = a*x^3 + b*x^2*y + c*x*y^2 + d*y^3;
	print "f =",f;
	print "f is prime:",f.is_prime();
	if not f.is_prime():
		print "f =",factor(f);
		sleep(3);

	maxM = 100;
	if S==None:
		S = primes_first_n(100);
	solveManyThueEquations(a,b,c,d,maxM,S,saveToFile=True);

#time testThue(0,1,1,0);
#time testThue(1,0,0,1);
#time testThue(1,0,0,2);
#time testThue(1,2,3,4);

#time solveThueEquation(1,-23,5,24,m=1,S=[2,3,5,7],modOutSymmetry=False);

def computeMWBasesForThueEquationsForDiscriminantInARange(deltaMax=10000,inMagmaUseHeegnerPointIfRank1=True,cacheFileName=None):
	global pathMordellWeil;	
	#delta is the discriminant of f:
	#deltaMax = 10000;
	m = 1;
	#Deltas = range(-deltaMax,deltaMax+1);
	Deltas = [delta for delta in range(-deltaMax,deltaMax+1) if delta % 4 in [0,3]];
	Deltas.remove(0);
	Deltas.sort(key = abs);
	ranks = {};
	min_delta_of_rank = {};
	mwBasesDict = load_full_mwBasisCache_as_dict();
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwSubbases.sobj"));
	mwSubbasesDict = mwBasesDict;
	for delta in Deltas:
		print "====================================";
		print "discriminant delta =",delta;

		a = 432 * delta * m^2;
		E = mordellCurve(a);

		mwBasis = mwBasisViaCacheMagmaOrSage(a,mwBasesDict=mwBasesDict,mwSubbasesDict=mwSubbasesDict,cacheFileName=cacheFileName,inMagmaUseHeegnerPointIfRank1=inMagmaUseHeegnerPointIfRank1);
		print "mwBasis:",mwBasis;
		r = len(mwBasis);
		print "RANK =",r;
		#ranks[delta] = len(mwBasis);
		if ranks.has_key(r):
			ranks[r] += 1;
		else:
			ranks[r] = 1;
			min_delta_of_rank[r] = delta;

		#So war we managed to find the MW-Basis for |delta|<=1200 except for delta=-755.
		#For most of them we used the standard magma algorithm.
		#For a = -858, -818, -727, -687, 558 we used sage's two_decent instead,
		# and for a=-755 we used magma's HeegnerPoint method.

		#For |delta|<5448 with delta=0,-1 mod 4, we computed more:
		#Magma did mostly all the job, except for
		#delta = -2316, -2716, -3005, -3292, -3293, -3720, -4629, -4796,
		#-5016, -5160, -5237, -5421, -5553, -5889, -6749, -6876, -7149,
		#-8008, 8124, -8333, -8584, -8760
		# where we used sage's two_decent again.
		#and for
		#delta = -3432, -4520, -4616, -5448, -8360, -8409, -9333
		# using magma's HeegnerPoint method.

		#Find all binary cubics with discriminant delta:
		#TODO

	print "ranks:",ranks;
	print "min_delta_of_rank:",min_delta_of_rank;

	return;
		
#time computeMWBasesForThueEquationsForDiscriminantInARange(deltaMax=100000,cacheFileName="mwThue.sobj");

def discriminantOfBinaryCubic(a,b,c,d):
	#F = ax^3 + bx^2y + cxy^2 + dy^3
	#Discriminant of F:
	D = 27*a^2*d^2 + 4*a*c^3 - 18*a*b*c*d + 4*b^3*d - b^2*c^2;
	#Note the sign convention! We use the opposite sign as Bennett-Ghadermarzi and Belabas.
	return D;

def is_irreducible_binary_cubic_over_Z(a,b,c,d):
	a,b,c,d = ZZ(a),ZZ(b),ZZ(c),ZZ(d);
	if a==0 or d==0:
		return False;
	if gcd([a,b,c,d]).is_unit() == False:
		return False;
	R.<x> = ZZ[];
	f = a*x^3 + b*x^2 + c*x + d;
	if f.is_irreducible() == False:
		return False;
	return True;		

def allThueEquationsWithBoundedDiscriminant(only_irreducible_forms=False,DeltaMax=100):
	#Computes all binary cubics over ZZ with discriminant D!=0 and |D|<=DeltaMax.
	#Some of the reducible forms may be equivalent (over SL2(Z))!

	print "Warning: This algorithm was not yet made numerically stable!";

	def is_reduced_form_BG(a,B,C,d):
		b = 3*B;
		c = 3*C;

		P = b^2 - 3*a*c;
		Q = b*c - 9*a*d;
		R = c^2 - 3*b*d;
		
		#Discriminant of F: (note that B-G use the opposite sign!)
		D = 27*a^2*d^2 + 4*a*c^3 - 18*a*b*c*d + 4*b^3*d - b^2*c^2;
		if D==0:
			return False;
		if D<0:
			if abs(B*C-a*d) > B^2 - a*C:
				return False;
			if B^2 - a*C > C^2 - B*d:
				return False;
			if a<=0:
				return False;
			if B<0:
				return False;
			if B==0 and d>=0:
				return False;
			if B*C == a*d and d>=0:
				return False;
			if B^2 - a*C == B*C - a*d and B>=abs(a-B):
				return False;
			if B^2 - a*C == C^2 - B*d and (a>abs(d) or B>=abs(C)):
				return False;
			return True;
		else:
			#D>0:
			print "TODO";
			return True;

	def is_reduced_form_Belabas(a,b,c,d):
		P = b^2 - 3*a*c;
		Q = b*c - 9*a*d;
		R = c^2 - 3*b*d;
		
		#Discriminant of F: (note that B-G use the opposite sign!)
		D = 27*a^2*d^2 + 4*a*c^3 - 18*a*b*c*d + 4*b^3*d - b^2*c^2;
		if D==0:
			return False;
		if D<0:
			if abs(Q) > P:
				return False;
			if P > R:
				return False;
			if R<=0:
				return False;
			if a<=0:
				return False;
			if b<0:
				return False;
			if b==0 and d>=0:
				return False;
			#if b==0 and d>0: #meine abgeschwaechte Version!
			#	return False;
			if Q==0 and d>=0:
				return False;
			#if Q==0 and d>0: #meine abgeschwaechte Version!
			#	return False;
			if P==Q and b>=abs(3*a-b):
				return False;
			#if P==Q and b>abs(3*a-b): #meine abgeschwaechte Version!
			#	return False;
			if P==R:
				if a>abs(d):
					return False;
				if a==abs(d) and b>=abs(c):
					return False;
				#if a==abs(d) and b>abs(c): #meine abgeschwaechte Version!
				#	return False;					
			return True;
		else:
			#D>0:
			if d^2 - a^2 + a*c - b*d <= 0:
				return False;
			if -(a-b)^2 - a*c >= a*d - b*c:
				return False;
			if a*d - b*c >= (a+b)^2 + a*c:
				return False;
			if a<=0:
				return False;
			if b<0:
				return False;
			if b==0 and d<=0:
				return False;
			return True;

	#we use and Belabas use F = ax^3 + bx^2y + cxy^2 + dy^3
	#b = 3B, c = 3C.
	#B-G uses ax^3 + 3Bx^2y + 3Cxy^2 + dy^3

	#B-G and Belabas use negative of our discriminant!

	R.<x> = RR[];

	QX.<X> = QQ[];

	'''
	#Negative discriminants, using B-G:
	a_min = 1;
	a_max = RR(DeltaMax^(1/4)*2/3/sqrt(3)).floor()
	for a in range(a_min,a_max+1):
		B_min = 0;
		B_max = RR(a/2+sqrt(sqrt(DeltaMax)-27*a^2/4)/3).floor();
		for B in range(B_min,B_max+1):
			poly = -4*x^3 + (3*a+6*B)^2*x^2 + 27*a^2*DeltaMax;
			roots = poly.roots(multiplicities=False);
			pos_root = max([root for root in roots if root in RR]);
			C_min = RR((9*B^2 - pos_root)/9/a).ceil();
			C_max = B-a;
			for C in range(C_min,C_max+1):
				#d_min = RR(((3*a+B)*C-B^2)/9/a).ceil(); #according to published BG paper.
				#d_max = RR(((3*a-B)*C-B^2)/9/a).floor(); #according to published BG paper.
				d_min = RR((B*C - abs(B^2-a*C))/a).ceil();
				d_max = RR((B*C + abs(B^2-a*C))/a).floor();				
				for d in range(d_min,d_max+1):
					b = 3*B;
					c = 3*C;
					#Discriminant of F:
					D = discriminantOfBinaryCubic(a,b,c,d);
					#print "D:",D;
					if -DeltaMax<=D and D<=0:
						if is_reduced_form_BG(a,B,C,d):
							print "a,b,c,d,D:",a,b,c,d,D
							#print "is reduced:",is_reduced_form(a,B,C,d);
	'''
	
	DeltasBelabas = set([]);
	IrreducibleForms = set([]);

	#Irreducible forms with negative discriminants, using Belabas:
	a_min = 1;
	a_max = RR(DeltaMax^(1/4)*2/3/sqrt(3)).floor()
	for a in range(a_min,a_max+1):
		b_min = 0;
		b_max = RR(3*a/2+sqrt(sqrt(DeltaMax)-27*a^2/4)).floor();
		for b in range(b_min,b_max+1):
			poly = -4*x^3 + (3*a+2*b)^2*x^2 + 27*a^2*DeltaMax;
			roots = poly.roots(multiplicities=False);
			pos_root = max([root for root in roots if root in RR]);
			c_min = RR((b^2 - pos_root)/3/a).ceil();
			c_max = b-3*a;
			for c in range(c_min,c_max+1):
				#Using |Q|<=P:
				d_min = RR((b*c - abs(b^2-3*a*c))/9/a).ceil();
				d_max = RR((b*c + abs(b^2-3*a*c))/9/a).floor();				
				for d in range(d_min,d_max+1):
					#Discriminant of F:
					D = discriminantOfBinaryCubic(a,b,c,d);
					#print "D:",D;
					if -DeltaMax<=D and D<=0:
						if is_reduced_form_Belabas(a,b,c,d):
							if is_irreducible_binary_cubic_over_Z(a,b,c,d):
								DeltasBelabas.add(D);
								IrreducibleForms.add((a,b,c,d));
								print "a,b,c,d,D:",a,b,c,d,D

	#Irreducible forms with positive discriminants, using Belabas:
	a_min = 1;
	a_max = RR((16/27*DeltaMax)^(1/4)).floor()
	for a in range(a_min,a_max+1):
		b_min = 0;
		b_max = RR(3*a/2+sqrt(sqrt(DeltaMax/3)-3/4*a^2)).floor();
		for b in range(b_min,b_max+1):
			c_min = 1-b;
			c_max = (DeltaMax/4/a)^(1/3);
			if a>=2*b/3:
				c_max += b^2/3/a;
			else:
				c_max += b - 3*a/4;
			c_max = RR(c_max).floor();
			for c in range(c_min,c_max+1):
				#Using |Q|<=P:
				d_min = RR((-(a-b)^2-a*c+b*c)/a).ceil();
				d_max = RR((+(a+b)^2+a*c+b*c)/a).floor();				
				for d in range(d_min,d_max+1):
					#Discriminant of F:
					D = discriminantOfBinaryCubic(a,b,c,d);
					#print "D:",D;
					if 0<=D and D<=DeltaMax:
						if is_reduced_form_Belabas(a,b,c,d):
							if is_irreducible_binary_cubic_over_Z(a,b,c,d):
								DeltasBelabas.add(D);
								IrreducibleForms.add((a,b,c,d));
								print "a,b,c,d,D:",a,b,c,d,D

	DeltasBelabasList = list(DeltasBelabas);
	DeltasBelabasList.sort();	
	print "DeltasBelabas:",DeltasBelabasList;
	print "len(DeltasBelabas):",len(DeltasBelabasList);				

	'''
	print "Mein aproximativer Algorithmus zum Testen:";
	DeltasTest = set([]);
	X = RR(DeltaMax^(1/3)).ceil();
	X += 3-(X % 3);
	for a in range(-X,X):
		for b in range(-X,X,1):
			for c in range(-X,X,1):
				for d in range(-X,X):
					#Discriminant of F:
					D = 27*a^2*d^2 + 4*a*c^3 - 18*a*b*c*d + 4*b^3*d - b^2*c^2;
					P = b^2 - 3*a*c;
					Q = b*c - 9*a*d;
					R = c^2 - 3*b*d;
					if -DeltaMax<=D and D<=DeltaMax:
							#if is_irreduzible_binary_cubic_over_Z(a,b,c,d):
							DeltasTest.add(D);
							if D==-1:
								print "a,b,c,d,D:",a,b,c,d,D,"!!!!!!!!";
								print "P,Q,R:",P,Q,R;
							if is_reduced_form_Belabas(a,b,c,d):
								print "a,b,c,d,D:",a,b,c,d,D

	DeltasTestList = list(DeltasTest);
	DeltasTestList.sort();	
	print "DeltasTest:   ",DeltasTestList;
	print "len(DeltasTest):",len(DeltasTest);				
	'''

	IrreducibleFormsList = list(IrreducibleForms);
	IrreducibleFormsList.sort(key=lambda x: discriminantOfBinaryCubic(x[0],x[1],x[2],x[3]));
	print "Irreducible forms:";
	for (a,b,c,d) in IrreducibleFormsList:
		print "a,b,c,d,D:",a,b,c,d,discriminantOfBinaryCubic(a,b,c,d);
	print "Number of irreducible forms:",len(IrreducibleForms);

	if only_irreducible_forms:
		return IrreducibleFormsList;

	print "Now consider the reducible (over ZZ) forms:";
	
	#Now add forms that have at least one linear factor, but gcd(a,b,c,d)=1:
	#We may assume that this linear factor is x, i.e. d=0:
	#f = x(ax^2+bx+c), gcd(a,b,c)=1.

	AllForms = IrreducibleForms;
	DeltasReducible = set([]);
	
	#First go through all primitive "reduced" (in our sense) reducible (over ZZ) forms.
	#The non-primitive ones are added below.

	#Irreducible over ZZ <=> irreducible over QQ and primitive.
	#So primitive and reducible implies that f splits as a product of a linear and a quadratic factor (over ZZ).
	#As f is primitive, we may change the coordinates (x,y) unimodularly such that the linear factor is x.
	#In other words we may assume d=0.

	d = 0;
	
	#With d=0, D = -c^2(b^2-4*a*c).
	#Let D2 = b^2-4*a*c. Then D = -c^2*D2
	#We have c!=0 because D!=0 (as we only consider D!=0 here).
	#We may assume c>0 via (x,y)->(-x,y).

	c_min = 1;
	c_max = RR(sqrt(DeltaMax)).floor();
	for c in range(c_min,1+c_max):
		#For any integral alpha, we have
		#f(y=alpha*x+y) = (a+b*alpha+c*alpha^2)*x^3 + (b+2*c*alpha)*x^2*y + c*x*y^2.
		#So we may assume -c < b <= c.
		#We further may assume 0<=b<=c using (x,y)->(x,-y), which leaves c and d=0 fixed.
		b_min = 0;
		b_max = c;
		for b in range(b_min,1+b_max):
			#Now a is bounded using the discriminant.
			#|b^2-4ac| <= maxDelta/c^2
			a_min = ((b^2 - DeltaMax/c^2)/(4*c)).ceil();
			a_max = ((b^2 + DeltaMax/c^2)/(4*c)).floor();
			for a in range(a_min,1+a_max):
				D = discriminantOfBinaryCubic(a,b,c,d);
				#print "D:",D,"with a,b,c,d:",a,b,c,d;
				if -DeltaMax<=D and D<=DeltaMax and D!=0:
					#Check primitivity:
					if gcd([a,b,c,d]).is_unit():
						DeltasReducible.add(D);
						AllForms.add((a,b,c,d));
						print "a,b,c,d,D:",a,b,c,d,D

	DeltasReducibleList = list(DeltasReducible);
	DeltasReducibleList.sort();	
	print "DeltasReducible:",DeltasReducibleList;
		
	

	#Allow furthermore an integral factor, i.e. add the remaining non-primitive forms:
	print "Add non-primitive forms:";
	AllFormsList = list(AllForms);
	for (a,b,c,d) in AllFormsList:
		D = discriminantOfBinaryCubic(a,b,c,d);
		f = 2;
		while abs(D)*f^4 <= DeltaMax:
			fa = f*a;
			fb = f*b;
			fc = f*c;
			fd = f*d;
			if (fa,fb,fc,fd) not in AllForms:
				print "a,b,c,d,D:",fa,fb,fc,fd,f^4*D,"with f =",f;
				AllForms.add((fa,fb,fc,fd));
			f += 1;

	AllFormsList = list(AllForms);
	AllFormsList.sort(key=lambda x: discriminantOfBinaryCubic(x[0],x[1],x[2],x[3]));
	#print "All forms:";
	#for (a,b,c,d) in AllFormsList:
	#	print "a,b,c,d,D:",a,b,c,d,discriminantOfBinaryCubic(a,b,c,d);
	print "Number of all forms:",len(AllForms);

	Deltas = set([]);
	for (a,b,c,d) in AllFormsList:
		D = discriminantOfBinaryCubic(a,b,c,d);
		Deltas.add(D);
	DeltasList = list(Deltas);
	DeltasList.sort();
	#print "Discriminants:",DeltasList;
	print "Number of discriminants:",len(DeltasList);
	
	return AllFormsList;
	
#allThueEquationsWithBoundedDiscriminant();

def solveAllThueEquationsWithBoundedDiscriminant(S=[],maxDelta=1000,only_irreducible_forms=False,saveToFile=True,saveToPath=pathData,in_parallel=True):
	t00 = walltime();
	forms = allThueEquationsWithBoundedDiscriminant(only_irreducible_forms,DeltaMax=maxDelta);
	
	solutions = [];

	if in_parallel:
		mwBasesDict = load_full_mwBasisCache_as_dict();
		parameters = [];
		for (a,b,c,d) in forms:
			m=1;
			S=S;
			modOutSymmetry=False;
			checkRelevantAbcTriples=False;
			verbose=True;

			mwBasesDict0 = {};
			D = discriminantOfBinaryCubic(a,b,c,d);
			k = 432*m^2*D
			k6 = sixthPowerFreeK(k);
			k27 = sixthPowerFreeK(-27*k);
			for key in [k,k6,k27]:
				if mwBasesDict.has_key(key):
					mwBasesDict0[key] = mwBasesDict[key];

			param = (a,b,c,d,m,S,modOutSymmetry,checkRelevantAbcTriples,verbose,mwBasesDict0);
			parameters.append(param);

		'''
		gen = solveThueEquation(parameters);
		for x in gen:
			a = x[0][0][0];
			b = x[0][0][1];
			c = x[0][0][2];
			d = x[0][0][3];
			solutions_for_abcd = x[1];
			solutions_for_abcd = list(solutions_for_abcd);
			solutions_for_abcd.sort();
			D = discriminantOfBinaryCubic(a,b,c,d);
			solutions.append((a,b,c,d,D,solutions_for_abcd));		
			if verbose:
				print "Done for a,b,c,d,D =",a,b,c,d,D;
				print "Output: ",solutions_for_abcd;
		'''
		results = my_run_in_parallel(parameters,solveThueEquation,print_param=False,print_result=False,return_param_index=True);
		for i,solutions_for_abcd in results:
			param = parameters[i];
			a,b,c,d = param[0],param[1],param[2],param[3];
			D = discriminantOfBinaryCubic(a,b,c,d);
			solutions.append((a,b,c,d,D,solutions_for_abcd));
			
	else:
		mwBasesDict = load_full_mwBasisCache_as_dict();
		for (a,b,c,d) in forms:
			print "============================";
			D = discriminantOfBinaryCubic(a,b,c,d);
			print "a,b,c,d,D:",a,b,c,d,D;
			solutions_for_abcd = solveThueEquation(a,b,c,d,m=1,S=S,modOutSymmetry=False,checkRelevantAbcTriples=False,verbose=True,mwBasesDict=mwBasesDict);
			solutions_for_abcd = list(solutions_for_abcd);
			solutions_for_abcd.sort();
			solutions.append((a,b,c,d,D,solutions_for_abcd));

	numSolutions = sum([len(sols) for (a,b,c,d,D,sols) in solutions]);
	totalTime = walltime(t00);

	solutions.sort(key=lambda (a,b,c,d,D,sol): D);

	if saveToFile:
		filename = "thue_"; #+myListToStr([a,b,c,d],"_");
		filename += "_maxD"+str(maxDelta);
		if S==primes_first_n(len(S)):
			filename += "_n"+str(len(S));
		else:
			filename += "_S_"+myListToStr(S,'_');
		if only_irreducible_forms:
			filename += "_irr";
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);
	
		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of pairs of S-integers (x,y) satisfying cubic Thue equations\n");
		out.write("# f(x,y) = 1, where\n");
		if only_irreducible_forms:
			out.write("# f = a*x^3 + b*x^2*y + c*x*y^2 + d*y^3 is any reduced irreducible binary cubic\n");
		else:
			out.write("# f is any reduced binary cubic with non-zero discriminant\n");
		out.write("# with discriminant bounded by |D(f)| <= "+str(maxDelta)+",\n");
		if S==primes_first_n(len(S)):
			out.write("# S is the set of the first "+str(len(S))+" primes.\n");
		else:
			out.write("# S = {"+myListToStr(S,',')+"}.\n");
		#if modOutSymmetry:
		#	out.write("# For each solution (x,y), only one of (x,y), (-x,-y) is listed.\n");
		out.write("# Note that some GL_2(Z)-equivalence classes of forms may have several reduced representatives.\n");
		out.write("# It contains "+str(numSolutions)+" pairs in total.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		#out.write("###\n");
		R.<x,y> = QQ[];
		for a,b,c,d,D,sols in solutions:
			out.write("#\n");
			out.write("# (a,b,c,d) = ("+str(a)+","+str(b)+","+str(c)+","+str(d)+") and D = "+str(D)+":\n");
			out.write("#\n");
			for (x,y) in sols:
				out.write("(%s,%s)\n" % (str(x),str(y)));
		out.close();

	print "Number of solutions:",numSolutions;

	return solutions;
		
#time solveAllThueEquationsWithBoundedDiscriminant(S=primes_first_n(0),maxDelta=10000,only_irreducible_forms=False,in_parallel=True);
#time solveAllThueEquationsWithBoundedDiscriminant(S=primes_first_n(100),maxDelta=10000,only_irreducible_forms=False,in_parallel=True);

########################################################################
### Testing some Thue-Mahler equations: ################################
########################################################################

#### works:
#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3],modOutSymmetry=True,verbose=True);
#Thue-Mahler equation has 3 ordered primitive solutions: set([(1, 0), (1, 1), (2, 1)])

#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,5],modOutSymmetry=True,verbose=True);
#Thue-Mahler equation has 3 ordered primitive solutions: set([(1, 0), (1, 1), (2, 1)])

#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,7],modOutSymmetry=True,verbose=True);
#Thue-Mahler equation has 14 ordered primitive solutions: set([(5, 4), (3, 1), (11, -2), (37, 17), (2, -1), (1, 1), (2, 1), (4, -1), (5, -3), (5, 1), (20, -17), (71, -23), (1, 0), (13, 11)])

#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,5,7],modOutSymmetry=True,verbose=True);
#Thue-Mahler equation has 19 ordered primitive solutions: set([(3, 2), (3, 1), (13, 2), (11, -2), (37, 17), (2, -1), (5, 4), (87, -62), (4, -1), (71, -23), (1, 1), (2, 1), (5, -3), (19, 1), (5, 1), (1, 0), (13, 11), (20, -17), (683, 397)])

#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,5,7,11],modOutSymmetry=True,verbose=True);
#Thue-Mahler equation has 21 ordered primitive solutions: set([(8, 3), (3, 1), (13, 2), (11, -2), (37, 17), (2, -1), (3, 2), (87, -62), (4, -1), (71, -23), (1, 1), (2, 1), (5, -3), (19, 1), (5, 4), (5, 1), (1, 0), (13, 11), (94, 71), (20, -17), (683, 397)])
#took 1 hour

#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,5,7,11,13],modOutSymmetry=True,verbose=True);
#Thue-Mahler equation has 86 ordered primitive solutions: set([(17, -12), (608, -311), (53, 17), (8, 5), (11, 5), (103, -101), (75, 53), (1, 1), (3, 2), (7, 5), (248, 127), (16, -1), (3, 1), (94, 23), (107, -74), (337, 191), (4033, 3527), (19, 8), (23, 22), (2, 1), (6, -5), (5, 1), (4, -1), (7, 2), (8, -7), (43, -25), (190, -163), (19, 11), (31, -19), (1621, 1349), (4, 1), (71, -23), (5, -2), (5, 4), (913, -313), (2, -1), (17, 1), (15, 7), (20, -17), (8, 3), (1241, -431), (89, 19), (3, -1), (87, -55), (19, 1), (94, 71), (97, -31), (128, 97), (181, 107), (1, 0), (231191, 77689), (47, -20), (179, 61), (31, -6), (29, -9), (7957, 491), (13, 2), (127, -121), (30746, 14629), (179, 118), (23, 1), (5, -3), (683, 397), (191, -146), (323, -37), (6544, 3257), (88, -43), (197, -32), (17, 16), (3287, -3257), (41, -5), (11, -2), (87, -62), (123, -2), (13, 11), (27, 23), (141, -137), (2752, -79), (9, -1), (10, 1), (50, 31), (22, -1), (73, 15), (37, 17), (4, 3), (11, -8)])
#Time: CPU 789.97 s, Wall: 221765.59 s

#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,5,7,11,13,17],modOutSymmetry=True,verbose=True);

#time solveThueMahlerEquation(1,0,0,3,m=1,S=[2,3,5,7,11],modOutSymmetry=True,verbose=True);
#time solveThueMahlerEquation(1,0,0,2,m=1,S=[2,3,5,7,11,13,17],modOutSymmetry=True,verbose=True);
#time solveThueMahlerEquation(1,0,0,3,m=1,S=[2,3,5,7,11,13,17],modOutSymmetry=True,verbose=True);

#Example from [Tzanakis-de Weger 92, Compositio]:
#time solveThueMahlerEquation(1,-23,5,24,m=1,S=[2,3,5,7],modOutSymmetry=True,verbose=True);
#Obtain 72 solutions, takes 1 day for the MW-bases, and 63 seconds for the rest.

#Example from [Tzanakis-de Weger 91, Math of computation]:
#time solveThueMahlerEquation(1,0,-3,-1,m=1,S=[3,17,19],modOutSymmetry=True,verbose=True);
#Obtain 78 solutions, takes 2-3 minutes to compute MW bases and 20 seconds to compute the solutions.

#Example from [Agrawal, Coates, Hunt, and van der Porten]:
#time solveThueMahlerEquation(1,-1,1,1,m=1,S=[11],modOutSymmetry=True,verbose=True);
#1.25 seconds!!! Hambrook's implementation takes "a couple of minutes"; [ACHP] is "by hand" using linear forms in logarithms.
#Obtain 7 solutions, agrees with [ACHP].

#Example from [Hambrook] with a lot (208) solutions:
#time solveThueMahlerEquation(1,1,-2,-1,m=1,S=[7,13,29,41],modOutSymmetry=True,verbose=True);

#### doesn't work: (as at least one Mordell-Weil basis cannot be computed with standard sage method)
#time solveThueMahlerEquation(1,0,0,1,m=1,S=[3,5,7],modOutSymmetry=True,verbose=True);
#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,11],modOutSymmetry=True,verbose=True);
#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,13],modOutSymmetry=True,verbose=True);
#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,17],modOutSymmetry=True,verbose=True);
#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,19],modOutSymmetry=True,verbose=True);
#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,23],modOutSymmetry=True,verbose=True);
#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,29],modOutSymmetry=True,verbose=True);
#time solveThueMahlerEquation(1,0,0,1,m=1,S=[2,3,31],modOutSymmetry=True,verbose=True);

def computeMWBasesForThueMahlerEquationsForDiscriminantInARange(Deltas=None,deltaMax=10000,deltaMin=0,n=None,S=None,m=1,cacheFileName=None,inMagmaUseHeegnerPointIfRank1=True,onlyPositiveDeltas=False,useSageRankBound=False,useSageRank=False,randomOrder=False,printAnalyticRank=False,reverseExponents=False,useMagma=True):
	global pathMordellWeil;
	#delta is the discriminant of f:
	#deltaMax = 100;
	#n = 4;
	if n!=None:
		S = primes_first_n(n);
	else:
		n = len(S);
	#m = 1;
	if Deltas == None:
		Deltas = [delta for delta in range(-deltaMax,1-deltaMin)+range(deltaMin,deltaMax+1) if delta % 4 in [0,3]];
		if onlyPositiveDeltas:
			Deltas = [delta for delta in Deltas if delta > 0];
		while 0 in Deltas:
			Deltas.remove(0);
	Deltas.sort(key = abs);
	ranks = {};
	#min_delta_of_rank = {};
	mwBasesDict = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwSubbases.sobj"));
	#mwSubbasesDict.update(dict(load(pathMordellWeil+"mwAll.sobj")));
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwAll.sobj"));
	mwSubbasesDict = mwBasesDict;
	if randomOrder:
		Deltas.sort(key = lambda x: randint(1,100000));
	for delta in Deltas:
		print "====================================";
		print "discriminant delta =",delta;
		Exponents = [w for w in Words([0,1,2],len(S))];
		if reverseExponents:
			Exponents.reverse();			
		for exponents in Exponents:
			if verbose:
				print "---------------------------------------------- delta =",delta;
				print "exponents:",exponents;
			z = prod([S[i]^exponents[i] for i in range(len(S))]);
			M = m*z;
			a = 432*M^2*delta;
			print "a =",a,"=",factor(a);

			E = mordellCurve(a);
			if printAnalyticRank:
				print "E.analytic_rank():",E.analytic_rank();

			mwBasis = mwBasisViaCacheMagmaOrSage(a,mwBasesDict=mwBasesDict,mwSubbasesDict=mwSubbasesDict,cacheFileName=cacheFileName,inMagmaUseHeegnerPointIfRank1=inMagmaUseHeegnerPointIfRank1,useSageRankBound=useSageRankBound,useSageRank=useSageRank,useMagma=useMagma);
			print "mwBasis:",mwBasis;
			r = len(mwBasis);
			print "RANK =",r;
			if ranks.has_key(r):
				ranks[r] += 1;
			else:
				ranks[r] = 1;
				#min_delta_of_rank[r] = delta;

			#We use magma's standard method, except for a few times we use
			#sage's two_decent method:
			#
			#and a few times we take magmas HeegnerPoint method:
			#

	print "ranks:",ranks;
	print "min_delta_of_rank:",min_delta_of_rank;

	return;
		
#time computeMWBasesForThueMahlerEquationsForDiscriminantInARange(deltaMax=10000,n=2,cacheFileName="mwThueMahlerN2.sobj");
#time computeMWBasesForThueMahlerEquationsForDiscriminantInARange(deltaMax=10000,n=3,cacheFileName="mwThueMahlerN3.sobj");
#time computeMWBasesForThueMahlerEquationsForDiscriminantInARange(deltaMax=10000,n=4,cacheFileName="mwThueMahlerN4.sobj");
#time computeMWBasesForThueMahlerEquationsForDiscriminantInARange(deltaMax=10000,n=5,cacheFileName="mwThueMahlerN5.sobj");
#time computeMWBasesForThueMahlerEquationsForDiscriminantInARange(deltaMax=10000,n=6,cacheFileName="mwThueMahlerN6.sobj");
#time computeMWBasesForThueMahlerEquationsForDiscriminantInARange(deltaMax=10000,n=6,cacheFileName="mwThueMahlerN6.sobj",onlyPositiveDeltas=True);
#time computeMWBasesForThueMahlerEquationsForDiscriminantInARange(Deltas=[-4],n=6,cacheFileName="mwThueMahlerN6.sobj",inMagmaUseHeegnerPointIfRank1=True);

def solveAllThueMahlerEquationsWithBoundedDiscriminant(S=[],maxDelta=1000,only_irreducible_forms=False,saveToFile=True,saveToPath=pathData,in_parallel=True):
	t00 = walltime();
	forms = allThueEquationsWithBoundedDiscriminant(only_irreducible_forms,DeltaMax=maxDelta);
	
	solutions = [];

	print "Solve all Thue-Mahler equations with S =",S," and 1 <= |D| <=",maxDelta;

	if in_parallel:
		parameters = [];
		for (a,b,c,d) in forms:
			m=1;
			S=S;
			modOutSymmetry=False;
			verbose_abcd=True;
			saveToFile_abcd=False;
			saveToPath_abcd=pathData;
			makeLog=False;
			mwBasesDict_abcd = None;
			param = (a,b,c,d,m,S,modOutSymmetry,verbose_abcd,saveToFile_abcd,saveToPath_abcd,makeLog,mwBasesDict_abcd);
			parameters.append(param);

		results = my_run_in_parallel(parameters,solveThueMahlerEquation,print_param=False,print_result=False,return_param_index=True);
		print "results:",results;

		for i,solutions_for_abcd in results:
			param = parameters[i];
			a,b,c,d = param[0],param[1],param[2],param[3];
			D = discriminantOfBinaryCubic(a,b,c,d);
			solutions_for_abcd = list(solutions_for_abcd);
			solutions_for_abcd.sort();
			solutions.append((a,b,c,d,D,solutions_for_abcd));

		print "solutions:",solutions;
			
	else:
		mwBasesDict = load_full_mwBasisCache_as_dict();
		for (a,b,c,d) in forms:
			print "============================";
			D = discriminantOfBinaryCubic(a,b,c,d);
			print "a,b,c,d,D:",a,b,c,d,D;
			solutions_for_abcd = solveThueMahlerEquation(a,b,c,d,m=1,S=S,modOutSymmetry=False,verbose=True,saveToFile=False,saveToPath=pathData,makeLog=False,mwBasesDict=mwBasesDict);
			solutions_for_abcd = list(solutions_for_abcd);
			solutions_for_abcd.sort();
			solutions.append((a,b,c,d,D,solutions_for_abcd));

	numSolutions = sum([len(sols) for (a,b,c,d,D,sols) in solutions]);
	totalTime = walltime(t00);

	solutions.sort(key=lambda (a,b,c,d,D,sol): D);

	print "sorted solutions:",solutions;

	if saveToFile:
		filename = "thueMahler_"; #+myListToStr([a,b,c,d],"_");
		filename += "_maxD"+str(maxDelta);
		if S==primes_first_n(len(S)):
			filename += "_n"+str(len(S));
		else:
			filename += "_S_"+myListToStr(S,'_');
		if only_irreducible_forms:
			filename += "_irr";
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all primitive integral solutions of the Thue-Mahler equations\n");
		out.write("# f(x,y) = z, where\n");
		if only_irreducible_forms:
			out.write("# f = a*x^3 + b*x^2*y + c*x*y^2 + d*y^3 is any reduced irreducible binary cubic\n");
		else:
			out.write("# f is any reduced binary cubic with non-zero discriminant\n");
		out.write("# with discriminant bounded by |D(f)| <= "+str(maxDelta)+",\n");
		out.write("# such that only primes dividing z are among S, where\n");
		if S==primes_first_n(len(S)):
			out.write("# S is the set of the first "+str(len(S))+" primes.\n");
		else:
			out.write("# S = {"+myListToStr(S,',')+"}.\n");
		#if modOutSymmetry:
		#	out.write("# For each solution (x,y), only one of (x,y), (-x,-y) is listed.\n");
		out.write("# Note that some GL_2(Z)-equivalence classes of forms may have several reduced representatives.\n");
		out.write("# It contains "+str(numSolutions)+" pairs in total.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		#out.write("###\n");
		R.<x,y> = QQ[];
		for a,b,c,d,D,sols in solutions:
			out.write("#\n");
			out.write("# (a,b,c,d) = ("+str(a)+","+str(b)+","+str(c)+","+str(d)+") and D = "+str(D)+":\n");
			out.write("#\n");
			for (x,y) in sols:
				out.write("(%s,%s)\n" % (str(x),str(y)));
		out.close();

	print "Number of solutions:",numSolutions;

	return solutions;
		
#time solveAllThueMahlerEquationsWithBoundedDiscriminant(S=primes_first_n(3),maxDelta=250,only_irreducible_forms=False,in_parallel=True);
#time solveAllThueMahlerEquationsWithBoundedDiscriminant(S=primes_first_n(4),maxDelta=50,only_irreducible_forms=False,in_parallel=True);

########################################################################
### Test Ramanujan-Nagell equations: ###################################
########################################################################

def computeMWBasesForRamanujanNagellXYEquationsForBInARange(Bs=None,bMax=10000,bMin=0,S=None,n=2,c=1,cacheFileName=None,inMagmaUseHeegnerPointIfRank1=True,onlyPositiveBs=False,useSageRankBound=False,useSageRank=False,randomOrder=False,printAnalyticRank=False,reverseExponents=False,useMagma=True):
	#If S=None, we take S=primes_first_n(n);
	#delta is the discriminant of f:
	#deltaMax = 100;
	#n = 4;
	#m = 1;
	global pathMordellWeil;
	if Bs == None:
		Bs = [b for b in range(-bMax,1-bMin)+range(bMin,bMax+1) if b!=0];
		if onlyPositiveBs:
			Bs = [b for b in Bs if b > 0];
		while 0 in Bs:
			Bs.remove(0);
	Bs.sort(key = abs);
	ranks = {};
	if cacheFileName == None:
		if n!=None:
			cacheFileName = "mwRamanujanNagellXY_N"+str(n)+".sobj";
	#mwBasesDict = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
	mwBasesDict = load_full_mwBasisCache_as_dict();
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwSubbases.sobj"));
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwThueMahlerN"+str(n)+".sobj"));
	#mwSubbasesDict.update(dict(load(pathMordellWeil+"mwAll.sobj")));
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwAll.sobj"));
	mwSubbasesDict = mwBasesDict;
	if randomOrder:
		Bs.sort(key = lambda x: randint(1,100000));

	if S==None:
		S = primes_first_n(n);
	else:
		n = len(S);	

	for b in Bs:
		print "====================================";
		print "b =",b;
		Exponents = [w for w in Words([0,1,2],n)];
		if reverseExponents:
			Exponents.reverse();			
		for exponents in Exponents:
			if verbose:
				print "---------------------------------------------- b =",b;
				print "exponents:",exponents;
			eps = prod([S[i]^exponents[i] for i in range(n)]);
			M = c*eps;
			a = -M^2*b;
			print "a =",a,"=",factor(a);

			E = mordellCurve(a);
			if printAnalyticRank:
				print "E.analytic_rank():",E.analytic_rank();

			mwBasis = mwBasisViaCacheMagmaOrSage(a,mwBasesDict=mwBasesDict,mwSubbasesDict=mwSubbasesDict,cacheFileName=cacheFileName,inMagmaUseHeegnerPointIfRank1=inMagmaUseHeegnerPointIfRank1,useSageRankBound=useSageRankBound,useSageRank=useSageRank,useMagma=useMagma);
			print "mwBasis:",mwBasis;
			r = len(mwBasis);
			print "RANK =",r;
			if ranks.has_key(r):
				ranks[r] += 1;
			else:
				ranks[r] = 1;
				#min_delta_of_rank[r] = delta;

			#We use magma's standard method, except for a few times we use
			#sage's two_decent method:
			#
			#and a few times we take magmas HeegnerPoint method:
			#

	print "ranks:",ranks;
	print "min_delta_of_rank:",min_delta_of_rank;

	return;
		
def solveAllRamanujanNagellXYEquationsWithBoundedB(S=[],maxB=1000,c=1,saveToFile=True,saveToPath=pathData,in_parallel=True,saveMWToCache=True):
	t00 = walltime();
	Bs = [b for b in range(-maxB,1+maxB) if b!=0];

	solutions = [];

	print "Solve all Ramanujan-Nagell(XY) equations with S =",S,", c =",c," and 1 <= |b| <=",maxB;

	if in_parallel:
		parameters = [];
		for b in Bs:
			b=b;
			c=c;
			S=S;
			mwBasesDict_b=None;
			verbose_b = True;
			saveMWToCache_b=saveMWToCache;
			saveToFile_b=False;
			saveToPath_b=pathData;
			param = (b,c,S,mwBasesDict_b,verbose_b,saveMWToCache_b,saveToFile_b,saveToPath_b);
			parameters.append(param);

			

		results = my_run_in_parallel(parameters,solveRamanujanNagellEquation_XY,print_param=False,print_result=False,return_param_index=True);
		print "results:",results;

		for i,solutions_for_b in results:
			param = parameters[i];
			b = param[0];
			solutions_for_b = list(solutions_for_b);
			solutions_for_b.sort();
			solutions.append((b,solutions_for_b));

		print "solutions:",solutions;
			
	else:
		cacheFileName = None;
		if S == primes_first_n(len(S)):
			#cacheFileName = "mwRamanujanNagellXY_N"+str(len(S))+".sobj";
			cacheFileName = None; #"mwMordellS.sobj";
		mwBasesDict = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
		for b in Bs:
			print "============================";
			print "b,c:",b,c;
			solutions_for_b = solveRamanujanNagellEquation_XY(b=b,c=c,S=S,mwBasesDict=mwBasesDict,verbose=True,saveMWToCache=saveMWToCache,saveToFile=False,saveToPath=pathData);
			solutions_for_b = list(solutions_for_b);
			solutions_for_b.sort();
			solutions.append((b,solutions_for_b));

	numSolutions = sum([len(sols) for (b,sols) in solutions]);
	totalTime = walltime(t00);

	solutions.sort(key=lambda (b,sol): b);

	print "sorted solutions:",solutions;

	if saveToFile:
		filename = "ramanujanNagellXY_"; #+myListToStr([a,b,c,d],"_");
		filename += "_maxB"+str(maxB);
		filename += "_c"+str(c);
		if S==primes_first_n(len(S)):
			filename += "_n"+str(len(S));
		else:
			filename += "_S_"+myListToStr(S,'_');
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all solutions (x,y) of the generalized Ramanujan-Nagell equations\n");
		out.write("# x^2 + b = "+str(c)+" * y, where\n");
		out.write("# x >= 0 is an S-integer and y an S-unit,\n");
		out.write("# b is an integer bounded by 1 <= |b| <= "+str(maxB)+", and\n");
		if S==primes_first_n(len(S)):
			out.write("# S is the set of the first "+str(len(S))+" primes.\n");
		else:
			out.write("# S = {"+myListToStr(S,',')+"}.\n");
		#if modOutSymmetry:
		#	out.write("# For each solution (x,y), only one of (x,y), (-x,-y) is listed.\n");
		out.write("# It contains "+str(numSolutions)+" pairs in total.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		#out.write("###\n");
		for b,sols in solutions:
			out.write("#\n");
			out.write("# b = "+str(b)+":\n");
			out.write("#\n");
			for x,y in sols:
				out.write("(%s,%s)\n" % (str(x),str(y)));
		out.close();

	print "Number of solutions:",numSolutions;

	return solutions;
		
def computeMWBasesForRamanujanNagellXNEquationsForBandDInARange(Bs=[7],Ds=range(1,1+1000),c=1,cacheFileName=None,inMagmaUseHeegnerPointIfRank1=True,onlyPositiveBs=False,useSageRankBound=False,useSageRank=False,randomOrder=False,printAnalyticRank=False):
	global pathMordellWeil;
	Bs.sort(key = abs);
	Ds.sort();
	ranks = {};
	if cacheFileName == None:
		cacheFileName = "mwRamanujanNagellXN"+".sobj";
	mwBasesDict = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwSubbases.sobj"));
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwThueMahlerN"+str(n)+".sobj"));
	#mwSubbasesDict.update(dict(load(pathMordellWeil+"mwAll.sobj")));
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwAll.sobj"));
	mwSubbasesDict = mwBasesDict;
	if randomOrder:
		Bs.sort(key = lambda x: randint(1,100000));
		Ds.sort(key = lambda x: randint(1,100000));
	for b in Bs:
		print "====================================";
		print "b =",b;
		for d in Ds:
			print "---------------------------------------------- b,d:",b,d;
			if not Mod(-b,c*d).is_square():
				print "Equation x^2 + b = c*d^n has no solutions for n>=1, thus we ignore this d.";
				continue;
			for n0 in [0,1,2]:
				if verbose:
					print "----------------------------------------------";
					print "n0:",n0;
				eps = d^n0;
				a = -b*(eps*c)^2;
				print "a =",a,"=",factor(a);

				E = mordellCurve(a);
				if printAnalyticRank:
					print "E.analytic_rank():",E.analytic_rank();

				mwBasis = mwBasisViaCacheMagmaOrSage(a,mwBasesDict=mwBasesDict,mwSubbasesDict=mwSubbasesDict,cacheFileName=cacheFileName,inMagmaUseHeegnerPointIfRank1=inMagmaUseHeegnerPointIfRank1,useSageRankBound=useSageRankBound,useSageRank=useSageRank);
				print "mwBasis:",mwBasis;
				r = len(mwBasis);
				print "RANK =",r;
				if ranks.has_key(r):
					ranks[r] += 1;
				else:
					ranks[r] = 1;
					#min_delta_of_rank[r] = delta;

	print "ranks:",ranks;

	return;

def solveAllRamanujanNagellXNEquationsForBCDInARange(Bs=[7],Cs=[1],Ds=range(2,1+888),saveToFile=True,saveToPath=pathData,in_parallel=True,saveMWToCache=True):
	t00 = walltime();
	solutions = [];
	print "Solve all Ramanujan-Nagell(XN) equations with Bs =",Bs,"and Cs =",Cs,"and Ds =",Ds;

	mwBasesDict = load_full_mwBasisCache_as_dict(cacheFileName="mwRamanujanNagellXN.sobj");
	
	for b in Bs:
		for c in Cs:
			for d in Ds:
				print "============================ b =",b," and c =",c," and d =",d;
				solutions_for_bcd = solveRamanujanNagellEquation_XN(b=b,c=c,d=d,mwBasesDict=mwBasesDict,verbose=True,saveMWToCache=True,saveToFile=False);
				solutions.append((b,c,d,solutions_for_bcd));
	print "solutions:",solutions;

	numSolutions = sum([len(sols) for (b,c,d,sols) in solutions]);
	totalTime = walltime(t00);

	#solutions.sort();

	print "solutions:",solutions;

	if saveToFile:
		filename = "ramanujanNagellXN_";
		if len(Bs)==1:
			filename += "_b"+str(Bs[0]);
		elif Bs == range(min(Bs),1+max(Bs)):
			filename += "_bMin"+str(min(Bs))+"_bMax"+str(max(Bs));
		else:
			filename += "_B_"+myListToStr(Bs,"_");
		if len(Cs)==1:
			filename += "_c"+str(Cs[0]);
		elif Cs == range(min(Cs),1+max(Cs)):
			filename += "_cMin"+str(min(Cs))+"_cMax"+str(max(Cs));
		else:
			filename += "_C_"+myListToStr(Cs,"_");
		if len(Ds)==1:
			filename += "_d"+str(Ds[0]);
		elif Ds == range(min(Ds),1+max(Ds)):
			if min(Ds)!=2:
				filename += "_dMin"+str(min(Ds));
			filename += "_dMax"+str(max(Ds));
		else:
			filename += "_D_"+myListToStr(Ds,"_");

		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all solutions (x,n) of the generalized Ramanujan-Nagell equations\n");
		out.write("# x^2 + b = c * d^n, where\n");
		out.write("# x >= 0 is an S-integer and n >= 0 is an integer,\n");
		if len(Bs)==1:
			out.write("# b = "+str(Bs[0])+",\n");
		elif Bs == range(min(Bs),1+max(Bs)):
			out.write("# "+str(min(Bs))+" <= b <=  "+str(max(Bs))+",\n");
		else:
			out.write("# b lies in {"+myListToStr(Bs,", ")+"},\n");
		if len(Cs)==1:
			out.write("# c = "+str(Cs[0])+", and\n");
		elif Cs == range(min(Cs),1+max(Cs)):
			out.write("# "+str(min(Cs))+" <= c <=  "+str(max(Cs))+", and\n");
		else:
			out.write("# c lies in {"+myListToStr(Cs,", ")+"}, and\n");
		if len(Ds)==1:
			out.write("# d = "+str(Ds[0])+".\n");
		elif Ds == range(min(Ds),1+max(Ds)):
			out.write("# "+str(min(Ds))+" <= d <=  "+str(max(Ds))+".\n");
		else:
			out.write("# d lies in {"+myListToStr(Ds,", ")+"}.\n");
		out.write("# It contains "+str(numSolutions)+" pairs in total.\n");
		out.write('# Format: "(x,n)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		#out.write("###\n");
		for b,c,d,sols in solutions:
			if len(sols)>0:
				out.write("#\n");
				out.write("# b = "+str(b)+", c = "+str(c)+", d = "+str(d)+":\n");
				out.write("#\n");
				for x,n in sols:
					out.write("(%s,%s)\n" % (str(x),str(n)));
		out.close();

	print "Number of solutions:",numSolutions;

	return solutions;

def solveIntegralRamanujanNagellXYEquation(n,b,saveToFile=True,saveToPath=pathData,saveMWToCache=True):
	#We find all integral solutions (x,y) of the RN equation x^2 + b = y, where y is an S(n)-unit.
	#Only implemented if b is a prime!

	if not b.is_prime():
		raise NotImplementedError("b is not a prime. This case is not implemented, but if you really need it, it's not too difficult to do it. The equation reduces similarly to generalized RN-equations with relatively small sets S.");

	mwBasesDict = load_full_mwBasisCache_as_dict();

	t00 = cputime();

	S = [];
	for p in primes_first_n(n):
		if p != b:
			if Mod(-7,p).is_square():
				S.append(p);
	print "n =",n;
	print "S =",S;

	solutions = [];

	for c in [1,b]:
		solutions_for_c = solveRamanujanNagellEquation_XY(b=b,c=c,S=S,mwBasesDict=mwBasesDict,verbose=True,saveMWToCache=saveMWToCache,saveToFile=False,saveToPath=pathData,reverseExponents=False);

		for (x,y) in solutions_for_c:
			if x in ZZ and y in ZZ:
				X = x;
				Y = c*y;
				solutions.append((X,Y));

	solutions.sort();
	print "solutions:",solutions;
	numSolutions = len(solutions);

	totalTime = cputime(t00);

	if saveToFile:
		filename = "ramanujanNagellIntegralXY";
		filename += "_b"+str(b);
		filename += "_n"+str(n);

		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all solutions (x,y) of the integral generalized Ramanujan-Nagell equation\n");
		out.write("# x^2 + "+str(b)+" = y, where\n");
		out.write("# x >= 0 is an integer and y >= 0 is an integral S-unit,\n");
		out.write("# where S is the set of the first "+str(n)+" primes.\n");
		out.write("# It contains "+str(numSolutions)+" pairs in total.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2016.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		#out.write("###\n");
		for x,y in solutions:
			out.write("(%s,%s)\n" % (str(x),str(y)));
		out.close();

	print "Number of solutions:",numSolutions;

	return solutions;				

########################################################################
### Testing Terai conjectures: #########################################
########################################################################

def computePhythagoreanTriples(cMin,cMax):
	triples = [];
	for n in range(1,RR(cMax.sqrt()).ceil()+1):
		for m in range(n+1,RR(max(0,cMax-n)).sqrt().ceil()+1):
			c = n^2 + m^2;
			if c < cMin:
				continue;
			if c > cMax:
				continue;
			a = 2*m*n;
			b = m^2 - n^2;
			if gcd(a,b).is_unit():
				triples.append((a,b,c));
	triples.sort(key = lambda (a,b,c): b);
	triples.sort(key = lambda (a,b,c): c);
	return triples;

def computeMWBasesForTeraiPhythagoreanConjecture(cMax=100,cMin=0,useFirstReduction=True,cacheFileName=None,inMagmaUseHeegnerPointIfRank1=True,onlyPositiveDeltas=False,useSageRankBound=False,useSageRank=False,randomOrder=False,printAnalyticRank=False,reverseExponents=False):
	global pathMordellWeil;
	triples = computePhythagoreanTriples(cMin,cMax);
	ranks = {};
	mwBasesDict = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwSubbases.sobj"));
	#mwSubbasesDict.update(dict(load(pathMordellWeil+"mwAll.sobj")));
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwAll.sobj"));
	mwSubbasesDict = mwBasesDict;
	
	solutions = [];
	
	if randomOrder:
		triples.sort(key = lambda x: randint(1,100000));
	for (A,B,C) in triples:
		print "====================================";
		print "Phythagorean triple =",A,B,C;
		if useFirstReduction:
			Exponents = [(eb,ec) for eb in range(6) for ec in range(3)];
		else:
			Exponents = [(eb,ec) for eb in range(3) for ec in range(6)];
		if reverseExponents:
			Exponents.reverse();			
		for (eb,ec) in Exponents:
			if verbose:
				print "---------------------------------------------- A,B,C:",A,B,C;
				print "exponents:",eb,ec;
			delta = B^eb;
			epsilon = C^ec;
			if useFirstReduction:
				a = -epsilon^2 * delta;
			else:
				a = delta^2 * epsilon;
			print "a =",a,"=",factor(a);

			E = mordellCurve(a);
			if printAnalyticRank:
				print "E.analytic_rank():",E.analytic_rank();

			mwBasis = mwBasisViaCacheMagmaOrSage(a,mwBasesDict=mwBasesDict,mwSubbasesDict=mwSubbasesDict,cacheFileName=cacheFileName,inMagmaUseHeegnerPointIfRank1=inMagmaUseHeegnerPointIfRank1,useSageRankBound=useSageRankBound,useSageRank=useSageRank);
			print "mwBasis:",mwBasis;
			r = len(mwBasis);
			print "RANK =",r;
			if ranks.has_key(r):
				ranks[r] += 1;
			else:
				ranks[r] = 1;

			if useFirstReduction:
				S = B.prime_factors();
			else:
				S = C.prime_factors();

			solutions_mordell = computeSIntegralPoints(E=E,S=S,mwBasis=mwBasis,verbose=False);
			print "Solutions of associated Mordell equation:", solutions_mordell;

			if useFirstReduction:
				#B^m = delta * B^{6m'}
				#C^n = epsilon * C^{3n'}
				#Solutions of Mordell equation must satisfy:
				# Y = epsilon*x/(B^{3m'}) is already reduced fraction, can obtain from it x and m')
				# X = epsilon*C^{n'}/(B^{2m'})
				for P in solutions_mordell:
					X,Y = P.xy();
					x = Y.numerator()/epsilon;
					Cnprime = X.numerator()/epsilon;
					Bmprime = ZZ(X.denominator().abs().sqrt());
					if x in ZZ and Cnprime in ZZ:
						print "X,Y:",X,Y;
						nprimeRR = RR(log(Cnprime)/log(C));
						mprimeRR = RR(log(Bmprime)/log(B));
						nprime = nprimeRR.round();
						mprime = mprimeRR.round();
						if B^mprime == Bmprime and C^nprime == Cnprime:
							print "nprimeRR:",nprimeRR;
							print "mprimeRR:",mprimeRR;
							print "Cnprime:",Cnprime;
							print "Bmprime:",Bmprime;
							m = eb + 6*mprime;
							n = ec + 3*nprime;
							if n>0 and m>0:
								print "Solution for Terai found!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!";
								solutions.append((x,B,C,m,n));
								print "Namely: x =",x,", B =",B,", C =",C,", m =",m,", n =",n;
			else:
				#B^m = delta * B^{3m'}
				#C^n = epsilon * C^{6n'}
				#Solutions of Mordell equation must satisfy:
				# Y = delta*x/(C^{3n'}) is already reduced fraction, can obtain from it x and m')
				# X = -delta*B^{m'}/(C^{2n'})
				for P in solutions_mordell:
					X,Y = P.xy();
					x = Y.numerator()/delta;
					Bmprime = -X.numerator()/delta;
					Cnprime = ZZ(X.denominator().sqrt());
					if x in ZZ and Cnprime in ZZ:
						print "X,Y:",X,Y;
						if Cnprime > 0 and Bmprime > 0:
							nprimeRR = RR(log(Cnprime)/log(C));
							mprimeRR = RR(log(Bmprime)/log(B));
							nprime = nprimeRR.round();
							mprime = mprimeRR.round();
							if B^mprime == Bmprime and C^nprime == Cnprime:
								print "nprimeRR:",nprimeRR;
								print "mprimeRR:",mprimeRR;
								print "Cnprime:",Cnprime;
								print "Bmprime:",Bmprime;
								m = eb + 3*mprime;
								n = ec + 6*nprime;
								if n>0 and m>0:
									print "Solution for Terai found!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!";
									solutions.append((x,B,C,m,n));
									print "Namely: x =",x,", B =",B,", C =",C,", m =",m,", n =",n;
				
				

	print "ranks:",ranks;

	print "solutions:",solutions;

	return;

def computeMWBasesForTerai2dm1Conjecture(dMax=100,dMin=2,useFirstReduction=True,cacheFileName=None,inMagmaUseHeegnerPointIfRank1=True,onlyPositiveDeltas=False,useSageRankBound=False,useSageRank=False,randomOrder=False,printAnalyticRank=False,reverseExponents=False):
	global pathMordellWeil;
	Ds = range(dMin,dMax+1);
	ranks = {};
	mwBasesDict = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwSubbases.sobj"));
	#mwSubbasesDict.update(dict(load(pathMordellWeil+"mwAll.sobj")));
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwAll.sobj"));
	mwSubbasesDict = mwBasesDict;
	if randomOrder:
		Ds.sort(key = lambda x: randint(1,100000));
	solutions = [];
	for d in Ds:
		B = ZZ(2*d-1);
		C = ZZ(d);
		print "====================================";
		print "d =",d
		if useFirstReduction:
			Exponents = [(eb,ec) for eb in range(6) for ec in range(3)];
		else:
			Exponents = [(eb,ec) for eb in range(3) for ec in range(6)];
		if reverseExponents:
			Exponents.reverse();			
		for (eb,ec) in Exponents:
			if verbose:
				print "---------------------------------------------- d:",d;
				print "exponents:",eb,ec;
			delta = B^eb;
			epsilon = C^ec;
			if useFirstReduction:
				a = -epsilon^2 * delta;
			else:
				a = delta^2 * epsilon;
			print "a =",a,"=",factor(a);

			E = mordellCurve(a);
			if printAnalyticRank:
				print "E.analytic_rank():",E.analytic_rank();

			mwBasis = mwBasisViaCacheMagmaOrSage(a,mwBasesDict=mwBasesDict,mwSubbasesDict=mwSubbasesDict,cacheFileName=cacheFileName,inMagmaUseHeegnerPointIfRank1=inMagmaUseHeegnerPointIfRank1,useSageRankBound=useSageRankBound,useSageRank=useSageRank);
			print "mwBasis:",mwBasis;
			r = len(mwBasis);
			print "RANK =",r;
			if ranks.has_key(r):
				ranks[r] += 1;
			else:
				ranks[r] = 1;

			if useFirstReduction:
				S = B.prime_factors();
			else:
				S = C.prime_factors();

			solutions_mordell = computeSIntegralPoints(E=E,S=S,mwBasis=mwBasis,verbose=False);
			print "Solutions of associated Mordell equation:", solutions_mordell;

			if useFirstReduction:
				#B^m = delta * B^{6m'}
				#C^n = epsilon * C^{3n'}
				#Solutions of Mordell equation must satisfy:
				# Y = epsilon*x/(B^{3m'}) is already reduced fraction, can obtain from it x and m')
				# X = epsilon*C^{n'}/(B^{2m'})
				for P in solutions_mordell:
					X,Y = P.xy();
					x = Y.numerator()/epsilon;
					Cnprime = X.numerator()/epsilon;
					Bmprime = ZZ(X.denominator().abs().sqrt());
					if x in ZZ and Cnprime in ZZ:
						print "X,Y:",X,Y;
						nprimeRR = RR(log(Cnprime)/log(C));
						mprimeRR = RR(log(Bmprime)/log(B));
						nprime = nprimeRR.round();
						mprime = mprimeRR.round();
						if B^mprime == Bmprime and C^nprime == Cnprime:
							print "nprimeRR:",nprimeRR;
							print "mprimeRR:",mprimeRR;
							print "Cnprime:",Cnprime;
							print "Bmprime:",Bmprime;
							m = eb + 6*mprime;
							n = ec + 3*nprime;
							if n>0 and m>0:
								print "Solution for Terai found!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!";
								solutions.append((x,B,C,m,n));
								print "Namely: x =",x,", B =",B,", C =",C,", m =",m,", n =",n;
			else:
				#B^m = delta * B^{3m'}
				#C^n = epsilon * C^{6n'}
				#Solutions of Mordell equation must satisfy:
				# Y = delta*x/(C^{3n'}) is already reduced fraction, can obtain from it x and m')
				# X = -delta*B^{m'}/(C^{2n'})
				for P in solutions_mordell:
					X,Y = P.xy();
					x = Y.numerator()/delta;
					Bmprime = -X.numerator()/delta;
					Cnprime = ZZ(X.denominator().sqrt());
					if x in ZZ and Cnprime in ZZ:
						print "X,Y:",X,Y;
						if Cnprime > 0 and Bmprime > 0:
							nprimeRR = RR(log(Cnprime)/log(C));
							mprimeRR = RR(log(Bmprime)/log(B));
							nprime = nprimeRR.round();
							mprime = mprimeRR.round();
							if B^mprime == Bmprime and C^nprime == Cnprime:
								print "nprimeRR:",nprimeRR;
								print "mprimeRR:",mprimeRR;
								print "Cnprime:",Cnprime;
								print "Bmprime:",Bmprime;
								m = eb + 3*mprime;
								n = ec + 6*nprime;
								if n>0 and m>0:
									print "Solution for Terai found!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!";
									solutions.append((x,B,C,m,n));
									print "Namely: x =",x,", B =",B,", C =",C,", m =",m,", n =",n;

	print "ranks:",ranks;

	print "solutions:",solutions;

	return;

########################################################################
### Test Mordell equation: #############################################
########################################################################

def computeMWBasesForMordellEquations(maxA=20000,minA=0,inMagmaUseHeegnerPointIfRank1=True,uncheckedAs=None,useSageRankBound=False,useSageRank=False):
	global pathMordellWeil;
	debug = False;
	#cacheFileName = "mwBases10000new.sobj";
	cacheFileName = "mwMordell.sobj";
	mwBasesDict = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwSubbases10000.sobj"));
	mwSubbasesDict = mwBasesDict;
	As = range(-maxA,1-minA) + range(minA,1+maxA);
	while 0 in As:
		As.remove(0);
	if uncheckedAs==None:
		uncheckedAs = [];
		if debug:
			for a in uncheckedAs:
				E = mordellCurve(a);
				print a,E.rank_bound();
			return;
	for a in uncheckedAs:
		As.remove(a);
	As.sort(key=abs);
	ranks = {};

	
	for a in As:
		print "---------------------------------------------- a =",a;
		E = mordellCurve(a);
		mwBasis = mwBasisViaCacheMagmaOrSage(a,mwBasesDict=mwBasesDict,mwSubbasesDict=mwSubbasesDict,cacheFileName=cacheFileName,inMagmaUseHeegnerPointIfRank1=inMagmaUseHeegnerPointIfRank1,useSageRankBound=useSageRankBound,useSageRank=useSageRank);
		print "mwBasis:",mwBasis;
		r = len(mwBasis);
		print "RANK =",r;
		r = len(mwBasis);
		print "RANK =",r;
		if ranks.has_key(r):
			ranks[r] += 1;
		else:
			ranks[r] = 1;
	print "ranks:",ranks;
	
	'''
	def xy_to_std_format(a,xy):
		E = mordellCurve(a);
		P = E(xy);
		if P[1] < 0:
			P = -P;
		xy = P.xy();
		return P; #xy;

	print "|Bases|    =",len(mwBasesDict);
	print "|Subbases| =",len(mwSubbasesDict);

	for a in As:
		if a != sixthPowerFreeK(a):
			print "skip a =",a,"as this is not sixth power free.";
			continue;
		print a,;
		E = mordellCurve(a);
		if not mwBasesDict.has_key(a):
			print "mwBasesDict.has_key(a) == False";
			return;
		if not mwSubbasesDict.has_key(a):
			print "mwSubbasesDict.has_key(a) == False";
			return;
		mwB = mwBasesDict[a];
		mwS = mwSubbasesDict[a];
		mwB = [xy_to_std_format(a,xy) for xy in mwB];
		mwS = [xy_to_std_format(a,xy) for xy in mwS];
		mwB.sort();
		mwS.sort();
		if mwB != mwS:
			print "Unuebereinstimmung bei a =",a;
			print "mwBasesDict[a]   :",mwBasesDict[a];
			print "mwSubbasesDict[a]:",mwSubbasesDict[a];
			satB = E.saturation(mwB);
			print "Saturate mwB:",satB;
			satS = E.saturation(mwS);
			print "Saturate mwS:",satS;
			if satB[1]==1:
				print "No problem, as mwB is saturated!";
			else:
				return;
	'''
	
	print "uncheckedAs:",uncheckedAs;
	return;

def KsForMordellEquationsWithGivenRadA(S=[2]):
	Ks = [];
	Exponents = [w for w in Words(range(6),len(S))];
	for exponents in Exponents:
		a = prod([S[i]^exponents[i] for i in range(len(S))]);
		Ks.append(a);
	return Ks;

def computeMWBasesForMordellEquationsWithGivenRadA(S=[2],cacheFileName=None,inMagmaUseHeegnerPointIfRank1=True,signs=[-1,+1],useSageRankBound=False,useSageRank=False,randomOrder=False,printAnalyticRank=False,reverseExponents=False,prescribedAnalyticRanks=None):
	global pathMordellWeil;
	ranks = {};
	if cacheFileName == None:
		cacheFileName = "mwMordellS.sobj";
	mwBasesDict = load_full_mwBasisCache_as_dict(cacheFileName=cacheFileName);
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwSubbases.sobj"));
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwThueMahlerN"+str(n)+".sobj"));
	#mwSubbasesDict.update(dict(load(pathMordellWeil+"mwAll.sobj")));
	#mwSubbasesDict = dict(load(pathMordellWeil+"mwAll.sobj"));
	mwSubbasesDict = mwBasesDict;
	#mwSubbasesDict = load_full_mwBasisCache_as_dict(cacheFileName=None);
	Exponents = [w for w in Words([0,1,2,3,4,5],len(S))];
	if reverseExponents:
		Exponents.reverse();			
	if randomOrder:
		signs.sort(key = lambda x: randint(1,100000));
		Exponents.sort(key = lambda x: randint(1,100000));
	for sign in signs:
		print "====================================";
		print "sign =",sign;
		for exponents in Exponents:
			if verbose:
				print "---------------------------------------------- sign,exponents =",sign,exponents;
				print "exponents:",exponents;
			a = sign * prod([S[i]^exponents[i] for i in range(len(S))]);
			print "a =",a,"=",factor(a);

			E = mordellCurve(a);
			analyticRank = E.analytic_rank();
			if printAnalyticRank:
				print "E.analytic_rank():",analyticRank;
			if prescribedAnalyticRanks!=None:
				if analyticRank not in prescribedAnalyticRanks:
					print "Not of prescribed analytic rank."
					continue;

			mwBasis = mwBasisViaCacheMagmaOrSage(a,mwBasesDict=mwBasesDict,mwSubbasesDict=mwSubbasesDict,cacheFileName=cacheFileName,inMagmaUseHeegnerPointIfRank1=inMagmaUseHeegnerPointIfRank1,useSageRankBound=useSageRankBound,useSageRank=useSageRank);
			print "mwBasis:",mwBasis;
			r = len(mwBasis);
			print "RANK =",r;
			if ranks.has_key(r):
				ranks[r] += 1;
			else:
				ranks[r] = 1;

	print "ranks:",ranks;

	return;

#S={2,3,5,7,11}: {0: 3360, 1: 3874, 2: 528, 3: 14}
		
def mordellEquation_studyRanks():
	mwCacheDict = load_full_mwBasisCache_as_dict(cacheFileName="mwMordellS.sobj");
	p1,p2,S = 2,3,[2,3,5];
	p1,p2,S = 3,5,[2,3,5];
	p1,p2,S = 2,5,[2,3,5];
	SwoP1P2 = copy(S);
	SwoP1P2.remove(p1);
	SwoP1P2.remove(p2);
	NS = prod(S);
	a6 = NS^6;
	BoolTo01 = {True: 1, False: 0};
	for exponents in [w for w in Words(range(6),len(SwoP1P2))]:
		a0 = prod([SwoP1P2[i]^exponents[i] for i in range(len(SwoP1P2))]);
		print "==== a0 =",a0,"=",factor(a0)," and exponents =",exponents;
		for e1 in range(6):
			for e2 in range(6):
				a = a0 * p1^e1 * p2^e2;
				basis = load_mwBasis_from_cache(a,mwCacheDict=mwCacheDict,cacheFileName=None);
				r = len(basis);
				print r % 2,;
			print "    ",;
			for e2 in range(6):
				a = a0 * p1^e1 * p2^e2;
				print BoolTo01[mod(a,a6).is_square()],;
			print "";

#time computeMWBasesForMordellEquations(useSageRankBound=False,useSageRank=False);

########################################################################
### Classifying elliptic curves /Q with good reduction outside S: ######
########################################################################

def M_S(S):
	result = 1;
	for p in S:
		if p==2:
			mp = p^8;
		elif p==3:
			mp = p^5;
		else:
			mp = p^2;
		result *= mp;
	return result;

def setsSOfPrimesWithBoundedMS(maxMS,allowSingletons=True):
	
	def getSs(minP = 2, SsoFar = [], remainingMS = 1, allowSingletons = allowSingletons):
		result = set([]);
		if SsoFar != [] and (allowSingletons or len(SsoFar)>=2):
			result.add(tuple(copy(SsoFar)));
		maxP = RIF(remainingMS).sqrt().upper().floor();
		for p in prime_range(minP,1+maxP):
			newSsoFar = SsoFar + [p];
			mp = M_S([p]);
			result_for_p = getSs(minP = p+1, SsoFar = newSsoFar, remainingMS = remainingMS/mp, allowSingletons = allowSingletons);
			result.update(result_for_p);
		return result;
	
	return getSs(minP = 2, SsoFar = [], remainingMS = maxMS, allowSingletons = allowSingletons);

def N_S(S):
	return prod(S);

def setsSOfPrimesWithBoundedNS(maxNS,allowSingletons=True):
	
	def getSs(minP = 2, SsoFar = [], remainingNS = 1, allowSingletons = allowSingletons):
		result = set([]);
		if SsoFar != [] and (allowSingletons or len(SsoFar)>=2):
			result.add(tuple(copy(SsoFar)));
		maxP = remainingNS.floor();
		for p in prime_range(minP,1+maxP):
			newSsoFar = SsoFar + [p];
			np = N_S([p]);
			result_for_p = getSs(minP = p+1, SsoFar = newSsoFar, remainingNS = remainingNS/np, allowSingletons = allowSingletons);
			result.update(result_for_p);
		return result;
	
	return getSs(minP = 2, SsoFar = [], remainingNS = maxNS, allowSingletons = allowSingletons);

def computeRank1MWBasesForCurveDB(S=[2,3,5,7,11,13],cacheFileName="mwMordellS6.sobj",onlyAnalyticRanks="all",mwBasesDict=None,mwSubbasesDict={},loadFromCacheIfPossible=True,saveMWToCacheAtTheEnd=True,saveMWToCacheSeparately=True,inMagmaUseHeegnerPointIfRank1=False,inSageUseTwoDescentInCaseOfFailure=True,useMagma=True,useSageRankBound=False,useSageRank=False,in_parallel=False,timeout=0,randomOrder=True,useParisHeegnerPoint=True,computeAnalyticRanks=False,skipTheFirstXRemainingKs=0):
	#Problem: Assume silently that 2 and 3 are in S!!!
	#The other cases are not implemented yet!
	if (2 not in S) or (3 not in S):
		raise NotImplementedError("2 or 3 is not in S!");
	Exponents = [w for w in Words([0,1,2,3,4,5],len(S))];
	#Ks = [prod([S[i]^w[i] for i in range(len(S))]) for w in Exponents];
	Ks = [];
	for w in Exponents:
		k = prod([S[i]^w[i] for i in range(len(S))]);
		if k % 3^3 == 0:
			k = ZZ(k/(-27));
		#E = mordellCurve(k);
		#if anRanks == "all" or E.analytic_rank() in anRanks:
		#	Ks.append(k);
		Ks.append(k);

	global pathMordellWeil;

	if computeAnalyticRanks:
		anRanks = [];
		for k in Ks:
			E = mordellCurve(k);
			analyticRank = E.analytic_rank();
			print "k,an_rank:",k,analyticRank;
			anRanks.append((k,analyticRank));
		save(anRanks,pathMordellWeil+"anRanks_"+cacheFileName);

	if onlyAnalyticRanks != "all":
		anRanks = load(pathMordellWeil+"anRanks_"+cacheFileName);
		anRanksDict = dict(anRanks);
		Ks = [k for k in Ks if anRanksDict[k] in onlyAnalyticRanks];

	if skipTheFirstXRemainingKs != 0:
		randomOrder = False;

	manyMWBasesViaCacheMagmaOrSage(Ks,onlyAnalyticRanks="all",mwBasesDict=None,mwSubbasesDict=mwSubbasesDict,loadFromCacheIfPossible=loadFromCacheIfPossible,saveMWToCacheAtTheEnd=saveMWToCacheAtTheEnd,saveMWToCacheSeparately=saveMWToCacheSeparately,cacheFileName=cacheFileName,inMagmaUseHeegnerPointIfRank1=inMagmaUseHeegnerPointIfRank1,inSageUseTwoDescentInCaseOfFailure=inSageUseTwoDescentInCaseOfFailure,useMagma=useMagma,useSageRankBound=useSageRankBound,useSageRank=useSageRank,in_parallel=in_parallel,timeout=timeout,randomOrder=randomOrder,useParisHeegnerPoint=useParisHeegnerPoint,skipTheFirstXRemainingKs=skipTheFirstXRemainingKs);

def computeMWBasesForCurveDBwithBoundedS(maxBound=100,minBound=None,boundType="NS",allowSingletons=True,AsToIgnore=[],cacheFileName="mwMordellS.sobj",mwBasesDict=None,mwSubbasesDict={},loadFromCacheIfPossible=True,saveMWToCacheAtTheEnd=True,saveMWToCacheSeparately=True,inMagmaUseHeegnerPointIfRank1=False,inSageUseTwoDescentInCaseOfFailure=True,useMagma=True,useSageRankBound=False,useSageRank=False,in_parallel=False,timeout=0,randomOrder=False,useParisHeegnerPoint=True):
	#We compute all MW-Bases for all S with bounded...
	# - N_S, if boundType = "NS", and
	# - M_S, if boundType = "MS".
	#Here:
	# N_S := prod_{p in S} p.
	# M_S := prod_{p in S} p^{f_p}, where f_2 = 8, f_3 = 5, and f_p = 2 otherwise.
	
	def boundForS(S,boundType=boundType):
		if boundType == "NS":
			return N_S(S);
		elif boundType == "MS":
			return M_S(S);
		else:
			raise NotImplementedError("Unknown boundType.");

	def getSs(maxBound,boundType,allowSingletons):
		if boundType == "NS":
			return setsSOfPrimesWithBoundedNS(maxBound,allowSingletons);
		elif boundType == "MS":
			return setsSOfPrimesWithBoundedMS(maxBound,allowSingletons);
		else:
			raise NotImplementedError("Unknown boundType.");
		
	Ss = getSs(maxBound,boundType,allowSingletons);
	if minBound != None:
		Ss = set([S for S in Ss if boundForS(S)>=minBound]);
		
	print "Ss:",Ss;
	print "len(Ss):",len(Ss);
	#return;

	Ks = set([]);

	for sign in [+1,-1]:
		for S in Ss:
			Exponents = [w for w in Words([0,1,2,3,4,5],len(S))];
			for w in Exponents:
				k = sign * prod([S[i]^w[i] for i in range(len(S))]);
				#if 2 not in S:
				#	k *= 2^6;
				if 3 not in S:
					k *= 3^3;
				while k % 3^3 == 0:
					k = ZZ(k/(-27));
				#if minAbsK!=None and abs(k)<minAbsK:
				#	continue;
				#if maxAbsK!=None and abs(k)>maxAbsK:
				#	continue;
				if k not in AsToIgnore:
					Ks.add(k);

	Ks = list(Ks);
	Ks.sort();

	manyMWBasesViaCacheMagmaOrSage(Ks,mwBasesDict=mwBasesDict,mwSubbasesDict=mwSubbasesDict,loadFromCacheIfPossible=loadFromCacheIfPossible,saveMWToCacheAtTheEnd=saveMWToCacheAtTheEnd,saveMWToCacheSeparately=saveMWToCacheSeparately,cacheFileName=cacheFileName,inMagmaUseHeegnerPointIfRank1=inMagmaUseHeegnerPointIfRank1,inSageUseTwoDescentInCaseOfFailure=inSageUseTwoDescentInCaseOfFailure,useMagma=useMagma,useSageRankBound=useSageRankBound,useSageRank=useSageRank,in_parallel=in_parallel,timeout=timeout,randomOrder=randomOrder,useParisHeegnerPoint=useParisHeegnerPoint);

#Have all bases for |M_S| <= 10^6.
#Have all bases for |N_S| <= 1000.

def computeAllRationalEllipticCurvesWithGoodReductionOutsideS(S=[],randomOrder=False,reverseExponents=False,verbose=True,useSagesAlgorithmForSintegralPoints=False,compareWithCremonaDB=False,mwCache=None):
	if mwCache==None:
		mwCache = load_full_mwBasisCache_as_dict(cacheFileName="mwMordellS.sobj");
	if verbose:
		print "Compute all rational elliptic curves with good reduction outside S =",S;

	solutions = set([]);

	Exponents = [w for w in Words([0,1,2,3,4,5],len(S))];
	if reverseExponents:
		Exponents.reverse();			
	if randomOrder:
		signs.sort(key = lambda x: randint(1,100000));
		Exponents.sort(key = lambda x: randint(1,100000));
	for sign in [-1,+1]:
		for exponents in Exponents:
			if verbose:
				print "---------------------------------------------- sign, exponents =",sign,exponents;
				print "exponents:",exponents;
			w = sign * prod([S[i]^exponents[i] for i in range(len(S))]);
			a = 1728 * w;
			print "a =",a,"=",factor(a);
			Ea = mordellCurve(a);

			solutions_a = set([]);

			mwBasis = load_mwBasis_from_cache(a,mwCacheDict=mwCache,cacheFileName=None);
			if mwBasis == None:
				print "Error: mwBasis not in our data base!"
			mwBasis = [Ea(P) for P in mwBasis];

			print "rank =",len(mwBasis);

			if useSagesAlgorithmForSintegralPoints:
				EaMin = ellipticCurveSMinimalModel(Ea,S);
				isoToOriginalCurve = EaMin.isomorphism_to(Ea);
				isoFromOriginalCurve = Ea.isomorphism_to(EaMin);
				mwBasisMin = [isoFromOriginalCurve(P) for P in mwBasis];
				points_EaMin = EaMin.S_integral_points(S,mw_base=mwBasisMin,both_signs=True);
				points_Ea = [isoToOriginalCurve(P) for P in points_EaMin];
			else:
				points_Ea = computeSIntegralPoints(Ea,S=S,mwBasis=mwBasis,Mmax0=None,verbose=False,bothSigns=True,saveToFile=False,saveToPath=pathData,debugParam={});
			print "# S-integral points on E_a:",len(points_Ea);

			for P in points_Ea:
				Exponents_d = [w for w in Words([0,1],len(S))];
				for exponents_d in Exponents_d:
					d = prod([S[i]^exponents_d[i] for i in range(len(S))]);
					x = P[0];
					y = P[1];
					s = d^2 * x;
					t = d^3 * y;
					E = EllipticCurve([0,0,0,-27*s,-54*t]);
					Emin = E.minimal_model();
					if Emin.has_good_reduction_outside_S(S):
						c4 = Emin.c4();
						c6 = Emin.c6();
						solutions_a.add((c4,c6));
						#print "x,y,s,t,c4,c6,j:",x,y,s,t,c4,c6,Emin.j_invariant();

			print "Num solutions for a:",len(solutions_a);
			solutions.update(solutions_a);
			
	#print "solutions:",solutions;

	#for (c4,c6) in solutions:
	#	E = EllipticCurve_from_c4c6(c4,c6);
	#	Emin = E.minimal_model();
	#	#print (c4,c6), ", D =",factor(Emin.discriminant()), ", j =",Emin.j_invariant();
		
	
	print "Number of solutions:",len(solutions);
	solutionsList = list(solutions);
	solutionsList.sort(key = lambda(c4,c6): c4^3-c6^2); #order by j


	Js = list(set([EllipticCurve_from_c4c6(c4,c6).j_invariant() for (c4,c6) in solutions]));
	Js.sort();
	print "j's:",Js;
	print "# j's:",len(Js);


	if compareWithCremonaDB:
		print "Comparision with Cremona's DB:";
		solutions_cremona = set([]);
		if 2 in S:
			Exp2 = range(1+8);
		else:
			Exp2 = [0];
		if 3 in S:
			Exp3 = range(1+5);
		else:
			Exp3 = [0];
		Srest = copy(S);
		if 2 in Srest:
			Srest.remove(2);
		if 3 in Srest:
			Srest.remove(3);
		for e2 in Exp2:
			for e3 in Exp3:
				for expRest in Words([0,1,2],len(Srest)):
					N = prod([Srest[i]^expRest[i] for i in range(len(Srest))]);
					N *= 2^e2 * 3^e3;
					for E in cremona_curves([N]):
						solutions_cremona.add(E.c_invariants());
						#print (E.c4(),E.c6()), "D =",factor(E.discriminant()), ", j =",E.j_invariant();
		print "len(solutions_cremona):",len(solutions_cremona);


		Js_cremona = list(set([EllipticCurve_from_c4c6(c4,c6).j_invariant() for (c4,c6) in solutions_cremona]));
		Js_cremona.sort();
		print "j's (cremona):",Js_cremona;
		print "# j's (cremona):",len(Js_cremona);

		print "Our {(c4,c6)} agrees with cremonas's {(c4,c6)}:",solutions==solutions_cremona;

		cremonas_solutions_minus_ours = [c4c6 for c4c6 in solutions_cremona if c4c6 not in solutions]
		print "cremonas_solutions_minus_ours:",cremonas_solutions_minus_ours;
		print "len(cremonas_solutions_minus_ours):",len(cremonas_solutions_minus_ours);

		if cremonas_solutions_minus_ours != []:
			raise ValueError("Error, not all curves in Cremona's DB have been found! Here, S = {"+myListToStr(S)+"}.");

	return solutionsList;

def computeAndSaveAllRationalEllipticCurvesWithGoodReductionOutsideS(S=[],additionalPrimeMax=None,randomOrder=False,reverseExponents=False,verbose=True,useSagesAlgorithmForSintegralPoints=False,saveToFile=True,saveToPath=pathData,compareWithCremonaDB=False):
	#If additionalPrime!=None, then we add to S an additional prime p<=additionalPrimeMax, and
	#compute then all E/Q with good reduction outside this enlarged set, for each such p.

	t00 = walltime();

	if additionalPrimeMax==None:
		pRange = [1];
	else:
		pRange = [p for p in prime_range(1,1+additionalPrimeMax) if p not in S];

	solutions = [];

	for p in pRange:
		if p==1:
			Sp = copy(S);
		else:
			Sp = S + [p];
		print "======================= S =",Sp;
		solutions_for_Sp = computeAllRationalEllipticCurvesWithGoodReductionOutsideS(S=Sp,randomOrder=randomOrder,reverseExponents=reverseExponents,verbose=verbose,useSagesAlgorithmForSintegralPoints=useSagesAlgorithmForSintegralPoints,compareWithCremonaDB=compareWithCremonaDB);

		if p==1:
			solutions_for_Sp = (S,solutions_for_Sp);
		else:
			solutions_for_Sp = (Sp,solutions_for_Sp);
		solutions.append(solutions_for_Sp);

	curves = set([]);
	for (Sp,solutions_for_Sp) in solutions:
		curves.update(set(solutions_for_Sp));

	numCurves = len(curves);

	totalTime = walltime(t00);

	if saveToFile:
		filename = "curves_"; #+myListToStr([a,b,c,d],"_");
		filename += "_S_"+myListToStr(S,'_');
		if additionalPrimeMax!=None:
			filename +="_p_pMax"+str(additionalPrimeMax);
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all rational elliptic curves with good reduction outside S, up to Q-isomorphisms,\n");
		if additionalPrimeMax == None:
			out.write("# where S = {"+myListToStr(S,', ')+"}.\n");
			out.write("# It contains "+str(numCurves)+" pairs (c4,c6).\n");
		else:
			out.write("# for all sets S = {"+myListToStr(S,', ')+", p},\n");
			out.write("# where p ranges over all other primes less or equal to "+str(additionalPrimeMax)+".\n");
			out.write("# It contains "+str(numCurves)+" pairs (c4,c6), some of which may appear for more than one S.\n");
		out.write('# Format: "(c4,c6)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for (Sp,solutions_for_Sp) in solutions:
			if additionalPrimeMax != None:
				out.write("#\n");
				out.write("# S = {"+myListToStr(Sp,', ')+"}:\n");
				out.write("#\n");
			for (c4,c6) in solutions_for_Sp:
				out.write("(%s,%s)\n" % (str(c4),str(c6)));
		out.close();

	print "Number of curves:",numCurves;

	return solutions;

def computeAndSaveAllRationalEllipticCurvesWithGoodReductionOutsideSForBoundedS(maxBound=100,minBound=None,boundType="NS",allowSingletons=True,useSagesAlgorithmForSintegralPoints=False,saveToFile=True,saveToPath=pathData,compareWithCremonaDB=False,mwCache=None,verbose=True):

	t00 = walltime();

	if mwCache==None:
		#mwCache = load_full_mwBasisCache_as_dict(cacheFileName="mwMordellS.sobj");
		mwCache = load_full_mwBasisCache_as_dict();
	if verbose:
		print "Compute all rational elliptic curves with good reduction outside some S with",boundType,"bounded by",minBound,"and",maxBound;

	def boundForS(S,boundType=boundType):
		if boundType == "NS":
			return N_S(S);
		elif boundType == "MS":
			return M_S(S);
		else:
			raise NotImplementedError("Unknown boundType.");

	def getSs(maxBound,boundType,allowSingletons):
		if boundType == "NS":
			return setsSOfPrimesWithBoundedNS(maxBound,allowSingletons);
		elif boundType == "MS":
			return setsSOfPrimesWithBoundedMS(maxBound,allowSingletons);
		else:
			raise NotImplementedError("Unknown boundType.");
		
	Ss = getSs(maxBound,boundType,allowSingletons);
	if minBound != None:
		Ss = set([S for S in Ss if boundForS(S)>=minBound]);
		
	
	sortedSs = list(Ss);
	#sortedSs.sort();
	#sortedSs.sort(key = len);
	def compareTwoSs(S1,S2):
		if len(S1)!=len(S2):
			return cmp(len(S1),len(S2));
		else:
			return cmp(S1,S2);
	sortedSs.sort(cmp = compareTwoSs);
	
	print "sortedSs:",sortedSs;
	print "len(Ss):",len(Ss);

	#return 0; #debug

	solutions = [];

	for S in sortedSs:
		solutions_for_S = computeAllRationalEllipticCurvesWithGoodReductionOutsideS(S=list(S),randomOrder=False,reverseExponents=False,verbose=True,useSagesAlgorithmForSintegralPoints=useSagesAlgorithmForSintegralPoints,compareWithCremonaDB=compareWithCremonaDB,mwCache=mwCache);
		solutions.append((S,solutions_for_S));

	curves = set([]);
	for (S,solutions_for_S) in solutions:
		curves.update(set(solutions_for_S));

	numCurves = len(curves);

	totalTime = walltime(t00);

	if saveToFile:
		filename = "curves";
		filename += "_max"+boundType+"_"+str(maxBound);
		if minBound != None:
			filename += "_min"+boundType+"_"+str(minBound);
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		fancyName = {"NS":"N_S", "MS":"M_S"};

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all rational elliptic curves with good reduction outside S, up to Q-isomorphisms,\n");
		out.write("# where S ranges over all finite sets of rational primes with\n");
		if minBound != None:
			out.write("# "+str(minBound)+" <= "+fancyName[boundType]+" <= "+str(maxBound)+",\n");
		else:
			out.write("# "+fancyName[boundType]+" <= "+str(maxBound)+",\n");
		if boundType == "NS":
			out.write("# and "+fancyName[boundType]+" = prod_{p in S} p.\n");
		elif boundType == "MS":
			out.write("# and "+fancyName[boundType]+" = prod_{p in S} p^{f_p}, where f_2 = 8, f_3 = 5, and f_p = 2. for p >= 5.\n");
		out.write("# It contains "+str(numCurves)+" pairs (c4,c6), some of which may appear for more than one S.\n");
		out.write('# Format: "(c4,c6)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for (S,solutions_for_S) in solutions:
			out.write("#\n");
			out.write("# S = {"+myListToStr(S,', ')+"}:\n");
			out.write("#\n");
			for (c4,c6) in solutions_for_S:
				out.write("(%s,%s)\n" % (str(c4),str(c6)));
		out.close();

	print "Number of curves:",numCurves;

	return solutions;

#S={2}: 24 curves/Q, 5 js.
#S={2,3}: 752 curves/Q, 83 js.
#S={2,3,5}: 7600 curves/Q, 442 js.
#S={2,3,5,7}: 71520 curves/Q, 2140 js.
#S={2,3,5,7,11}: 592192 curves/Q, ???? js.

def testConjectureOnNumberOfEllipticCurves(saveToFile=True):

	#The code of this method can be easily optimized in its running time...

	global pathData;

	'''
	Ss = [];
	for p in prime_range(3,1+250):
		Ss.append([2,p]);
	for p in prime_range(5,1+100):
		Ss.append([2,3,p]);
	for p in prime_range(7,1+31):
		Ss.append([2,3,5,p]);
	Ss.append([2,3,5,7,11]);
	c4c6s = [];
	'''

	S_c4c6s = [];
	S_c4c6s += load(pathData + "curves__S_2_p_pMax250.sobj");
	S_c4c6s += load(pathData + "curves__S_2_3_p_pMax100.sobj");
	S_c4c6s += load(pathData + "curves__S_2_3_5_p_pMax31.sobj");
	#S_c4c6s += load(pathData + "curves__S_2_3_5_7_11.sobj");
	#S_c4c6s += load(pathData + "curves_maxMS_1000000.sobj");
	#S_c4c6s += load(pathData + "curves_maxNS_1000.sobj");

	
	Ss = [];
	c4c6s = set([]);
	for S,c4c6s_forS in S_c4c6s:
		Ss.append(S);
		c4c6s.update(set(c4c6s_forS));
	print "Ss:",Ss;
	print "#c4c6s:",len(c4c6s);

	subSs = set([]);
	for S in Ss:
		for subS in Combinations(S):
			if subS!=[]:
				subSlist = list(subS);
				subSlist.sort();
				subSs.add(tuple(subSlist));
	subSsList = list(subSs);
	subSsList.sort();
	subSsList.sort(key = lambda(subS): len(subS));
	print "#subSs:",len(subSs);

	numCurves_per_S = {};
	js_per_S = {};
	for subS in subSs:
		numCurves_per_S[subS] = 0;
		js_per_S[subS] = set([]);

	for (c4,c6) in c4c6s:
		E = EllipticCurve_from_c4c6(c4,c6);
		E = E.minimal_model();
		for subS in subSs:
			if E.has_good_reduction_outside_S(list(subS)):
				numCurves_per_S[subS] += 1;
				js_per_S[subS].add(E.j_invariant());

	for subS in subSsList:
		print subS,":",numCurves_per_S[subS],len(js_per_S[subS]),len([j for j in js_per_S[subS] if j>0]);

	if saveToFile:
		filename = pathData + "numberOfCurves";
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of certain finite sets S of rational primes together with\n");
		out.write("# the number of rational elliptic curves up to rational isomorphisms\n");
		out.write("# with good reduction outside S.\n");
		out.write("# Number curves in whole database: "+str(len(c4c6s))+"\n");
		out.write("# Number of sets S in the following list: "+str(subS)+"\n");
		#out.write('# Format: "S: numberOfCurves".\n');
		#out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for subS in subSsList:
			out.write("# S = {"+myListToStr(subS,', ')+"}: "+str(numCurves_per_S[subS])+"\n");
		out.close();

		filename = pathData + "numberOfJs";
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of certain finite sets S of rational primes together with\n");
		out.write("# the number of j-invariants of rational elliptic curves up to rational isomorphisms\n");
		out.write("# with good reduction outside S.\n");
		out.write("# Number curves in whole database: "+str(len(c4c6s))+"\n");
		out.write("# Number of sets S in the following list: "+str(subS)+"\n");
		#out.write('# Format: "S: numberOfCurves".\n');
		#out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for subS in subSsList:
			out.write("# S = {"+myListToStr(subS,', ')+"}: "+str(len(js_per_S[subS]))+"\n");
		out.close();

def testConjectureOnNumberOfEllipticCurves2():
	numberOfCurves_n = [0,24,752,7600,71520,592192];
	print "number of curves for S(n):",numberOfCurves_n;
	c = numberOfCurves_n;
	for n in range(len(c)):
		print n,log(c[n].n())/n;

########################################################################
### Test elliptic curve data base: ####################################
########################################################################

def solveSUnitEquationViaOurEllipticCurveDB(S=[2]):

	def curvesFromABCsq(abcSq,S):
		solutionsABC = set([]);
		if abcSq <= 0:
			return solutionsABC;
		if abcSq.is_square() == False:
			return solutionsABC;
		abc = ZZ(sqrt(abcSq));
		s = prime_divisors(abc);
		if not all(p in S for p in s):
			return solutionsABC;
		primePowersABC = [p^abc.ord(p) for p in s];
		for primePowersA in subsets(primePowersABC):
			a = prod(primePowersA);
			primePowersBC = [x for x in primePowersABC if x not in primePowersA];
			for primePowersB in subsets(primePowersBC):
				primePowersC = [x for x in primePowersBC if x not in primePowersB];
				b = prod(primePowersB);
				c = prod(primePowersC);
				list_abc = [a,b,c];
				list_abc.sort();
				a0,b0,c0 = tuple(list_abc);
				if a0 + b0 == c0:
					solutionsABC.add((a0,b0,c0));
		return solutionsABC;
	
	curvesDB = load(pathData+"curves__S_"+myListToStr(S,"_")+".sobj");
	curves = set([]);
	for s,curves_s in curvesDB:
		curves.update(set(curves_s));
	print "#Curves in DB:",len(curves);

	solutions = set([]);
	for c4,c6 in curves:
		E = EllipticCurve_from_c4c6(c4,c6);
		E = E.minimal_model();
		Delta = E.discriminant();
		if Delta % 2^4 == 0:
			solutions.update(curvesFromABCsq(abs(Delta/2^4),S));
		solutions.update(curvesFromABCsq(abs(Delta*2^8),S));

	print "len(solutions):",len(solutions);

#sage: solveSUnitEquationViaOurEllipticCurveDB(S=primes_first_n(1))
##Curves in DB: 24
#len(solutions): 1
#sage: solveSUnitEquationViaOurEllipticCurveDB(S=primes_first_n(2))
##Curves in DB: 752
#len(solutions): 4
#sage: solveSUnitEquationViaOurEllipticCurveDB(S=primes_first_n(3))
##Curves in DB: 7600
#len(solutions): 17
#sage: solveSUnitEquationViaOurEllipticCurveDB(S=primes_first_n(4))
##Curves in DB: 71520
#len(solutions): 63
#sage: solveSUnitEquationViaOurEllipticCurveDB(S=primes_first_n(5))
##Curves in DB: 592192
#len(solutions): 190

########################################################################
### S-integral points on elliptic curves in Cremona's DB: ##############
########################################################################

def saveCremonasDBwithMWBasesToFile(maxN=10000):
	global pathMordellWeil;
	label_a_mws = [];
	cremonaDB = CremonaDatabase();
	for N in range(1+maxN):
		print "==== N:",N;
		mwDict = cremonaDB.allgens(N);
		#print "mwDict:",mwDict;
		label_coeff = [(label,coeff) for (label,coeff) in cremonaDB.allcurves(N).iteritems()];
		label_coeff.sort();
		for label,coeff in label_coeff:
			print "label:",label;
			fullLabel = str(N)+label;
			a_invariants = coeff[0];
			mwBasis = mwDict[label];
			label_a_mws.append((fullLabel,a_invariants,mwBasis));
	print "num curves:",len(label_a_mws);
	save(label_a_mws,pathMordellWeil+"mwCremonaDB"+str(maxN)+".sobj");

def computeSIntegralPointsForCremonasDB(maxN=20,S=[],saveToFile=True,saveToPath=pathData,in_parallel=True,verbose_local=False):
	t00 = walltime();
	
	print "Compute all S-integral points on all rational elliptic curves (in Cremona's DB) up to N <=",maxN,"for S =",S,".";
	
	parameters = [];

	'''
	cremonaDB = CremonaDatabase();
	#for E in curves:
	for N in range(1+maxN):
		print "==== N:",N;
		mwDict = cremonaDB.allgens(N);
		print "mwDict:",mwDict;
		for label,coeff in cremonaDB.allcurves(N).iteritems():
			print "label:",label;
			a_invariants = coeff[0];
			E_local = EllipticCurve(a_invariants);
			S_local = S;
			mwBasis_local = mwDict[label]; #E.gens(); #cremonaDB.allgens(E.conductor())[E.cremona_label()];
	'''

	global pathMordellWeil;
	if maxN <= 10000:
		label_a_mws = load(pathMordellWeil+"mwCremonaDB10000.sobj");
	elif maxN <= 100000:
		label_a_mws = load(pathMordellWeil+"mwCremonaDB100000.sobj");
	else:
		raise ValueError("maxN is bigger than the part of the database that we stored.");

	for label,a_invariants,mw in label_a_mws:
		E_local = EllipticCurve(a_invariants);
		if E_local.conductor()>maxN:
			break;
		S_local = S;
		mwBasis_local = mw;
		Mmax0_local = None;
		verbose_local = verbose_local;
		bothSigns_local = True;
		saveToFile_local = False;
		saveToPath_local = saveToPath;
		debugParam_local = {};
		param = (E_local,S_local,mwBasis_local,Mmax0_local,verbose_local,bothSigns_local,saveToFile_local,saveToPath_local,debugParam_local);

		if len(mw)>=2:
			print "debug: rank =",len(mw),"for index",len(parameters);

		parameters.append(param);
		if len(S)<=100 and maxN<=100:
			print param;

	solutions = [];
	solutionsDict = {}; #This dict is only used for sorting the solutions via E in the same way as the E's are ordered in Cremona's DB.

	if in_parallel:
		results = my_run_in_parallel(parameters,computeSIntegralPoints,print_param=False,print_result=False,return_param_index=True);
		print "#results:",len(results);

		for i,solutions_for_E in results:
			param = parameters[i];
			E = param[0];
			solutions_for_E = list(solutions_for_E);
			#solutions_for_E.sort();
			solutionsDict[E.label()] = solutions_for_E;

		print "#solutions:",len(solutions);
			
	else:
		for param in parameters:
			E_local = param[0];
			print "============================";
			print "E:",E;
			solutions_for_E = computeSIntegralPoints(param[0],param[1],param[2],param[3],param[4],param[5],param[6],param[7],param[8]);
			solutions_for_E = list(solutions_for_E);
			#solutions_for_E.sort();
			solutionsDict[E.label()] = solutions_for_E;

	print "All labels:",solutionsDict.keys();

	for label,a_invariants,mw in label_a_mws:
		E_local = EllipticCurve(a_invariants);
		if E_local.conductor()>maxN:
			break;
		fullLabel = E_local.label();
		solutions_for_E = solutionsDict[fullLabel];
		solutions.append((E_local.a_invariants(),solutions_for_E));

	numSolutions = sum([len(sols) for (a_invariants,sols) in solutions]);
	totalTime = walltime(t00);

	#solutions.sort();

	print "sorted solutions:",solutions;

	if saveToFile:
		filename = "sIntegralPoints_"; 
		filename += "_maxN"+str(maxN);
		if S==primes_first_n(len(S)):
			filename += "_n"+str(len(S));
		else:
			filename += "_S_"+myListToStr(S,'_');
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all S-integral points on all rational elliptic curves (using Cremona's database) up to conductor "+str(maxN)+",\n");
		if S==primes_first_n(len(S)):
			out.write("# where S is the set of the first "+str(len(S))+" primes.\n");
		else:
			out.write("# where S = {"+myListToStr(S,',')+"}.\n");
		out.write("# It contains "+str(numSolutions)+" points in total.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		for a_invariants,sols in solutions:
			out.write("#\n");
			E = EllipticCurve(a_invariants);
			out.write("# a-invariants: ("+myListToStr(E.a_invariants(),", ")+")\n");
			out.write("# Cremona label: "+E.cremona_label()+"\n");
			out.write("#\n");
			for P in sols:
				out.write("(%s,%s)\n" % (str(P[0]),str(P[1])));
		out.close();

	print "Number of solutions:",numSolutions;

	return solutions;

#smallest N of a rank 1 curve: 37
#smallest N of a rank 2 curve: 389
#smallest N of a rank 3 curve: 5077 (bis N<10000 nur seine solche Rang-3-Kurve)
#smallest N of a rank 4 curve: 234446

########################################################################
### Solving x + y = z^2: ###############################################
########################################################################

def solveSumsOfUnitsBeingASquare(S=[],mwBasesDict=None,saveToFile=True,saveToPath=pathData,verbose=True):
	#We solve the equation m + n = z^2, such that
	#m,n,z are integers, and m,n are S-units, and gcd(m,n) is square-free.
	#We assume w.l.o.g. m>=n.

	t00 = walltime();
	solutions = set([]);

	#We reduce it to Ramanujan-Nagell equations with (b,c=1,S), where b runs over all negative divisors of N_S.
	#We write m = -b*u^2 with b,u in ZZ and b|N_S,
	#         n = y*u^2, and
	#  define x = z/u.
	#Then m + n = z^2 turns into
	#    -b + y = x^2, i.e. x^2 + b = y.

	if mwBasesDict == None:
		mwBasesDict = load_full_mwBasisCache_as_dict();
	s = len(S);
	Exponents = [w for w in Words([0,1],s)];
	#if reverseExponents:
	#	Exponents.reverse();			
	for exponents in Exponents:
		b = -prod([S[i]^exponents[i] for i in range(s)]);
		if verbose:
			print "----------------------------------------------====", "exponents:",exponents,"b =",b;
		solutions_for_b = solveRamanujanNagellEquation_XY(b,c=1,S=S,mwBasesDict=mwBasesDict,verbose=True,saveMWToCache=True,saveToFile=False,reverseExponents=False);

		for (x,y) in solutions_for_b:
			z = x.numerator();
			u = x.denominator();
			m = -b*u^2;
			n = y*u^2;
			m, n = max(m,n), min(m,n);
			solutions.add((m,n));
			print "solution:",(m,n);

	numSolutions = len(solutions);
	solutionsList = list(solutions);
	solutionsList.sort();

	totalTime = walltime(t00);

	if saveToFile:
		filename = "sumsOfUnitsBeingASquare_"; 
		#if S==primes_first_n(len(S)):
		#	filename += "_n"+str(len(S));
		#else:
		#filename += "_S_"+myListToStr(S,'_');
		filename += "_S_"+myListToStr(S,'_');
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutionsList,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all pairs of integers (x,y) such that\n");
		out.write("# x + y is a square, gcd(x,y) is square-free, and the only primes dividing x and y lie in S,\n");
		if S==primes_first_n(len(S)):
			out.write("# where S is the set of the first "+str(len(S))+" primes;\n");
		else:
			out.write("# where S = {"+myListToStr(S,',')+"};\n");
		out.write("# and furthermore we break symmetries by requiring x >= y.\n");
		out.write("# It contains "+str(numSolutions)+" pairs in total.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for (m,n) in solutionsList:
			out.write("(%s,%s)\n" % (str(m),str(n)));
		out.close();
		
	print "#solutions:",numSolutions;
	return solutionsList;
	
def solveManySumsOfUnitsBeingASquare(S=[],additionalPrimeMax=None,mwBasesDict=None,saveToFile=True,saveToPath=pathData):
	#If additionalPrime!=None, then we add to S an additional prime p<=additionalPrimeMax for each such p.

	t00 = walltime();

	if mwBasesDict == None:
		mwBasesDict = load_full_mwBasisCache_as_dict();

	if additionalPrimeMax==None:
		pRange = [1];
	else:
		pRange = [p for p in prime_range(1,1+additionalPrimeMax) if p not in S];
	solutions = [];
	for p in pRange:
		if p==1:
			Sp = copy(S);
		else:
			Sp = S + [p];
		print "======================= S =",Sp;
		solutions_for_Sp = solveSumsOfUnitsBeingASquare(S=Sp,mwBasesDict=mwBasesDict,verbose=verbose,saveToFile=False);

		if p==1:
			solutions_for_Sp = (S,solutions_for_Sp);
		else:
			solutions_for_Sp = (Sp,solutions_for_Sp);
		solutions.append(solutions_for_Sp);
	pairs = set([]);
	for (Sp,solutions_for_Sp) in solutions:
		pairs.update(set(solutions_for_Sp));
	numPairs = len(pairs);
	totalTime = walltime(t00);
	if saveToFile:
		filename = "sumsOfUnitsBeingASquare_";
		filename += "_S_"+myListToStr(S,'_');
		if additionalPrimeMax!=None:
			filename +="_p_pMax"+str(additionalPrimeMax);
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all pairs of integers (x,y) such that\n");
		out.write("# x + y is a square, gcd(x,y) is square-free, x >= y, and the only primes dividing x and y lie in S,\n");
		if additionalPrimeMax == None:
			out.write("# where S = {"+myListToStr(S,', ')+"}.\n");
			out.write("# It contains "+str(numPairs)+" pairs (x,y).\n");
		else:
			out.write("# for all sets S = {"+myListToStr(S,', ')+", p},\n");
			out.write("# where p ranges over all other primes less or equal to "+str(additionalPrimeMax)+".\n");
			out.write("# It contains "+str(numPairs)+" pairs (x,y), some of which may appear for more than one S.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for (Sp,solutions_for_Sp) in solutions:
			if additionalPrimeMax != None:
				out.write("#\n");
				out.write("# S = {"+myListToStr(Sp,', ')+"}:\n");
				out.write("#\n");
			for (m,n) in solutions_for_Sp:
				out.write("(%s,%s)\n" % (str(m),str(n)));
		out.close();

	print "Number of pairs:",numPairs;

	return solutions;

########################################################################
### Solving x + y = z^3: ###############################################
########################################################################

def solveSumsOfUnitsBeingACube(S=[],mwBasesDict=None,saveToFile=True,saveToPath=pathData,verbose=True,removeTrivialSolutions=False):
	#We solve the equation m + n = z^3, such that
	#m,n,z are integers, and m,n are S-units, and gcd(m,n) is cube-free.
	#We assume w.l.o.g. m>=n and abs(m)>=abs(n).

	t00 = walltime();
	solutions = set([]);

	#We reduce it to 2*6^|S| many Mordell equations.
	#m = m'^3 * m0, mit m'| N_S^2.
	#Then m0 + n/m'^3 = (z/m')^3.
	#x := z/m' is S-integer
	#y := n/m'^3 is S-unit
	#Then m0 + y = x^3.
	#y = w*y'^2, w in ZZ, w|N_S, y' S-unit.
	#Put X := xw, Y := y'*w^2, a := -m0*w^3.
	#Y^2 = X^3 + a.
	#Compare with proof of Corollary 9.3(ii) in the paper.

	if mwBasesDict == None:
		mwBasesDict = load_full_mwBasisCache_as_dict();
	s = len(S);
	for exp_m0 in [word for word in Words([0,1,2],s)]:
		m0 = prod([S[i]^exp_m0[i] for i in range(s)]);

		for sign_w in [-1,+1]:
			for exp_w in [word for word in Words([0,1],s)]:
				w = sign_w * prod([S[i]^exp_w[i] for i in range(s)]);
				a = -m0*w^3;
				if verbose:
					print "---------------------------------------------";
					print "a =",a;
				E = mordellCurve(a);
				mwBasis = load_mwBasis_from_cache(a,mwCacheDict=mwBasesDict);
				solutions_for_a = computeSIntegralPoints(E=E,S=S,mwBasis=mwBasis,saveToFile=False,verbose=False);
				print "Mordell equation has",len(solutions_for_a),"solutions.";
				for P in solutions_for_a:
					X = P[0];
					Y = P[1];
					x = X/w;
					yp = Y/w^2;
					y = yp^2*w;
					z = x.numerator();
					mp = x.denominator();
					n = ZZ(y*mp^3);
					m = ZZ(mp^3*m0);
					m, n = max(m,n), min(m,n);
					if abs(m)<abs(n): #break symmetry
						continue;
					if removeTrivialSolutions and n==-m:
						continue;
					if QQ(m).is_S_unit(S) and QQ(n).is_S_unit(S):
						solutions.add((m,n));
						print "solution:",(m,n),"and check:",(m+n)^(1/3);

	numSolutions = len(solutions);
	solutionsList = list(solutions);
	solutionsList.sort();

	totalTime = walltime(t00);

	if saveToFile:
		filename = "sumsOfUnitsBeingACube_"; 
		#if S==primes_first_n(len(S)):
		#	filename += "_n"+str(len(S));
		#else:
		#filename += "_S_"+myListToStr(S,'_');
		filename += "_S_"+myListToStr(S,'_');
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutionsList,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all pairs of integers (x,y) such that\n");
		out.write("# x + y is a cube, gcd(x,y) is cube-free, and the only primes dividing x and y lie in S,\n");
		if S==primes_first_n(len(S)):
			out.write("# where S is the set of the first "+str(len(S))+" primes;\n");
		else:
			out.write("# where S = {"+myListToStr(S,',')+"};\n");
		out.write("# and furthermore we break symmetries by requiring x >= y and |x| >= |y|.\n");
		out.write("# It contains "+str(numSolutions)+" pairs in total.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for (m,n) in solutionsList:
			out.write("(%s,%s)\n" % (str(m),str(n)));
		out.close();
		
	print "#solutions:",numSolutions;
	return solutionsList;
	
def solveManySumsOfUnitsBeingACube(S=[],additionalPrimeMax=None,mwBasesDict=None,saveToFile=True,saveToPath=pathData):
	#If additionalPrime!=None, then we add to S an additional prime p<=additionalPrimeMax for each such p.

	t00 = walltime();

	if mwBasesDict == None:
		mwBasesDict = load_full_mwBasisCache_as_dict();

	if additionalPrimeMax==None:
		pRange = [1];
	else:
		pRange = [p for p in prime_range(1,1+additionalPrimeMax) if p not in S];
	solutions = [];
	for p in pRange:
		if p==1:
			Sp = copy(S);
		else:
			Sp = S + [p];
		print "======================= S =",Sp;
		solutions_for_Sp = solveSumsOfUnitsBeingACube(S=Sp,mwBasesDict=mwBasesDict,verbose=verbose,saveToFile=False);

		if p==1:
			solutions_for_Sp = (S,solutions_for_Sp);
		else:
			solutions_for_Sp = (Sp,solutions_for_Sp);
		solutions.append(solutions_for_Sp);
	pairs = set([]);
	for (Sp,solutions_for_Sp) in solutions:
		pairs.update(set(solutions_for_Sp));
	numPairs = len(pairs);
	totalTime = walltime(t00);
	if saveToFile:
		filename = "sumsOfUnitsBeingACube_";
		filename += "_S_"+myListToStr(S,'_');
		if additionalPrimeMax!=None:
			filename +="_p_pMax"+str(additionalPrimeMax);
		if saveToPath != None:
			if not saveToPath.endswith("/"):
				saveToPath += "/";
			filename = saveToPath + filename;
			if not os.path.exists(os.path.dirname(filename)):
				os.makedirs(os.path.dirname(filename))
			
		save(solutions,filename);

		#Furthermore save the solutions to a text file:
		out = file(filename+'.txt','w')
		#out.write("###\n");
		out.write("# List of all pairs of integers (x,y) such that\n");
		out.write("# x + y is a cube, gcd(x,y) is cube-free, x >= y, |x| >= |y|, and the only primes dividing x and y lie in S,\n");
		if additionalPrimeMax == None:
			out.write("# where S = {"+myListToStr(S,', ')+"}.\n");
			out.write("# It contains "+str(numPairs)+" pairs (x,y).\n");
		else:
			out.write("# for all sets S = {"+myListToStr(S,', ')+", p},\n");
			out.write("# where p ranges over all other primes less or equal to "+str(additionalPrimeMax)+".\n");
			out.write("# It contains "+str(numPairs)+" pairs (x,y), some of which may appear for more than one S.\n");
		out.write('# Format: "(x,y)".\n');
		out.write("# Computing this list took "+str(ceil(totalTime))+" seconds.\n");
		out.write("# Authors: Rafael von Känel and Benjamin Matschke, 2015.\n");
		out.write("# License: Creative commons 3.0 by-nc.\n");
		out.write("#\n");
		for (Sp,solutions_for_Sp) in solutions:
			if additionalPrimeMax != None:
				out.write("#\n");
				out.write("# S = {"+myListToStr(Sp,', ')+"}:\n");
				out.write("#\n");
			for (m,n) in solutions_for_Sp:
				out.write("(%s,%s)\n" % (str(m),str(n)));
		out.close();

	print "Number of pairs:",numPairs;

	return solutions;

########################################################################
### Testing rank of Mordell equations: #################################
########################################################################

def testSmallRankMordellCurves():
	n = 0;
	for k in range(1,1+10):
		E = mordellCurve(k+1234567890123);
		ar = E.analytic_rank();
		print k,ar
		if ar<=1:
			n += 1;
		#print k, E.analytic_rank_upper_bound();
	print "n =",n;

#time testSmallRankMordellCurves();

########################################################################
### Testing some Mordell equations: ####################################
########################################################################

'''
List of 10^k th primes:
0                2
1               29
2              541
3            7.919
4          104.729
5        1.299.709
6       15.485.863
7      179.424.673
8    2.038.074.743
9   22.801.763.489
10 252.097.800.623
'''

#computeSIntegralPointsForManymordellCurves(100,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(1000,rank=1,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(200,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(2000,rank=1,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(300,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(3000,rank=1,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(400,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(4000,rank=1,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(500,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(5000,rank=1,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(600,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(6000,rank=1,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(700,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(7000,rank=1,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(800,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(8000,rank=1,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(900,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(9000,rank=1,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(1000,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(10000,rank=1,maxA=100,verbose=True);

a = kPosOfRank[1];
#a = kPosOfRank[2];
#a = kPosOfRank[3];
#a = kPosOfRank[4];
#a = kPosOfRank[5];
#a = kPosOfRank[6];
#a = kPosOfRank[7]; #from here on Sage gives a warning that the MW bases that it computes may not be fully saturated. Take instead the bases below.
#a = kPosOfRank[8];
#a = kPosOfRank[9];
#a = kPosOfRank[12];
#a = 225; #The associated E has rank 2 and torsion order 3.
#a = 16; #The associated E is non-minimal at 2, and of rank 0.
#a = 80; #The associated E is non-minimal and of rank 1.
#a = 8; #Contains a point (2,0) whose x-coodinate has only 1 lift (-> a 2-torsion point).
#a = -432
#a = -1215000; #Has problems to compute MW-basis
#a = 10^8+1; #rank 2
#a = 956; #first reduction at 2 yields Mmaxes[2] = 0.
#a = 7823; #has rank 1 with huge MW-basis generator, roughly of height 77. GPZ were missing its MW basis.
#a = -4347;
#a = -7779240000;
#a = -7086; #not saturated in GPZ97! (rank 1)
#a = -6789; #not saturated in GPZ97! (rank 1)
#a = -9353; #rank 1, with generator of height 140.98
#a = -48;
#a = 3489; #debug
#a = -1825200; #running time test, is used for Thue equation 0,1,1,0,65.
E = EllipticCurve([0,0,0,0,a])

if my_mwBasis_for_mordellCurves.has_key(a):
	basis = my_mwBasis_for_mordellCurves[a];
else:
	basis = None;

#E = EllipticCurve([0,1,1,-2,0]); #Example of Smart[ca '95]

#S = primes_first_n(100);
#E = EllipticCurve([1,-1,0,849,-25939]); basis = [(62, 481)]; #Raises a PrecisionError during my_padic_elliptic_logarithm() (which is completely fine, but previously we only caught ZeroDivisionErrors).
#E = EllipticCurve([1,0,0,-5037552,4351465395]); basis = [(1302, -261)]; #Made Mmax=+Infinity because for the PGHZ-Bound it computed Delta1=0.?e15, because it was not computed numerically stable.
#E = EllipticCurve([0,-1,1,-2,0]); basis = [(-1, 0), (0, 0)]; #Broke at some point because of lack of memory.
#time computeSIntegralPoints(E,S=S,mwBasis=basis,saveToFile=False,saveToPath=pathData,verbose=True);

#Stroeker-Tzanakis vom Rang 6:
#E = EllipticCurve

#Curve (Kretschmer) in Siksek's Paper of rank 8 with known MW-basis (unconditionally):
#E = EllipticCurve([1,0,0,-5818216808130,5401285759982786436]);
#basis = [(1410240,-29977314),(1704648,-661672482),(1421184,-55353570),(259761720/125,-189069355038/125),(4740024,9180268266),(975216,808674546),(7028688,-17659711842),(-2623596,-1613325930)]

#Mestre curve of rank 12, for which MW-basis is known up to BSD (due to Siksek '95):
#E = EllipticCurve([0,0,1,-6349808647,193146346911036]);
#basis = [(49421,200114),(49493,333458),(2739835340/5041,141949849330392/357911),(49632,502899),(49667,538049),(49797,654674),(38756,-2294721),(208314,88938858),(50165,921837),(50215,954017),(50823,1305633),(51108,1454591)];

#Rank 14 curve von Fermigier (1996) (rank known exactly, but basis might NOT be saturated!):
#E = EllipticCurve([0,1,0,-1692310759026568999140789578145,839379398840982294584587970773038145228669599]);
#basis = [(988927329611391, 11530632350958995292984),(681925764652050, 1568465432141985518043),(982479697930607, 11183605599461162465976),(665315262684159, 2820867968019861832248),(816133831449855, 1353961721252033023032),(20572279820626749/25, 250389733064763724244532/125),(681455320541454489/841, 8773166366975333247857352/24389),(8076800853180114, 716978870073714829212603),(7335280971697741/9, 33055815750694859233124/27),(457957201387226901/529, 58522059114298646792700636/12167),(127856380845197460021/625, 1445688913020859355673024573444/15625),(435462740765918268153/157609, 8219252385969460300109469047112/62570773),(811768719821415721233/18769, 23118208949065563006261517438272/2571353),(299475331388281185601/345744, 983394088087157723809198920329/203297472)];
#basis = [E(P) for P in basis];

#Rang 17 curve by Elkies (2005) (rank known exactly, but basis might NOT be saturated):
#From https://web.math.pmf.unizg.hr/~duje/tors/rkeq17.html
#Also directly from [Elkies, NMBRTHRY Archives June 2005], with different points, but both generate the same subgroup of E(Q).
#E = EllipticCurve([1,0,1,-957089489055751752507625259831765957846101,351598252970651757672333752869879740192822872602430248013582348]);
#basis = [(1037048102780198794447, 21779881979625846052436063081576),(640151922319155456727, 1116379497785052017163204160436),(8215515531545032362283/4, 671712937153262899818205610666563/8),(-252494436924143857397/4, 162335292364600094400633862613143/8),(3033356276097950346763/4, 62943339550041852920918618404183/8),(-697039650804322492943, 26077977524885678965262644558346),(11414518769372982291382, 1215170223607965741833261815562846),(891674633090402503696, 14392420123651702644251835214211),(94919125996596744048847, 29242036615099659730101568678875176),(636565095929048595313, 542487929999796513742831489802),(4202001410067480893647, 265563310660870839720550898955176),(438987621400369262071, 4005643151170292277973367502092),(-1055345243070301537073, 13647840402839172835783080260936),(-1120995419674665243803, 3976668559063776088092945926576),(476001270991734096802, 1968115763191782636541113312386),(639949947842762264623, 1091505880400660592954070253744),(45374293429909818890233/64, 2776529523851458968917039502401287/512)];
#basis = [E(P) for P in basis];

#Rang 19 curve by Elkies (2009) (rank known exactly, but basis might NOT be saturated):
#E = EllipticCurve([1,-1,1,31368015812338065133318565292206590792820353345,302038802698566087335643188429543498624522041683874493555186062568159847]);
#basis = [(-499155234006326082923757, 402509376386904307636088023311932246),(14139901902190764472167779, 53177370026792370019660919624681843910),(165026138566397083648829, 558309596396209485460849837556760960),(463343337635697262499219, 645016881525945325912024782026024790),(-428490311544140084738931, 458176166275251046654351925125281840),(-3076708833879670305775, 549492732729622717403028037016638716),(-37665731401560276357421, 548455893205160937812792765224762710),(-589425676522172250643765, 280659706984671022310703064556433246),(-481732375371853545253165, 418490225997586738600806619185884118),(3690858926941989311074375079, 224228684581316592254479552957274125288710),(6130049174458433978294529, 15193625860788829982804926312716459660),(99629044314032316202835, 553310835513576760020037678256777046),(-336069400109872546513581, 503527960099926164391149483607861590),(3296316187302021571885259, 6018489996489383086719697427657451870),(239450610550684059490919, 568576446830597022058144468592457990),(1116036406771517906484819, 1314196172527374653201729069765173590),(1104492511976272577147219, 1297713008801587828896903435227547990),(-556915090457934898225581, 334424588793955899397684278466715990),(142518206539016399870550419, 1701397854372553501423223969798389683990)];
#basis = [E(P) for P in basis];

#Elkies curve of rank >= 28, with 28 independed points (probably NO basis!):
E = EllipticCurve([1,-1,1,-20067762415575526585033208209338542750930230312178956502,34481611795030556467032985690390720374855944359319180361266008296291939448732243429]);
basis = [(-2124150091254381073292137463, 259854492051899599030515511070780628911531), (2334509866034701756884754537, 18872004195494469180868316552803627931531), (-1671736054062369063879038663, 251709377261144287808506947241319126049131), (2139130260139156666492982137, 36639509171439729202421459692941297527531), (1534706764467120723885477337, 85429585346017694289021032862781072799531), (-2731079487875677033341575063, 262521815484332191641284072623902143387531), (2775726266844571649705458537, 12845755474014060248869487699082640369931), (1494385729327188957541833817, 88486605527733405986116494514049233411451), (1868438228620887358509065257, 59237403214437708712725140393059358589131), (2008945108825743774866542537, 47690677880125552882151750781541424711531), (2348360540918025169651632937, 17492930006200557857340332476448804363531), (-1472084007090481174470008663, 246643450653503714199947441549759798469131), (2924128607708061213363288937, 28350264431488878501488356474767375899531), (5374993891066061893293934537, 286188908427263386451175031916479893731531), (1709690768233354523334008557, 71898834974686089466159700529215980921631), (2450954011353593144072595187, 4445228173532634357049262550610714736531), (2969254709273559167464674937, 32766893075366270801333682543160469687531), (2711914934941692601332882937, 2068436612778381698650413981506590613531), (20078586077996854528778328937, 2779608541137806604656051725624624030091531), (2158082450240734774317810697, 34994373401964026809969662241800901254731), (2004645458247059022403224937, 48049329780704645522439866999888475467531), (2975749450947996264947091337, 33398989826075322320208934410104857869131), (-2102490467686285150147347863, 259576391459875789571677393171687203227531), (311583179915063034902194537, 168104385229980603540109472915660153473931), (2773931008341865231443771817, 12632162834649921002414116273769275813451), (2156581188143768409363461387, 35125092964022908897004150516375178087331), (3866330499872412508815659137, 121197755655944226293036926715025847322531), (2230868289773576023778678737, 28558760030597485663387020600768640028531)];
basis = [E(P) for P in basis];

#Elliptic curves of rank 0,1,2,3,4 of minimal conductor (only one for each rank):
E0 = EllipticCurve([0, -1, 1, 0, 0]); #N = 11
E1 = EllipticCurve([0, 0, 1, -1, 0]); #N = 37
E2 = EllipticCurve([0, 1, 1, -2, 0]); #N = 389
E3 = EllipticCurve([0, 0, 1, -7, 6]); #N = 5077
E4 = EllipticCurve([1, -1, 0, -79, 289]); #N = 234446

#Smart's example '94:
#E = EllipticCurve([0,1,1,-2,0]);

#Petho-Zimmer-Gebel-Herrmann '99:
#E = EllipticCurve([0,0,0,-172,505])
#Here, PZGH can reduce the coefficient bound to 17, we can reduce it to 12, and sage's algorithm to 7, which seems too good t

#testMWBases();
#points = test_findMWBasis(k=kNegOfRank[12],rank_bound=12,height_limit=18,via_rat_points=True);
#test_compareRunningTimeForLogComputationForDifferentHeightBounds();
#E,P = test_7823();

#studyMWBases();
#testRank0Curves();

#compareWithBennettGhadermarzi();

#computeSIntegralPointsForManymordellCurves(10,rank=1,maxA=10,verbose=True);
#computeSIntegralPointsForManymordellCurves(100,rank=2,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(100000,rank=1,maxA=10,verbose=True);
#computeSIntegralPointsForManymordellCurves(100,rank=3,maxA=100,verbose=True);
#computeSIntegralPointsForManymordellCurves(100,rank=1,As=[80],verbose=True);
#computeSIntegralPointsForManymordellCurves(10,rank=None,verbose=True);
#computeSIntegralPointsForManymordellCurves(1,rank=4,verbose=True);
#computeSIntegralPointsForManymordellCurves(10,rank=1,maxA=10,verbose=True,saveToOneFile=True,saveToFileSeparately=False);
#computeSIntegralPointsForManymordellCurves(1000,rank=None,maxA=100,verbose=True,saveToOneFile=True,saveToFileSeparately=True);

#computeSIntegralPointsForManymordellCurves(0,rank=0,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False);
#computeSIntegralPointsForManymordellCurves(100,rank=1,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False);
#computeSIntegralPointsForManymordellCurves(200,rank=1,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False);
#computeSIntegralPointsForManymordellCurves(300,rank=1,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False);
#computeSIntegralPointsForManymordellCurves(1000,rank=1,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False);
#computeSIntegralPointsForManymordellCurves(10000,rank=1,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False);
#computeSIntegralPointsForManymordellCurves(300,rank=2,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=True);
#computeSIntegralPointsForManymordellCurves(300,rank=3,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=True);
#computeSIntegralPointsForManymordellCurves(300,rank=4,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=True);
#computeSIntegralPointsForManymordellCurves(0,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);

#computeSIntegralPointsForManymordellCurves(200,rank=2,As=[-4347],verbose=True,saveToOneFile=True,saveToFileSeparately=True);

#S = primes_first_n(5);
#time computeSIntegralPoints(E,S=S,mwBasis=basis,saveToFile=True,saveToPath=pathData,verbose=True);
#time computeSIntegralPoints(E,S=S,saveToFile=True,saveToPath=pathData,verbose=True);
#time computeSIntegralPoints(E,S=S,mwBasis=my_mwBasis_for_mordellCurves[a],saveToFile=True,saveToPath=pathData,verbose=True);
#print "Comparison: Number of solutions from original S_integral_points():",len(E.S_integral_points(S));
#time computeSIntegralPoints(E,S=primes_first_n(10),saveToFile=True,saveToPath=pathData,verbose=True);
#time computeSIntegralPoints(mordellCurve(kPosOfRank[12]),S=primes_first_n(0),saveToFile=True,saveToPath=pathData,verbose=True);
#time computeSIntegralPoints(E,S=[3,5],mwBasis=[(0,0),(1,0)],Mmax0=10^40,saveToFile=True,saveToPath=pathData,verbose=True);
#time computeSIntegralPoints(E,S=S,mwBasis=[],saveToFile=True,saveToPath=pathData,verbose=True);

def test_compare_running_times(Mmax0 = None):

	#debugParam = {"heightLogSieve_Method":"Automatic_Weak_or_NoTest"}
	
	debugParam = {};
	debugParam["tMax"] = 0;
	debugParam["heightLogSieve_Method"] = "NoTest";
	time computeSIntegralPoints(E,S=S,mwBasis=basis,saveToFile=False,saveToPath=pathData,verbose=True,debugParam=debugParam,Mmax0 = Mmax0);
	print "debugParam used:",debugParam;

	#r=8, n=3: (first reduction: 7 sec)
	#{'tMax': 3} 57 sec (t is anyway at most 2, so no difference to tMax=2)
	#{'tMax': 2} 57 sec (refined enumeration up to h=23)
	#{'tMax': 1} 76 sec (refined enumeration up to h=25)
	#{'tMax': 0} 2891 sec (refined enumeration up to h=82)

	#r=8, n=5: (first reductions: 13 sec)
	#{'tMax': 4} 123 sec (refined enumeration up to h=30)
	#{'tMax': 3} 130 sec (refined enumeration up to h=30)
	#{'tMax': 2} 148 sec (refined enumeration up to h=32)
	#{'tMax': 1} 360 sec (refined enumeration up to h=37)
	#{'tMax': 0} 21371 sec (refined enumeration up to h=130)

	#r=8, n=10: (first reductions: 21 sec)
	#{'tMax': 3} 1359 sec (refined enumeration up to h=)
	#{'tMax': 2} 1667 sec (refined enumeration up to h=54)
	#{'tMax': 1} 5146 sec (refined enumeration up to h=69)
	#{'tMax': 0}  sec (refined enumeration up to h=305)

	#r=12

	return;

#test_compare_running_times();

def test_running_time_for_checking_S_integrality():
	def check_S_integrality(Q,S):
		return Q[0].is_S_integral(S);

	P = E(basis[0]);
	
	for i in range(100):
		print i;
		time check_S_integrality(100*i*P,S);
	
#test_running_time_for_checking_S_integrality();

#debug:
#for i in range(100):
#	time computeSIntegralPoints(E,S=S,mwBasis=basis,Mmax0=1000,saveToFile=False,saveToPath=pathData,verbose=True);

#for n in range(0,2001,50):
#	computeSIntegralPoints(E,S=primes_first_n(n),mwBasis=basis,saveToFile=True,saveToPath=pathData,verbose=True);

def test_compare_our_algorithm_with_cremona(n=2):
	Ks = [kPosOfRank[r] for r in range(1,1+8)];
	verbose = False;
	Mmax0 = 10^3;
	S = primes_first_n(n);
	print "S =",S;
	for k in Ks:
		print "-------------------";
		E = mordellCurve(k);
		if my_mwBasis_for_mordellCurves.has_key(k):
			basis = my_mwBasis_for_mordellCurves[k];
			basis = [E(P) for P in basis];
		else:
			basis = None;
		print "k =",k,"and rank =",len(basis),":";

		t0 = walltime();
		computeSIntegralPoints(E,S=S,mwBasis=basis,Mmax0=Mmax0,verbose=verbose);
		time_ours = walltime(t0);
		print "Our algo took",time_ours;
		
		t0 = walltime();
		E.S_integral_points(S=S,mw_base=basis,verbose=verbose);
		time_sage = walltime(t0);
		print "Sage's algo took",time_sage;

### Comparison with GPZ's tables:
#for a in ksGPZ96:
#	computeSIntegralPoints(mordellCurve(a),S=S,saveToFile=True,saveToPath=pathData+"GPZ96/",verbose=True);
#for a in ksGPZ97:
#	computeSIntegralPoints(mordellCurve(a),S=S,saveToFile=True,saveToPath=pathData+"GPZ97/",verbose=True);
#pathData += "GPZ97/";
#computeSIntegralPointsForManymordellCurves(0,rank=0,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);
#computeSIntegralPointsForManymordellCurves(3,rank=0,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);
#computeSIntegralPointsForManymordellCurves(0,rank=1,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);
#computeSIntegralPointsForManymordellCurves(3,rank=1,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);
#computeSIntegralPointsForManymordellCurves(0,rank=2,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);
#computeSIntegralPointsForManymordellCurves(3,rank=2,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);
#computeSIntegralPointsForManymordellCurves(0,rank=3,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);
#computeSIntegralPointsForManymordellCurves(3,rank=3,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);
#computeSIntegralPointsForManymordellCurves(0,rank=4,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);
#computeSIntegralPointsForManymordellCurves(3,rank=4,maxA=10000,verbose=True,saveToOneFile=True,saveToFileSeparately=False,bothSigns=True);

#time computeSIntegralPoints(mordellCurve(kPosOfRank[9]),S=S,mwBasis=my_mwSublatticeBasis_for_mordellCurves[kPosOfRank[9]],saveToFile=True,saveToPath=pathData,verbose=True);

#test()
#test_QuarticCovariants();

#sol = computeSIntegralPoints(E3,S=primes_first_n(300),saveToFile=True,verbose=True,Mmax0 = 10^10,debugParam={"heightLogSieve_Method":"Automatic_Weak_or_NoTest"})

#sol = computeSIntegralPoints(E3,S=primes_first_n(30),saveToFile=True,verbose=True,Mmax0 = 10^10,debugParam={"heightLogSieve_Method":"Automatic_Weak_or_NoTest"})
#Refined sieves and refined enumerations: 84.957601
#sol = computeSIntegralPoints(E3,S=primes_first_n(30),saveToFile=True,verbose=True,Mmax0 = 10^10,debugParam={"heightLogSieve_Method":"Automatic_Strong_or_NoTest"})
#Refined sieves and refined enumerations: 89.390197
#sol = computeSIntegralPoints(E3,S=primes_first_n(30),saveToFile=True,verbose=True,Mmax0 = 10^10,debugParam={"heightLogSieve_Method":"NoTest"})
#Refined sieves and refined enumerations: 64.376953
#sol = computeSIntegralPoints(E3,S=primes_first_n(30),saveToFile=True,verbose=True,Mmax0 = 10^10,debugParam={"heightLogSieve_Method":"NoTest","tMax":0})
#Refined sieves and refined enumerations: 203.451876

'''
Among all Mordell curves with |a|<=10000, there are:
- 6532 curves of rank 0,
- 9546 curves of rank 1,
- 3426 curves of rank 2,
-  478 curves of rank 3,
-   18 curves of rank 4.
Note that we have one less rank 1 curve and one more rank 3 curve than GPZ97!

Computing S-integral points for n=100 took
- rank 1:  5901 sec
- rank 2: 70206 sec
- rank 3: 42848 sec
- rank 4: 14467 sec
Computing S-integral points for n=200 took
- rank 1:   9942 sec
- rank 2: 324507 sec
- rank 3: 191775 sec
- rank 4: 180376 sec
Computing S-integral points for n=300 took
- rank 1:  13582 sec
- rank 2: 559268 sec (on metis, i.e. roughly 5 times as fast)
- rank 3: 459238 sec
- rank 4: 619074 sec
Computing S-integral points for n=1000 took
- rank 1: 35392 sec
Computing S-integral points for n=10000 took
- rank 1: 489472 sec

#One day has
- 1440 minutes,
- 86400 seconds.

#Version 14:

#rank 1, s=10: 1 sec
#rank 1, s=100: 5 sec
#rank 1, s=1000: 51 sec, old: 95 sec
#rank 1, s=10000: 922 sec, old: 1313 sec
#rank 1, s=100000: previously on selene: ca. 15000 sec
#takes around 1GB of memory for each 10000 primes.

#rank 2, s=10: 3 sec
#rank 2, s=50: 73 sec
#rank 2, s=100: 192 sec
#rank 2, s=150: 515 sec (818 theia)
#rank 2, s=200: 1758 sec (1884 theia)
#rank 2, s=250: 5072 sec theia
#rank 2, s=300: 9745 sec theia
#rank 2, s=350: 13672 sec theia
#rank 2, s=400: 49654 sec theia
#rank 2, s=450: 43161 sec theia
#rank 2, s=500: 38683 sec theia
#rank 2, s=550: 211451 sec theia
#rank 2, s=600: 151410 sec theia
#rank 2, s=650: 122755 sec theia
#rank 2, s=700: 105347 sec theia
#rank 2, s=750: 500659 sec theia
#rank 2, s=800: 376133 sec theia
#rank 2, s=850: 364894 sec theia
#rank 2, s=900:  sec theia
#rank 2, s=950:  sec theia
#rank 2, s=1000:  sec theia

#rank 3, s=10: 10 sec
#rank 3, s=50: 374 sec (theia)
#rank 3, s=100: 1621 sec theia, old: 1626 sec
#rank 3, s=150: 3485 sec theia
#rank 3, s=200: 8422 sec (9211 theia)
#rank 3, s=250: 29045 sec theia
#rank 3, s=300: 25859 sec theia
#rank 3, s=350: 81285 sec theia
#rank 3, s=400: 65444 sec theia
#rank 3, s=450: 202004 sec theia
#rank 3, s=500: 240464 sec theia
#rank 3, s=550: 219333 sec theia
#rank 3, s=600: 204398 sec theia
#rank 3, s=650: got killed on theia

#rank 4, s=10: 34 sec
#rank 4, s=20: 169 sec 
#rank 4, s=30: 402 sec
#rank 4, s=40: 865 sec
#rank 4, s=50: 1710 sec
#rank 4, s=100: 14376 sec (selene)
#rank 4, s=200: 180376 sec (selene)
#rank 4, s=300: 613861 sec (selene)

#rank 5, s=10: 66 sec
#rank 5, s=15: 177 sec
#rank 5, s=20: 499 sec
#rank 5, s=25: 1058 sec (1391 theia)
#rank 5, s=30: 2481 sec theia
#rank 5, s=35: 3846 sec theia
#rank 5, s=40: 6731 sec theia
#rank 5, s=45: 9280 sec theia
#rank 5, s=50: 13331 sec theia
#rank 5, s=55: 20362 sec theia
#rank 5, s=60: 26211 sec theia
#rank 5, s=65: 36713 sec theia
#rank 5, s=70: 38505 sec theia
#rank 5, s=75: 55901 sec theia
#rank 5, s=80: 54090 sec theia
#rank 5, s=85: 67232 sec theia
#rank 5, s=90: 78358 sec theia
#rank 5, s=95: 97096 sec theia
#rank 5, s=100: 163402 sec theia
#rank 5, s=105: 230408 sec theia
#rank 5, s=110: 258403 sec theia
#rank 5, s=115: 352529 sec theia
#rank 5: s=120: 415167 sec theia

#rank 6: s=2: 5 sec
#rank 6: s=4: 13 sec
#rank 6: s=6: 33 sec
#rank 6: s=8: 79 sec (jetzt 96 auf Laptop, bottleneck: refined sieve+refined enumeration)
#rank 6, s=10: 282 sec, old: 148 sec (jetzt 182 auf Laptop)
#rank 6: s=12: 296 sec
#rank 6: s=14: 464 sec
#rank 6: s=16: 907 sec (selene 1437)
#rank 6: s=18: 1895 sec (selene)
#rank 6: s=20: 3237 sec (selene)
#rank 6: s=22: 5009 sec (selene)
#rank 6: s=24: 7146 sec (selene)
#rank 6: s=26: 7513 sec (selene)
#rank 6: s=28: 10738 sec (selene)
#rank 6: s=30: 14177 sec (selene)
#rank 6: s=32: 19313 sec (selene)
#rank 6: s=34: 23679 sec (selene)
#rank 6: s=36: 27438 sec (selene)
#rank 6: s=38: 27636 sec (selene)
#rank 6: s=40: 38170 sec (selene)
#rank 6: s=42: 60913 sec (selene)
#rank 6: s=44: 43499 sec (selene)
#rank 6: s=46: 53864 sec (selene)
#rank 6: s=48: 57819 sec (selene)
#rank 6: s=50: 65922 sec (selene)
#rank 6: s=52: 157593 sec (selene)
#rank 6: s=54: 218060 sec (selene)
#rank 6: s=56: 273674 sec (selene)
#rank 6: s=58: 298836 sec (selene)
#rank 6: s=60: 363583 sec (selene)
#rank 6: s=62:  sec (selene)
#rank 6: s=64:  sec (selene)

#rank 7, s=10: 356 sec
#rank 7, s=12: 632 sec
#rank 7, s=14: 977 sec (2666 selene)
#rank 7, s=16: 4012 sec selene
#rank 7, s=18: 6453 sec selene
#rank 7, s=20: 9712 sec selene
#rank 7, s=22: 17259 sec selene
#rank 7, s=24: 27060 sec selene
#rank 7, s=26: 35006 sec selene
#rank 7, s=28: 41940 sec selene
#rank 7, s=30: 59550 sec selene
#rank 7, s=32: 68569 sec selene
#rank 7, s=34: 84608 sec selene
#rank 7, s=36: 96590 sec selene
#rank 7, s=38: 158430 sec selene
#rank 7, s=40: 247348 sec selene
#rank 7, s=42: 344005 sec selene
#rank 7, s=44:  sec selene
#rank 7, s=46:  sec selene
#rank 7, s=48:  sec selene
#rank 7, s=50:  sec selene

#rank 8: s=0: 2 sec, old: 3 sec
#rank 8: s=1: 21 sec, old: 25 sec
#rank 8, s=2: 37 sec, old: 62 sec
#rank 8, s=3: 70 sec, old: 135 sec
#rank 8, s=4: 113 sec, old: 212 sec
#rank 8, s=5: 175 sec, new after comparing t's: 126
#rank 8, s=6: 537 sec (theia)
#rank 8, s=7: 826 sec (theia)
#rank 8, s=8: 1570 sec (theia)
#rank 8: s=9: 2473 (theia)
#rank 8, s=10; 1975 sec, old: 1698 sec, new after comparing t's: 1881, neu: 1359
#rank 8, s=10; 3861 sec (theia)
#rank 8, s=12; 7922 sec (theia)
#rank 8, s=14; 17992 sec (theia)
#rank 8, s=16; 32401 sec (theia)
#rank 8, s=18; 68467 sec (theia)
#rank 8, s=20; 112157 sec (theia)
#rank 8, s=25: 217525 sec (selene)
#rank 8, s=30: 399041 sec (selene)

#Rank 9: Possibly not saturated mwBasis! (I.e. some solutions might be missed.)
#rank 9: s=0: 3 sec
#rank 9: s=1: 17 sec
#rank 9: s=2: 60 sec
#rank 9: s=3: 122 sec
#rank 9: s=4: 205 sec
#rank 9: s=5: 335 sec

#Mestre:
#rank 12: s=0: 70 sec (155 theia) (142 selene)
#rank 12: s=1: 3730 sec (7256 theia)
#rank 12: s=2: 29354 sec (theia)
#rank 12: s=3: 128480 sec (theia) (davon first reductions: 97112)
#rank 12: s=4: 104087 sec (theia) (davon first reductions: 52218) #??? doen't fit with s=3, maybe due to caching.
#rank 12: s=5: 284582 sec (theia) (davon first reductions: 217024)
#rank 12, s=6: 304262 sec (theia) (davon first reductions: 200292)
#rank 12, s=7: 1317329 sec (theia) (davon first reductions: 1135832, i.e. 86%)

Number of curves with conductor <= Nmax:
Nmax 100: 302
Nmax 1000: 5113
Nmax 10000: 64687
Nmax 100000: 657396
'''
