
only_quality_geq_1 = True

def radical_abc(abc):
	return radical(prod(abc))

def quality_abc(abc):
	return RR(log(max(*abc)))/RR(log(radical(prod(abc))))

def factor_str(a):
	if a < 0:
		return "-"+factor_str(-a)
	if a == 1:
		return "1"
	result = ""
	for p,e in a.factor():
		result += str(p)+"^"+str(e)+" "
	return result.rstrip(" ")



for n in range(1,16+1):
	S = primes_first_n(n)
	S_str = "_".join(str(p) for p in S)
	abcs = list(load("../solutions_"+S_str+".sobj"))
	abcs.sort(key = quality_abc)
	abcs.sort(key = radical_abc)
	abcrqs = [(a,b,c,radical_abc((a,b,c)),quality_abc((a,b,c))) for a,b,c in abcs]
	
	if only_quality_geq_1:
		filename = "solutions_"+S_str+"_factored_q_1+.txt"
	else:
		filename = "solutions_"+S_str+"_factored.txt"
	with open(filename,"w") as f:
		for a,b,c,r,q in abcrqs:
			Sr_str = ",".join(str(p) for p in sorted(r.prime_divisors()))
			if only_quality_geq_1 and q < 1:
				continue
			line = "%s: %s + %s = %s (%0.3f): %s + %s = %s" % \
					(Sr_str,a,b,c,q,factor_str(a),factor_str(b),factor_str(c))
			f.write(line+"\n")			
	
	#break
