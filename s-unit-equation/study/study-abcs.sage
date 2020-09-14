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


'''
only_quality_geq_1 = True
#sort_by = "radical"
sort_by = "quality"




for n in range(1,16+1):
	S = primes_first_n(n)
	S_str = "_".join(str(p) for p in S)
	abcs = list(load("../solutions_"+S_str+".sobj"))
	if sort_by == "radical":
		abcs.sort(key = quality_abc)
		abcs.sort(key = radical_abc)
	elif sort_by == "quality":
		abcs.sort(key = radical_abc)
		abcs.sort(key = quality_abc)
	
	abcrqs = [(a,b,c,radical_abc((a,b,c)),quality_abc((a,b,c))) for a,b,c in abcs]
	
	filename = "solutions_"+S_str+"_factored"
	if only_quality_geq_1:
		filename += "_q_1+"
	if sort_by == "quality":
		filename += "_sort_by_q"

	with open(filename+".txt","w") as f:
		for a,b,c,r,q in abcrqs:
			Sr_str = ",".join(str(p) for p in sorted(r.prime_divisors()))
			if only_quality_geq_1 and q < 1:
				continue
			line = "%s: %s + %s = %s (%0.3f): %s + %s = %s" % \
					(Sr_str,a,b,c,q,factor_str(a),factor_str(b),factor_str(c))
			f.write(line+"\n")			
	
	#break
'''

def migrate_abcs_to_abcs_with_q_geq_1():
	for n in range(1,16+1):
		S = primes_first_n(n)
		S_str = "_".join(str(p) for p in S)
		filename_from = "../solutions_"+S_str+".sobj"
		filename_to = "solutions_"+S_str+"_q_1+.sobj"
		abcs = set(abc for abc in load(filename_from) if quality_abc(abc)>=1)
		save(abcs,filename_to)
		
migrate_abcs_to_abcs_with_q_geq_1()
