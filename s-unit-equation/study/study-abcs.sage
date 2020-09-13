
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

for n in range(1,2+1):
	S = primes_first_n(n)
	S_str = "_".join(str(p) for p in S)
	abcs = list(load("../solutions_"+S_str+".sobj"))
	abcs.sort(key = quality_abc)
	abcs.sort(key = radical_abc)
	abcrqs = [(a,b,c,radical_abc((a,b,c)),quality_abc((a,b,c))) for a,b,c in abcs]
	
	filename = "solutions_"+S_str+"_factored.txt"
	with open(filename,"w") as f:
		for a,b,c,r,q in abcrqs:
			line = "%s: %s + %s = %s (%s): %s + %s = %s" % \
					(r,a,b,c,q,factor_str(a),factor_str(b),factor_str(c))
			f.write(line+"\n")			
	
	#break
