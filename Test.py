inverseval = [[0,0]]*7

def gf_division(x,y):
    if y == 0:
        print("Division By Zero")
        return null
    return gf_multiplication(x,inverseval[y-1][1])

def create_inverse():
    for i in range(0,7):
        inverseval[i] = [gf_pow(2,i),gf_pow(2,7-i)]
    #bubble
    temp = [0,0]
    for i in range(0,7):
        for i in range(0,6):
            if inverseval[i+1][0] < inverseval[i][0]:
                temp = inverseval[i+1]
                inverseval[i+1] = inverseval[i]
                inverseval[i] = temp



def no_carry_multiplication(x,y):
    z = 0
    i = 0
    while (y >> i) > 0:
        if y & (1 << i):
            z ^= x << i
        i += 1
    return z

def gf_multiplication(x, y):
    mul = no_carry_multiplication(x,y)
    return reduction(mul)

def gf_xor(a, b):
    return a ^ b

def reduction(x):
    a = 0b1011
    xl = (x).bit_length()
    al = (a).bit_length()
    if xl < al:
        return x
    b = xl - al
    a = a << b

    xl2 = xl
    while xl2 >= al:
        x = x ^ a
        xl2 = x.bit_length()
        difference = xl - xl2
        xl = xl2
        a = a >> difference
    return x

def gf_pow(a,n):
    result = a
    if n == 0:
        return 1
    for i in range(1,n):
        result = gf_multiplication(result,a)
    return result

create_inverse()
#that was the end of the basic gf operations
#next I define functions on polynomials whose coefficients are themselves elements of the galois field
print(inverseval)
#create the generator poly
def gen_polynomial(n, a):
    result = [1]

    for i in range(1,n+1):
        result = poly_mul(result, [1, gf_pow(a,i)])
    return result



def poly_scale(poly,r):
    for i in range(0, len(poly)):
        poly[i] = gf_multiplication(poly[i],r)
    return poly

def poly_add(x,y):
    length = max(len(x), len(y))
    result = [0] * length
    if len(x) > len(y):
       for i in range(0, len(y)) :
           result[i] = x[i] ^ y[i]

       for i in range(len(y), len(result)):
           result[i] = x[i]
    else:
        for i in range(0, len(x)):
            result[i] = x[i] ^ y[i]
        for i in range(len(x), len(result)):
            result[i] = y[i]
    return result

def poly_mul(x,y):
    length = len(x) + len(y) - 1
    result = [0] * length
    for i in range(len(x)):
        for j in range(len(y)):
            result[i+j] = result[i+j] ^ gf_multiplication(x[i],y[j])
    return result

def poly_eval(poly, a):
    y = poly[0]
    for i in range(1,len(poly)):
        y = gf_xor(gf_multiplication(poly[i], gf_pow(a,i)),y)
    return y

def poly_div(dividend,divisor):
        msg_out = list(dividend)
        for i in range(0, len(dividend) - (len(divisor) - 1)):
            coef = msg_out[i]
            if coef != 0:
                for j in range(1, len(divisor)):
                    if divisor[j] != 0:
                        msg_out[i + j] ^= gf_multiplication(divisor[j], coef)


        separator = -(len(divisor) - 1)
        return msg_out[:separator], msg_out[separator:]


def encode(m, nsym):
    gen = gen_polynomial(nsym, 2)
    revm = [0]*len(m)
    for i in range(len(m)):
        revm[i] = m[len(m)-i-1]
    m= revm
    _, remainder = poly_div(m+([0] * (len(gen) - 1)), gen)
    resulta = m + remainder
    result = [0]*len(resulta)
    for i in range(0,len(resulta)):
        result[i] = resulta[len(resulta) -i -1]
    return result

# decoding
# syndromes

def syndromes(m, nsym):
    result = [0] * nsym
    for i in range(0, nsym):
        result[i] = poly_eval(m, gf_pow(2, i+1))
    return result


def syn_encode(syndromes):
    result = [0]
    for i in range(0, nsym):
        result += polyscale(syndromes[i], gf_pow(2, i))
    return result


def berlekamp_massey(syndromes, codelen):
    # initial m
    m = -1
    lambda_m = [1]
    lm = 0
    msublm = -1
    dm = 1

    #print("Initial M: M = ", m, ";  \u039B(m) = ", lambda_m, "; lm = ", lm, "; m-lm = ", msublm, "; dm = ", dm)
     #initial r

    r = 0
    lambda_r = [1]
    lr = 0
    rsublr = 0
    dr = syndromes[0]

    #print("Initial R: R = ", r, ";  \u039B(r) = ", lambda_m, "; lr = ", lr, "; r-lr = ", rsublr, "; dr = ", dr)
    #print("target R is: ", len(syndromes))
    for i in range(1, len(syndromes)+1):
        #print("     Now fnding \u039Br(", i, ")")
        #print("         Current M:  M = ", m, ";  \u039B(m) = ", lambda_m, "; lm = ", lm, "; m-lm = ", msublm,"; dm = ", dm)
        #print("         Current R: R = ", r, ";  \u039B(r) = ", lambda_r, "; lr = ", lr, "; r-lr = ", rsublr, "; dr = ",dr)
        if (dr == 0 ):
            rp1 = r + 1
            lrp1 = lr
            rp1sublrp1 = rp1-lrp1
            lambda_rp1 = lambda_r
            drp1 = 0
            if i != len(syndromes):
                for j in range(0, lrp1 + 1):
                    drp1 = gf_xor(drp1, gf_multiplication(lambda_rp1[j], syndromes[rp1 - j]))

            if (rsublr >= msublm) and (dr != 0):
                m = r
                lambda_m = lambda_r
                lm = lr
                msublm = rsublr
                dm = dr

            r = rp1
            lambda_r = lambda_rp1
            lr = lrp1
            rsublr = rp1sublrp1
            dr = drp1
            #print("         R to find (dr==0): ", rp1, "; Degree (lrp1): ", lrp1, "; (R+1)-l(r+1): ", rp1sublrp1,"; \u039B(", rp1, "): ", lambda_rp1, )
        else:

            # l sub (r+1)
            rp1 = r + 1
            lrp1 = max(lr, lm + r - m)

            # rsublr
            rp1sublrp1 = rp1 - lrp1

            # lambda_rp1
            interim_poly = [0] * (r - m + 1)
            if dm == 0:
                return [0]
            interim_poly[r - m] = gf_multiplication(dr, gf_division(1, dm))
            #print("                 dr: ", dr, "; 1/dm:", gf_division(1, dm), "; interimpoly[r-m]:", interim_poly[r-m])
            lambda_rp1 = poly_add(lambda_r, poly_mul(interim_poly, lambda_m))
            #print("             \u039B(", rp1, "): ", lambda_rp1, "; \u039B(", r, "): ", lambda_r, "; polymulterm: ",poly_mul(interim_poly, lambda_m))
            #print("         R to find: ", rp1, "; Degree (lrp1): ", lrp1, "; (R+1)-l(r+1): ", rp1sublrp1, "; \u039B(", rp1, "): ", lambda_rp1, )

            #drp1
            if (i != len(syndromes)):
                drp1 = 0
                #print(i)
                for j in range(0, lrp1 + 1):
                    #print("                 j: ",j , "; \u039B(", rp1, "): ", lambda_rp1, "; syndromes: ", syndromes, "; rp1-j: ", rp1-j)

                    drp1 = gf_xor(drp1, gf_multiplication(lambda_rp1[j], syndromes[rp1 - j]))
                    #print("                     drp1: ", drp1)
                #print("              d(r+1) :", drp1, "; rp1 : ", rp1, "; lrp1: ", lrp1)

            if (rsublr >= msublm):
                m = r
                lambda_m = lambda_r
                lm = lr
                msublm = rsublr
                dm = dr

            r = rp1
            lambda_r = lambda_rp1
            lr = lrp1
            rsublr = rp1sublrp1
            dr = drp1
    #print("expected result = ", [1,3,2])
    return lambda_rp1


def error_loc_roots(elocpoly):
    errors = [0] * 7
    xmin1 = [0] * (len(elocpoly) - 1)
    j = 0
    for i in range(0, 7):
        x = poly_eval(elocpoly, gf_pow(2, i))
        if x == 0:
            xmin1[j] = gf_pow(2, i)
            j += 1
            if i == 0:
                errors[0] = "X"
            else:
                errors[7 - i] = "X"
            #print(i, "    ", 7 - i, "   ", gf_pow(2, i), "     ", gf_pow(2, 6 - i))
    #print(xmin1)
    if xmin1[0] == 1:
        tempxmin = xmin1[1:]
        #print(tempxmin)
        tempxmin.reverse()
        #print(tempxmin)
        xmin1[1:] = tempxmin
    else:
        xmin1.reverse()

    return [errors,xmin1]

def forney(s_x, l_x, e_x, xm1):
    
    #Omega(x)
    O_x = poly_mul(s_x, l_x)
    #print(xm1)
    #print("s_x", s_x, "    ,l_x", l_x)
    #print("long O_x:", O_x)
    if len(O_x) > 4:
        O_x = O_x[0:4]

    #print("short O_x", O_x)

    #Lambda' x
    lambda_dash_x = [0]*(len(l_x)-1)
    for i in range(1, len(l_x)):
        if i % 2 == 1:
            lambda_dash_x[i-1] = l_x[i]
    #print(l_x)
    #print("l'_x: ", lambda_dash_x)
    #print("x^-1: ", xm1)
    #let e_x be a list of the locations of the errors rathen than what eloc roots currently produces.
    result = [0]*7
    #this should be correct but not most useful form?
    j=0
    for i in range(0,len(e_x)):
        if e_x[i] != 0:
            dividend = poly_eval(O_x, xm1[j])
            #print("     O(x) = ", dividend)
            divisor = poly_eval(lambda_dash_x, xm1[j])
            #print("     L(x) = ", divisor)
            result[i] = gf_division(dividend, divisor)
            j+=1

    return result







for i in range(0,8):
    print(i, ",    ", gf_pow(2,i))
print(gf_multiplication(2,5))
print(gen_polynomial(4,2))
msg = [6,6,1]
print(msg)
originalcode = encode(msg, 4)
code = [0]*len(originalcode)
for i in range(0,len(originalcode)):
    code[i] = originalcode[i]
print(code)



f = 0

if True:
    for i in range(0, 6):

        for j in range(0, 8):
            for k in range(i + 1, 7):
                for l in range(0, 8):
                    if i != k:

                        #f += 1
                        #print("")
                        code[i] = j
                        code[k] = l
                        #print("i: ", i, " k: ", k)
                        #print("Corrupted code: ", code)
                        syndrome = syndromes(code, 4)
                        if syndrome == [0]*len(syndrome):
                            repaired = code
                        else:
                            #print("Syndromes: ", syndrome)
                            bmresult = berlekamp_massey(syndrome, len(code))
                            #print("Error locator poly: ", bmresult)
                            locations = error_loc_roots(bmresult)[0]
                            xmin1 = error_loc_roots(bmresult)[1]
                            #print("Error locations: ", locations)

                            error_poly = forney(syndrome, bmresult, locations, xmin1)
                            #print("Error polynomial: ", error_poly)
                            repaired = poly_add(error_poly, code)
                        if (repaired == [5,2,1,2,6,6,1]) :
                            print(f)
                            f += 1
                            print("Corrupted code: ", code)
                            print("i: ", i, " k: ", k)
                            print("     Error Poly: ", error_poly)
                            print("X^-1: ", xmin1)
                            print("     Repaired code: ", repaired)
                            print("     Check: ", poly_add(repaired, code))
                            print("     Decrypted message: ", repaired[4:])
                            print("")
                            print("--------------------")
                            print("")



                        #print("Check: ", poly_add(repaired, code))
                        #print("Decrypted message: ", repaired[4:])
                        #print("")
                        #print("--------------------")
                        #print("")
                    code[i] = originalcode[i]
                    code[k] = originalcode[k]

            for k in range(0, 7):
                for l in range(0, 7):
                    if i != k:
                        pass


if False:
    for i in range(0, 7):
        for j in range(0, 8):
            code[i] = j
            print("i: ", i, "j", j)
            print("code", code)
            syn = syndromes(code, 4)
            print("syndromes", syn)
            bmresult = berlekamp_massey(syn, 7)
            print("elocpoly", bmresult)
            print("errorlocations", error_loc_roots(bmresult))
            code[i] = originalcode[i]



