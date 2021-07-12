import random
import math
import msvcrt

#This is a software implentation of Reed-Solomon Codes.
#This particular implentation will allow you to write a message of up to 223 ASCII characters.
#It will then encode this message into a code 255 characters long.
#Then it will allow you to introduce errors into parts of the code (to simulate transmission errors).
#This type of Reed-Solomon code can correct up to 16 mistakes
#Feel free to introduce more.
#The decoder will then retrieve the original message.

#Please note, terminal should be emulated for the input function to work.
#in Pycharm, in the top-right on the left of the play button -> edit configuration -> check "emulate terminal in console".




#The following are functions that will allow addition,subtraction, multiplication, division and powers in a galois field size 2^8
#They will be useful later on to essentially overide the normal operators

inverseval = [[0,0]]*255

def gf_division(x,y):
    if y == 0:
        print("Division By Zero")
        return null
    return gf_multiplication(x,inverseval[y-1][1])

#the fastest way to find the multiplicative inverse is to use a lookup table, so this is making it.
def create_inverse():
    for i in range(0,255):
        inverseval[i] = [gf_pow(2,i),gf_pow(2,255-i)]
    #bubble sort
    temp = [0,0]
    for i in range(0,255):
        for i in range(0,254):
            if inverseval[i+1][0] < inverseval[i][0]:
                temp = inverseval[i+1]
                inverseval[i+1] = inverseval[i]
                inverseval[i] = temp

#multiplication in galois fields is polynomial multiplication followed by taking the remainder after dividing by an irreducible polynomial
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
    a = 0b100011101
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

#that was the end of the basic gf operations
#next I define functions on polynomials whose coefficients are themselves elements of the galois field

#create the generator poly. Multiply this by the message, and the new code will be a polynomial with same roots as this generator poly
def gen_polynomial(n, a):
    result = [1]

    for i in range(1,n+1):
        result = poly_mul(result, [1, gf_pow(a,i)])
    return result


#multiply a polynomial by a scalar
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

#evaluate a polynomial at a given value
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

#now the encoding function:
#the simple method is to multiply the message poly by the generator poly. However a systematic encoding can hold the original message in the code and have all the same desirable properties.
#because of this it is very simple to extract the original message from the decoded word at the end.

def encode(m,nsym):
    gen = gen_polynomial(nsym, 2)
    revm = [0] * len(m)
    for i in range(len(m)):
        revm[i] = m[len(m) - i - 1]
    m = revm
    _, remainder = poly_div(m + ([0] * (len(gen) - 1)), gen)

    resulta = m + remainder
    result = [0] * len(resulta)
    for i in range(0, len(resulta)):
        result[i] = resulta[len(resulta) - i - 1]
    return result


#decoding:

#syndromes calculation; remember that the code word poly when evaluated at each the roots of the generator poly is 0.
# evaluating the received message at each of these roots SHOULD produce all 0s in which case no errors have happened.
#however if they do not then we get different values which will indicate what the errors are.

def syndromes(m,nsym):
    result = [0] * nsym
    for i in range(0, nsym):
        result[i] = poly_eval(m, gf_pow(2, i + 1))
    return result

def syn_encode(syndromes):
    result = [0]
    for i in range(0, nsym):
        result += polyscale(syndromes[i], gf_pow(2, i))
    return result

#Explaining how this algorithm works in comments is too much.
#It produces a new polynomial lambda(x), the error locator poly. We can use it later to find the locations of the errors.
#Originally lambda(x) was found using matrix inversion, but the berlekamp-massey algorithm runs faster.
    
def berlekamp_massey(syndromes, codelen):
    # initial m
    m = -1
    lambda_m = [1]
    lm = 0
    msublm = -1
    dm = 1

    # initial r

    r = 0
    lambda_r = [1]
    lr = 0
    rsublr = 0
    dr = syndromes[0]

    for i in range(1, len(syndromes)+1):
        if (dr == 0 ):
            rp1 = r + 1
            lrp1 = lr
            rp1sublrp1 = rp1-lrp1
            lambda_rp1 = lambda_r

            if i != len(syndromes):
                drp1 = 0
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
            lambda_rp1 = poly_add(lambda_r, poly_mul(interim_poly, lambda_m))

            # drp1
            if (i != len(syndromes)):
                drp1 = 0
                for j in range(0, lrp1 + 1):
                    drp1 = gf_xor(drp1, gf_multiplication(lambda_rp1[j], syndromes[rp1 - j]))

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
    return lambda_rp1

#Let the Xi be equal to a^i where the i represents the location of an error. The error locator poly when evaluated at X^-1 produces a 0 iff there is an error at i.
#having an ordered list of X^-1 will also be useful later so this function returns that as well.

def error_loc_roots(elocpoly):
    errors = [0] * 255
    xmin1 = [0] * (len(elocpoly)-1)
    j=0
    for i in range(0, 255):
        x = poly_eval(elocpoly, gf_pow(2, i))

        if x == 0:
            xmin1[j] = gf_pow(2, i)
            j+=1
            if i == 0:
                errors[0] = "X"
            else:
                errors[255 - i] = "X"
    if xmin1[0] == 1:
        tempxmin = xmin1[1:]
        tempxmin.reverse()
        xmin1[1:] = tempxmin
    else:
        xmin1.reverse()



    return [errors, xmin1]


#This algorithm finds the value of the errors at each position where there is an error, producing an error poly.

def forney(s_x, l_x, e_x, xm1):

    #Omega(x)
    O_x = poly_mul(s_x, l_x)

    if len(O_x) > 32:
        O_x = O_x[0:32]


    #Lambda' x
    lambda_dash_x = [0]*(len(l_x)-1)
    for i in range(1, len(l_x)):
        if i % 2 == 1:
            lambda_dash_x[i-1] = l_x[i]

    result = [0]*255
    j=0
    for i in range(0,len(e_x)):
        if e_x[i] != 0:
            dividend = poly_eval(O_x, xm1[j])
            divisor = poly_eval(lambda_dash_x, xm1[j])
            result[i] = gf_division(dividend, divisor)
            j+=1

    return result

#all these functions combined like this will will produce an error polynomial, which just needs to be subtracted from the corrupted code.
#(remember subtraction and addition are the same here).
# then the corrected code has been retreived and the original message merely needs to be extracted.

def decode(code, nsym):
    syndrome = syndromes(code, nsym)
    if syndrome == [0] * len(syndrome):
        repaired = code
    else:
        bmresult = berlekamp_massey(syndrome, len(code))
        locations = error_loc_roots(bmresult)[0]
        xmin1 = error_loc_roots(bmresult)[1]

        error_poly = forney(syndrome, bmresult, locations, xmin1)
        repaired = poly_add(error_poly, code)
    return repaired[32:]


def main_function():
    x = True
    while x:
        print("please type the string you want to encode:")
        msg = [48]*223
        char = '0'
        string = list('0'*223)
        a = 0
        truncatevalue = -1
        for i in range(0,223):
            if a == 0:
                char = msvcrt.getche()
                if ord(char.decode('utf-8')) == 13:
                    a = 1
                else:
                    truncatevalue = i
                    msg[i] = ord(char.decode('utf-8'))
                    string[i] = char.decode('utf-8')
            else:
                msg[i] = 48
                string[i] = '0'
        emptystring = ""
        outputstring = emptystring.join(string)


        code = encode(msg, 32)

        encodedstring = list('0'*255)
        for i in range(0,255):
            encodedstring[i] = chr(code[i])
        print("encoded string: " , "".join(encodedstring))
        u_in = input("Please type the number of errors you want (Max is 16) : ")
        no_of_errors = int(u_in)
        errorlist = [0]*no_of_errors
        print("Please type the locations of the errors (0-255)")
        for i in range(0,no_of_errors):
            errorlist[i] = int(input())

        print("Please type the value of the errors: ")
        for i in range(0, no_of_errors):
            code[errorlist[i]] = ord(input())
            encodedstring[errorlist[i]] = chr(code[errorlist[i]])
        print("Corrupted message: ", "".join(encodedstring))

        print("Decoding Time: ")
        print("Decoded message is:")
        result = decode(code, 32)
        if truncatevalue != -1:

            result = result[:(truncatevalue+1)]
        chrresult = list('0'* len(result))
        for i in range(len(result)):
            chrresult[i] = chr(result[i])
        print("".join(chrresult))
        if (input("Press Q to quit, or another key to encode again:") == "Q"):
            x = False;

#functional programming (almost) ftw

create_inverse()
main_function()

