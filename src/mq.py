#!/usr/lib/sagemath/ sage
# -*- coding: UTF-8 -*-

#http://stackoverflow.com/questions/193161/what-is-the-best-project-structure-for-a-python-application
#https://learnpythonthehardway.org/book/ex46.html
#http://docs.python-guide.org/en/latest/writing/structure/
#https://github.com/kennethreitz/samplemod

#http://doc.sagemath.org/html/en/tutorial/tour_algebra.html
#https://en.wikipedia.org/wiki/Remainder
from pprint import pprint
from random import choice
from random import randint
from random import shuffle
from sage.all import *
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildIrred_list
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildRandomIrred_list
import logging
import time

logging.basicConfig(level=logging.INFO, format='%(levelname)s %(name)s::%(funcName)s %(message)s')

__author__ = "Maroš Polák"
__copyright__ = "Copyright (c) 2016 - 2017, Maroš Polák"
__license__ = "GPL"
__version__ = "1.0.1"
__email__ = "xpolakm4 at stuba dot sk"
__status__ = "In progress"

class MQ(object):
  """
  sústave nelineárnych rovníc viacerých premenných nad konečným poľom
  Attributes:
    n         -- pocet premennych | count of variables
    m         -- pocet rovnic | count of equations
  """
  VARIABLE_X = 'x'
  VARIABLE_Y = 'y'
  VARIABLE_LAMBDA = 'L'
  OPERATOR_PLUS = '+'
  OPERATOR_MUL = '*'
  OPERATOR_POWER = '^'
  EQUATION_SEPARATOR = ' + '
  X_RAISED_TO = VARIABLE_X + OPERATOR_POWER
  LAMBDA_RAISED_TO = VARIABLE_LAMBDA + OPERATOR_POWER
  
  def __init__(self, n, m):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of MQ')
    if( n < 1 ):
      raise ValueError('Count of variables have to be greater than 1')
    if( m < 1 ):
      raise ValueError('Count of equations have to be greater than 1')
    
    self.n = n
    self.m = m
    self.product = self.create_product()
  
  def create_product(self):
    """
    Return product of x variables as list: 
    x1, x2, x1*x2, x3, x1*x3, x2*x3, x4, ..., xn
    """
    product = [MQ.VARIABLE_X + '1']
    
    n = self.n + 1
    for i in range(2, n):
      product.append(MQ.VARIABLE_X + str(i))
      
      for j in range(1, i):
        product.append(MQ.VARIABLE_X + str(j) + MQ.OPERATOR_MUL + MQ.VARIABLE_X + str(i))
    
    return product
    
  def create_equation(self):
    """
    Return equation in form x_1*Alpha^0 + x_2*Alpha^1 + ... + x_n*Alpha^(n-1),
    transformed into dictionary where keys are Alphas as strings 
    (MQ.VARIABLE_LAMBDA + MQ.OPERATOR_POWER + exponent) i.e. L^2
    """
    X = {};
    
    for exponent in range(self.n):
      X[MQ.LAMBDA_RAISED_TO + str(exponent)] = set([MQ.VARIABLE_X + str(exponent + 1)])
    
    return X
  
  def create_irreducible_polynomial(self, variable):
    """
    http://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_gf2x.html#sage.rings.polynomial.polynomial_gf2x.GF2X_BuildIrred_list
    Return the list of coefficients of the lexicographically smallest 
    irreducible polynomial of degree n over the Gladis field of 2 elements.
    """
    return GF(2)[variable](GF2X_BuildIrred_list(self.n))
  
  def create_random_irreducible_polynomial(self, variable):
    """
    http://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_gf2x.html#sage.rings.polynomial.polynomial_gf2x.GF2X_BuildRandomIrred_list
    Return the list of coefficients of an irreducible polynomial of degree n 
    of minimal weight over the Gladis field of 2 elements.
    """
    return GF(2)[variable](GF2X_BuildRandomIrred_list(self.n))

class AffineTransformation:
  def __init__(self, dimension, transformation_type):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of AffineTransformation')
    
    if dimension < 2:
      raise ValueError("Dimension have to be greather then 2")
    
    u_choice = transformation_type.upper()
    
    if u_choice == 'S':
      self.transformation_type = 'x'
    elif u_choice == 'T':
      self.transformation_type = 'y'
    else:
      raise ValueError("Transformation type should be 'S' or 'T'")
    
    self.dimension = dimension
    self.group = AffineGroup(dimension, GF(2))
    self.element = self.group.random_element()
    self.matrix = self.element.A() # treba tuto premennu?
    self.vector = self.element.b() # treba tuto premennu?
    self.transformation = {}
    
    self.compute_transformation()
    # inverza transformacia ~self.matrix alebo self.matrix.inverse()
    
  def compute_transformation(self):
    for row in range(self.dimension):
      equation = []
      
      for column in range(self.dimension):
        if self.matrix[row][column] == 1:
          equation.append(self.transformation_type + str(column + 1))
      
      if self.vector[row] == 1:
        equation.append('1')
      
      self.transformation[self.transformation_type + str(row + 1)] = equation



# MQ trapdoors
class UOV(object):
  def __init__(self, MQ):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of UOV')
    self.mq = MQ
    self.oil = []
    self.vinegar = []
    self._P = {}
    self.create_trapdoor()
    
  def create_trapdoor(self):
    self.logger.info('Creating trapdoor for UOV')
    # create list of variables that may occure in result
    variables = [MQ.VARIABLE_X + str(i) for i in range(1, self.mq.n + 1)]
    shuffle(variables)

    # divide them in oil and vinegar variables
    middle = self.mq.n / 2
    self.oil = variables[0:middle]
    self.vinegar = variables[middle:]
    
    vinegar_len = len(self.vinegar)
    oil_len = len(self.oil)
    variables.append('1')
    
    # add product of variables(vinegar*vinegar, vinegar*oil) that may be used in equation
    for i in range(vinegar_len): # loop through all vinegar variables
      for j in range(i + 1, vinegar_len):
        # insert product of vinegar variables alphabetically ordered
        if self.vinegar[i] < self.vinegar[j]:
          variables.append(self.vinegar[i] + MQ.OPERATOR_MUL + self.vinegar[j])
        else:
          variables.append(self.vinegar[j] + MQ.OPERATOR_MUL + self.vinegar[i])

      for j in range(oil_len): # loop through all oil variables
        # insert product of oil and vinegar variables alphabetically ordered
        if self.vinegar[i] < self.oil[j]:
          variables.append(self.vinegar[i] + MQ.OPERATOR_MUL + self.oil[j])
        else:
          variables.append(self.oil[j] + MQ.OPERATOR_MUL + self.vinegar[i])
    
    self.logger.info('vinegar variables %s' % self.vinegar)
    self.logger.info('oil variables %s' % self.oil)
    self.logger.info('product of variables %s' % variables)
    
    c_min = self.mq.n - 1
    c_max = self.mq.n + 1
    lottery = [i for i in range(len(variables))]
    i = 1
    while i < self.mq.m + 1: # for each equation
      self._P[MQ.VARIABLE_Y + str(i)] = set()     
      count = randint(c_min, c_max) # random count of variables in equation
      shuffle(lottery)
      
      nonlinear = False # ensuring that equation contain nonlinear variable
      for j in range(count):
        self._P[MQ.VARIABLE_Y + str(i)] |= set([variables[lottery[j]]])
        
        # condition added because of saving string comparasion cost
        if nonlinear == False:
          if MQ.OPERATOR_MUL in variables[lottery[j]]:
            nonlinear = True
      
      if nonlinear == False:
        i -= 1
      
      i += 1
    
    pprint(self._P)



class STS(object):
  """
  Class for Stepwise Triangular Systems.
  
  Attributes:
    MQ -- rodic | parent
    layers_count -- pocet vrstiev | total count of layers
    equations_in_layer -- pocet rovnic v danej vrstve | count of equations in each layer
    variables_in_layer -- pocet premennych v danej vrstve | count of variables in each layer
  """
  
  def __init__(self, MQ, layers_count, variables_in_layer, equations_in_layer):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of STS')
    self.mq = MQ
    self._P = {}
    self.layers_count = layers_count
    self.variables_in_layer = variables_in_layer
    self.equations_in_layer = equations_in_layer
    self.create_trapdoor()
    
  def check_params(self): 
    """
    metoda skontroluje ci pocet rovnice v jednotlivych vrstvach sa rovna 
    celkovemu poctu rovnic layers_count
    """
    if self.layers_count > self.mq.n:
      raise ValueError('Count of layers(' + str(self.layers_count) + ') is more than count of equation(' + str(self.mq.n) + ')')
    
    if sum(self.equations_in_layer) != self.layers_count:
      self.logger.warning('Count of equations is not equal to layers_count')
      raise ValueError('Count of equations is not equal to layers_count')
  
  def create_trapdoor(self):
    self.logger.info('creating trapdoor for STS')
    
    # ake premenne sa maju vyskytovat v rovniciach
    should_contains = [MQ.VARIABLE_X + str(i) for i in range(1, self.mq.n + 1)]
    
    for layer in range(self.layers_count):
      if self.variables_in_layer[layer] > self.mq.n:
        raise ValueError('Count of variables in layer ' + str(layer + 1) + ' is more than is possible -> ' + str(self.mq.n))
      
      variables_count = self.variables_in_layer[layer]
      triangle_number = variables_count * (variables_count + 1) / 2
      
      if self.equations_in_layer[layer] > triangle_number:
        raise ValueError('Count of equations in layer ' + str(layer + 1) + ' is more than is possible -> ' + str(triangle_number))
      
      sub_product = self.mq.product[:triangle_number]
      shuffle(sub_product)
      
      print("Layer: " + str(layer + 1))
      i = 0
      # pre pocet rovnic vo vrstve
      while i < self.equations_in_layer[layer]:
        actual_equation = MQ.VARIABLE_Y + str(i)
        
        rand = randint(self.variables_in_layer[layer], triangle_number)
        self._P[actual_equation] = set(sub_product[:rand])
        
        # skontrolujem ci vytvorena rovnica obsahuje vsetky premenne
        contain_vars = set(should_contains[:variables_count])
        for variables in self._P[actual_equation]:
          contain_vars -= set(variables.split('*'))
          if len(contain_vars) == 0:
            break
        
        # ak zostali nejake premenne tak ich treba pridat do rovnice
        for remaining_vars in contain_vars:
          num = int(remaining_vars[1:])
          triangle_number_min = (num - 1) * num / 2
          triangle_number_max = num * (num + 1) / 2
          triangle_number_max -= 1
          self._P[actual_equation] |= set([self.mq.product[randint(triangle_number_min, triangle_number_max)]])
        
        print("  Equation " + str(i + 1) + ": " + str(self._P[actual_equation]))
        
        # kontrolujem ci sa predchadzajuca rovnica nezhoduje s aktualnou
        if i > 0:
          actual_eq_len = len(self._P[actual_equation])
          
          for j in range(i):
            if actual_eq_len == len(self._P[MQ.VARIABLE_Y + str(j)]):
              if self._P[actual_equation] == self._P[MQ.VARIABLE_Y + str(j)]:
                print("Equation " + str(i + 1) + " equals with equation " + str(j + 1) + " -> creating new equation")
                i -= 1
        
        i += 1
        shuffle(sub_product)
    #print(self._P)
    
#    variables = var(variables_y)
#    eq1 = x1*x2 + x1 == 1
#    eq2 = x1*x2 + x2 == 0
#    res = solve([eq1, eq2], variables)
#    print(res)



class PolynomialBasedTrapdoor(MQ):
  def compute_remainder(self, irreducible_polynomial, key):
    """
    Return dictionary with remainders after raising irreducible polynomial 
    over its size
    """
    R = PolynomialRing(GF(2), key)
    S = R.quotient(irreducible_polynomial, key)
    a = S.gen()
    
    key_raised_to = key + MQ.OPERATOR_POWER
    
    remainder = {key_raised_to + '0': a ** 0}
    
    count = (irreducible_polynomial.degree() ** 2) - 1
    for exponent in range(1, count):
      remainder[key_raised_to + str(exponent)] = remainder[key_raised_to + str(exponent - 1)] * a
    
    return remainder
  
  def choose_operation(self, dictonary, key, left_value, right_value, as_set):
    if left_value == right_value:
      self.insert_value(dictonary, key, left_value, as_set)
    else:
      product = ''
      
      if left_value < right_value:
        product = left_value + MQ.OPERATOR_MUL + right_value
      else:
        product = right_value + MQ.OPERATOR_MUL + left_value
      
      self.insert_value(dictonary, key, product, as_set)  
  
  def square_polynomial(self, polynomial, times, remainders):
    """
    Raises the polynomial with exponent 2 n-times; polynomial^2^times
    """
    lambda_raised_to = MQ.VARIABLE_LAMBDA + MQ.OPERATOR_POWER
    
    # create copy of dictionary
    polynomial_copy = {}
    for key in polynomial:
      polynomial_copy[key] = polynomial[key].copy()
    
    for counter in range(times): # square polynomial n-times
      squared_polynomial = {}
      
      for key in polynomial_copy: # loop through all keys in dictionary {L^0, L^1, ..., L^(n-1)}
        # get exponent of actual key | lambda: L^x
        exponent = int(key[2:]) * 2
        
        if exponent < self.mq.n:
          squared_polynomial[lambda_raised_to + str(exponent)] = polynomial_copy[key]
        else:
          remand_keys = str(remainders[lambda_raised_to + str(exponent)]).split(' + ')
          
          for remand_key in remand_keys: # loop through all keys in array
            self.insert_value(squared_polynomial, remand_key, polynomial_copy[key], False)
          
      polynomial_copy = squared_polynomial
    
    return polynomial_copy
  
  def multiply_polynomials(self, left_side, right_side, remainders):
    result = {}
    
    for left_key in left_side:
      left_key_exponent = int(left_key[2:])
      
      for left_value in left_side[left_key]:
        self.logger.debug("Left key and value %s %s", left_key, left_value)
        
        for right_key in right_side:
          right_key_exponent = int(right_key[2:])
          
          for right_value in right_side[right_key]:
            self.logger.debug("Right key and value %s, %s", right_key, right_value)
            exponent_sum = left_key_exponent + right_key_exponent
            key = MIA.lambda_raised_to + str(exponent_sum)
            
            if exponent_sum < self.mq.n:
              self.choose_operation(result, key, left_value, right_value, True)
              self.logger.debug("After inserting\n%s", result)
            else:
              ired_keys = str(self.irred_polynomial_rem[key]).split(' + ')
              
              for ired_key in ired_keys:
                self.choose_operation(result, ired_key, left_value, right_value, True)
                self.logger.debug("After inserting\n%s", result)
              
          self.logger.debug("\n-------------")
      self.logger.debug('\n--------------------------')
    return result
  
  def insert_value(self, dictonary, key, value, as_set):
    if len(key) < 3:
      key = self.edit_key(key)
    
    self.logger.debug("Inserting at key = %s, value = %s", key, value)
    self.logger.debug("Before inserting\n%s", dictonary)
    
    if key in dictonary:
      if as_set == True:
        dictonary[key] ^= set([value]) # new set with elements in either s or t but not both
      else:
        dictonary[key] ^= value # new set with elements in either s or t but not both
    else:
      if as_set == True:
        dictonary[key] = set([value]) # new set with elements from both s and t
      else:
        dictonary[key] = value # new set with elements from both s and t
  
  def edit_key(self, key):
    # fix as sagemath return L^0 as 1 and L^1 as L
    if key == '1':
      return MQ.VARIABLE_LAMBDA + '^0'
    elif key == MQ.VARIABLE_LAMBDA:
      return MQ.VARIABLE_LAMBDA + '^1'
    else:
      raise ValueError('Key \'%s\' not found ', key)



class MIA(PolynomialBasedTrapdoor):
  """
  Matsumoto-Imai
  http://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_gf2x.html
  1. vygenerovat lambdu ak je to mozne -> GCD(2^n - 1, 2^L + 1) == 1
  2. vygenerovat vyraz v tvare x1 + x2*L^1 + x3*L^2 + ... x_n*L^n-1
  3. vygenerovat ireducibilny polynom stupna n
  4. zistit zvysky po deleni pre zvoleny ireducibilny polynom -> napr pre x3 + x + 1 = x1->x1, x2->x2, x3->x + 1, x4->x^2 + x, ...
  5. umocnit vygenerovany vyraz na 2^L + 1
  6. za labdy stupna vacsieho ako n dosadit zvysky po deleni
  7. roznasobit zatvorky
  8. vyjmut premenne pre dane lambdy
  """
  lambda_raised_to = MQ.VARIABLE_LAMBDA + MQ.OPERATOR_POWER
  
  def __init__(self, MQ):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of MIA')
    self.mq = MQ
    self._P = {}
    self._lambda = None
    self.create_trapdoor()
    
  def create_trapdoor(self):
    self._lambda = self.compute_lambda()
    left_side = self.mq.create_equation()
    right_side = self.mq.create_equation()#left_side.copy() # or dict(left_side)
    self.irred_polynomial = self.mq.create_irreducible_polynomial(MQ.VARIABLE_X)
    self.irred_polynomial_rem = self.compute_remainder(self.irred_polynomial, MQ.VARIABLE_LAMBDA)
    
    self.logger.info('Created irreducible polynomial = %s', str(self.irred_polynomial))
    # the equation is P`(X) = X ^ (2 ^ labda + 1) we break this into two parts
    
    # first part: a = left_side ^ (2 ^ lambda), will be calculated using the Frobenius automorphisms
    left_side = self.square_polynomial(left_side, self._lambda, self.irred_polynomial_rem)
    self.logger.info('For lambda = %s computed left side\n%s', self._lambda, left_side)
    self.logger.info('Multipling with right side\n%s\n-------------------------', right_side)
    
    # second part: P`(x) = a * X ^ 1
    self._P = self.multiply_polynomials(left_side, right_side, self.irred_polynomial_rem)
    self.logger.info('Result')
    pprint(self._P)
    
  def compute_lambda(self):
    """
    Computes number L, which fulfills the condition 
    GCD((2^n)-1, (2^L)+1) == 1, if this number is not found until the condition 
    (2^n)-1 < (2^L)+1 is fulfilled, where n is degree of polynomial then is
    raised error
    """
    lamb = 1
    first = 2 ** self.mq.n - 1
    second = 2 ** lamb + 1
    
    while second < first:
      if gcd(first, second) == 1:
        return lamb
      
      lamb += 1
      second = 2 ** lamb + 1
    
    raise ValueError('Lambda not found for n = ' + str(self.mq.n))



class HFE(PolynomialBasedTrapdoor):
  """
  Hidden Field Equations
  """
  
  def __init__(self, MQ):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of HFE')
    self.mq = MQ
    self._P = {}
    self.d = 0
    self.create_trapdoor()

  def create_trapdoor(self):
    self.logger.info('Creating trapdoor for HFE')
    self.irred_polynomial = self.mq.create_irreducible_polynomial(MQ.VARIABLE_X)
    self.irred_polynomial_rem = self.compute_remainder(self.irred_polynomial, MQ.VARIABLE_LAMBDA)
    base_polynomial = self.mq.create_equation()
    
    #d_range = range(self.mq.n, (self.mq.n * count) + 1) # pick d that should be small ?!
    d_range = range(self.mq.n, self.mq.n + 3) # pick d that should be small ?!
    self.d = choice(d_range) # pick random value from range
    self.logger.debug('Ireducible polynomial %s, polynomial degree d = %s', self.irred_polynomial, self.d)
    
    HFE = self.create_hfe_polynomial(self.d)
    self.logger.info('Created polynomial in HFE form %s' % HFE)
    #--------------------------------------------------------------------------#
    # umocnenie a nasobenie rovnic
    subs = {}
    for key in HFE:
      if key == MQ.X_RAISED_TO + '0':
        continue
      
      exponent = int(key[2:])
      
      if exponent > 1:
        times = exponent / 2
        squared = self.square_polynomial(base_polynomial, times, self.irred_polynomial_rem)
        
        if exponent % 2:
          multiplied = self.multiply_polynomials(squared, base_polynomial, self.irred_polynomial_rem)
          subs[key] = multiplied
        else:
          subs[key] = squared
      else:
        subs[key] = base_polynomial
    self.logger.info('Created polynomial in HFE form %s' % subs)
    #--------------------------------------------------------------------------#   
    for key_sub in subs: # for each x^1, x^2, ... x^d
      for key_lambda in subs[key_sub]: # for each L^0, L^1, L^2, ... L^(n - 1) in subs
        l_exponent = int(key_lambda[2:])
        self.logger.debug('key_sub=%s, key_lambda=%s, l_exponent=%s' % (key_sub, key_lambda, l_exponent))
        
        for equation in HFE[key_sub]:
          multiples = str(equation).split(' + ')
          
          for m in multiples:
            if len(m) < 3:
              m = self.edit_key(m)
            
            self.logger.debug('4 hodnoty nasobenia %s, -> %s' % (multiples, m))
            
            m_exponent = int(m[2:])
            sum_exponent = m_exponent + l_exponent
            value = subs[key_sub][key_lambda].copy()
            self.logger.debug('sucet exponentov=%s, vkladat sa bude=%s' % (sum_exponent, value))
            
            if sum_exponent < self.mq.n:  
              key = MQ.LAMBDA_RAISED_TO + str(sum_exponent)  
              
              self.insert_value(self._P, key, value, False)
              self.logger.debug(self._P)
            else:
              remainders = self.irred_polynomial_rem[MQ.LAMBDA_RAISED_TO + str(sum_exponent)]
              remainders = str(remainders).split(' + ')
              
              for remainder in remainders:
                if len(remainder) < 3:
                  remainder = self.edit_key(remainder)
                # care - creating copy of value because it will be inserted more
                # times and result would contain several references on it
                self.insert_value(self._P, remainder, value.copy(), False)
                self.logger.debug(self._P)
        self.logger.debug('\t----next lambda key----')
      self.logger.debug('----next subs----')
    
    # insertin x^0 values
    for values in HFE[MQ.X_RAISED_TO + '0']:
      values_list = str(values).split(' + ')
      
      for key in values_list:
        self.insert_value(self._P, key, '1', True)
    
    pprint(self._P)
    return self._P
          
  def create_hfe_polynomial(self, degree):
    # Let's create polynomial in HFE form
    C = {}
    B = {}
    A = {}
    i = 0
    j = 0
    
    while True:
      power_i = 2 ** i
      
      if power_i > degree:
        break
      
      while True:
        power_sum = power_i + (2 ** j)
        
        if power_sum <= degree:
          self.logger.debug('i=' + str(i) +', j=' + str(j) + ', 2^i + 2^j=' + str(power_sum))
          c_key = choice(list(self.irred_polynomial_rem.keys())) # random.choice() from keys in dictonary
          c_value = set([self.irred_polynomial_rem[c_key]]) # vyber nahodny zvysok po deleni polynomom
          x_key = self.X_RAISED_TO + str(power_sum)
          
          if x_key in C:
            C[x_key] ^= set(c_value)
          else:
            C[x_key] = set(c_value)
          
          j += 1
        else:
          j = 0
          break
      
      b_key = choice(list(self.irred_polynomial_rem.keys())) # random.choice() from keys in dictonary
      B[self.X_RAISED_TO + str(power_i)] = set([self.irred_polynomial_rem[b_key]]) # vyber nahodny zvysok po deleni polynomom
      i += 1

    a_key = choice(list(self.irred_polynomial_rem.keys())) # random.choice() from keys in dictonary
    A[self.X_RAISED_TO + '0'] = set([self.irred_polynomial_rem[a_key]]) # vyber nahodny zvysok po deleni polynomom
    #--------------------------------------------------------------------------#
    HFE = C # just rename
    HFE.update(A) # copy dict A to dict X

    for key in B: # copy dict B to dict X
      if key in HFE:
        HFE[key] |= B[key]
      else:
        HFE[key] = B[key]
    
    # equation in HFE form
    return HFE

# Main
class MHRS:
  # 1. vygenerovat maticu A_s, vektor b_s
  # 2. vyjadrit rovnice(1) z matice a vektora = x_m
  # 3. pouzit vybranu strukturu = y_m
  
  # 4. vygenerovat maticu A_t, vektor b_t
  # 5. vyjadrit rovnice(3) z matice a vektora = y_m
  # dosadit rovnice(2) do rovnic(3) y_m
  def __init__(self, degree):
    self.T = AffineTransformation(degree) # affine transformation, private
    self.trapdoor = None # private
    self.S = AffineTransformation(degree) # affine transformation, private
    self.P = [] # public, P = T o _P o S
    
  def compute_p(self):
    self.P = 0
    
    
def premenne_z(n):
  premenneZ = []
  
  n += 1
  
  for i in range(2, n):
    for j in range(1, i):
      premenneZ.append('z' + str(j) + '_' + str(i))
          
  return premenneZ

def premenne(n, premenneZ):
  premenne = []
  
  n += 1
  
  for i in range(1, n):
    premenne.append('x' + str(i))
  # join | concanetate two lists
  premenne += premenneZ
  
  A = BooleanPolynomialRing(names=premenne)
  #print "A = ", A
  A.inject_variables(verbose=false)
  #print "A inject = ", A
  Slovnik = A.gens_dict()
  print "Slovnik = ", Slovnik
  
  n -= 1
  Slovnik2 = {}
  for i in range(1, n):
    for j in range(i + 1, n + 1):
      Slovnik2[Slovnik['x' + str(i)] * Slovnik['x' + str(j)]] = Slovnik['z' + str(i) + '_' + str(j)]
  print(Slovnik2)
  
def create_polynomial(elements, degree):
  if elements <= 1:
    return []
  
  result = range(1, elements)
  
  for i in range(degree):
    x_var = 'x^' + str(i + 1)
    
    result.append(x_var)
    list_len = len(result) - 1
    
    x_var += '+'
    for j in range(list_len):
      result.append(x_var + str(result[j]))
  
  return result

#1.HFE ak je d = 4 tak mam zabezpecit aby to vygenerovalo L^4
#2.HFE co znamena nemalo byt nic velke? napisat moznost o ruletovom vybere
#3.STS netreba teda aby v nasledujucej vrstve boli premenne z predchadzajucej vrstvy len nove premenne
#4.pocet olejovych ma byt viac ako octovych alebo naopak? aky pomer? a kolko premennych ma byt v rovnici?
#
# compute_remainder: spravit v metode nech L a 1 vracia uz ako L^1 a L^0
# subs: optimalizacia

def run_test(times = 1):
  average = 0
  for test_runs in range(times):
    start = time.time()
    ###################
    
    ###################
    average += (time.time() - start)
  print(average / times)
  
if __name__ == "__main__":
  mq = MQ(4, 4)
  #run_test(30)
  uov = UOV(mq)
  #sts = STS(mq, 2, [2, 4], [2, 2])
  #mia = MIA(mq)
  #hfe = HFE(mq)
