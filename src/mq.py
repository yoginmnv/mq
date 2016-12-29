#!/usr/lib/sagemath/ sage
# -*- coding: UTF-8 -*-

#http://stackoverflow.com/questions/193161/what-is-the-best-project-structure-for-a-python-application
#https://learnpythonthehardway.org/book/ex46.html
#http://docs.python-guide.org/en/latest/writing/structure/
#https://github.com/kennethreitz/samplemod

from pprint import pprint
from random import choice
from random import randint
from random import shuffle
from sage.all import *
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildIrred_list
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildRandomIrred_list
import logging
import time

# levels = NOTSET INFO DEBUG WARNING
logging.basicConfig(level=logging.DEBUG, format='%(levelname)s %(name)s::%(funcName)s %(message)s')

__author__ = "Maroš Polák"
__copyright__ = "Copyright (c) 2016 - 2017, Maroš Polák"
__license__ = "GPL"
__version__ = "1.0.1"
__email__ = "xpolakm4 at stuba dot sk"
__status__ = "In progress"

class MQ(object):
  """
  sústave nelineárnych rovníc viacerých premenných nad konečným poľom
  set of nonlinear(quadratics) polynomials over a finite field
  
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
  VARIABLE_SEPARATOR = ' + '
  X_RAISED_TO = VARIABLE_X + OPERATOR_POWER
  LAMBDA_RAISED_TO = VARIABLE_LAMBDA + OPERATOR_POWER
  
  def __init__(self, n, m, trapdoor):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of MQ n=%s, m=%s' % (n, m))
    if( n < 1 ):
      raise ValueError('Count of variables have to be greater than 1')
    if( m < 1 ):
      raise ValueError('Count of equations have to be greater than 1')
    
    self.n = n
    self.m = m
    self.set_trapdoor(trapdoor)
  
  def set_trapdoor(self, trapdoor):
    self.logger.debug('Enter ------------------------------')
    self.trapdoor = trapdoor
    self.trapdoor.create_trapdoor(self) # create private key
    pprint(self.trapdoor._P)
    exit(0)
    self.S = AffineTransformation(self.n, 'S') # private key
    
    if isinstance(trapdoor, UOV) or isinstance(trapdoor, STS):
      self.T = AffineTransformation(self.m, 'T') # private key
    else:
      self.T = AffineTransformation(self.n, 'T') # private key
    
    self._PS_product = self.substitute_and_multiply(self.trapdoor._P, self.S.transformation)
    self.T_PS_product = self.substitute(self.T.transformation, self._PS_product) # public key
    
    if 0:
      pprint(self.trapdoor._P)
      pprint(self.S.transformation)
      pprint(self.T.transformation)
      print('------------------------------')
      pprint(self._PS_product)
      pprint(self.T_PS_product)
    
  def substitute_and_multiply(self, trapdoor, transformation_s):
    self.logger.debug('Enter ------------------------------')
    result = {}
    
    for key in trapdoor: # loop throug all keys(y1, y2, ...yn) in trapdoor
      self.logger.debug('Key %s' % key)
      
      for variable in trapdoor[key]: # for each variable in equation
        self.logger.debug('Variable %s' % variable)
        
        if MQ.OPERATOR_MUL in variable: # if contain * we must multiply them
          var = variable.split(MQ.OPERATOR_MUL)
          
          eq1 = transformation_s[var[0]].split(MQ.VARIABLE_SEPARATOR)
          eq2 = transformation_s[var[1]].split(MQ.VARIABLE_SEPARATOR)
          for eq1_var in eq1:
            for eq2_var in eq2:
              if eq1_var == '1':
                if eq2_var == '1':
                  self.insert_value_dictionary(result, key, '1', True)
                else:
                  self.insert_value_dictionary(result, key, eq2_var, True)
              elif eq2_var == '1':
                self.insert_value_dictionary(result, key, eq1_var, True)
              else:
                self.insert_value_ordered(result, key, eq1_var, eq2_var, True)
        
        elif variable == '1':
          self.insert_value_dictionary(result, key, '1', True)
        
        else:
          for transformation_variable in transformation_s[variable].split(MQ.VARIABLE_SEPARATOR):
            self.logger.debug('transformation_variable %s' % transformation_variable)
            self.insert_value_dictionary(result, key, transformation_variable, True)
      
    self.logger.info('_P o S=%s' % result)
    return result
  
  def substitute(self, transformation_t, _PS):
    self.logger.debug('Enter ------------------------------')
    result = {}
    
    for key in transformation_t:
      self.logger.debug('Key %s' % key)
      variables = transformation_t[key].split(MQ.VARIABLE_SEPARATOR)
      
      for variable in variables:
        self.logger.debug('Variable %s' % variable)
        if variable == '1':
          self.insert_value_dictionary(result, key, '1', True)
        else:
          self.insert_value_dictionary(result, key, _PS[variable], False)
    
    self.logger.info('T o _P o S=%s' % result)
    return result
  
  def insert_value_list(self, array, value1, value2):
    """
    Appends product of values to list arranged according to index: val1_index, val2_index
    """
    self.logger.debug('Enter ------------------------------')
    
    if value1 < value2:
      array.append(value1 + MQ.OPERATOR_MUL + value2)
    else:
      array.append(value2 + MQ.OPERATOR_MUL + value1)
  
  def insert_value_ordered(self, dictionary, key, value1, value2, as_set):
    self.logger.debug('Enter ------------------------------')
    
    if value1 == value2:
      self.insert_value_dictionary(dictionary, key, value1, as_set)
    elif value1 < value2:
      self.insert_value_dictionary(dictionary, key, value1 + MQ.OPERATOR_MUL + value2, as_set)
    else:
      self.insert_value_dictionary(dictionary, key, value2 + MQ.OPERATOR_MUL +  value1, as_set)
  
  def insert_value_dictionary(self, dictionary, key, value, as_set):
    self.logger.debug('Enter ------------------------------')
    self.logger.debug('Inserting at key = %s, value = %s' % (key, value))
    self.logger.debug('Dictionary before inserting\n%s' % dictionary)
    
    if key in dictionary:
      if as_set == True:
        dictionary[key] ^= set([value]) # new set with elements in either s or t but not both
      else:
        dictionary[key] ^= value # new set with elements in either s or t but not both
    else:
      if as_set == True:
        dictionary[key] = set([value]) # new set with elements from both s and t
      else:
        dictionary[key] = value # new set with elements from both s and t
    
    self.logger.debug('Dictionary after inserting\n%s' % dictionary)



class AffineTransformation(object):
  """
  Create matrix of dimension n * n over finite field with 2 elements: 0 and 1, and vector n-bits long
  http://doc.sagemath.org/html/en/reference/groups/sage/groups/affine_gps/affine_group.html
  """
  def __init__(self, dimension, transf_type):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of AffineTransformation of size=%s' % dimension)
    
    if dimension < 2:
      raise ValueError('Dimension have to be greather then 2')
    if not (transf_type == 'S' or transf_type == 'T'):
      raise ValueError('Transformation type shoudl be S or T')
    
    self.transf_type = transf_type
    self.group = AffineGroup(dimension, GF(2))
    self.element = self.group.random_element()
    self.matrix = self.element.A()
    self.vector = self.element.b()
    self.logger.debug('created matrix=%s' % self.matrix)
    self.logger.debug('created vector=%s' % self.vector)
    self.transformation = self.compute_transformation(dimension)
    # inverzna transformacia ~self.matrix alebo self.matrix.inverse()
    
  def compute_transformation(self, dimension):
    self.logger.debug('Enter ------------------------------')
    
    transformation = {}
    variable = ''
    if self.transf_type == 'S':
      variable = MQ.VARIABLE_X
    else:
      variable = MQ.VARIABLE_Y
    
    for row in range(dimension): # for each row in matrix
      row_index = variable + str(row + 1) # create row index
      
      for column in range(dimension): # for each column in matrix
        if self.matrix[row][column] == 1: # if matrix[row][column] == 1 add variable to equation
          if row_index in transformation: # if key exists
            transformation[row_index] += (MQ.VARIABLE_SEPARATOR + variable + str(column + 1))
          else:
            transformation[row_index] = variable + str(column + 1)
      
      if self.vector[row] == 1:
        if row_index in transformation: 
          transformation[row_index] += (MQ.VARIABLE_SEPARATOR + '1')
        else:
          transformation[row_index] = '1'
    
    self.logger.info('Transformation %s=%s' % (self.transf_type, transformation))
    return transformation



# MQ trapdoors
class UOV(MQ):
  """
  Unbalanced oil and vinegar
  """
  def __init__(self):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of UOV')
    self.oil = []
    self.vinegar = []
    self._P = {}
  
  def create_trapdoor(self, mq):
    self.logger.info('Creating trapdoor for UOV')
    self.mq = mq
    # create list of variables that may occure in result
    variables = [MQ.VARIABLE_X + str(i) for i in range(1, mq.n + 1)]
    shuffle(variables)
    
    # divide them in oil and vinegar variables
    middle = mq.n / 2
    self.oil = variables[0:middle]
    # the more vinegar variables the harder is it to get original message
    self.vinegar = variables[middle:]
    
    # get lenght of list for for loops
    oil_len = middle
    if mq.n & 1 == 0:
      vinegar_len = middle
    else:
      vinegar_len = middle + 1
    
    variables.append('1')
    # add product of variables(vinegar*vinegar, vinegar*oil) that may be occure in equation
    for i in range(vinegar_len): # loop through all vinegar variables
      for j in range(i + 1, vinegar_len):
        # insert product of vinegar variables arranged according to index
        self.insert_value_list(variables, self.vinegar[i], self.vinegar[j])
      
      for j in range(oil_len): # loop through all oil variables
        # insert product of oil and vinegar variables arranged according to index
        self.insert_value_list(variables, self.vinegar[i], self.oil[j])
    
    self.logger.info('Vinegar variables %s' % self.vinegar)
    self.logger.info('Oil variables %s' % self.oil)
    if logging.getLogger().getEffectiveLevel() == logging.DEBUG:
      variables.sort()
    self.logger.debug('Product of variables %s' % variables)
    
    c_min = mq.n - 1
    c_max = mq.n + 1
    lottery = [i for i in range(len(variables))]
    i = 1
    while i < mq.m + 1: # for each equation
      shuffle(lottery) # shuffle values
      count = randint(c_min, c_max) # random count of variables for equation
      nonlinear = False # ensuring that equation contain nonlinear variables
      
      for j in range(count): # insert count variables into dictionary
        self.insert_value_dictionary(self._P, MQ.VARIABLE_Y + str(i), variables[lottery[j]], True)
        
        # if condition added because of saving string comparasion cost
        if nonlinear == False:
          if MQ.OPERATOR_MUL in variables[lottery[j]]:
            nonlinear = True
      
      if nonlinear == False:
        i -= 1
      
      i += 1
    
    self.logger.info('_P=%s' % self._P)
    return self._P



class STS(MQ):
  """
  Class for Stepwise Triangular Systems.
  
  Attributes:
    MQ -- rodic | parent
    layers_count -- pocet vrstiev | total count of layers
    equations_in_layer -- pocet rovnic v danej vrstve | count of equations in each layer
    variables_in_layer -- pocet premennych v danej vrstve | count of variables in each layer
  """
  
  def __init__(self, layers_count, variables_in_layer, equations_in_layer):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of STS')
    self._P = {}
    self.layers_count = layers_count
    self.variables_in_layer = variables_in_layer
    self.equations_in_layer = equations_in_layer
    
  def check_params(self): 
    """
    metoda skontroluje ci pocet rovnice v jednotlivych vrstvach sa rovna 
    celkovemu poctu rovnic layers_count
    """
    if self.layers_count > self.mq.n:
      raise ValueError('Count of layers(' + str(self.layers_count) + ') is more than count of equation(' + str(self.mq.n) + ')')
    
    if sum(self.equations_in_layer) != self.layers_count:
      raise ValueError('Count of equations is not equal to layers_count')
  
  def create_trapdoor(self, mq):
    self.logger.info('Creating trapdoor for STS')
    self.mq = mq
    
    product = self.create_product(self.mq.n) # x1, x2, x1*x2, x3, x1*x3, x2*x3, x4, ...
    # ake premenne sa maju vyskytovat v rovniciach
    should_contains = [MQ.VARIABLE_X + str(i) for i in range(1, self.mq.n + 1)]
    
    for layer in range(self.layers_count): # for each layer
      if self.variables_in_layer[layer] > self.mq.n: # check if count of variables is not higher then total count of variables
        raise ValueError('Count of variables in layer ' + str(layer + 1) + ' is more than is possible -> ' + str(self.mq.n))
      
      variables_count = self.variables_in_layer[layer]
      triangle_number = variables_count * (variables_count + 1) / 2 # compute how many variables can be picked from list product for current count variables in layer
      
      if self.equations_in_layer[layer] > triangle_number: # check if is possible to generate so much equations
        raise ValueError('Count of equations in layer ' + str(layer + 1) + ' is more than is possible -> ' + str(triangle_number))
      
      sub_product = product[:triangle_number]
      shuffle(sub_product)
      
      self.logger.debug("Layer: " + str(layer + 1))
      i = 0
      # pre pocet rovnic vo vrstve
      while i < self.equations_in_layer[layer]:
        actual_equation = MQ.VARIABLE_Y + str(i)
        
        rand = randint(self.variables_in_layer[layer], triangle_number)
        self._P[actual_equation] = set(sub_product[:rand])
        
        # skontrolujem ci vytvorena rovnica obsahuje vsetky premenne
        contain_vars = set(should_contains[:variables_count])
        for variables in self._P[actual_equation]:
          contain_vars -= set(variables.split(MQ.OPERATOR_MUL))
          if len(contain_vars) == 0:
            break
        
        # ak zostali nejake premenne tak ich treba pridat do rovnice
        for remaining_vars in contain_vars:
          num = int(remaining_vars[1:])
          triangle_number_min = (num - 1) * num / 2
          triangle_number_max = num * (num + 1) / 2
          triangle_number_max -= 1
          self._P[actual_equation] |= set([self.mq.product[randint(triangle_number_min, triangle_number_max)]])
        
        self.logger.debug("  Equation " + str(i + 1) + ": " + str(self._P[actual_equation]))
        
        # kontrolujem ci sa predchadzajuca rovnica nezhoduje s aktualnou
        if i > 0:
          actual_eq_len = len(self._P[actual_equation])
          
          for j in range(i):
            if actual_eq_len == len(self._P[MQ.VARIABLE_Y + str(j)]):
              if self._P[actual_equation] == self._P[MQ.VARIABLE_Y + str(j)]:
                self.logger.debug("Equation " + str(i + 1) + " equals with equation " + str(j + 1) + " -> creating new equation")
                i -= 1
        
        i += 1
        shuffle(sub_product)
    
    self.logger.info('_P=%s' % self._P)
    return self._P

  def create_product(self, n):
    """
    Return product of x variables as list: 
    x1, x2, x1*x2, x3, x1*x3, x2*x3, x4, ..., xn
    """
    self.logger.debug('Enter ------------------------------')
    
    product = [MQ.VARIABLE_X + '1']
    
    n += 1
    for i in range(2, n):
      variable = MQ.VARIABLE_X + str(i)
      product.append(variable)
      
      for j in range(1, i):
        product.append(MQ.VARIABLE_X + str(j) + MQ.OPERATOR_MUL + variable)
    
    return product



class PolynomialBasedTrapdoor(MQ):
  def create_irreducible_polynomial(self, variable, n):
    """
    http://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_gf2x.html#sage.rings.polynomial.polynomial_gf2x.GF2X_BuildIrred_list
    Return the list of coefficients of the lexicographically smallest 
    irreducible polynomial of degree n over the Gladis field of 2 elements.
    """
    self.logger.debug('Enter ------------------------------')
    
    return GF(2)[variable](GF2X_BuildIrred_list(n))
  
  def create_random_irreducible_polynomial(self, variable, n):
    """
    http://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_gf2x.html#sage.rings.polynomial.polynomial_gf2x.GF2X_BuildRandomIrred_list
    Return the list of coefficients of an irreducible polynomial of degree n 
    of minimal weight over the Gladis field of 2 elements.
    """
    self.logger.debug('Enter ------------------------------')
    
    return GF(2)[variable](GF2X_BuildRandomIrred_list(n))
  
  def create_equation(self, n):
    """
    Return equation in form x_1*Alpha^0 + x_2*Alpha^1 + ... + x_n*Alpha^(n-1),
    transformed into dictionary where keys are Alphas as strings 
    (MQ.VARIABLE_LAMBDA + MQ.OPERATOR_POWER + exponent) i.e. L^2
    """
    self.logger.debug('Enter ------------------------------')
    
    X = {};
    
    for exponent in range(n):
      X[MQ.LAMBDA_RAISED_TO + str(exponent)] = set([MQ.VARIABLE_X + str(exponent + 1)])
    
    return X
  
  def compute_remainder(self, irreducible_polynomial, key):
    """
    Return dictionary with remainders after raising irreducible polynomial 
    over its size
    """
    self.logger.debug('Enter ------------------------------')
    
    R = PolynomialRing(GF(2), key)
    S = R.quotient(irreducible_polynomial, key)
    a = S.gen()
    
    key_raised_to = key + MQ.OPERATOR_POWER
    
    remainder = {key_raised_to + '0': a ** 0}
    
    count = (irreducible_polynomial.degree() ** 2) - 1
    for exponent in range(1, count):
      remainder[key_raised_to + str(exponent)] = remainder[key_raised_to + str(exponent - 1)] * a
    
    return remainder
  
  def square_polynomial(self, polynomial, times, remainders):
    """
    Raises the polynomial with exponent 2 n-times; polynomial^2^times
    """
    self.logger.debug('Enter ------------------------------')
    
    # create copy of dictionary, as we don't want to change it
    polynomial_copy = {}
    for key in polynomial:
      polynomial_copy[key] = polynomial[key].copy()
    
    for counter in range(times): # square polynomial n-times
      squared_polynomial = {}
      
      for key in polynomial_copy: # loop through all keys in dictionary {L^0, L^1, ..., L^(n-1)}
        # get exponent of actual key | lambda: L^x
        exponent = int(key[2:]) * 2
        
        if exponent < self.mq.n:
          squared_polynomial[MQ.LAMBDA_RAISED_TO + str(exponent)] = polynomial_copy[key]
        else:
          remand_keys = str(remainders[MQ.LAMBDA_RAISED_TO + str(exponent)]).split(MQ.VARIABLE_SEPARATOR)
          
          for remand_key in remand_keys: # loop through all keys in array
            if len(remand_key) < 3:
              remand_key = self.edit_key(remand_key)
            
            self.insert_value_dictionary(squared_polynomial, remand_key, polynomial_copy[key], False)
      
      polynomial_copy = squared_polynomial
    
    return polynomial_copy
  
  def multiply_polynomials(self, left_side, right_side, remainders):
    self.logger.debug('Enter ------------------------------')
    
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
            key = MQ.LAMBDA_RAISED_TO + str(exponent_sum)
            
            if exponent_sum < self.mq.n:
              self.insert_value_ordered(result, key, left_value, right_value, True)
            else:
              ired_keys = str(self.irred_polynomial_rem[key]).split(MQ.VARIABLE_SEPARATOR)
              
              for ired_key in ired_keys:
                if len(ired_key) < 3:
                  ired_key = self.edit_key(ired_key)
                self.insert_value_ordered(result, ired_key, left_value, right_value, True)
              
          self.logger.debug("\n-------------")
      self.logger.debug('\n--------------------------')
    return result
  
  def edit_key(self, key):
    self.logger.debug('Enter ------------------------------')
    
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
  use n that is not divisible by 2^n: 4, 8, 16, 32, 64, ...
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
  
  def __init__(self):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of MIA')
    self._P = {}
    
  def create_trapdoor(self, mq):
    self.logger.info('Creating trapdoor for MIA')
    self.mq = mq
    self._lambda = self.compute_lambda()
    self.irred_polynomial = self.create_irreducible_polynomial(MQ.VARIABLE_X, mq.n)
    self.irred_polynomial_rem = self.compute_remainder(self.irred_polynomial, MQ.VARIABLE_LAMBDA)
    base_polynomial = self.create_equation(mq.n)
    
    self.logger.info('Created irreducible polynomial=%s' % self.irred_polynomial)
    # the equation is P'(X) = X ^ (2 ^ labda + 1) we break this into two parts
    
    # first part: a = left_side ^ (2 ^ lambda), will be calculated using the Frobenius automorphisms
    left_side = self.square_polynomial(base_polynomial, self._lambda, self.irred_polynomial_rem)
    self.logger.info('For lambda=%s computed left side\n%s' % (self._lambda, left_side))
    self.logger.info('Multipling left side with right side\n%s' % base_polynomial)
    
    # second part: P'(x) = a * X ^ 1
    self._P = self.multiply_polynomials(left_side, base_polynomial, self.irred_polynomial_rem)
    
    # just renaming keys from L^x to yx
    result = {}
    for i in range(self.mq.n):
      result[MQ.VARIABLE_Y + str(i + 1)] = self._P[MQ.LAMBDA_RAISED_TO + str(i)]
    
    self._P = result
    self.logger.info('_P=%s' % self._P)
    return self._P
    
  def compute_lambda(self):
    """
    Computes number L, which fulfills the condition 
    GCD((2^n)-1, (2^L)+1) == 1, if this number is not found until the condition 
    (2^n)-1 < (2^L)+1 is fulfilled, where n is degree of polynomial then is
    raised error
    """
    self.logger.debug('Enter ------------------------------')
    
    lamb = 1
    first = 2 ** self.mq.n - 1
    second = 2 ** lamb + 1
    
    while second < first:
      if gcd(first, second) == 1:
        return lamb
      
      lamb += 1
      second = 2 ** lamb + 1
    
    raise ValueError('Lambda not found for n=%s' % self.mq.n)



class HFE(PolynomialBasedTrapdoor):
  """
  Hidden Field Equations
  """
  
  def __init__(self):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of HFE')
    self._P = {}
  
  def create_trapdoor(self, mq):
    self.logger.info('Creating trapdoor for HFE')
    self.mq = mq
    self.irred_polynomial = self.create_irreducible_polynomial(MQ.VARIABLE_X, mq.n)
    self.irred_polynomial_rem = self.compute_remainder(self.irred_polynomial, MQ.VARIABLE_LAMBDA)
    base_polynomial = self.create_equation(mq.n)
    
    #d_range = range(self.mq.n, (self.mq.n * count) + 1) # pick d that should be small ?!
    d_range = range(mq.n, mq.n + 3) # pick d that should be small ?!
    self.d = choice(d_range) # pick random value from range
    self.logger.debug('Ireducible polynomial=%s, polynomial degree d=%s' % (self.irred_polynomial, self.d))
    
    HFE = self.create_hfe_polynomial(self.d)
    self.logger.info('Created polynomial in HFE form\n%s' % HFE)
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
    self.logger.info('Raised HFE polynomial\n%s' % subs)
    #--------------------------------------------------------------------------#   
    for key_sub in subs: # for each x^1, x^2, ... x^d
      for key_lambda in subs[key_sub]: # for each L^0, L^1, L^2, ... L^(n - 1) in subs
        l_exponent = int(key_lambda[2:])
        self.logger.debug('key_sub=%s, key_lambda=%s, l_exponent=%s' % (key_sub, key_lambda, l_exponent))
        
        for equation in HFE[key_sub]:
          multiples = str(equation).split(MQ.VARIABLE_SEPARATOR)
          
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
              
              self.insert_value_dictionary(self._P, key, value, False)
            else:
              remainders = self.irred_polynomial_rem[MQ.LAMBDA_RAISED_TO + str(sum_exponent)]
              remainders = str(remainders).split(MQ.VARIABLE_SEPARATOR)
              
              for remainder in remainders:
                if len(remainder) < 3:
                  remainder = self.edit_key(remainder)
                # care - creating copy of value because it will be inserted more
                # times and result would contain several references on it
                self.insert_value_dictionary(self._P, remainder, value.copy(), False)
        self.logger.debug('\t----next lambda key----')
      self.logger.debug('----next subs----')
    
    # insertin x^0 values
    for values in HFE[MQ.X_RAISED_TO + '0']:
      values_list = str(values).split(MQ.VARIABLE_SEPARATOR)
      
      for key in values_list:
        self.insert_value_dictionary(self._P, key, '1', True)
    
    # just renaming keys from L^x to yx
    result = {}
    for i in range(mq.n):
      result[MQ.VARIABLE_Y + str(i + 1)] = self._P[MQ.LAMBDA_RAISED_TO + str(i)]
    
    self._P = result
    self.logger.info('_P=%s' % self._P)
    return self._P
          
  def create_hfe_polynomial(self, degree):
    self.logger.debug('Enter ------------------------------')
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
  if 0 == 1:
    run_test(1000)
    exit(0)
  
  trapdoor = {
    'uov': UOV(),
    'sts': STS(2, [2, 4], [2, 4]),
    'mia': MIA(),
    'hfe': HFE()
  }
  mq = MQ(4, 4, trapdoor['sts'])