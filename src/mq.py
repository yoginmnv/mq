#!/usr/lib/sagemath/ sage
# -*- coding: UTF-8 -*-

#http://stackoverflow.com/questions/193161/what-is-the-best-project-structure-for-a-python-application
#https://learnpythonthehardway.org/book/ex46.html
#http://docs.python-guide.org/en/latest/writing/structure/
#https://github.com/kennethreitz/samplemod
#https://www.python.org/dev/peps/pep-0008/
#http://sphinxcontrib-napoleon.readthedocs.io/en/latest/example_google.html

from collections import OrderedDict
from datetime import datetime
from pprint import pprint
from random import choice, randint, sample, shuffle
from sage.all import *
from sage.groups.affine_gps.affine_group import AffineGroup # AffineGroup()
# the "same" as bellow from sage.rings.finite_rings.all import GF # GF
from sage.rings.finite_rings.finite_field_constructor import FiniteField as GF # GF
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildIrred_list
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildSparseIrred_list
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildRandomIrred_list
import irreducible_polynomials
import json
import logging
import subprocess
import time

import mrhs
import jamrichova

__author__ = "Maroš Polák"
__copyright__ = "Copyright (c) 2016 - 2017, Maroš Polák"
__credits__ = "Viliam Hromada"
__license__ = "GPL"
__version__ = "1.2.1"
__email__ = "xpolakm4 at stuba dot sk"
__status__ = "ready but still in progress"

# TODO
# Optimalizovat HFE
# HFE ak je d = 4 tak mam zabezpecit aby to vygenerovalo L^4
#
# compute_remainder: spravit v metode nech L a 1 vracia uz ako L^1 a L^0
#
# vyskusat secure_random = random.SystemRandom()
#
# neimportovat vsetko zo sage, lebo to dlho trva
# skusit najst sposob aby nebol problem z ImportError: cannot import name ZZ
#
#if logging.getLogger().getEffectiveLevel() == logging.DEBUG:

# levels = WARNING INFO DEBUG NOTSET
logging.basicConfig(level=logging.INFO, format='%(levelname)s %(name)s::%(funcName)s %(message)s')

# pretty print
HUMAN_PRINT = 0

def main():
  # main tests that was used as a result in diploma thesis
  #Test(range(5, 6), range(4, 8), [3], [], comment="test")
 
  # sample usage, set size of n, m pick one trapdoor set is as attribute to MQ
  # object store the resulting public key in MQ Challenge format or perform some
  # tests
  n = 4
  m = 4
  trapdoor = {
    'uov': UOV(),
    'sts': STS(2, [2, 3], [2, 3]),
    'mia': MIA(),
    'hfe': HFE()
  }
  mq = MQ(n, m, trapdoor['uov'])
  #jamrichova.convert(mq)
  
  mc = MQChallenge(mq)
  #mc.store()
  mrhs.convert(data=mc.polynomial_matrix)
  
  # previously used as performance tests for tasks
  #if 0 == 1:
  #  run_test(1)
  #  exit(0)
  
  # previously testing test but were not used
  #estimate_complexity()



class MQ(object):
  """
  sústave nelineárnych rovníc viacerých premenných nad konečným poľom
  set of nonlinear(quadratics) polynomials over a finite field
  
  add trapdoor to attribute TRAPDOORS in method __init__
  
  Args:
    n (int): pocet premennych | count of variables
    m (int): pocet rovnic | count of equations
    trapdoor:
    
  Raises:
  """
  VARIABLE_X = 'x'
  VARIABLE_Y = 'y'
  VARIABLE_LAMBDA = 'L'
  VARIABLE_SEPARATOR = ' + '
  OPERATOR_MUL = '*'
  OPERATOR_PLUS = '+'
  OPERATOR_POWER = '^'
  X_RAISED_TO = VARIABLE_X + OPERATOR_POWER
  LAMBDA_RAISED_TO = VARIABLE_LAMBDA + OPERATOR_POWER
  
  def __init__(self, n, m, trapdoor):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of MQ n=%s, m=%s' % (n, m))
    TRAPDOORS = (UOV, STS, MIA, HFE)
    
    if( n < 1 ):
      raise ValueError('Count of variables have to be greater than 1')
    if( m < 1 ):
      raise ValueError('Count of equations have to be greater than 1')
    
    if not isinstance(trapdoor, TRAPDOORS):
      raise ValueError('Unknow trapdoor=\"%s\"' % (type(trapdoor)))
    
    self.n = n
    self.m = m
    # just for MQChallenge format used in MIA and HFE
    self.irred_polynomial = None
    if isinstance(trapdoor, MIA) or isinstance(trapdoor, HFE):
      self.m = n
      self.logger.info('Setting m=%d (due %s)' % (self.m, type(trapdoor)))
    
    self.set_trapdoor(trapdoor)
  
  def set_trapdoor(self, trapdoor):
    self.logger.debug('Enter')
    self.trapdoor = trapdoor
    self.trapdoor.create_trapdoor(self) # create private key
    
    if HUMAN_PRINT:
      print('==============================')
    
    self.S = AffineTransformation('S', self.n) # private key
    self._PS_product = self.__substitute_and_multiply(self.trapdoor._P, self.S.transformation)
    
    if not isinstance(trapdoor, UOV):
      self.T = AffineTransformation('T', self.m) # private key
      self.T_PS_product = self.__substitute(self.T.transformation, self._PS_product) # public key
    else:
      self.T = self.create_identitiy_matrix(self.m) # private key
      self.T_PS_product = self.__substitute(self.T, self._PS_product) # public key
        
    if HUMAN_PRINT:
      print('Affine transformation S')
      pprint(self.S.transformation)
      print('Affine transformation T')
      if hasattr(self.T, 'transformation'):
        pprint(self.T.transformation)
      else:
        pprint(self.T)
      print('==============================')
      print('_P o S')
      pprint(self._PS_product)
      print('T o _P o S')
      pprint(self.T_PS_product)
    
  def __substitute_and_multiply(self, trapdoor, transformation_s):
    """
    Args:
      trapdoor (dictionary of sets): 
      transformation_s (2d int array): representing Affine transformation S
    """
    self.logger.debug('Enter')
    computed = {}
    result = {}
    
    for key in trapdoor:
      self.logger.debug('key: %s: ' % key)
      
      for variable in trapdoor[key]:
        self.logger.debug('variable: %s' % variable)

        if MQ.OPERATOR_MUL in variable: # if contain * we must multiply them
          if variable in computed:
            self.logger.debug("variable in computed=%s" % computed[variable])
            for var in computed[variable]:
              if key in result:
                result[key] ^= set([var])
              else:
                result[key] = set([var])
            #self.insert_value_dictionary(result, key, computed[variable], False)
            self.logger.debug("variable in result[key]=%s" % result[key])
          else:
            var = variable.split(MQ.OPERATOR_MUL)

            eq1 = transformation_s[int(var[0][1:]) - 1]
            eq2 = transformation_s[int(var[1][1:]) - 1]
            #self.logger.info('eq1=%s' % eq1)
            #self.logger.info('eq2=%s' % eq2)
            for eq1_var in eq1:
              for eq2_var in eq2:
                if eq1_var == '1':
                  if eq2_var == '1':
                    #self.insert_value_dictionary(result, key, '1', True)
                    #self.insert_value_dictionary(computed, variable, '1', True)
                    if variable in computed:
                      computed[variable] ^= set(['1'])
                    else:
                      computed[variable] = set(['1'])
                  else:
                    #self.insert_value_dictionary(result, key, eq2_var, True)
                    #self.insert_value_dictionary(computed, variable, eq2_var, True)
                    if variable in computed:
                      computed[variable] ^= set([eq2_var])
                    else:
                      computed[variable] = set([eq2_var])
                    
                elif eq2_var == '1':
                  #self.insert_value_dictionary(result, key, eq1_var, True)
                  #self.insert_value_dictionary(computed, variable, eq1_var, True)
                  if variable in computed:
                    computed[variable] ^= set([eq1_var])
                  else:
                    computed[variable] = set([eq1_var])
                else:
                  #self.insert_value_ordered(result, key, eq1_var, eq2_var, True)
                  #self.insert_value_ordered(computed, variable, eq1_var, eq2_var, True)
                  if eq1_var == eq2_var:
                    if variable in computed:
                      computed[variable] ^= set([eq1_var])
                    else:
                      computed[variable] = set([eq1_var])
                  elif eq1_var < eq2_var:
                    if variable in computed:
                      computed[variable] ^= set([eq1_var + MQ.OPERATOR_MUL + eq2_var])
                    else:
                      computed[variable] = set([eq1_var + MQ.OPERATOR_MUL + eq2_var])
                  else:
                    if variable in computed:
                      computed[variable] ^= set([eq2_var + MQ.OPERATOR_MUL + eq1_var])
                    else:
                      computed[variable] = set([eq2_var + MQ.OPERATOR_MUL + eq1_var])
                    
            self.logger.debug("now computed=%s", computed[variable])
            for var in computed[variable]:
              if key in result:
                result[key] ^= set([var])
              else:
                result[key] = set([var])
            #self.insert_value_dictionary(result, key, computed[variable], False)
            self.logger.debug("now result=%s", result[key])
        
        elif variable == '1':
          #self.insert_value_dictionary(result, key, '1', True)
          if key in result:
            result[key] ^= set(['1'])
          else:
            result[key] = set(['1'])
        
        else:
          for transformation_variable in transformation_s[int(variable[1:]) - 1]:
            self.logger.debug('transformation_variable %s' % transformation_variable)
            #self.insert_value_dictionary(result, key, transformation_variable, True)
            if key in result:
              result[key] ^= set([transformation_variable])
            else:
              result[key] = set([transformation_variable])
    
    self.logger.info('_P o S=%s' % result)
    return result
  
  def __substitute(self, transformation_t, _PS):
    """
    Args:
      transformation_t (2d int array): representing Affine transformation T
      _PS (dictionary of sets): 
    """
    self.logger.debug('Enter')
    result = {}
    
    index = 1
    for row in transformation_t:
      self.logger.debug('Equation %s' % row)
      key = MQ.VARIABLE_Y + str(index)
      
      for variable in row:
        self.logger.debug('Variable %s' % variable)
        # if processed variable is y_x not 1
        if MQ.VARIABLE_Y in variable[0]:
          if variable not in _PS:
            continue
          
          for value in _PS[variable]:
            self.logger.debug("%s, %s" % (key, value))
            if key in result:
              result[key] ^= set([value])
            else:
              result[key] = set([value])
          #self.insert_value_dictionary(result, key, _PS[variable], False)
        else:
          if key in result:
            result[key] ^= set(['1'])
          else:
            result[key] = set(['1'])
          #self.insert_value_dictionary(result, key, '1', True)
          
      index += 1
    self.logger.info('T o _P o S=%s' % result)
    return result
  
  def create_identitiy_matrix(self, degree):
    """
    Unbalanced Oil and Vinegar schemes (UOV) omit the affine transformation T
    but only use S. To fit in our framework, we set it to be the identity 
    transformation.
    This method creates identity matrix of degree that has been passed as 
    argument into this method
    """
    self.logger.info('Creating identity matrix of degree=%s' % degree)
    return [[MQ.VARIABLE_Y + str(row + 1)] for row in range(degree)]
  
  def insert_value_list(self, array, value1, value2):
    """
    Appends product of values to list arranged according to index
    """
    self.logger.debug('Enter')
    
    if value1 < value2:
      array.append(value1 + MQ.OPERATOR_MUL + value2)
    else:
      array.append(value2 + MQ.OPERATOR_MUL + value1)
  
  def insert_value_dictionary(self, dictionary, key, value, as_set):
    # TODO pass value as copy, check correctness of this method
    self.logger.debug('Enter')
    self.logger.debug('Inserting at key = %s, value = %s' % (key, value))
    self.logger.debug('Dictionary before inserting\n%s' % dictionary)
    
    if key in dictionary:
      if as_set:
        dictionary[key] ^= set([value]) # new set with elements in either s or t but not both
      else:
        dictionary[key] ^= value # new set with elements in either s or t but not both
    else:
      if as_set:
        dictionary[key] = set([value]) # new set with elements from both s and t
      else:
        dictionary[key] = value # new set with elements from both s and t
    
    self.logger.debug('Dictionary after inserting\n%s' % dictionary)
  
  def insert_value_ordered(self, dictionary, key, value1, value2, as_set):
    self.logger.debug('Enter')
    
    if value1 == value2:
      self.insert_value_dictionary(dictionary, key, value1, as_set)
    elif value1 < value2:
      self.insert_value_dictionary(dictionary, key, value1 + MQ.OPERATOR_MUL + value2, as_set)
    else:
      self.insert_value_dictionary(dictionary, key, value2 + MQ.OPERATOR_MUL +  value1, as_set)



# MQ trapdoors
class UOV(MQ):
  """
  Unbalanced oil and vinegar
  
  Args:
    oil_count (int): positive number
    {
      if zero: count of vinegar variables will be twice or more than oil variables
        other: count of vinegar variables will equals to (count of variables in cryptosystem(n)) - (oil_count)
    }
  
  Raise:
    ValueError
    
  Return:
    _P (dictionary): private key
  """
  def __init__(self, oil_count=0):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of UOV')
    self.oil_count = oil_count
    self.oil = []
    self.vinegar = []
    self._P = {}
    if oil_count < 0:
      raise ValueError('Count of oil variables must be > 0')
  
  def create_trapdoor(self, mq):
    self.logger.info('Creating trapdoor for UOV')
    self.mq = mq
    # create base list of variables that may occure in result
    variables = [MQ.VARIABLE_X + str(i) for i in range(1, mq.n + 1)]
    shuffle(variables)
    
    oil_count = self.oil_count
    # if user doesn't specify count of oil variables
    if not oil_count:
      if mq.n > 2:
        # ensures that count of vinegar variables will be twice as many as count of oil variables
        oil_count     = mq.n / 3
        vinegar_count = mq.n - oil_count

        self.oil     = variables[0:oil_count]
        self.vinegar = variables[oil_count:]
      else:
        # n = 2, n < 2 is treated in MQ class
        oil_count    = vinegar_count = 1
        self.oil     = [variables[0]]
        self.vinegar = [variables[1]]
    else:
      vinegar_count = mq.n - oil_count
      if vinegar_count < 1:
        raise ValueError('Count of vinegar variables is < 1, check setting of params: mq.n, uov.oil_count')
      
      if (vinegar_count / 2) < oil_count:
        if vinegar_count < oil_count:
          self.logger.warning('Scheme is not secure: count of vinegar variables is < count of oil variables')
        else:
          self.logger.warning('Scheme may not be secure: count of vinegar variables is not as 2 * count of oil variables')
      
      self.oil = variables[0:oil_count]
      self.vinegar = variables[oil_count:]
    
    self.logger.info('Oil variables %s' % self.oil)
    self.logger.info('Vinegar variables %s' % self.vinegar)
    
    self.oil_count = oil_count
    self.vinegar_count = vinegar_count
    
    # create product of variables(vinegar*vinegar, vinegar*oil) that may occure in equation
    for i in range(vinegar_count): # loop through all vinegar variables
      for j in range(i + 1, vinegar_count):
        # insert product of vinegar variables arranged according to index
        self.insert_value_list(variables, self.vinegar[i], self.vinegar[j])
      
      for j in range(oil_count): # loop through all oil variables
        # insert product of vinegar and oil variables arranged according to index
        self.insert_value_list(variables, self.vinegar[i], self.oil[j])
    
    variables.append('1')
    
    self.logger.debug('Product of variables %s' % variables)
    
    c_min = oil_count
    c_max = oil_count * 2
    lottery = [i for i in range(len(variables))]
    i = 1
    while i < (mq.m + 1): # for each equation
      # SECURITY it depends on shuffle and randint how randomized will be the system
      # shuffle values
      shuffle(lottery)
      # random count of variables for equation
      count = randint(c_min, c_max)
      # ensuring that equation contain nonlinear variable
      nonlinear = False
      
      key = MQ.VARIABLE_Y + str(i)
      # insert selected count of variables into equation
      for j in range(count):
        self.insert_value_dictionary(self._P, key, variables[lottery[j]], True)
        
        # if condition added because of saving string comparasion cost
        if not nonlinear:
          if MQ.OPERATOR_MUL in variables[lottery[j]]:
            nonlinear = True
      
      if nonlinear:
        i += 1
      else:
        self._P[key] = set()
    
    self.logger.info('_P=%s' % self._P)
    if HUMAN_PRINT:
      self.human_print()
    
    del variables
    del lottery
    
    return self._P

  def human_print(self):
    print self.__class__.__name__
    print 'Počet premenných =', self.mq.n
    print 'Počet rovníc =', self.mq.m
    print 'Octové premenné:',
    for variable in self.vinegar:
      print variable + ',',
    print('')

    print 'Olejové premenné:',
    for variable in self.oil:
      print variable + ',',
    print('\n----------------\n_P=')

    pprint(self._P)



class STS(MQ):
  """
  Class for Stepwise Triangular Systems.
  
  Args:
    layers_count (int): pocet vrstiev | total count of layers
    variables_in_layer (list of int's): pocet premennych v danej vrstve | count of variables in each layer
    equations_in_layer (list of int's): pocet rovnic v danej vrstve | count of equations in each layer
    
    Example: n = 8, m = 8
    2 layers, [4, 4] variables, [4, 4] equation
    2 layers, [2, 6] variables, [4, 4] equation
    
    4 layers, [2, 2, 2, 2] variables, [2, 4, 6, 8] equation
    4 layers, [1, 2, 2, 3] variables, [1, 2, 2, 3] equation
  
  Return:
    _P (dictionary): private key
  """
  
  def __init__(self, layers_count, variables_in_layer, equations_in_layer):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of STS')
    self.layers_count = layers_count
    self.variables_in_layer = variables_in_layer
    self.equations_in_layer = equations_in_layer
    self._P = {}
    
    if layers_count < 1:
      raise ValueError('Count of layers must be greater than 0')
    
    for (variable, equation) in zip(variables_in_layer, equations_in_layer):
      if variable < 1:
        raise ValueError('Count of variables in layer must be greater than 0')
      if equation < 1:
        raise ValueError('Count of equations in layer must be greater than 0')    
  
  def create_trapdoor(self, mq):
    self.logger.info('Creating trapdoor for STS\nlayers=%d, variables=%s, equations=%s', self.layers_count, self.variables_in_layer, self.equations_in_layer)
    self.mq = mq
    self.check_params()
    
    product = self.create_product(mq.n) # x1, x2, x1*x2, x3, x1*x3, x2*x3, x4, ..., xn
    self.logger.debug('Product of variables=\n%s' % (product))
    
    triangle = [0]
    for i in range(1, mq.n + 1):
      triangle.append(triangle[i - 1] + i)
    self.logger.debug('triangle=\n%s' % (triangle))
    
    equation_index = 0
    variables_count = 0
    for layer in range(self.layers_count):
      variables_new_from = variables_count
      variables_count += self.variables_in_layer[layer]
      variables_new_to = variables_count
      self.logger.debug("from=%d, to=%d" % (variables_new_from, variables_new_to))
      
      for equation in range(self.equations_in_layer[layer]):
        equation_index += 1
        
        new_values = set(
          sample(
            product[triangle[variables_new_from]:triangle[variables_new_to]],
            randint(1, triangle[variables_new_to] - triangle[variables_new_from])
          )
        )         
        self.logger.debug('new_values=%s' % new_values)
        
        # ensuring that equation contain nonlinear variable
        nonlinear = False
        for value in new_values:
          if MQ.OPERATOR_MUL in value:
            nonlinear = True
            break
        
        if not nonlinear:
          new_values |= set([product[triangle[variables_new_to] - 1]])
          self.logger.debug('Adding %s to new_values=%s' % (product[triangle[variables_new_to] - 1], new_values))
        
        if variables_new_from:
          old_values = set(
            sample(
              product[:triangle[variables_new_from]],
              randint(1, triangle[variables_new_from])
            )
          )
          self.logger.debug('old_values=%s' % (old_values))
          new_values |= old_values
        
        self._P[MQ.VARIABLE_Y + str(equation_index)] = new_values
    
    self.logger.info('_P=%s' % (self._P))
    if HUMAN_PRINT:
      self.human_print()
    
    del product
    del triangle
    
    return self._P
  
  def check_params(self):
    """
    The method checks whether the specified parameters are correct
    """
    if self.layers_count > self.mq.m:
      raise ValueError('Count of layers(%d) is more than count of equation(%d)' % (self.layers_count, self.mq.m))
    
    if sum(self.variables_in_layer) != self.mq.n:
      raise ValueError('Sum of variables in layers is not equal to count of variables' % ())
    
    if sum(self.equations_in_layer) != self.mq.m:
      raise ValueError('Sum of equations in layers is not equal to count of equations' % ())

  def create_product(self, n):
    """
    Return product of x variables as list: 
    x1, x2, x1*x2, x3, x1*x3, x2*x3, x4, ..., xn
    """
    self.logger.debug('Enter')
    
    product = [MQ.VARIABLE_X + '1']
    
    for i in range(2, n + 1):
      variable = MQ.VARIABLE_X + str(i)
      product.append(variable)
      
      for j in range(1, i):
        product.append(MQ.VARIABLE_X + str(j) + MQ.OPERATOR_MUL + variable)
    
    return product
  
  def human_print(self):
    print self.__class__.__name__
    print('Počet premenných=%d' % (self.mq.n))
    print('Počet rovníc=%d' % (self.mq.m))
    print('Počet vrstiev=%d' % (self.layers_count))
    print('----------------\n_P=')
    pprint(self._P)



class PolynomialBasedTrapdoor(MQ):
  last_n = 0
  equation = 0
  polyonomial = 0
  #ip = IrreduciblePolynomials(MQ.VARIABLE_X)
  
  def create_irreducible_polynomial(self, variable, n):
    """
    http://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_gf2x.html#sage.rings.polynomial.polynomial_gf2x.GF2X_BuildIrred_list
    Return the list of coefficients of the lexicographically smallest 
    irreducible polynomial of degree n over the Gladis field of 2 elements.
    
    Args:
      n(int): positive number greather than 1
    """
    self.logger.debug('Enter')
    #return GF(2)[variable].irreducible_element(n, algorithm="first_lexicographic")
    PBT = PolynomialBasedTrapdoor
    
    if PBT.last_n == n: # rely on that n is positive number greater than 1
      return PBT.polyonomial
    else:
      PBT.last_n = n
      #PBT.polyonomial = GF(2)[variable].irreducible_element(n, algorithm="first_lexicographic")
      PBT.polyonomial = GF(2)[variable](GF2X_BuildIrred_list(n))
      return PBT.polyonomial
  
  def create_random_irreducible_polynomial(self, variable, n):
    """    
    http://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_gf2x.html#sage.rings.polynomial.polynomial_gf2x.GF2X_BuildRandomIrred_list
    Return the list of coefficients of an irreducible polynomial of degree n 
    of minimal weight over the Gladis field of 2 elements.
    
    Args:
      n(int): positive number greather than 1
    """
    self.logger.debug('Enter')
    #return GF(2)[variable].irreducible_element(n, algorithm="random")
    return GF(2)[variable](GF2X_BuildRandomIrred_list(n))
    #TODO try
    #BuildSparseIrred_GF2X()
  
  def create_equation(self, n):
    """
    Return equation in form x_1*Alpha^0 + x_2*Alpha^1 + ... + x_n*Alpha^(n-1),
    transformed into dictionary where keys are Alphas as strings 
    (MQ.VARIABLE_LAMBDA + MQ.OPERATOR_POWER + exponent) i.e. L^2
    
    Args:
      n(int): positive number greather than 1
    """
    self.logger.debug('Enter')
    PBT = PolynomialBasedTrapdoor
    
    if PBT.last_n == n:
      return PBT.equation
    else:
      PBT.last_n = n
      PBT.equation = {} # or just add (n - PBT.last_n) variables if n > PBT.last_n
      for exponent in range(n):
        PBT.equation[MQ.LAMBDA_RAISED_TO + str(exponent)] = set([MQ.VARIABLE_X + str(exponent + 1)])
      return PBT.equation
  
  def compute_remainder(self, irreducible_polynomial, key, all_remainders):
    """
    Return dictionary with remainders after raising irreducible polynomial 
    over its size
    
    Args:
      irreducible_polynobmial(sage.rings.polynomial.polynomial_gf2x.Polynomial_GF2X): polynomial that is used in trapdoor
      key(string): string that will be used as keys for the result dictionary
    """
    self.logger.debug('Enter')
    
    R = PolynomialRing(GF(2), key)
    S = R.quotient(irreducible_polynomial, key)
    a = S.gen() # generator of this quotient ring
    
    key_raised_to = key + MQ.OPERATOR_POWER
    
    remainder = {key_raised_to + '0': a ** 0}
    count = 0
    if all_remainders:
      count = (2 ** irreducible_polynomial.degree()) - 1
    else:
      count = ((irreducible_polynomial.degree() - 1) * 2) + 1
    
    for exponent in range(1, count):
      remainder[key_raised_to + str(exponent)] = remainder[key_raised_to + str(exponent - 1)] * a
    
    return remainder
  
  def square_polynomial(self, polynomial, times, remainders):
    """
    Raises the polynomial with exponent 2 n-times; polynomial^2^times
    calculated using the Frobenius automorphismus
    
    polynomial(dictionary of sets containing strings)
    """
    self.logger.debug('Enter')
    
    # create copy of dictionary, as we don't want to change it
    pol_old = {}
    for key in polynomial:
      for value in polynomial[key]:
        pol_old[key] = set([value])
    
    # square polynomial n-times
    for counter in range(times):
      self.logger.debug('raising %d times' % (counter + 1))
      pol_new = {}
    
      for pol_old_key in pol_old:
        exponent = int(pol_old_key[2:]) * 2
        self.logger.debug('from pol_old_key=%s -> to exponent=%d' % (pol_old_key, exponent))
        
        if exponent < self.mq.n:
          self.logger.debug('1 pol_old=%s' % (pol_old))
          
          for pol_old_value in pol_old[pol_old_key]:
            insert_key = MQ.LAMBDA_RAISED_TO + str(exponent)
            if insert_key in pol_new:
              pol_new[insert_key] ^= set([pol_old_value])
            else:
              pol_new[insert_key]  = set([pol_old_value])
          
          self.logger.debug('1 pol_new=%s' % (pol_new))
        else:
          remainder_keys = str(remainders[MQ.LAMBDA_RAISED_TO + str(exponent)]).split(MQ.VARIABLE_SEPARATOR)
          self.logger.debug('2 remainder_keys=%s, %s' % (remainder_keys, pol_old[pol_old_key]))
          
          for remainder_key in remainder_keys:
            if len(remainder_key) < 3:
              remainder_key = self.edit_key(remainder_key)
              
            for pol_old_value in pol_old[pol_old_key]:
              if remainder_key in pol_new:
                pol_new[remainder_key] ^= set([pol_old_value])
              else:
                pol_new[remainder_key] = set([pol_old_value])
          
          self.logger.debug('2 pol_new=%s' % (pol_new))
        
      for pol_new_key in pol_new:
        #for pol_new_value in pol_new[pol_new_key]:
        pol_old[pol_new_key] = pol_new[pol_new_key]
      self.logger.debug('====================================================')
    
    return pol_old
  
  def multiply_polynomials(self, left_side, right_side, remainders):
    """
    Method multiplies two polynomials
    """
    self.logger.debug('Enter')
    
    result = {}
    
    for left_key in left_side:
      left_key_exponent = int(left_key[2:])
      
      for left_value in left_side[left_key]:
        self.logger.debug('Left key and value %s %s', left_key, left_value)
        
        for right_key in right_side:
          right_key_exponent = int(right_key[2:])
          
          for right_value in right_side[right_key]:
            self.logger.debug('Right key and value %s, %s', right_key, right_value)
            exponent_sum = left_key_exponent + right_key_exponent
            key = MQ.LAMBDA_RAISED_TO + str(exponent_sum)
            
            if exponent_sum < self.mq.n:
              self.insert_value_ordered(result, key, left_value, right_value, True)
            else:
              ired_keys = str(remainders[key]).split(MQ.VARIABLE_SEPARATOR)
              
              for ired_key in ired_keys:
                if len(ired_key) < 3:
                  ired_key = self.edit_key(ired_key)
                
                self.insert_value_ordered(result, ired_key, left_value, right_value, True)
              
          self.logger.debug('\n-------------')
      self.logger.debug('\n--------------------------')
    return result
  
  def edit_key(self, key):
    self.logger.debug('Enter')
    
    # fix as sagemath return L^0 as 1 and L^1 as L
    if key == '1':
      return MQ.VARIABLE_LAMBDA + '^0'
    elif MQ.VARIABLE_LAMBDA in key:
      return MQ.VARIABLE_LAMBDA + '^1'
    else:
      raise ValueError('Key \'%s\' not found ', key)



class MIA(PolynomialBasedTrapdoor):
  """
  Matsumoto-Imai
  use n that is not divisible by 2^n: 2, 4, 8, 16, 32, 64, ...
  http://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_gf2x.html
  
  1. vygenerovat lambdu ak je to mozne -> GCD(2^n - 1, 2^L + 1) == 1
  2. vygenerovat ireducibilny polynom stupna n
  3. zistit zvysky po deleni pre zvoleny ireducibilny polynom ->
      napr pre x3 + x + 1 = x1->x1, x2->x2, x3->x + 1, x4->x^2 + x, ...
  4. vygenerovat vyraz v tvare x1 + x2*L^1 + x3*L^2 + ... x_n*L^n-1
  5. umocnit vygenerovany vyraz na (2^L + 1)
  5a. za lambdy stupna vacsieho ako n dosadit zvysky po deleni
  5b. roznasobit zatvorky
  6. vyjmut premenne pre dane lambdy
  """
  
  def __init__(self):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of MIA')
    self._P = {}
    
  def create_trapdoor(self, mq):
    self.logger.info('Creating trapdoor for MIA')
    self.mq = mq
    self._lambda = self.compute_lambda()
    #mq.irred_polynomial = self.create_irreducible_polynomial(MQ.VARIABLE_X, mq.n)
    mq.irred_polynomial = self.create_random_irreducible_polynomial(MQ.VARIABLE_X, mq.n)
    self.irred_polynomial_rem = self.compute_remainder(mq.irred_polynomial, MQ.VARIABLE_LAMBDA, False)
    base_polynomial = self.create_equation(mq.n)
    
    self.logger.info('_lambda=%d, irred_polynomial=%s' % (self._lambda, mq.irred_polynomial))
    self.logger.debug('irred_polynomial_rem=%s' % (self.irred_polynomial_rem))
    # the equation is P'(X) = X ^ ((2^lambda) + 1) we break this into two parts
    
    # first part: left_side = X ^ (2^lambda), will be squared
    left_side = self.square_polynomial(base_polynomial, self._lambda, self.irred_polynomial_rem)
    self.logger.debug('For lambda=%s computed left side\n%s' % (self._lambda, left_side))
    self.logger.debug('Multipling left side with right side\n%s' % base_polynomial)
    
    # second part: P'(x) = left_side * X^1 will be multiplied
    self._P = self.multiply_polynomials(left_side, base_polynomial, self.irred_polynomial_rem)
    
    # just renaming keys from L^x to yx
    result = {}
    for key in self._P:
      result[MQ.VARIABLE_Y + key[2:]] = self._P[key]
    
    self._P = result
    self.logger.info('_P=%s' % self._P)
    if HUMAN_PRINT:
      self.human_print(base_polynomial)
    
    return self._P
  
  def compute_lambda(self, first_lambda=False):
    """
    Computes number L, which fulfills the condition 
    GCD((2^n)-1, (2^L)+1) == 1, if this number is not found until the condition 
    (2^n)-1 > (2^L)+1 is fulfilled, where n is degree of polynomial then is
    raised error
    
    if lamb == mq.n then square_polynomial return the same base_polynomial
    Args:
      first_lambda(boolean): 
      {
        true: then returns the first lambda that fulfills the condition
        false: then returns random lambda from all which have fulfilled the condition
      }
    
    Raise:
      ValueError if any lambda was found
    """
    self.logger.debug("Enter")
    result = []
    
    lamb   = 1
    first  = (2 ** self.mq.n) - 1
    second = (2 ** lamb) + 1
    
    while (first > second) and (lamb < self.mq.n):
      if gcd(first, second) == 1:
        if first_lambda:
          return lamb
        
        result.append(lamb)
      
      lamb  += 1
      second = (2 ** lamb) + 1
    
    if not result:
      raise ValueError('Lambda not found for n=%s' % (self.mq.n))
    else:
      self.logger.debug('result = %s' % (result))
      return choice(result)
  
  def human_print(self, base_polynomial):
    print self.__class__.__name__
    
    for key in base_polynomial:
      for value in base_polynomial[key]:
        print str(value) + ' * +',
    print('')
    
    for key in self._P:
      print key + ' =',
      for values in self._P[key]:
        print values + ' +',
      print('')



class HFE(PolynomialBasedTrapdoor):
  """
  Hidden Field Equations
  
  Args:
    degree(int): degree of the created HFE equation if not provided random value
      form range <n, n + 2> will be picked
  
  Return:
    _P(dictionary): created equations that presents private key
  """
  
  def __init__(self, degree=0):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of HFE')
    self._P = {}
    self.degree = degree
  
  def create_trapdoor(self, mq):
    self.logger.info('Creating trapdoor for HFE')
    self.mq = mq
    #mq.irred_polynomial = self.create_irreducible_polynomial(MQ.VARIABLE_X, mq.n)
    mq.irred_polynomial = self.create_random_irreducible_polynomial(MQ.VARIABLE_X, mq.n)
    self.irred_polynomial_rem = self.compute_remainder(mq.irred_polynomial, MQ.VARIABLE_LAMBDA, False)
    base_polynomial = self.create_equation(mq.n)
    
    if not self.degree:
      #count = (2 ** self.mq.n) - 1 # modulo
      #d_range = range(self.mq.n, (self.mq.n * count) + 1) # pick d that should be small ?!
      self.degree = randint(mq.n, mq.n + 2) # pick random value from range
    elif self.degree < 2:
      raise ValueError('Cannot create HFE equation due degree=%d' % (self.degree))
    
    self.logger.debug('Ireducible polynomial=%s, polynomial degree d=%s' % (mq.irred_polynomial, self.degree))
    
    HFE = self.create_hfe_polynomial(self.degree, self.irred_polynomial_rem)
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
    if HUMAN_PRINT:
      self.human_print()
    
    return self._P
    
  def create_hfe_polynomial(self, degree, remainders):
    self.logger.debug('Enter')
    # Let's create polynomial in HFE form
    C = {}
    B = {}
    A = {}
    
    max_index = len(remainders)
    #c_rem = [str(i) for i in range(self.mq.n + 1)]
    c_rem = [str(i) for i in range(max_index)]
    shuffle(c_rem)
    c_index = 0
    
    #b_rem = [str(i) for i in range(self.mq.n + 1)]
    b_rem = list(c_rem)
    shuffle(b_rem)
    b_index = 0
    
    self.logger.debug('\nc_rem=%s\nb_rem=%s' % (c_rem, b_rem))
    self.logger.debug('degree=%d, len(remainders)=%d,\nremainders=%s' % (degree, len(remainders), remainders))
    
    i = 0
    j = 0
    while True:
      power_i = 2 ** i
      
      if power_i > degree:
        break
      
      while True:
        power_sum = power_i + (2 ** j) # + power_j
        
        if power_sum <= degree:
          self.logger.debug('C: i=%d, j=%d,  2^i + 2^j=%d' % (i, j, power_sum))
          c_key = MQ.LAMBDA_RAISED_TO + c_rem[c_index]
          key = MQ.X_RAISED_TO + str(power_sum)
          
          if key in C:
            C[key] ^= set([remainders[c_key]])
          else:
            C[key]  = set([remainders[c_key]])
          
          c_index += 1
          if c_index == max_index:
            c_index = 0
            # to do not take the same items in next iteration
            shuffle(c_rem)
            self.logger.debug('c_rem=%s' % (c_rem))
            
          j += 1
        else:
          j = 0
          break
      
      self.logger.debug('B: i=%d, 2^i=%d' % (i, power_i))
      b_key = MQ.LAMBDA_RAISED_TO + b_rem[b_index]
      B[MQ.X_RAISED_TO + str(power_i)] = set([remainders[b_key]])
      
      b_index += 1
      if b_index == max_index:
         b_index = 0
         # to do not take the same items in next iteration
         shuffle(b_rem)
         self.logger.debug('b_rem=%s' % (b_rem))
      
      i += 1
    
    a_key = choice(list(remainders.keys())) # random.choice() from keys in dictonary
    A[MQ.X_RAISED_TO + '0'] = set([remainders[a_key]])
    #--------------------------------------------------------------------------#
    self.logger.debug('C=%s' % (C))
    self.logger.debug('B=%s' % (B))
    self.logger.debug('A=%s' % (A))
    HFE = C
    
    for key in B: # copy dict B to dict HFE
      if key in HFE:
        HFE[key] ^= B[key]
      else:
        HFE[key] = B[key]

    HFE.update(A) # copy dict A to dict HFE
    self.logger.debug('HFE=%s' % (HFE))
    
    for key, values in HFE.items():
      # remove X's with empty values
      if not values:
        del HFE[key]
      # remove same remainders
      else:
        self.logger.debug('key=%s' % (key))
        summary = 0
        for value in values:
          summary += value
          self.logger.debug('%s' % (values))
        self.logger.debug('summary=%s' % (summary))
        HFE[key] = set([summary])
    # equation in HFE form
    return HFE
  
  def human_print(self):
    print self.__class__.__name__
    
    for equation in self._P:
      print equation + ' =',
      for variable in self._P[equation]:
        print variable + ' +',
      print('')



class AffineTransformation(object):
  """
  Create matrix of dimension n * n over finite field with 2 elements: 0 and 1, and vector n-bits long
  http://doc.sagemath.org/html/en/reference/groups/sage/groups/affine_gps/affine_group.html
  
  Args:
    transf_type(string): either 'S' or 'T'
    degree(int): positive number greater than two
  """
  def __init__(self, transf_type, degree):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of AffineTransformation of degree=%s' % degree)
    
    if degree < 2:
      raise ValueError('Dimension have to be equals or greater than 2')
    if not (transf_type == 'S' or transf_type == 'T'):
      raise ValueError('Transformation type should be either S or T')
    
    self.transf_type = transf_type
    self.group = AffineGroup(degree, GF(2))
    self.element = self.group.random_element()
    self.matrix = self.element.A()
    self.vector = self.element.b()
    self.logger.debug('created matrix=%s' % self.matrix)
    self.logger.debug('created vector=%s' % self.vector)
    self.transformation = self.compute_transformation(transf_type, degree)
    # inverzna transformacia ~self.matrix alebo self.matrix.inverse()
    
  def compute_transformation(self, transf_type, degree):
    self.logger.debug('Enter')
    
    transformation = [[] for row in range(degree)] # self.group.degree()
    variable = MQ.VARIABLE_X if 'S' in transf_type else MQ.VARIABLE_Y
    
    for row in range(degree):
      for column in range(degree):
        if self.matrix[row][column] == 1:
          transformation[row].append(variable + str(column + 1))
      
      if self.vector[row] == 1:
        transformation[row].append('1')
    
    self.logger.info('Transformation %s=%s' % (transf_type, transformation))
    return transformation



class MQChallenge(object):
  """
  MQ challenge system https://www.mqchallenge.org/
  
   Args:
    mq (MQ):
  """
  PATH = 'Toy/'
  FILENAME = 'toytoy'
  
  def __init__(self, mq):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.info('Creating instance of MQChallenge')
    self.mq = mq
    #self.triangle = [((i * (i + 1)) / 2) for i in range(n + 2)]
    self.triangle = [0]
    # we need just + 1 but + 2 is for saving computation the matrix column size in method convert()
    for i in range(1, mq.n + 2):
      self.triangle.append(self.triangle[i - 1] + i)
    
    self.convert()
  
  class SystemType(object):
    """
    Coefficient field F in MQ system
    """
    # Type I-III: Encryption,	m=2n
    # Type IV-VI: Signature,	n≈1.5m
    TYPE_I   = TYPE_IV = '2'
    TYPE_II  = TYPE_V  = '2**8'
    TYPE_III = TYPE_VI = '31'
  
  class SeedType(object):
    """
    seed used to generate the MQ system
    """
    _0, _1, _2, _3, _4 = range(5)
  
  class OrderType(object):
    """
    monomials representation in MQ system more on http://www.math.uiuc.edu/Macaulay2/doc/Macaulay2-1.9/share/doc/Macaulay2/Macaulay2Doc/html/_monomial_sporderings.html
    """
    LEX = 'lexicographical monomial order'
    GREVLEX = 'graded reverse lex order'
    
  def convert(self, system_type=SystemType.TYPE_I, seed_type=SeedType._0, order_type=OrderType.GREVLEX):
    self.logger.info('Converting public key to MQ Challenge format')
    self.system_type = system_type
    self.seed_type = seed_type
    self.order_type = order_type
    self.polynomial_matrix = [[0 for column in range(self.triangle[-1])] for row in range(self.mq.m)]
    
    public_key = self.mq.T_PS_product
    for key in public_key: # y1, y2, ..., y_m
      key_index = int(key[1:]) - 1 # indexing from zero
      
      for item in public_key[key]: # equation for key
        if order_type == self.OrderType.GREVLEX:
          if MQ.OPERATOR_MUL in item:
            # quadratic term:
            (first, second) = item.split(MQ.OPERATOR_MUL)
            self.polynomial_matrix[key_index][self.triangle[int(second[1:]) - 1] + (int(first[1:]) - 1)] = 1
          elif MQ.VARIABLE_X in item[0]:
            # linear term:
            self.polynomial_matrix[key_index][self.triangle[-2] + int(item[1:]) - 1] = 1
          else:
            # absolute term: insert at the end
            self.polynomial_matrix[key_index][self.triangle[-1] - 1] = 1
  
  def store(self, filename=""):
    """
    stores generated mq public key in MQ Challenge format
    
    Args:
      filename(string): name of the created file, if not provided then default value will be euqal to MQChallenge.FILENAME
    """
    if filename:
      self.filename = filename
    else:
      self.filename = MQChallenge.FILENAME
    
    self.logger.info('Storing public key into file %s' % self.filename)
    
    if not self.polynomial_matrix:
      self.logger.error('polynomial_matrix is empty')
    else:
      f = open(MQChallenge.PATH + self.filename, 'w')

      if self.system_type == self.SystemType.TYPE_II or self.system_type == self.SystemType.TYPE_V:
        if not self.mq.irred_polynomial:
          raise BaseException('Irreducible polynomial not provided by creating MQChallenge object')
        else:
          f.write('Galois Field : GF(2)[%s] / %s\n' % (MQ.VARIABLE_X, self.mq.irred_polynomial))
      else:
        f.write('Galois Field : GF(%s)\n' % self.system_type)

      f.write('Number of variables (n) : %d\n' % self.mq.n)
      f.write('Number of equations (m) : %d\n' % self.mq.m)
      f.write('Seed : %d\n' % self.seed_type)
      f.write('Order : %s\n\n' % self.order_type)
      f.write('*********************\n')

      for row in range(self.mq.m):
        for column in range(self.triangle[-1]):
          f.write('%d ' % self.polynomial_matrix[row][column])
        f.write(';\n')
      f.close()



class MHRS:
  def __init__(self, mq):
    self.mq = mq
  
  def transform(self):
    pass



class Test:
  """
  performs test on passed trapdoor with function and other arguments
  
  Args:
    trapdoor(list): 1 for not secure UOV,
                    2 for secure UOV,
                    3 for STS,
                    4 for MIA,
                    5 for HFE
    n(list): passed as argument when creating trapdoor
    repeat(list): how many times should the test run for given trapdoor with 
      argument n
    function(list): arguments to function that will evaluate the given trapdoor
    file_name(string): name of the file where will be the result stored
  """
  def __init__(self, trapdoor=[], n=[], repeat=[], function=[], file_name="", comment=""):
    self.logger = logging.getLogger(self.__class__.__name__)
    self.trapdoor = trapdoor
    self.n = n
    self.repeat = repeat
    self.function = function
    self.file_name = file_name
    self.comment = comment
    self.estimate_complexity()
  
  def estimate_complexity(self):
    with open("./tests/test" + datetime.now().strftime('%Y-%m-%d %H:%M:%S') + ".txt", "a", 0) as outfile:
      if self.comment:
        outfile.write("*****************************************************\n")
        outfile.write("trapdoors=%s\nn=%s\nrepeat=%s\n" % (self.trapdoor, self.n, self.repeat))
        outfile.write("%s\n" % self.comment)
        outfile.write("*****************************************************\n")
      
      for trapdoor in self.trapdoor:
        latex_graph = []
        
        for n in self.n:
          stop = False
          average_complexity = 0
          average_time = 0
          
          for test_run in range(self.repeat[0]):
            self.logger.info('test run=%d', test_run)
            time_start = time.time()
            # ---------------------------------------------------------------- #
            # UOV not secure
            if trapdoor == 1:
              mq = MQ(n, n, UOV())
            # UOV secure
            elif trapdoor == 2:
              n_var = (n * 2 + n)
              
              if n_var < 20:
                mq = MQ(n_var, n_var, UOV(n))
              else:
                stop = True
                break
            # STS
            elif trapdoor == 3:
              u = v = n / 2
              l = u + 1

              ones = [1] * v
              if n & 1:
                u += 1
                v += 1
              layer_variables = [u] + ones
              layer_equation  = ones + [v]

              mq = MQ(n, n, STS(l, layer_variables, layer_equation))
            # MIA
            elif trapdoor == 4:
              if n & (n - 1) == 0:
                stop = True
                break
              mq = MQ(n, n, MIA())
            # HFE
            elif trapdoor == 5:
              if n == 2:
                stop = True
                break
              mq = MQ(n, n, HFE())
            # Not implemented
            else:
              raise BaseException('trapdoor not implemented')
            # ---------------------------------------------------------------- #
            time_end = 0
            for function in self.function:
              if callable(function):
                
                if function is mrhs.convert:
                  mc = MQChallenge(mq)
                  result = mrhs.convert(data=mc.polynomial_matrix)
                  average_complexity += result
                  time_end = (time.time() - time_start)
                  if isinstance(mq.trapdoor, UOV) and trapdoor == 2:
                    outfile.write('%s n=%d, m=%d, complexity=%5d, time=%s\n' % (type(mq.trapdoor), n * 2 + n, n, result, time_end))
                  else:
                    outfile.write('%s n=%d, m=%d, complexity=%5d, time=%s\n' % (type(mq.trapdoor), n, n, result, time_end))
                
                elif function is jamrichova.convert:
                  pass
                else:
                  raise BaseException('passed function \'%s\' is not implemented' % (function))
              else:
                raise BaseException('passed argument \'%s\' in function is not function' % (function))
            
            average_time += time_end
          if not stop:
            test_run += 1.0 # due for loop and to divide as double
            ac = average_complexity / test_run
            at = average_time / test_run
            outfile.write('average complexity=%.1f, average time=%.5f\n\n' % (ac, at))
            latex_graph.append([n, ac])
      
        outfile.write('Latex graph data\n')
        for data in latex_graph:
          outfile.write('(%d, %.1f)' % (data[0], data[1]))
        outfile.write('\n\n')
    exit(0)



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

def estimate_complexity():
  with open("./tests/out" + datetime.now().strftime('%Y-%m-%d %H:%M:%S') + ".json", "a", 0) as outfile:
    next_obj = False
    outfile.write("[")
    
    for mq in run_test():
      output = subprocess.check_output(["./run.sh", "Toy/", "-e"])
      subprocess.call(["rm Toy/*.conf Toy/*.mrhs"], shell=True)
      
      line = output.split("\n")
      pos = line[10].find("Expected")
      
      data = OrderedDict([
        ("trapdoor", str(type(mq.trapdoor))),
        ("n", mq.n),
        ("m", mq.m),
        ("MRHS", OrderedDict([
          ("n", int(line[3][18:].rstrip())),
          ("m", int(line[4][18:].rstrip())),
          ("l", int(line[5][18:].rstrip())),
          ("k", int(line[6][18:].rstrip())),
          ("Expected count", int(line[8][18:].rstrip())),
          ("XORs", int(line[10][0:pos - 1].split(" ")[1])),
          ("Expected", line[10][pos + 10:]),
          ("Solutions", int(line[12][11:]))
        ]))
      ])
      
      if next_obj:
        outfile.write(",")
      json.dump(data, outfile, sort_keys=False, indent=4)
      next_obj = True
    outfile.write("]")
    outfile.close()
    exit(0)

def run_test(times=1):
  logger = logging.getLogger('')
  time_average = 0
  
  for test_runs in range(times):
    for trapdoor in range(1, 5):
      n_start = 2
      time_start = time.time()
      ###################
      for n in range(n_start, 21):
        logger.info('Test case for n=%d' % n)
        if trapdoor == 1:
          mq = MQ(n * 2 + n, n, UOV(n))
        elif trapdoor == 2:
          u = v = n / 2
          l = u + 1

          ones = [1] * v
          layer_variables = [u] + ones
          layer_equation  = ones + [v]

          mq = MQ(n, n, STS(l, layer_variables, layer_equation))
        elif trapdoor == 3:
          if n & (n - 1) == 0:
            continue
          mq = MQ(n, n, MIA())
        else:
          mq = MQ(n, n, HFE())

        MQChallenge(mq).store()
        yield mq
        logger.info('=========================================')
      ###################
      time_average += (time.time() - time_start)
    logger.info("Test duration %d[s]" % (time_average / times))

if __name__ == "__main__":
  main()