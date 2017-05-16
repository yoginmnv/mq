#!/usr/lib/sagemath/ sage
# -*- coding: UTF-8 -*-

#http://stackoverflow.com/questions/193161/what-is-the-best-project-structure-for-a-python-application
#https://learnpythonthehardway.org/book/ex46.html
#http://docs.python-guide.org/en/latest/writing/structure/
#https://github.com/kennethreitz/samplemod

from collections import OrderedDict
from datetime import datetime
from pprint import pprint
from random import choice, randint, sample, shuffle
from sage.all import *
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildIrred_list
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildRandomIrred_list
import inspect
import json
import logging
import subprocess
import time
import jamrichova
import zajac

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
    n (int): pocet premennych | count of variables
    m (int): pocet rovnic | count of equations
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
    self.irred_polynomial = None # just for MQChallenge
    if isinstance(trapdoor, MIA) or isinstance(trapdoor, HFE):
      self.m = n
      self.logger.info('Setting m=%d (due %s)' % (self.m, type(trapdoor)))
    
    self.set_trapdoor(trapdoor)
  
  def set_trapdoor(self, trapdoor):
    self.logger.debug('Enter ------------------------------')
    self.trapdoor = trapdoor
    self.trapdoor.create_trapdoor(self) # create private key
    
    if HUMAN_PRINT:
      print('==============================')
    
    self.S = AffineTransformation('S', self.n) # private key
    self._PS_product = self.substitute_and_multiply(self.trapdoor._P, self.S.transformation)
    
    if not isinstance(trapdoor, UOV):
      self.T = AffineTransformation('T', self.m) # private key
      self.T_PS_product = self.substitute(self.T.transformation, self._PS_product) # public key
    else:
      self.T = self.create_identitiy_matrix(self.m) # private key
      self.T_PS_product = self.substitute(self.T, self._PS_product) # public key
        
    if HUMAN_PRINT:
      print('Affine transformation S')
      pprint(self.S.transformation)
      print('Affine transformation T')
      if hasattr(self.T, 'transformation'):
        pprint(self.T.transformation)
      else:
        pprint(self.T)
      print('------------------------------')
      print('_P o S')
      pprint(self._PS_product)
      print('T o _P o S')
      pprint(self.T_PS_product)
    
  def substitute_and_multiply(self, trapdoor, transformation_s):
    """
    Attributes:
      trapdoor (dictionary of sets): 
      transformation_s (2d int array): representing Affine transformation S
    """
    self.logger.debug('Enter ------------------------------')
    result = {}
    
    for key in trapdoor:
      self.logger.debug('key: %s: ' % key)
      
      for variable in trapdoor[key]:
        self.logger.debug('variable: %s' % variable)

        if MQ.OPERATOR_MUL in variable: # if contain * we must multiply them
          var = variable.split(MQ.OPERATOR_MUL)
          
          eq1 = transformation_s[int(var[0][1:]) - 1]
          eq2 = transformation_s[int(var[1][1:]) - 1]
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
          for transformation_variable in transformation_s[int(variable[1:]) - 1]:
            self.logger.debug('transformation_variable %s' % transformation_variable)
            self.insert_value_dictionary(result, key, transformation_variable, True)
    
    self.logger.info('_P o S=%s' % result)
    return result
  
  def substitute(self, transformation_t, _PS):
    """
    Attributes:
      transformation_t (2d int array): representing Affine transformation T
      _PS (dictionary of sets): 
    """
    self.logger.debug('Enter ------------------------------')
    result = {}
    
    index = 1
    for row in transformation_t:
      self.logger.debug('Equation %s' % row)
      key = MQ.VARIABLE_Y + str(index)
      
      for variable in row:
        self.logger.debug('Variable %s' % variable)
        if MQ.VARIABLE_Y in variable[0]:
          if variable not in _PS:
            continue
          
          self.insert_value_dictionary(result, key, _PS[variable], False)
        else:
          self.insert_value_dictionary(result, key, '1', True)
      
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
    self.logger.debug('Enter ------------------------------')
    
    if value1 < value2:
      array.append(value1 + MQ.OPERATOR_MUL + value2)
    else:
      array.append(value2 + MQ.OPERATOR_MUL + value1)
  
  def insert_value_dictionary(self, dictionary, key, value, as_set):
    self.logger.debug('Enter ------------------------------')
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
    self.logger.debug('Enter ------------------------------')
    
    if value1 == value2:
      self.insert_value_dictionary(dictionary, key, value1, as_set)
    elif value1 < value2:
      self.insert_value_dictionary(dictionary, key, value1 + MQ.OPERATOR_MUL + value2, as_set)
    else:
      self.insert_value_dictionary(dictionary, key, value2 + MQ.OPERATOR_MUL +  value1, as_set)



class AffineTransformation(object):
  """
  Create matrix of dimension n * n over finite field with 2 elements: 0 and 1, and vector n-bits long
  http://doc.sagemath.org/html/en/reference/groups/sage/groups/affine_gps/affine_group.html
  
  Attributes:
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
    self.logger.debug('Enter ------------------------------')
    
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
  
   Attributes:
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
    
    Attributes:
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



# MQ trapdoors
class UOV(MQ):
  """
  Unbalanced oil and vinegar
  
  Attributes:
    oil_count (int): positive number
    {
      if zero: count of vinegar variables will be twice or more than oil variables
        other: count of vinegar variables will equals to (count of variables in cryptosystem(n)) - (oil_count)
    }
  
  Raise:
    BaseException
    
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
        raise BaseException("Count of vinegar variables is < 1, check setting of params: mq.n, uov.oil_count")
      
      if vinegar_count < oil_count:
        self.logger.warning("Scheme is not secure: count of vinegar variables is < count of oil variables")
      
      if vinegar_count < (oil_count / 2):
        self.logger.warning("Scheme may not be secure: count of vinegar variables is not as 2 * count of oil variables")
      
      self.oil = variables[0:oil_count]
      self.vinegar = variables[oil_count:]
    
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
    
    self.logger.info('Vinegar variables %s' % self.vinegar)
    self.logger.info('Oil variables %s' % self.oil)
    self.logger.info('Product of variables %s' % variables)
    
    c_min = oil_count
    c_max = oil_count * 2
    lottery = [i for i in range(len(variables))]
    i = 1
    while i < (mq.m + 1): # for each equation
      # SECURITY it depends on shuffle and randint how randomized will be the system
      shuffle(lottery) # shuffle values
      count = randint(c_min, c_max) # random count of variables for equation
      nonlinear = False # ensuring that equation contain nonlinear variable
      
      key = MQ.VARIABLE_Y + str(i)
      for j in range(count): # insert selected count of variables into equation
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
    print('')

    print('_P')
    for variable in self._P:
      print variable + ' =',
      plus = None
      for eq in self._P[variable]:
        if plus == None:
          print eq,
        else:
          print '+ ' + eq,
        plus = 0
      print('')

class STS(MQ):
  """
  Class for Stepwise Triangular Systems.
  
  Attributes:
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
  
  def create_trapdoor(self, mq):
    self.logger.info('Creating trapdoor for STS')
    self.mq = mq
    self.check_params()
    
    product = self.create_product(mq.n) # x1, x2, x1*x2, x3, x1*x3, x2*x3, x4, ..., xn
    self.logger.debug('Product of variables=\n%s' % product)
    
    triangle = [0]
    for i in range(1, mq.n + 1):
      triangle.append(triangle[i - 1] + i)
    #del triangle[0]
    self.logger.debug('triangle=\n%s' % triangle)
    
    equation_index = 0
    variables_count = 0
    for layer in range(self.layers_count):
      variables_new_from = variables_count
      variables_count += self.variables_in_layer[layer]
      variables_new_to = variables_count
      self.logger.debug("from=%d, to=%d" %(variables_new_from, variables_new_to))
      
      for equation in range(self.equations_in_layer[layer]):
        equation_index += 1
        
        new_values = set(
          sample(
            product[triangle[variables_new_from]:triangle[variables_new_to]],
            randint(1, triangle[variables_new_to] - triangle[variables_new_from])
          )
        )         
        self.logger.debug('new_values=%s' % new_values)
        
        # check if equation contains quadratic term, if no add one
        linear_system = True
        for value in new_values:
          if MQ.OPERATOR_MUL in value:
            linear_system = False
            break
        
        if linear_system:
          new_values |= set([product[triangle[variables_new_to] - 1]])
          self.logger.debug('Adding %s to new_values=%s' % (product[triangle[variables_new_to] - 1], new_values))
        
        if variables_new_from:
          old_values = set(
            sample(
              product[:triangle[variables_new_from]],
              randint(1, triangle[variables_new_from])
            )
          )
          self.logger.debug('old_values=%s' % old_values)
          new_values |= old_values
        
        self._P[MQ.VARIABLE_Y + str(equation_index)] = set(new_values)
     
    self.logger.info('_P=%s' % self._P)
    if HUMAN_PRINT:
      self.human_print()
    
    del product
    del triangle
    
    return self._P
  
  def human_print(self):
    print self.__class__.__name__
    print 'Počet premenných =', self.mq.n
    print 'Počet rovníc =', self.mq.m
    print 'Počet vrstiev =', self.layers_count
    print '----------------'
    #self.variables_in_layer = variables_in_layer
    #self.equations_in_layer = equations_in_layer
    for variable in self._P:
      print variable + ' =',
      plus = None
      for eq in self._P[variable]:
        if plus == None:
          print eq,
        else:
          print '+ ' + eq,
        plus = 0
      print('')
  
  def check_params(self): 
    """
    The method checks whether the specified parameters are correct
    """
    if self.layers_count > self.mq.m:
      raise ValueError('Count of layers(' + str(self.layers_count) + ') is more than count of equation(' + str(self.mq.m) + ')')
    
    for layer in range(self.layers_count): # for each layer
      if self.variables_in_layer[layer] > self.mq.n: # check if count of variables in actual layer is not higher then n
        raise ValueError('Count of variables in layer ' + str(layer + 1) + ' is more than is possible -> ' + str(self.mq.n))
      
      if self.equations_in_layer[layer] > self.mq.m:  # check if count of equations in actual layer is not higher then m
        raise ValueError('Count of equations in layer ' + str(layer + 1) + ' is more than is possible -> ' + str(self.mq.m))

  def create_product(self, n):
    """
    Return product of x variables as list: 
    x1, x2, x1*x2, x3, x1*x3, x2*x3, x4, ..., xn
    """
    self.logger.debug('Enter ------------------------------')
    
    product = [MQ.VARIABLE_X + '1']
    
    for i in range(2, n + 1):
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
    
    Args:
      irreducible_polynobmial (type sage.rings.polynomial.polynomial_gf2x.Polynomial_GF2X): polynomial that is used in trapdoor
      key (string): string that will be used as keys for the result dictionary
    """
    self.logger.debug('Enter ------------------------------')
    
    R = PolynomialRing(GF(2), key)
    S = R.quotient(irreducible_polynomial, key)
    a = S.gen() # generator of this quotient ring
    
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
        # get exponent of actual key and raise them | lambda: L^x
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
  use n that is not divisible by 2^n: 2, 4, 8, 16, 32, 64, ...
  http://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_gf2x.html
  
  1. vygenerovat lambdu ak je to mozne -> GCD(2^n - 1, 2^L + 1) == 1
  2. vygenerovat vyraz v tvare x1 + x2*L^1 + x3*L^2 + ... x_n*L^n-1
  3. vygenerovat ireducibilny polynom stupna n
  4. zistit zvysky po deleni pre zvoleny ireducibilny polynom -> napr pre x3 + x + 1 = x1->x1, x2->x2, x3->x + 1, x4->x^2 + x, ...
  5. umocnit vygenerovany vyraz na 2^L + 1
  6. za lambdy stupna vacsieho ako n dosadit zvysky po deleni
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
    mq.irred_polynomial = self.create_irreducible_polynomial(MQ.VARIABLE_X, mq.n)
    self.irred_polynomial_rem = self.compute_remainder(mq.irred_polynomial, MQ.VARIABLE_LAMBDA)
    base_polynomial = self.create_equation(mq.n)
    
    self.logger.info('Created irreducible polynomial=%s' % mq.irred_polynomial)
    # the equation is P'(X) = X ^ (2 ^ labda + 1) we break this into two parts
    
    # first part: a = left_side ^ (2 ^ lambda), will be calculated using the Frobenius automorphisms
    left_side = self.square_polynomial(base_polynomial, self._lambda, self.irred_polynomial_rem)
    self.logger.info('For lambda=%s computed left side\n%s' % (self._lambda, left_side))
    self.logger.info('Multipling left side with right side\n%s' % base_polynomial)
    
    # second part: P'(x) = a * X ^ 1
    self._P = self.multiply_polynomials(left_side, base_polynomial, self.irred_polynomial_rem)
    
    # just renaming keys from L^x to yx
    result = {}
    for i in range(mq.n):
      result[MQ.VARIABLE_Y + str(i + 1)] = self._P[MQ.LAMBDA_RAISED_TO + str(i)]
    
    self._P = result
    self.logger.info('_P=%s' % self._P)
    if HUMAN_PRINT:
      self.human_print(base_polynomial)
    
    return self._P
  
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
  
  def compute_lambda(self):
    """
    Computes number L, which fulfills the condition 
    GCD((2^n)-1, (2^L)+1) == 1, if this number is not found until the condition 
    (2^n)-1 > (2^L)+1 is fulfilled, where n is degree of polynomial then is
    raised error
    """
    self.logger.debug('Enter ------------------------------')
    
    lamb   = 1
    first  = (2 ** self.mq.n) - 1
    second = (2 ** lamb) + 1
    
    while first > second:
      if gcd(first, second) == 1:
        return lamb
      
      lamb  += 1
      second = (2 ** lamb) + 1
    
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
    mq.irred_polynomial = self.create_irreducible_polynomial(MQ.VARIABLE_X, mq.n)
    self.irred_polynomial_rem = self.compute_remainder(mq.irred_polynomial, MQ.VARIABLE_LAMBDA)
    base_polynomial = self.create_equation(mq.n)
    
    #count = (2 ** self.mq.n) - 1 # modulo
    #d_range = range(self.mq.n, (self.mq.n * count) + 1) # pick d that should be small ?!
    d_range = range(mq.n, mq.n + 3) # pick d that should be small ?!
    self.d = choice(d_range) # pick random value from range
    self.logger.debug('Ireducible polynomial=%s, polynomial degree d=%s' % (mq.irred_polynomial, self.d))
    
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
    if HUMAN_PRINT:
      self.human_print()
    
    return self._P
  
  def human_print(self):
    print self.__class__.__name__
    
    for equation in self._P:
      print equation + ' =',
      for variable in self._P[equation]:
        print variable + ' +',
      print('')
    
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

class MHRS:
  def __init__(self, mq):
    self.mq = mq
  
  def transform(self):
    pass

class TEST:
  """
  performs test on passed trapdoor with function and other arguments
  
  Attributes:
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
  def __init__(self, trapdoor=[], n=[], repeat=[], function=[], file_name=""):  
    self.trapdoor = trapdoor
    self.n = n
    self.repeat = repeat
    self.function = function
    self.file_name = file_name
    self.estimate_complexity()
  
  def estimate_complexity(self):
    with open("./tests/test" + datetime.now().strftime('%Y-%m-%d %H:%M:%S') + ".txt", "a", 0) as outfile:
      for trapdoor in self.trapdoor:
        stop = False
        
        for n in self.n:
          if stop:
            break
          average_complexity = 0
          average_time = 0
          
          for test_run in range(self.repeat[0]):
            time_start = time.time()
            # ---------------------------------------------------------------- #
            # UOV not secure
            if trapdoor == 1:
              mq = MQ(n, n, UOV())
            # UOV secure
            elif trapdoor == 2:
              n_var = (n * 2 + n)
              
              if n_var < 20:
                mq = MQ(n_var, n, UOV(n))
              else:
                stop = True
                break
            # STS
            elif trapdoor == 3:
              u = v = n / 2
              l = u + 1

              ones = [1] * v
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
              mq = MQ(n, n, HFE())
            # Not implemented
            else:
              raise BaseException("trapdoor not implemented")
            # ---------------------------------------------------------------- #
            for function in self.function:
              if callable(function):
                
                if function is zajac.convert:
                  mc = MQChallenge(mq)
                  if isinstance(mq.trapdoor, STS):
                    logging.info(mc.polynomial_matrix)
                  
                  result = zajac.convert(data=mc.polynomial_matrix)
                  average_complexity += result
                  time_end = (time.time() - time_start)
                  if isinstance(mq.trapdoor, UOV) and trapdoor == 2:
                    outfile.write("%s n=%d, m=%d, complexity=%5d, time=%s\n" % (type(mq.trapdoor), n * 2 + n, n, result, time_end))
                  else:
                    outfile.write("%s n=%d, m=%d, complexity=%5d, time=%s\n" % (type(mq.trapdoor), n, n, result, time_end))
                
                elif function is jamrichova.convert:
                  pass
                else:
                  raise BaseException("passed function '%s' is not implemented" % (function))
              else:
                raise BaseException("passed argument '%s' in function is not function" % (function))
            
            average_time += time_end
          if not stop:
            test_run += 1.0 # due for loop and to divide as double
            outfile.write("average complexity=%.1f, average time=%.5f\n\n" % (average_complexity / test_run, average_time / test_run))
  
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
#4.STS 'Nech v prvej vrstve sú 2 premenné x_1 , x_2', moze byt samostatna rovnica len v tvare x_1*x2=y, alebo tam maju byt vzdy dva cleny ako napr x_1 + x_2 
#5.UOV pocet olejovych ma byt viac ako octovych alebo naopak? aky pomer? a kolko premennych ma byt v rovnici?
#
# compute_remainder: spravit v metode nech L a 1 vracia uz ako L^1 a L^0
# HFE subs: optimalizacia
#if logging.getLogger().getEffectiveLevel() == logging.DEBUG:

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

# levels = NOTSET INFO DEBUG WARNING
logging.basicConfig(level=logging.INFO, format='%(levelname)s %(name)s::%(funcName)s %(message)s')

# pretty print
HUMAN_PRINT = 0
if __name__ == "__main__":
  if 0 == 1:
    run_test(1)
    exit(0)
  
  TEST(range(3, 4), range(2, 15), [10], [zajac.convert])
  #exit(0)
  
  #estimate_complexity()
  n = 4
  m = 4
  trapdoor = {
    'uov': UOV(),
    'sts': STS(2, [2, 2], [2, 2]),
    'mia': MIA(),
    'hfe': HFE()
  }
  mq = MQ(n, m, trapdoor['uov'])
  exit(0)
  mc = MQChallenge(mq)
  mc.store()
  zajac.convert(data=mc.polynomial_matrix)
  #jamrichova.convert(mq)