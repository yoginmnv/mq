#!/usr/lib/sagemath/ sage
# -*- coding: UTF-8 -*-

#http://stackoverflow.com/questions/193161/what-is-the-best-project-structure-for-a-python-application
#https://learnpythonthehardway.org/book/ex46.html
#http://docs.python-guide.org/en/latest/writing/structure/
#https://github.com/kennethreitz/samplemod

#http://doc.sagemath.org/html/en/tutorial/tour_algebra.html
#http://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_gf2x.html
#http://doc.sagemath.org/html/en/constructions/polynomials.html
import logging
from random import randint
from random import shuffle
from sets import Set
from pprint import pprint
import sys
from sage.all import *
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildIrred_list
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildRandomIrred_list

import time

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

__author__ = "Maroš Polák"
__copyright__ = "Copyright (c) 2016 - 2017, Maroš Polák"
__license__ = "GPL"
__version__ = "1.0.1"
__email__ = "xpolakm4 at stuba dot sk"
__status__ = "In progress"



class MQ(object):
  """
  Attributes:
    n         -- pocet premennych | count of variables
    m         -- pocet rovnic | count of equations
  """
  variable_x = 'x'
  variable_y = 'y'
  operator_mul = ' * '
  operator_power = '**'
  
  def __init__(self, n, m):
    self.logger = logging.getLogger('MQ')
    self.logger.info('creating instance of MQ')
    
    if( n < 1 ):
      raise ValueError('Count of variables have to be greater than 1')
    if( m < 1 ):
      raise ValueError('Count of equations have to be greater than 1')
    
    self.n = n
    self.m = m
    self.product = self.create_product()
    
  def create_product(self):
    product = [MQ.variable_x + '1']
    
    n = self.n + 1
    for i in range(2, n):
      product.append(MQ.variable_x + str(i))
      for j in range(1, i):
        product.append(MQ.variable_x + str(j) + MQ.operator_mul + MQ.variable_x + str(i))

    return product



class AffineTransformation:
  def __init__(self, dimension, transformation_type):
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
  # 3. vygenerovat rovnice(2) pre UOV schemu
  # 3a. dosadit rovnice(1) do rovnic(2) y_m
  
  def __init__(self, oil_vector, vinegar_vector = []):
    self.logger = logging.getLogger('UOV')
    self._P = []
    self.oil = oil_vector
    
    if not vinegar_vector:
      self.vinegar = []
    else:
      self.vinegar = vinegar_vector
  
  # skontrolovat ci su rovnice v UOV strukture V*V,V*O, ale nie O*O
  def check_struct(self):
    #super(UOV, slef).get_dimension
    print(self._P)
    
 
 
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
    self.logger = logging.getLogger('STS')
    self.logger.info('creating an instance of STS')
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

    variable_x = 'x'
    variable_y = 'y'
    # ake premenne sa maju vyskytovat v rovniciach
    should_contains = [variable_x + str(i) for i in range(1, self.mq.n + 1)]
    
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
        actual_equation = variable_y + str(i)
        
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
            if actual_eq_len == len(self._P[variable_y + str(j)]):
              if self._P[actual_equation] == self._P[variable_y + str(j)]:
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



class MIA(object):
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
  variable_lambda = 'L'
  
  def __init__(self, MQ):
    self.logger = logging.getLogger('MIA')
    self.logger.info('creating an instance of MIA')
    self.mq = MQ
    self._P = None
    self.irred_polynomial = None
    self.irred_polynomial_rem = {}
    self.lamb = None
    self.h = 0
    self.create_trapdoor()
    
  def create_trapdoor(self):
    self.lamb = self.compute_lambda(self.mq.n)
    X = self.create_equation() # x1 + x2 * L + x3 * L^2 + ...
    self.irred_polynomial = GF(2)[MQ.variable_x](GF2X_BuildIrred_list(self.mq.n))
    #self.irred_polynomial = GF(2)[MQ.variable_x](GF2X_BuildRandomIrred_list(self.mq.n))
    self.irred_polynomial_rem = self.compute_remainder(self.irred_polynomial)
    
    # the equation is P`(X) = X ^ (2 ^ labda + 1) we break this into two parts
    
    # first part: a = X ^ (2 ^ lambda)
    count_of_squaring = 2 ** self.lamb
    for counter in range(count_of_squaring):
      X_squared = {}
      
      for key in X:
        print('Key from X:' + key)
        exponent = int(key[2:]) * 2 # get exponent of actual lambda: L^x
        
        if exponent >= self.mq.n:
          ired_keys = str(self.irred_polynomial_rem[MIA.variable_lambda + '^' + str(exponent)]).split(' + ')
          print('Keys ', ired_keys)
          
          for ired_key in ired_keys:
            # fix as sagemath return L^1 as L
            if ired_key == MIA.variable_lambda:
              ired_key = MIA.variable_lambda + '^1'
            
            if ired_key in X_squared:
              X_squared[ired_key] ^= X[key] # new set with elements in either s or t but not both
            else:
              X_squared[ired_key] = X[key]
            
        else:
          X_squared[MIA.variable_lambda + '^' + str(exponent)] = X[key]
          print('In loop ', X_squared)
      print('------------------')
      X = X_squared
    
    # second part: P`(x) = a * X ^ 1
    
    
    return
#    R = GF(2)['x1, x2, x3, L'].gens()
#    X = (R[0]*R[3]**0 + R[1]*R[3]**1 + R[2]*R[3]**2 )
#    print(X)
#    X2 =(R[0]*R[3]**0 + R[1]*R[3]**1 + R[2]*R[3]**2 )**2
#    print(X2)
#    print(X2[0])
#    power = 2 ** self.lamb + 1
    #print(X)
    
  def compute_lambda(self, n):
    first = 2 ** n - 1
    lamb = 1
    while True:
      second = 2 ** lamb + 1
      
      if first < second:
        raise ValueError('Lambda not found for n = ' + str(self.mq.n))

      if gcd(first, second) == 1:
        return lamb
      
      lamb += 1
  
  def create_equation(self):
    X = {};
    
    for i in range(self.mq.n):
      X[MIA.variable_lambda + '^' + str(i)] = set([MQ.variable_x + '^' + str(i + 1)])
      
    return X
    
  def compute_remainder(self, irreducible_polynomial):
    R = PolynomialRing(GF(2), MIA.variable_lambda)
    S = R.quotient(irreducible_polynomial, MIA.variable_lambda)
    a = S.gen()
    
    irred_polynomial_rem = {MIA.variable_lambda + '^0': a ** 0} #irred_polynomial_rem[MIA.variable_lambda + '0'] = a**0
    
    count = self.mq.n ** 2 - 2
    for i in range(1, count):
      irred_polynomial_rem[MIA.variable_lambda + '^' + str(i)] = irred_polynomial_rem[MIA.variable_lambda + '^' + str(i - 1)] * a
        
    return irred_polynomial_rem



class HFE(MQ):
  """
  Hidden Field Equations
  """
  def __init__(self):
    self.logger = logging.getLogger('HFE')
    self.logger.info('creating an instance of HFE')

    self._P = []



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

if __name__ == "__main__":    
  mq = MQ(3, 24)
  
  #sts = STS(mq, 4, [3, 4, 5, 5], [6, 6, 6, 6])
  mia = MIA(mq)
  
  #x = PolynomialRing(GF(2), 'x').gen()
  #f = x**4 + x + 1
  #g = x + 1
  #print(f.gcd(g))