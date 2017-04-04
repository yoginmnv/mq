from setuptools import setup, find_packages

setup (
       name='mq',
       version='0.1',
       packages=find_packages(),

       # Declare your packages' dependencies here, for eg:
       install_requires=['foo>=3'],

       # Fill in these to make your Egg ready for upload to
       # PyPI
       author='Maroš Polák',
       author_email='xpolakm4 at stuba dot sk',

       #summary = 'Just another Python package for my diploma thesis',
       url='https://github.com/yoginmnv/mq/',
       license='GPL',
       long_description='Implementation of MQ trapdoors: UOV, STS, MIA, HFE',

       # could also include long_description, download_url, classifiers, etc.

  
       )
