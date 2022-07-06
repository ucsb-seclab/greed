import os

from setuptools import setup, find_packages

assert 'VIRTUAL_ENV' in os.environ, "Cannot install outside of a Python virtualenv"

setup(
    name='SEtaac',
    version='0.1.0',
    packages=find_packages(),
    install_requires=[
        'ipython>=7.16.3',
        'networkx>=2.5.1',
        'pysha3>=1.0.2',
        'solc-select>=0.2.1',
        'z3-solver>=4.8.17.0',
        'sympy>=1.9'
    ],
    python_requires='>=3.8',
)
