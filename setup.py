import os

from setuptools import setup, find_packages

assert 'VIRTUAL_ENV' in os.environ, "Cannot install outside of a Python virtualenv"

setup(
    name='greed',
    version='0.1.0',
    packages=find_packages(),
    install_requires=[
        'ipython>=7.16.3',
        'networkx>=2.5.1',
        'pytest==7.2.1',
        'solc-select>=0.2.1',
        'sympy>=1.9',
        'web3>=5.31.1',
    ],
    python_requires='>=3.8',
)
