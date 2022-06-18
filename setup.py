from setuptools import setup, find_packages

setup(
    name='SEtaac',
    version='0.1.0',
    packages=find_packages(),
    install_requires=[
        'z3-solver>=4.8.17.0',
        'pysha3>=1.0.2',
        'matplotlib>=3.5.2',
        'networkx>=2.5.1',
        'web3>=5.29.2',
        'dill>=0.3.4',
        'solc-select>=0.2.1',
        'teether@git+ssh://git@github.com/nescio007/teether.git'
    ],
    python_requires='>=3.5',
)
