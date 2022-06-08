from setuptools import setup, find_packages

setup(
    name='SEtaac',
    version='0.1.0',
    packages=find_packages(),
    install_requires=[
        'z3-solver>=4.8.17.0',
        'pysha3>=1.0.2',
        'networkx>=2.8.3'
    ],
    python_requires='>=3.5',
)
