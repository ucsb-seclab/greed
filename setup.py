import os
import subprocess
from setuptools import setup, find_packages
from setuptools.command.install import install
from setuptools.command.develop import develop


class CustomInstallCommand(install):
    """Customized setuptools install command - prints a friendly greeting."""
    def run(self):
        subprocess.run('./setup.sh', shell=True)
        install.run(self)


class CustomDevelopCommand(develop):
    """Customized setuptools install command - prints a friendly greeting."""
    def run(self):
        subprocess.run('./setup.sh', shell=True)
        develop.run(self)


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
    ],
    cmdclass={
        'develop': CustomDevelopCommand,
        'install': CustomInstallCommand,
    },
    python_requires='>=3.6',
)
