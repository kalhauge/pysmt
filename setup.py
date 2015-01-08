
from setuptools import setup, find_packages
from setuptools.command.test import test as TestCommand

import pysmt

class PyTest(TestCommand):
    def finalize_options(self):
        TestCommand.finalize_options(self)
        self.test_args = []
        self.test_suite = True

    def run_tests(self):
        import pytest
        errcode = pytest.main(self.test_args)
        sys.exit(errcode)

setup(
    name="pysmt",
    version=pysmt.__version__,
    license='MIT',
    packages=['pysmt', 'pysmt.theories'],
    cmdclass={'test': PyTest},
    classifiers = [
        'Programming Language :: Python',
        'Development Status :: 2 - Pre-Alpha',
        'Natural Language :: English',
        'Operating System :: OS Independent',
    ],
    platforms="any",
    description="A SMT solver and modifier",
    long_description = open('README').read(),
    extras_require={
        'testing': ['pytest'],
    }
)
