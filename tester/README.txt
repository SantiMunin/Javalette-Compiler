The Javalette test programs are in (subdirectories of) directory examples.

This directory contains a test driver (Grade.hs, RunCommand.hs and KompTest.hs) that
can be used to run the tests for your project.

Prerequisites
----------

We expect that you are using a Unix-like system (including Linux and
Mac OS X) and have the Haskell compiler ghc in your path.
You will then just have to do 

make

in this directory to compile  the test program. This  gives the executable program 
Grade in this same directory.

Running the tests
-----------------

Assume that your submission directory is dir and that your
compiler is called jlc. Assume also that dir/lib 
contains the runtime support file (Runtime.class for submission A,
runtime.bc and/or runtime.o for submission B). For submission A, 
also jasmin.jar should be in dir/lib.

The test driver takes a number of options and two directories as
command line arguments. The possible options are

-s <name>                   The name of your compiler (in directory dir) is <name> (default is "jlc")
-b JVM                              Target files are JVM .class files
-b LLVM                           Target files are LLVM .bc files
-b x86                              Target files are x86 .o files..
-x <extension>     Implemented extensions.

The first of the two path arguments specifies where to find the
directory examples which contains the testsuite (it is in this
directory). The second specifies your submission directory. 
Thus, from this directory you may run
./Grade . dir

to compile all the basic javalette programs. The test driver will not 
attempt to run the good programs, so you may do the above
already when you have the parser working, and then when you 
have the typechecker working. 

To also run the good programs, you must specify the backend as
indicated above, i.e. for submission A

./Grade -b JVM . dir

The test driver will report its activities in compiling the test
programs and running the good ones. If your compiler is correct, 
output will end as follows:

Summary:
 0 Compiling core programs (48/48)
 0 Running core programs (22/22)

Credits total: 0

All 48 test programs were compiled and gave correct indication OK or
ERROR to stderr. The 22 correct programs were run and gave correct output.


Preparing a submission
-------------------

Your submission must be structured as specified in Appendix A of the
project description. We suggest that, after having prepared your tar
ball, you place it in an empty directory dir1 and run

./Grade -b JVM . dir1 

from this directory. The grading program, when it finds a tar ball in
the submission directory, starts by extracting and building your
compiler, before running the test suite. This is how we test your
submission, so you can check whether building and testing succeeds 
before you submit. Note that if the tester does not succeed on your 
submission, we will reject it without further checks, and you will
anyhow have to redo the submission according to specification. 

