This is an initial incorporation of the MPACK library into Macaulay 2

Installation:
1. Download and compile the MPACK library on your computer (assuming linux). See: http://mplapack.sourceforge.net/
2. Replace the files dmat.cpp dmat.hpp lapack.cpp lapack.hpp Makefile.in in M2/Macaulay2/e folder(from the trunk of the local svn image), with the files of the same name in this folder
3. Replace the file Makefile.in in M2/Macaulay2/bin folder with the file Makefile.in_binfolder in this folder after renaming the file to Makefile.in
4. Replace the file mpreal.h in /usr/local/include/mpack/ with the file of the same name in this folder
5. Replace the files mutablemat.m2 exports.m2 in M2/Macaulay2/m2 with the files of the same name in this folder
6. Remake M2 from source

The currently supported functionality is solve linear systems over the field of complex numbers up to arbitrary precision.
This can be called by specifying an optional argument in the function solve in this format "solve(MatrixA, MatrixB, Precision=>n)" where n is the number of precision in bits.

7/29/11
Henry Duong


Based on:
URL: svn://svn.macaulay2.com/Macaulay2/trunk/M2
Repository Root: svn://svn.macaulay2.com/Macaulay2
Repository UUID: a8012f80-5f13-0410-8dc0-eb77bd940c0d
Revision: 13313
Node Kind: directory
Schedule: normal
Last Changed Author: dan
Last Changed Rev: 13313
Last Changed Date: 2011-07-04 14:24:15 -0400 (Mon, 04 Jul 2011)


