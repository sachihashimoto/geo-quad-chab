# geo-quad-chab
Code for the paper "Geometric Quadratic Chabauty and p-adic heights"

Authors: Juanita Duque-Rosero, Sachi Hashimoto, Pim Spelier

The main file is geometricQuadChab.m

This code runs on Magma, and has been tested on Magma V2.26-11

This repository depends on a Magma installation of <https://github.com/edgarcosta/endomorphisms>, see the ReadMe in the repository for more details.

The folder Heights contains code written by Raymond von Bommel, David Holmes, and J. Steffen Muller
The file QCMod contains the repository <https://github.com/steffenmueller/QCMod> with modifications to the divisor_heights.m file.  In particular, we add lines 611 and 612 to the file qc_modular to verify that the constant v' from Proposition 5.2 is zero.
The file BalancedDivisorOddDDeg.m contains code by Andrew V. Sutherland with a small modification for our odd degree models
The file jacobianpointfixed.m contains a bug fix for the JacobianPoint intrinsic in Magma
