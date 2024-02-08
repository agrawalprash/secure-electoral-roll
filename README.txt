Supplementary material: Publicly auditable privacy-preserving electoral rolls
=============================================================================

This repository contains supplementary material for the paper ``Publicly Auditable Privacy-Preserving Electoral Rolls'' by Prashant Agrawal, Mahabir Prasad Jhanwar, Subodh Vishnu Sharma and Subhashis Banerjee.

The repository contains two main artifacts:

1) File eps_delta.py containing our computer program for estimating the epsilon and delta functions reported in the paper. Running this program does not require any additional dependencies beyond Python.
- [Running the program] python3 eps_delta.py 1 1 (for both generation and plotting of data; switch the bits off if a functionality is not required)
 
2) Our sample implementation of the proposed electoral roll protocol (with dummy oracles). This program depends on the Charm cryptographic library. We provide an installation script named `install.sh` to install these dependencies in a Linux environment. 

- [Installation] Run `./install.sh` from the `electoral-rolls` directory.
- [Testing the functionality] Run `python3 electoralroll.py test` from the `electoral-rolls` directory. Sample output can be found in the `sample_test_output.txt` file.
- [Running the benchmarks] Run `python3 electoralroll.py bench n` from the `electoral-rolls` directory, where n denotes the number of registering voters. Sample output for `n=100` can be found in the `sample_bench_output_n100.txt` file.
