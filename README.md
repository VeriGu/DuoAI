# Duo: Fast, Automated Inference of Inductive Invariants for Verifying Distributed Protocols

Duo is an automated tool to formally verify distributed protocols (e.g., Paxos) by inferring inductive invariants.

## Installation

1. Download and install Anaconda from https://www.anaconda.com/products/individual. Use version >= Python 3.8.

2. The Ivy verification tool only works on Python 2. Install it by 
    ```
    $ conda create --name py2 python=2.7
    $ conda activate py2
    $ pip install ms-ivy
    ```
   
3. Configure Ivy path

    - Run `which ivy_check` to get the absolute path of the Ivy checker. We assume it is `ANACODNA_PATH/envs/py2/bin/ivy_check`.

    - Append the following line to `~/.bashrc`
        ```
        alias ivy_check="ANACODNA_PATH/envs/py2/bin/ivy_check"
        ```
    
    - Copy and replace the absolute path at `#define IVY_CHECK_PATH` in `src-c/InvRefiner.h`. (This is a workaround for calling Python2 from a Python3 conda environment. We would appreciate any suggestion to make this more elegant)

4. Install Python libraries 
    ```
    $ conda activate base
    $ conda install numpy scipy pandas
    ```

5. Build C++ source files
    ```
    $ cd src-c
    $ make
    $ source ~/.bashrc
    ```

## Usage

Given a distributed protocol, ```python Duo.py PROTOCOL_NAME``` simulates the protocol, enumerate the invariants and applies top-down/bottom-up refinement until an inductive invariant is found. For example,

```
$ python Duo.py client_server_db_ae
```

As suggested on the screen, the inductive invariant is written to ```outputs/client_server_db_ae/client_server_db_ae_e0_inv_main.ivy```. 
One can verify this by running 
```
$ ivy_check outputs/client_server_db_ae/client_server_db_ae_e0_inv_main.ivy
```

Besides the final result, one can also inspect the intermediate files. ```auto_samplers/client_server_db_ae/``` lists the Python simulation scripts that run in parallel. 
```traces/client_server_db_ae/``` lists the simulated samples of different instance sizes.
If a protocol is solved by bottom-up refinement (e.g., ```flexible_paxos```), then ```src-c/runtime/flexible_paxos/bottom_up/``` shows the universal inductive core and the noncore candidates.


## Structure  

- protocols/:
  The 27 distributed protocols in Ivy. 
  
- src-py/:
  The python source code for protocol simulation
  - translate.py: parse an Ivy protocol file; generates simulation scripts in Python and a configuration file
  - translate_helper.py: provides functionality for translate.py
  - ivy_parser.py: parse an Ivy expression and generates a syntax tree, used by translate.py
  
- src-c/:
  The C++ source code for invariant enumeration, top-down refinement, and bottom-up refinement
  - main.cpp: the program entry
  - basics.h/cpp: define the representation for samples, predicates, invariants, etc.; define basic operations on them
  - preprocessing.h/cpp: read and process the csv trace files and the configuration file
  - Solver.h/cpp: enumerate candidate invariants following the minimum implication graph and check them against samples
  - InvRefiner.h/cpp: implement the top-down and bottom-up refinement (the former a subprocedure of the latter); make Ivy calls and analyze the results
  - CounterexampleHandler.h/cpp: parse the counterexamples given by Ivy and filter candidate invariants accordingly
  - Helper.h/cpp: perform formula and graph transformations which is used by Solver and InvRefiner

- Duo.py:
  The top-level wrapper. Manage multiple simulation and refinement processes running in parallel.
