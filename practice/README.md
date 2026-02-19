\# Consensus SMT Models



This repository contains SMT encodings (Z3) for crash-fault consensus protocols.

\#Rules

Specification: every node who made a decision must make the same decision
Nodes can crash at any round and will not return if they do so
If all nodes have same input state, all decisions must match the input state. If they are not the same, can choose either.
We can assume there is always a surviving (non-crashed) node at the end

Initial state is 0, 1 for each node

At round 1: observe own initial state, output whatever flags
Round k: input: observe flags raised by non-crashed nodes, output whatever flag

If a node crashes, only some of its messages can be assumed lost, i.e., its message may be received by some nodes but not others.

Final decision: 0,1 for each node

Find a correct protocol for this problem



\## Files



\- `consensus\_2n\_2r.py`  

&nbsp; SMT model for 2-node, 2-round consensus.  



\- `consensus\_3n\_3r.py`  

&nbsp; SMT model for 3-node, 3-round consensus.  


\- `consensus\_nn\_nr.py`  

&nbsp; SMT model for n-node, n-round consensus. 


\## Setup



```bash

pip install z3-solver



