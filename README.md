# Automated Normative Reasoning for ECtHR Cases via Deontic Defeasible Logic (DDL)

This repository contains an Isabelle/HOL mechanization of DDL together with an executable case study formalising ECtHR Article 6.

## Contents

- `DDL_main.thy`  
  Core types and abbreviations

- `DDL_inference.thy`  
  Syntactic derivation system (proof theory)

- `DDL_automation.thy`  
  Lightweight proof automation layer:

- `Example_ECtHR_Article6_Final.thy`  
  Executable case study for ECtHR Article 6:
 
## How to Run

1. Open Isabelle/HOL.
2. Load the theories in the usual order.
3. The main results are in `Example_ECtHR_Article6_Final.thy`
