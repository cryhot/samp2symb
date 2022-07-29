# Samp2Symb
_Python library for inferring symbolic structures (e.g., Linear temporal logic formulas, Deterministic Finite Automata) from examples (sample of traces)._

---

## Installation

To install all dependencies, run the following script: [`./install.sh`](install.sh) (root privilege will be asked).
Run this script **at your own risk** (it is recommended to read it and to run only commands that you understand).

One might intall only a subset of the dependencies:
- python libraries listed in [`requirements.txt`](requirements.txt)
- [Z3](https://github.com/Z3Prover/z3#python) with python bindings: SAT solver
- [spot](https://spot.lrde.epita.fr/install.html): used to convert LTL formulas to Buchi automatas
- [mona](https://www.brics.dk/mona/): used by [ltlf2dfa](https://github.com/whitemech/LTLf2DFA) to convert LTL formulas to deterministic finite automatas
- [clingo](https://github.com/potassco/clingo): ASP solver
- [caqe](https://github.com/ltentrup/caqe.git): QBF solver, used by [qasp2qbf](https://github.com/potassco/qasp2qbf) (see [`./samp2symb/algo/asp/README.md`](samp2symb/algo/asp/README.md))


## How to run

Example:
```sh
./infer -o "stats.json" specific LTL -f traces/generated/5to10OneThree/0020.trace -n=4 --method=CE
```

Please read help (`./infer -h` and subcommands help) for more info.

<!-- insert help -->

## Acknowledgments

This project reuses code from [cryhot/samples2LTL](https://github.com/cryhot/samples2LTL) and [rajarshi008/Scarlet](https://github.com/rajarshi008/Scarlet/).