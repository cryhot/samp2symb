# Samp2Symb
[![Python package](https://github.com/cryhot/samp2symb/actions/workflows/pythonpackage.yaml/badge.svg)](https://github.com/cryhot/samp2symb/actions/workflows/pythonpackage.yaml)

_Python library for inferring symbolic structures (e.g., Linear temporal logic formulas, Deterministic Finite Automata) from examples (sample of traces)._

---

## Installation

To install all dependencies, run the following script: [`./install.sh`](install.sh) (do not use ~`sudo`~, root privilege will be asked when required).
Run this script **at your own risk** (it is recommended to read it and to run only commands that you understand).

One might intall only a subset of the dependencies:
- python libraries listed in [`requirements.txt`](requirements.txt)
<!-- - [Z3](https://github.com/Z3Prover/z3#python) with python bindings: SAT solver -->
- [spot](https://spot.lrde.epita.fr/install.html): used to convert LTL formulas to Buchi automatas (infinite traces)
- [mona](https://www.brics.dk/mona/): used by [ltlf2dfa](https://github.com/whitemech/LTLf2DFA) to convert LTL formulas to deterministic finite automatas (finite traces)
- [clingo](https://github.com/potassco/clingo): ASP solver
- [caqe](https://github.com/ltentrup/caqe.git): QBF solver, used by [qasp2qbf](https://github.com/potassco/qasp2qbf) (see [`./samp2symb/algo/asp/README.md`](samp2symb/algo/asp/README.md))


## How to run

Example:
```sh
# inference of DFAs
./infer --log=INFO -o "stats.json" specific DFA -f "traces/dummy.words" --dfa="dfa.dot" --dfa-new="dfa-{attempt}.dot" -n=3 --method=CE

# inference of LTLf formulas (finite traces)
./infer -o "stats.json" specific LTL -f "traces/ltlf/TracesFiles/f:01-nw:10000-ml:10-0.trace" -n=4 --method=CE
./infer -o "stats.json" specific LTL -f "traces/ltlf/TracesFiles/f:01-nw:10000-ml:10-0.trace" -n=4 --method=HYBRID --horizon=8

# inference of LTL formulas (infinite traces)
./infer -o "stats.json" specific LTL -f "traces/generated/5to10OneThree/0020.trace" -n=4 --method=CE
./infer -o "stats.json" specific LTL -f "traces/generated/5to10OneThree/0020.trace" -n=4 --method=HYBRID --horizon=8
```

Please read help (`./infer -h` and subcommands help) for more info.

<!-- insert help -->

### Generating data

```sh
./genBenchmarks -T=dfa_spec -f traces/dfa_specs.txt -o traces/dfa/ --size 500,0
./genBenchmarks -T=ltl -f traces/formulas.txt -o traces/ltlf/ --size 10000,0 --lengths 10
```

## Acknowledgments

This project reuses code from [cryhot/samples2LTL](https://github.com/cryhot/samples2LTL) and [rajarshi008/Scarlet](https://github.com/rajarshi008/Scarlet/).