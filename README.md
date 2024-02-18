# Samp2Symb
[![Python package](https://github.com/cryhot/samp2symb/actions/workflows/pythonpackage.yaml/badge.svg)](https://github.com/cryhot/samp2symb/actions/workflows/pythonpackage.yaml)

_Python library for inferring symbolic structures (e.g., Linear temporal logic formulas, Deterministic Finite Automata) from examples (sample of traces)._

---

## Installation

One might intall only a subset of the dependencies:
- python libraries listed in [`requirements.txt`](requirements.txt)
<!-- - [Z3](https://github.com/Z3Prover/z3#python) with python bindings: SAT solver -->
- [spot](https://spot.lrde.epita.fr/install.html): used to convert LTL formulas to Buchi automatas (infinite traces)
- [mona](https://www.brics.dk/mona/): used by [ltlf2dfa](https://github.com/whitemech/LTLf2DFA) to convert LTL formulas to deterministic finite automatas (finite traces)
- [clingo](https://github.com/potassco/clingo): ASP solver
- [caqe](https://github.com/ltentrup/caqe.git): QBF solver, used by [qasp2qbf](https://github.com/potassco/qasp2qbf) (see [`./samp2symb/algo/asp/README.md`](samp2symb/algo/asp/README.md))

We provide a convenient script for installing all dependencies on a **fresh linux install** (run **at your own risk** on your personal install, it is recommended to read it and to run only commands that you understand):
[`./install.sh`](install.sh) (do not use ~`sudo`~, root privilege will be asked when required).


## How to run

Example:
```sh
# inference of DFAs
./infer --log=INFO -o "stats.json" specific DFA -f "traces/dummy.words" --dfa="dfa.dot" --dfa-new="dfa-{attempt}.dot" -n=3 --method=CE

# inference of LTLf formulas (finite traces)
./infer -o "stats.json" specific LTL -f "traces/ltlf/TracesFiles/f:01-nw:10000-ml:10-0.trace" -n=4 --method=CE
./infer -o "stats.json" specific LTL -f "traces/ltlf/TracesFiles/f:01-nw:10000-ml:10-0.trace" -n=4 --method=S-SYMB --horizon=8

# inference of LTL formulas (infinite traces)
./infer -o "stats.json" specific LTL -f "traces/generated/5to10OneThree/0020.trace" -n=4 --method=CE
./infer -o "stats.json" specific LTL -f "traces/generated/5to10OneThree/0020.trace" -n=4 --method=S-SYMB --horizon=8
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

## Cite us
Check out our paper: [_Learning Interpretable Temporal Properties from Positive Examples Only_](https://ojs.aaai.org/index.php/AAAI/article/download/25800/25572)

```
@article{RoyGBNXT_2023_pos2LTL,
	doi = {10.1609/aaai.v37i5.25800},
	url = {https://doi.org/10.1609%2Faaai.v37i5.25800},
	year = 2023,
	month = {jun},
	publisher = {Association for the Advancement of Artificial Intelligence ({AAAI})},
	volume = {37},
	number = {5},
	pages = {6507--6515},
	author = {Rajarshi Roy and Jean-Raphaël Gaglione and Nasim Baharisangari and Daniel Neider and Zhe Xu and Ufuk Topcu},
	title = {Learning Interpretable Temporal Properties from Positive Examples Only},
	journal = {Proceedings of the {AAAI} Conference on Artificial Intelligence}
}
```