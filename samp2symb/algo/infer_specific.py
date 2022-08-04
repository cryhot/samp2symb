#!/usr/bin/env python3

import sys
import logging
import termcolor
from pytictoc import TicToc


def find_specific_formula(
    sample, formula=None, *,
    start_size=1, max_size,
    check_horizon=float('inf'), check_finite="auto",
    grow_sample=True, # start with an empty sample, and add traces when required
    force_sub = False, force_nsup = False, # force next inferred formula to be \subseteq / \nsupseteq wrt previous formula
    timeout=float("inf"),
    dbg_dots=False, # show progress as colored dots
    json_stats=None, # provide your own dict to be filled
    program_file=None, # "*.lp" file, usefull for debugging
):
    from samp2symb.base.ltl import Formula
    from samp2symb.base.trace import PropTrace
    from samp2symb.algo.asp import LTLSolver
    logger = logging.getLogger("LTL-finder")
    tictoc_solver,  time_solver = TicToc(), 0
    tictoc_transInfinite,  time_transInfinite   = TicToc(), 0
    tictoc_transFinite,    time_transFinite     = TicToc(), 0
    tictoc_genInfinite,    time_genInfinite     = TicToc(), 0
    tictoc_genFinite,      time_genFinite       = TicToc(), 0
    tictoc_total = TicToc()
    tictoc_total.tic()

    # sanitize arguments
    if force_sub: force_nsup = True
    if check_finite == "auto":
        if len(sample)==0: check_finite = "both"
        elif all(trace.finite for trace in sample): check_finite = "finite"
        elif all(trace.infinite for trace in sample): check_finite = "infinite"
        else: check_finite = "both"
    if check_finite == "finite": check_finite = True
    if check_finite == "infinite": check_finite = False
    if check_finite == "both": check_finite = None
    if formula is None: formula = Formula.loads("true")
    else: assert sample.isFormulaConsistent(formula), "sample is not consistant with formula"

    # prepare variables
    trace1 = next(iter(sample))
    literals = trace1.literals
    effective_sample = sample.copy()
    if grow_sample:
        effective_sample.clear()
        traces = sorted(((trace,label) for trace,label in sample.items()), key=lambda x: len(x[0].vector))
    size = start_size-1
    formulas_candidate = iter(())
    formula_kwargs = dict(check_horizon=check_horizon, check_finite=check_finite)
    logger.info(f"considering sample: {sample.summary()}")
    if json_stats is None: json_stats = dict()
    json_stats.setdefault('method', dict()).update(
        force_sub=force_sub,
        force_nsup=force_nsup,
        requires_QASP=force_sub, # assuming that
        check_finite=check_finite in [True, None],
        check_infinite=check_finite in [False, None],
    )
    if check_horizon<float('inf'): json_stats['method']['check_horizon'] = check_horizon
    json_stats.setdefault('sample', dict()).update(
        sample.json_summary(),
    )
    json_stats.setdefault('progress', dict()).update(
        inferred=0, # num total inferred formulas
        formulas=[], # distinct inferred formulas
        traces_sample = len(effective_sample), # used sample traces
        traces_ce = 0, # generated counter-example traces
    )
    json_stats.setdefault('elapsed', dict())
    json_stats['progress']['formulas'].append(formula.prettyPrint())

    while True:
        tictoc_solver.tic()
        if formulas_candidate is None:
            solver = LTLSolver(size=size, atoms=literals)
            solver.add_sample(effective_sample)
            if force_sub: solver.add_formula(formula, sup=True, sub=False, **formula_kwargs)
            elif force_nsup: solver.add_formula(formula, sub=False, **formula_kwargs)
            if program_file is not None:
                path=program_file.format()
                with open(path, 'w') as fp: fp.write(str(solver))

            if solver.requires_QASP:
                assert force_nsup, "we supposed that there will be progress in 1 iteration"
                formulas_candidate = filter((lambda f: f is not None), (solver.solve_qbf(timeout=timeout-tictoc_total.tocvalue()),))
            else:
                formulas_candidate = solver.iter_solve_asp(timeout=timeout-tictoc_total.tocvalue())
        
        try:
            formula_candidate = next(formulas_candidate)
            json_stats['progress']['inferred'] += 1
        except TimeoutError as err:
            print(f"Best formula before timeout: {formula}")
            raise err
        except KeyboardInterrupt as err:
            print(f"Best formula before interruption: {formula}")
            raise err
        except StopIteration:
            if size >= start_size:
                json_stats['elapsed'][size] = dict(
                    total=tictoc_total.tocvalue(),
                    solver=time_solver,
                    ce=time_transFinite+time_transInfinite+time_genFinite+time_genInfinite,
                    ce_trans=time_transFinite+time_transInfinite,
                    ce_trans_finite=time_transFinite,
                    ce_trans_infinite=time_transInfinite,
                    ce_gen=time_genFinite+time_genInfinite,
                    ce_gen_finite=time_genFinite,
                    ce_gen_infinite=time_genInfinite,
                )
            size += 1
            if size > max_size: break
            logger.debug(f"trying size={size}")
            if dbg_dots: sys.stdout.write(termcolor.colored("+", color='cyan', attrs=['bold'])); sys.stdout.flush()
            formulas_candidate = None
            continue
        finally:
            time_solver += tictoc_solver.tocvalue()

        # check consistency with sample
        for i,(trace,label) in enumerate(traces): # if a trace in the sample is not consistent...
            if trace.evaluate(formula_candidate) == label: continue
            effective_sample.append(trace, label=label) # ...ensure that it is considered
            json_stats['progress']['traces_sample'] += 1
            del traces[i]
            formulas_candidate = None
            break
        if formulas_candidate is None: continue

        # check that L(A') \subseteq L(A)
        neg_trace = None
        if force_sub and check_horizon>=float('inf'): neg_trace = False # skip conterexample
        if neg_trace is None and check_finite in [True, None]: # finite trace
            tictoc_transFinite.tic()
            f = Formula(['!', Formula(['->', formula_candidate, formula]) ]).to_dfa(literals)
            time_transFinite += tictoc_transFinite.tocvalue()
            tictoc_genFinite.tic()
            try: neg_trace = f.generate_random_word_length(-1)
            except RuntimeError: neg_trace = None
            else: neg_trace = PropTrace(neg_trace, literals=literals, intendedEvaluation=False)
            time_genFinite += tictoc_genFinite.tocvalue()
        if neg_trace is None and check_finite in [False, None]: # infinite trace
            tictoc_transInfinite.tic()
            import spot
            f1, f2 = formula_candidate.to_spot().translate(), spot.formula.Not(formula.to_spot()).translate()
            time_transInfinite += tictoc_transInfinite.tocvalue()
            tictoc_genInfinite.tic()
            neg_trace = f1.intersecting_word(f2)
            if neg_trace is not None: neg_trace = PropTrace.from_spot(neg_trace, literals)
            time_genInfinite += tictoc_genInfinite.tocvalue()
        if neg_trace is not None and neg_trace is not False: # found negative counterexample
            effective_sample.append(neg_trace, label=False)
            json_stats['progress']['traces_ce'] += 1
            formulas_candidate = None
            if dbg_dots: sys.stdout.write(termcolor.colored(".", color='red', attrs=['bold'])); sys.stdout.flush()
            logger.debug(f"considering new negative counterexample")
            continue
        
        # check that L(A') \subset L(A)
        neg_trace = None
        if force_nsup and check_horizon>=float('inf'): neg_trace = False # skip conterexample
        if neg_trace is None and check_finite in [True, None]: # finite trace
            tictoc_transFinite.tic()
            f = Formula(['!', Formula(['->', formula, formula_candidate]) ]).to_dfa(literals)
            time_transFinite += tictoc_transFinite.tocvalue()
            tictoc_genFinite.tic()
            try: neg_trace = f.generate_random_word_length(-1)
            except RuntimeError: neg_trace = None
            else: neg_trace = PropTrace(neg_trace, literals=literals, intendedEvaluation=False)
            time_genFinite += tictoc_genFinite.tocvalue()
        if neg_trace is None and check_finite in [False, None]: # infinite trace
            tictoc_transInfinite.tic()
            import spot
            f1, f2 = formula.to_spot().translate(), spot.formula.Not(formula_candidate.to_spot()).translate()
            time_transInfinite += tictoc_transInfinite.tocvalue()
            tictoc_genInfinite.tic()
            neg_trace = f1.intersecting_word(f2)
            if neg_trace is not None: neg_trace = PropTrace.from_spot(neg_trace, literals)
            time_genInfinite += tictoc_genInfinite.tocvalue()
        if neg_trace is not None: # found negative counterexample
            if neg_trace is not False:
                effective_sample.append(neg_trace, label=False)
                json_stats['progress']['traces_ce'] += 1
            formula = formula_candidate
            formulas_candidate = None
            if dbg_dots: sys.stdout.write(termcolor.colored("!", color='red', attrs=['bold'])); sys.stdout.flush()
            json_stats['progress']['formulas'].append(formula.prettyPrint())
            logger.info(f"found new formula: {formula_candidate.prettyPrint()}")
            continue
        
        if dbg_dots: sys.stdout.write(termcolor.colored(".", color='yellow', attrs=['bold'])); sys.stdout.flush()
        # logger.debug(f"found equivalent formula")
        logger.debug(f"found equivalent formula: {formula.prettyPrint()} <=> {formula_candidate.prettyPrint()}")

    logger.debug(f"returning formula: {formula.prettyPrint()}")
    json_stats['formula'] = formula.prettyPrint()
    logger.info(f"{tictoc_total.tocvalue():.3f}s elapsed ("
        f"{time_solver:.3f}s on solving, "
        f"{time_transFinite:.3f}s+{time_transInfinite:.3f}s={time_transFinite+time_transInfinite:.3f}s on translating formulas to DFA/Buchi Automata, "
        f"{time_genFinite:.3f}s+{time_genInfinite:.3f}s={time_genFinite+time_genInfinite:.3f}s on generating finite/infinite counterexamples"
        ")")
    return formula


def find_specific_dfa(
    sample, dfa=None, *,
    start_size=1, max_size,
    check_finite="auto",
    grow_sample=True, # start with an empty sample, and add traces when required
    force_sub = False, force_nsup = False, # force next inferred formula to be \subseteq / \nsupseteq wrt previous formula
    timeout=float("inf"),
    dbg_dots=False, # show progress as colored dots
    json_stats=None, # provide your own dict to be filled
    dfa_candidate_filename=None, # .dot file
    dfa_new_filename=None, # .dot file
    dfa_filename=None, # .dot file
):
    from samp2symb.base.dfa import DFA, word_with_labels
    from samp2symb.base.trace import AlphaTrace
    from samp2symb.algo.pysat import DFASolver
    logger = logging.getLogger("DFA-finder")
    tictoc_solver,  time_solver = TicToc(), 0
    # tictoc_genInfinite,    time_genInfinite     = TicToc(), 0
    tictoc_genFinite,      time_genFinite       = TicToc(), 0
    tictoc_total = TicToc()
    tictoc_total.tic()

    # sanitize arguments
    if force_sub: force_nsup = True
    if check_finite == "auto":
        if len(sample)==0: check_finite = "both"
        elif all(trace.finite for trace in sample): check_finite = "finite"
        elif all(trace.infinite for trace in sample): check_finite = "infinite"
        else: check_finite = "both"
    if check_finite == "finite": check_finite = True
    if check_finite == "infinite": check_finite = False
    if check_finite == "both": check_finite = None
    alphabet = sample.alphabet
    if dfa is None:
        dfa = DFA( # this DFA accepts every words
            # alphabet = alphabet,
            # states = [0],
            # transitions = {(0,letter):0 for letter in alphabet},
            # init_states = [0],
            # accepting_states = [0],
            init_state = 0,
            final_states = [0],
            transitions = {0:{letter:0 for letter in alphabet}}
        )
    else:
        assert all(dfa.is_word_in(trace)==label for trace,label in sample.items()), "sample is not consistant with DFA"

    # prepare variables
    trace1 = next(iter(sample))
    effective_sample = sample.copy()
    if grow_sample:
        effective_sample.clear()
        traces = sorted(((trace,label) for trace,label in sample.items()), key=lambda x: len(x[0].vector))
    size = start_size-1
    dfas_candidate = iter(())
    # dfa_kwargs = dict(check_finite=check_finite)
    dfa_kwargs = dict()
    logger.info(f"considering sample: {sample.summary()}")
    if json_stats is None: json_stats = dict()
    json_stats.setdefault('method', dict()).update(
        force_sub=force_sub,
        force_nsup=force_nsup,
        check_finite=check_finite in [True, None],
        # check_infinite=check_finite in [False, None],
    )
    json_stats.setdefault('sample', dict()).update(
        sample.json_summary(),
    )
    json_stats.setdefault('progress', dict()).update(
        inferred=0, # num total inferred dfas
        dfas=[], # distinct inferred dfas
        traces_sample = len(effective_sample), # used sample traces
        traces_ce = 0, # generated counter-example traces
    )
    json_stats.setdefault('elapsed', dict())
    dot_kwargs=dict(keep_alphabet=True, group_separator=";")
    
    dfa_path = None
    if dfa_new_filename is not None:
        dfa_path = dfa_new_filename.format(attempt=json_stats['progress']['inferred'])
        dfa.export_dot(dfa_path, **dot_kwargs)
    json_stats['progress']['dfas'].append(dfa_path)

    while True:
        tictoc_solver.tic()
        if dfas_candidate is None:
            solver = DFASolver(size, alphabet=alphabet)
            solver.add_sample(effective_sample)
            if force_sub: solver.add_dfa(dfa, sup=True, sub=False, **dfa_kwargs)
            elif force_nsup: solver.add_dfa(dfa, sub=False, **dfa_kwargs)

            dfas_candidate = solver.iter_solve_rc2(timeout=timeout-tictoc_total.tocvalue())
        
        try:
            dfa_candidate = next(dfas_candidate)
            if dfa_candidate_filename is not None:
                dfa_path = dfa_candidate_filename.format(attempt=json_stats['progress']['inferred'])
                dfa.export_dot(dfa_path, **dot_kwargs)
            json_stats['progress']['inferred'] += 1
        except TimeoutError as err:
            # print(f"Best formula before timeout: {formula}")
            raise err
        except KeyboardInterrupt as err:
            # print(f"Best formula before interruption: {formula}")
            raise err
        except StopIteration:
            if size >= start_size:
                json_stats['elapsed'][size] = dict(
                    total=tictoc_total.tocvalue(),
                    solver=time_solver,
                    ce=time_genFinite,#+time_genInfinite,
                    ce_gen=time_genFinite,#+time_genInfinite,
                    ce_gen_finite=time_genFinite,
                    # ce_gen_infinite=time_genInfinite,
                )
            size += 1
            if size > max_size: break
            logger.debug(f"trying size={size}")
            if dbg_dots: sys.stdout.write(termcolor.colored("+", color='cyan', attrs=['bold'])); sys.stdout.flush()
            dfas_candidate = None
            continue
        finally:
            time_solver += tictoc_solver.tocvalue()

        # check consistency with sample
        for i,(trace,label) in enumerate(traces): # if a trace in the sample is not consistent...
            if trace.evaluate(dfa_candidate) == label: continue
            effective_sample.append(trace, label=label) # ...ensure that it is considered
            json_stats['progress']['traces_sample'] += 1
            del traces[i]
            dfas_candidate = None
            break
        if dfas_candidate is None: continue

        # check that L(A') \subseteq L(A)
        neg_trace = None
        if force_sub: neg_trace = False # skip conterexample
        if neg_trace is None and check_finite in [True, None]: # finite trace
            tictoc_genFinite.tic()
            neg_trace = word_with_labels((dfa,dfa_candidate), (False,True))
            time_genFinite += tictoc_genFinite.tocvalue()
        if neg_trace is None and check_finite in [False, None]: # infinite trace
            raise NotImplementedError("infinite words")
        if neg_trace is not None and neg_trace is not False: # found negative counterexample
            effective_sample.append(neg_trace, label=False)
            json_stats['progress']['traces_ce'] += 1
            dfas_candidate = None
            if dbg_dots: sys.stdout.write(termcolor.colored(".", color='red', attrs=['bold'])); sys.stdout.flush()
            logger.debug(f"considering new negative counterexample")
            continue
        
        # check that L(A') \subset L(A)
        neg_trace = None
        if force_nsup: neg_trace = False # skip conterexample
        if neg_trace is None and check_finite in [True, None]: # finite trace
            tictoc_genFinite.tic()
            neg_trace = word_with_labels((dfa,dfa_candidate), (True,False))
            time_genFinite += tictoc_genFinite.tocvalue()
        if neg_trace is None and check_finite in [False, None]: # infinite trace
            raise NotImplementedError("infinite words")
        if neg_trace is not None: # found negative counterexample
            if neg_trace is not False:
                effective_sample.append(neg_trace, label=False)
                json_stats['progress']['traces_ce'] += 1
            dfa = dfa_candidate
            dfas_candidate = None
            if dbg_dots: sys.stdout.write(termcolor.colored("!", color='red', attrs=['bold'])); sys.stdout.flush()
            dfa_path = None
            if dfa_new_filename is not None:
                dfa_path = dfa_new_filename.format(attempt=json_stats['progress']['inferred'])
                dfa.export_dot(dfa_path, **dot_kwargs)
            json_stats['progress']['dfas'].append(dfa_path)
            logger.info(f"found new dfa: {dfa_path}")
            continue
        if dbg_dots: sys.stdout.write(termcolor.colored(".", color='yellow', attrs=['bold'])); sys.stdout.flush()
        # logger.debug(f"found equivalent dfa")
        logger.debug(f"found equivalent dfa")

    dfa_path = None
    if dfa_filename is not None:
        dfa_path = dfa_filename.format()
        dfa.export_dot(dfa_path, **dot_kwargs)
    logger.debug(f"returning dfa: {dfa_path}")
    json_stats['dfa'] = dfa_path
    logger.info(f"{tictoc_total.tocvalue():.3f}s elapsed ("
        f"{time_solver:.3f}s on solving, "
        f"{time_genFinite:.3f}s on generating finite counterexamples"
        ")")
    return dfa

