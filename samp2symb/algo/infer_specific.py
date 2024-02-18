#!/usr/bin/env python3

import sys
import contextlib
import logging
import termcolor
import copy

from ..utils.timer import TimeKeeper


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
    from samp2symb.base.dfa import iter_prod
    logger = logging.getLogger("LTL-finder")
    timekeeper = TimeKeeper()
    def elapsed_summary():
        return (f"{timer_total.elapsed:.3f}s elapsed ("
            f"{timekeeper['solver'].elapsed:.3f}s on solving, "
            f"{timekeeper['ce_trans'].elapsed:.3f}s on translating formulas to DFA/Buchi Automata, "
            f"{timekeeper['ce_gen'].elapsed:.3f}s on generating finite/infinite counterexamples"
            ")")
    with timekeeper['total'] as timer_total:
        try:
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
            else: assert sample.positive.isFormulaConsistent(formula), "formula is not consistant with the positive traces"

            # prepare variables
            trace1 = next(iter(sample))
            literals = trace1.literals
            effective_sample = sample.copy()
            traces = []
            effective_force_nsup = force_nsup
            if grow_sample:
                effective_sample.clear()
                traces = sorted(((trace,label) for trace,label in sample.items()), key=lambda x: len(x[0].vector))
            size = start_size-1
            formulas_candidate = iter(())
            formula_kwargs = dict(check_horizon=check_horizon, check_finite=check_finite)
            logger.info(f"considering sample: {sample.summary()}")

            # populate json_stats
            if json_stats is None: json_stats = dict()
            json_stats.setdefault('method', dict()).update(
                force_sub=force_sub,
                force_nsup=force_nsup,
                requires_QASP=force_sub, # assuming that
                check_finite=check_finite in [True, None],
                check_infinite=check_finite in [False, None],
            )
            if check_horizon<float('inf') and (force_sub or force_nsup):
                json_stats['method'].update(check_horizon=check_horizon)
            if timeout<float('inf'):
                json_stats['method'].update(timeout=timeout)
            json_stats.setdefault('sample', dict()).update(sample.json_summary())
            json_stats.setdefault('results', dict()).update(
                sat=0, unsat=0, # count of solver calls
                formulas=[], # more and more specific inferred formulas
                traces_sample = len(effective_sample), # used sample traces
                traces_ce = 0, # generated counter-example traces
                # elapsed = timekeeper.elapsed,
            )
            json_stats.setdefault('iterations', dict())
            if sample.negative.isFormulaConsistent(formula):
                json_stats['results']['formulas'].append(formula.prettyPrint())

            while True:

                with timekeeper['solver']:
                    if formulas_candidate is None:
                        solver = LTLSolver(size=size, atoms=literals)
                        solver.add_sample(effective_sample)
                        if force_sub or effective_force_nsup:
                            solver.add_formula(formula,
                                sup=True  if force_sub  else None,
                                sub=False if effective_force_nsup else None,
                                **formula_kwargs,
                            )
                        if program_file is not None:
                            path=program_file.format()
                            with open(path, 'w') as fp: fp.write(str(solver))

                        if solver.requires_QASP:
                            assert effective_force_nsup, "we supposed that there will be progress in 1 iteration"
                            formulas_candidate = filter((lambda f: f is not None), (solver.solve_qbf(timeout=timeout-timer_total.elapsed),))
                        else:
                            formulas_candidate = solver.iter_solve_asp(timeout=timeout-timer_total.elapsed)
                    
                    try:
                        formula_candidate = next(formulas_candidate)
                        json_stats['results']['sat'] += 1
                    except TimeoutError as err:
                        logger.info(f"TIMED OUT: {elapsed_summary()}")
                        logger.debug(f"Best formula before timeout: {formula.prettyPrint()}")
                        raise err
                    except KeyboardInterrupt as err:
                        logger.info(f"INTERRUPTED: {elapsed_summary()}")
                        logger.debug(f"Best formula before interruption: {formula.prettyPrint()}")
                        raise err
                    except StopIteration:
                        # # enforce language-minimality
                        # if effective_force_nsup and check_horizon<2**(2**size+2**formula.size): # relax problem to find longer counter-examples
                        #     json_stats['results']['unsat'] += 1
                        #     effective_force_nsup = False
                        #     if dbg_dots: sys.stdout.write(termcolor.colored("~", color='cyan', attrs=['bold'])); sys.stdout.flush()
                        #     logger.debug(f"trying to find counterexamples longer than horizon: force_nsup={effective_force_nsup}")
                        #     formulas_candidate = None; continue
                        with timekeeper[:].exclude:
                            if size >= start_size:
                                json_stats['results']['unsat'] += 1
                                json_stats['results']['elapsed'] = timekeeper.elapsed
                                json_stats['iterations'][str(size)] = copy.deepcopy(json_stats['results'])
                        size += 1
                        if size > max_size: break
                        effective_force_nsup = force_nsup
                        with timekeeper[:].exclude:
                            if dbg_dots: sys.stdout.write(termcolor.colored("+", color='cyan', attrs=['bold'])); sys.stdout.flush()
                            logger.debug(f"trying size={size}")
                        formulas_candidate = None; continue

                # check consistency with sample
                with timekeeper['sample']:
                    for i,(trace,label) in enumerate(traces): # if a trace in the sample is not consistent...
                        if trace.evaluate(formula_candidate) == label: continue
                        effective_sample.append(trace, label=label) # ...ensure that it is considered
                        json_stats['results']['traces_sample'] += 1
                        if dbg_dots: sys.stdout.write(termcolor.colored(".", color='green', attrs=['bold'])); sys.stdout.flush()
                        logger.debug(f"considering new {['negative','positive'][label]} example from the sample")
                        del traces[i]
                        formulas_candidate = None; break
                    if formulas_candidate is None: continue

                # check that L(A') \subseteq L(A)
                neg_trace = None
                if force_sub and check_horizon>=2**(2**size+2**formula.size): neg_trace = False # skip conterexample
                # if neg_trace is None:
                #     with timekeeper['ce']:
                #         neg_trace = (~(formula_candidate >> formula)).accepting_word(finite=check_finite, literals=literals)
                # if neg_trace is None:
                #     with timekeeper['ce']:
                #         neg_trace = formula_candidate.intersecting_word(~formula, finite=check_finite, literals=literals)
                if neg_trace is None and check_finite in [True, None]: # finite trace
                    with timekeeper['ce', 'ce_trans', 'ce_trans_finite']:
                        a = (~(formula_candidate >> formula)).to_dfa(literals)
                    with timekeeper['ce', 'ce_gen', 'ce_gen_finite']:
                        # neg_trace = tuple(a.accepting_word())
                        try:
                            neg_trace = next(
                                word
                                for state, word in iter_prod(a, labels=(True,))
                                if len(word) > 0  # search for non empty word
                            )
                        except StopIteration:
                            neg_trace = None
                        if neg_trace is not None: neg_trace = PropTrace(neg_trace, literals=literals, intendedEvaluation=False)
                if neg_trace is None and check_finite in [False, None]: # infinite trace
                    with timekeeper['ce', 'ce_trans', 'ce_trans_infinite']:
                        a1, a2 = formula_candidate.to_spot().translate(), (~formula).to_spot().translate()
                    with timekeeper['ce', 'ce_gen', 'ce_gen_infinite']:
                        neg_trace = a1.intersecting_word(a2)
                        if neg_trace is not None: neg_trace = PropTrace.from_spot(neg_trace, literals)
                if neg_trace is not None and neg_trace is not False: # found negative counterexample
                    with timekeeper[:].exclude:
                        if dbg_dots: sys.stdout.write(termcolor.colored(".", color='red', attrs=['bold'])); sys.stdout.flush()
                        logger.debug(f"considering new negative counterexample")
                    if neg_trace is not False:
                        if neg_trace in effective_sample:
                            # logger.warning(f"counterexample already considered!")
                            logger.warning(f"counterexample already considered! {neg_trace.dumps()}")
                        effective_sample.append(neg_trace, label=False)
                        json_stats['results']['traces_ce'] += 1
                    formulas_candidate = None; continue
                
                # check that L(A') \subset L(A)
                neg_trace = None
                if effective_force_nsup: neg_trace = False # skip conterexample
                # if neg_trace is None:
                #     with timekeeper['ce']:
                #         neg_trace = (~(formula >> formula_candidate)).accepting_word(finite=check_finite, literals=literals)
                # if neg_trace is None:
                #     with timekeeper['ce']:
                #         neg_trace = formula.intersecting_word(~formula_candidate, finite=check_finite, literals=literals)
                if neg_trace is None and check_finite in [True, None]: # finite trace
                    with timekeeper['ce', 'ce_trans', 'ce_trans_finite']:
                        a = (~(formula >> formula_candidate)).to_dfa(literals)
                    with timekeeper['ce', 'ce_gen', 'ce_gen_finite']:
                        # neg_trace = tuple(a.accepting_word())
                        try:
                            neg_trace = next(
                                word
                                for state, word in iter_prod(a, labels=(True,))
                                if len(word) > 0  # search for non empty word
                            )
                        except StopIteration:
                            neg_trace = None
                        if neg_trace is not None: neg_trace = PropTrace(neg_trace, literals=literals, intendedEvaluation=False)
                if neg_trace is None and check_finite in [False, None]: # infinite trace
                    with timekeeper['ce', 'ce_trans', 'ce_trans_finite']:
                        a1, a2 = formula.to_spot().translate(), (~formula_candidate).to_spot().translate()
                    with timekeeper['ce', 'ce_gen', 'ce_gen_finite']:
                        neg_trace = a1.intersecting_word(a2)
                        if neg_trace is not None: neg_trace = PropTrace.from_spot(neg_trace, literals)
                if neg_trace is not None: # found negative counterexample
                    formula = formula_candidate
                    with timekeeper[:].exclude:
                        if dbg_dots: sys.stdout.write(termcolor.colored("!", color='red', attrs=['bold'])); sys.stdout.flush()
                        json_stats['results']['formulas'].append(formula.prettyPrint())
                        logger.info(f"found new formula: {formula.prettyPrint()}")
                    if neg_trace is not False:
                        if neg_trace in effective_sample:
                            logger.warning(f"counterexample already considered!")
                        effective_sample.append(neg_trace, label=False)
                        json_stats['results']['traces_ce'] += 1
                    formulas_candidate = None; continue
                
                with timekeeper[:].exclude:
                    if dbg_dots: sys.stdout.write(termcolor.colored(".", color='yellow', attrs=['bold'])); sys.stdout.flush()
                    # logger.debug(f"found equivalent formula")
                    logger.debug(f"found equivalent formula: {formula.prettyPrint()} <=> {formula_candidate.prettyPrint()}")

            logger.info(f"{elapsed_summary()}")
            logger.debug(f"returning formula: {formula.prettyPrint()}")
            return formula
        finally:
            json_stats['results']['elapsed'] = timekeeper.elapsed


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
    timekeeper = TimeKeeper()
    def elapsed_summary():
        return (f"{timer_total.elapsed:.3f}s elapsed ("
            f"{timekeeper['solver'].elapsed:.3f}s on solving, "
            f"{timekeeper['ce_gen'].elapsed:.3f}s on generating finite counterexamples"
            ")")
    with timekeeper['total'] as timer_total:
        try:
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
                assert all(dfa.is_word_in(trace)==label for trace,label in sample.positive.items()), "DFA is not consistant with the positive traces"

            # prepare variables
            trace1 = next(iter(sample))
            effective_sample = sample.copy()
            traces = []
            if grow_sample:
                effective_sample.clear()
                traces = sorted(((trace,label) for trace,label in sample.items()), key=lambda x: len(x[0].vector))
            size = start_size-1
            dfas_candidate = iter(())
            # dfa_kwargs = dict(check_finite=check_finite)
            dfa_kwargs = dict()
            logger.info(f"considering sample: {sample.summary()}")

            # populate json_stats
            if json_stats is None: json_stats = dict()
            json_stats.setdefault('method', dict()).update(
                force_sub=force_sub,
                force_nsup=force_nsup,
                check_finite=check_finite in [True, None],
                # check_infinite=check_finite in [False, None],
            )
            if timeout<float('inf'):
                json_stats['method'].update(timeout=timeout)
            json_stats.setdefault('sample', dict()).update(sample.json_summary())
            json_stats.setdefault('results', dict()).update(
                sat=0, unsat=0, # count of solver calls
                dfas=[], # more and more specific inferred dfas
                traces_sample = len(effective_sample), # used sample traces
                traces_ce = 0, # generated counter-example traces
                # elapsed = timekeeper.elapsed,
            )
            json_stats.setdefault('iterations', dict())
            dot_kwargs=dict(keep_alphabet=True, group_separator=";")

            dfa_path = None
            if dfa_new_filename is not None:
                dfa_path = dfa_new_filename.format(attempt=json_stats['results']['sat'])
                assert dfa_path.endswith(".dot")
                with contextlib.redirect_stdout(None): dfa.to_aalpy().save(dfa_path[:-4])
                # dfa.export_dot(dfa_path, **dot_kwargs)
            if all(dfa.is_word_in(trace)==label for trace,label in sample.negative.items()):
                json_stats['results']['dfas'].append(dfa_path)

            while True:

                with timekeeper['solver']:
                    if dfas_candidate is None:
                        solver = DFASolver(size, alphabet=alphabet)
                        solver.add_sample(effective_sample)
                        if force_sub or force_nsup:
                            solver.add_dfa(dfa,
                                sup=True  if force_sub  else None,
                                sub=False if force_nsup else None,
                                **dfa_kwargs,
                            )

                        dfas_candidate = solver.iter_solve_rc2(timeout=timeout-timer_total.elapsed)
                    
                    try:
                        dfa_candidate = next(dfas_candidate)
                        with timekeeper[:].exclude:
                            dfa_path = None
                            if dfa_candidate_filename is not None:
                                dfa_path = dfa_candidate_filename.format(attempt=json_stats['results']['sat'])
                                assert dfa_path.endswith(".dot")
                                with contextlib.redirect_stdout(None): dfa_candidate.to_aalpy().save(dfa_path[:-4])
                                # dfa_candidate.export_dot(dfa_path, **dot_kwargs)
                            json_stats['results']['sat'] += 1
                    except TimeoutError as err:
                        # print(f"Best formula before timeout: {formula}")
                        logger.info(f"TIMED OUT: {elapsed_summary()}")
                        raise err
                    except KeyboardInterrupt as err:
                        # print(f"Best formula before interruption: {formula}")
                        logger.info(f"INTERRUPTED: {elapsed_summary()}")
                        raise err
                    except StopIteration:
                        with timekeeper[:].exclude:
                            if size >= start_size:
                                json_stats['results']['unsat'] += 1
                                json_stats['results']['elapsed'] = timekeeper.elapsed
                                json_stats['iterations'][str(size)] = copy.deepcopy(json_stats['results'])
                        size += 1
                        if size > max_size: break
                        with timekeeper[:].exclude:
                            if dbg_dots: sys.stdout.write(termcolor.colored("+", color='cyan', attrs=['bold'])); sys.stdout.flush()
                            logger.debug(f"trying size={size}")
                        dfas_candidate = None; continue

                # check consistency with sample
                with timekeeper['sample']:
                    for i,(trace,label) in enumerate(traces): # if a trace in the sample is not consistent...
                        if trace.evaluate(dfa_candidate) == label: continue
                        effective_sample.append(trace, label=label) # ...ensure that it is considered
                        json_stats['results']['traces_sample'] += 1
                        if dbg_dots: sys.stdout.write(termcolor.colored(".", color='green', attrs=['bold'])); sys.stdout.flush()
                        del traces[i]
                        dfas_candidate = None; break
                    if dfas_candidate is None: continue

                # check that L(A') \subseteq L(A)
                neg_trace = None
                if force_sub: neg_trace = False # skip conterexample
                if neg_trace is None and check_finite in [True, None]: # finite trace
                    with timekeeper['ce', 'ce_gen', 'ce_gen_finite']:
                        neg_trace = dfa_candidate.intersecting_word(~dfa)
                if neg_trace is None and check_finite in [False, None]: # infinite trace
                    raise NotImplementedError("infinite words")
                if neg_trace is not None and neg_trace is not False: # found negative counterexample
                    with timekeeper[:].exclude:
                        if dbg_dots: sys.stdout.write(termcolor.colored(".", color='red', attrs=['bold'])); sys.stdout.flush()
                        logger.debug(f"considering new negative counterexample")
                    if neg_trace is not False:
                        if neg_trace in effective_sample:
                            logger.warning(f"counterexample already considered!")
                        effective_sample.append(neg_trace, label=False)
                        json_stats['results']['traces_ce'] += 1
                    dfas_candidate = None; continue
                
                # check that L(A') \subset L(A)
                neg_trace = None
                if force_nsup: neg_trace = False # skip conterexample
                if neg_trace is None and check_finite in [True, None]: # finite trace
                    with timekeeper['ce', 'ce_gen', 'ce_gen_finite']:
                        neg_trace = dfa.intersecting_word(~dfa_candidate)
                if neg_trace is None and check_finite in [False, None]: # infinite trace
                    raise NotImplementedError("infinite words")
                if neg_trace is not None: # found negative counterexample
                    dfa = dfa_candidate
                    with timekeeper[:].exclude:
                        if dbg_dots: sys.stdout.write(termcolor.colored("!", color='red', attrs=['bold'])); sys.stdout.flush()
                        if dfa_new_filename is not None:
                            dfa_path = dfa_new_filename.format(attempt=json_stats['results']['sat'])
                            assert dfa_path.endswith(".dot")
                            with contextlib.redirect_stdout(None): dfa.to_aalpy().save(dfa_path[:-4])
                            # dfa.export_dot(dfa_path, **dot_kwargs)
                        json_stats['results']['dfas'].append(dfa_path)
                        logger.info(f"found new dfa: {dfa_path}")
                    if neg_trace is not False:
                        if neg_trace in effective_sample:
                            logger.warning(f"counterexample already considered!")
                        effective_sample.append(neg_trace, label=False)
                        json_stats['results']['traces_ce'] += 1
                    dfas_candidate = None; continue
                
                with timekeeper[:].exclude:
                    if dbg_dots: sys.stdout.write(termcolor.colored(".", color='yellow', attrs=['bold'])); sys.stdout.flush()
                    # logger.debug(f"found equivalent dfa")
                    logger.debug(f"found equivalent dfa")

            dfa_path = None
            if dfa_filename is not None:
                dfa_path = dfa_filename.format()
                assert dfa_path.endswith(".dot")
                with contextlib.redirect_stdout(None): dfa.to_aalpy().save(dfa_path[:-4])
                # dfa.export_dot(dfa_path, **dot_kwargs)
            logger.debug(f"returning dfa: {dfa_path}")
            logger.info(f"{elapsed_summary()}")
            if dfa_path is not None: logger.debug(f"returning dfa: {dfa}")
            return dfa
        finally:
            json_stats['results']['elapsed'] = timekeeper.elapsed

