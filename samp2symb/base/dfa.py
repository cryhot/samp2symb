#!/usr/bin/env python3
import sys, os, io
from typing import Iterable
from graphviz import Source
import random
import itertools
# from ltlf2dfa.parser.ltlf import LTLfParser
# from .ltl import Formula

class DFA:
    def __init__(self, init_state, final_states, transitions):
        self.final_states = self.accepting_states = final_states
        self.init_state = init_state
        self.init_states = [init_state]
        self.transitions = transitions
        self.states = list(transitions.keys())
        self.alphabet = list(transitions[init_state].keys())
        self.current_state = self.init_state

        # Calculating number of words of length 0 accepted of length 0 from a state
        self.number_of_words = {(state, 0):int(state in self.final_states) for state in self.states}
        self.calculated_till = 0

    def is_word_in(self, word):
        '''
        checks if a word belongs to the language of the DFA
        '''
        state = self.init_state
        for letter in word:
            state = self.transitions[state][letter]
            
        return state in self.final_states

    def complement(self):
        '''
        returns a complement of the self object
        '''
        comp_final_states = [state for state in self.states if state not in self.final_states]
        d = DFA(self.init_state, comp_final_states, dict(self.transitions))
        return d

    def show(self, filename="test.gv"):
        '''
        Produces an image of the DFA
        '''
        dot_str =  "digraph g {\n"

        dot_str += ('__start0 [label="start" shape="none"]\n')

        for s in self.states:
            if s in self.final_states:
                shape = "doublecircle"
            else:
                shape = "circle"
            dot_str += ('{} [shape="{}" label="{}"]\n'.format(s, shape, s))

        dot_str += ('__start0 -> {}\n'.format(self.init_state))

        for s1 in self.transitions.keys():
            tran = self.transitions[s1]
            for letter in tran.keys():
                dot_str += ('{} -> {}[label="{}"]\n'.format(s1, tran[letter], letter))
        dot_str += ("}\n")
        
        s = Source(dot_str, filename=filename, format="png")
        s.view()
        

    def save(self, filename):
        with open(filename + ".dot", "w") as file:
            file.write("digraph g {\n")
            file.write('__start0 [label="" shape="none]\n')

            for s in self.states:
                if s in self.final_states:
                    shape = "doublecircle"
                else:
                    shape = "circle"
                file.write('{} [shape="{}" label="{}"]\n'.format(s, shape, s))

            file.write('__start0 -> {}\n'.format(self.init_state))

            for s1 in self.transitions.keys():
                tran = self.transitions[s1]
                for letter in tran.keys():
                    file.write('{} -> {}[label="{}"]\n'.format(s1, tran[letter], letter))
            file.write("}\n")


    def __str__(self):
        '''
        prints the dfas in a readable format
        '''
        output_str = ''
        output_str += 'Init: '+str(self.init_state) + '\n'
        output_str += 'States: '+','.join(list(map(str, self.states))) + '\n'
        output_str += 'Transitions:\n'
        for state in self.transitions:
            for letter in self.alphabet:
                output_str += str(state)+ '-'+str(letter)+'->'+str(self.transitions[state][letter])+','
            output_str += '\n'
        output_str += 'Final states: '+','.join(list(map(str,self.final_states)))
        return output_str

    def generate_all_accepting_words(self):
        '''
        returns all words that are accepted by DFA
        '''
        return self.generate_accepting_words(self.init_state)


    def generate_accepting_words(self, state):
        '''
        returns all words that are accepted by a DFA from a given state 
        '''
        all_words = []
        if state in self.final_states:
            all_words += ['']

        for letter in self.alphabet:
            successor_states = self.transitions[state][letter]

            for next_state in successor_states:
                all_words += [letter+word for word in self.generate_accepting_words(next_state)]

        return all_words

    def generate_num_accepting_words(self, length):
        '''
        Computes the number of words that are accepted of a particular length.
        Use negative lenght to compute for the shortest word lenght (which will be returned). 
        '''
        for i in range(1,self.calculated_till+1): # empty word is buggy, hence starting at 1
            if length<0 and self.number_of_words[(self.init_state,i)] > 0: return i
        for i in range(self.calculated_till+1,(length if length>=0 else len(self.states))+1):
            for state in self.states:
                self.number_of_words[(state, i)] = sum(
                    self.number_of_words[(self.transitions[state][letter], i-1)]
                    for letter in self.alphabet
                )
            self.calculated_till = i
            if length<0 and self.number_of_words[(self.init_state,i)] > 0: return i
        return i


    # def generate_random_short_word(self):
    #     '''
    #     returns a minimal random word that is accepted
    #     '''
    #     random_length = random.randint(0,100)
    #     return self.generate_random_word_length(random_length)

    def generate_random_word(self):
        '''
        returns any random word that is accepted
        '''
        random_length = random.randint(0,100)
        return self.generate_random_word_length(random_length)

    # Algorithm taken from https://link.springer.com/article/10.1007/s00453-010-9446-5
    def generate_random_word_length(self, length):
        '''
        returns a random word of a particular length that is accepted
        '''
        length = self.generate_num_accepting_words(length)

        rand_word = tuple()
        state = self.init_state
        for i in range(1,length+1):
            transition_list = []
            prob_list = []
            num_accepted_trans = self.number_of_words[(state, length-i+1)]
            if num_accepted_trans == 0: raise RuntimeError(f"no accepted word of length {length} exist")
            for letter in self.alphabet:
                # for next_state in self.transitions[state][letter]: # this code is wrong because transitions[s][l] is a SINGLE state
                for next_state in self._next_states([state], letter):
                    transition_list.append((letter, next_state))
                    prob_list.append(self.number_of_words[(next_state, length-i)]/num_accepted_trans)

            next_transition = random.choices(transition_list, weights=prob_list)[0]
            state = next_transition[1]
            
            rand_word+=(next_transition[0],)	
        return rand_word


    def generate_random_words_in_batch(self, length_range, batch_size):

        epsilon = 0.01
        
        if self.calculated_till < length_range[1]:
            self.generate_num_accepting_words(length_range[1])

        word_list = []
        last_path = [] 
        prob_dict = {}
        length_list = list(range(length_range[0], length_range[1]+1))
        valid_length = []
        for l in length_list:
            if self.number_of_words[(self.init_state,l)] != 0:
                valid_length.append(l)

        if valid_length == []:
            raise Exception('No traces with the given lengths') 

        transition_count = {}

        num=0
        for num in range(batch_size):
            
            rand_word = tuple()
            state = self.init_state
            length = random.choice(valid_length)
            
            
            for i in range(1,length+1):
                non_sink_transitions = [] #letters which lead to some accepting states
                prob_list = []
                count_list = []

                for letter in self.alphabet:
                    
                    next_state = self.transitions[state][letter]
                    
                    if (state, letter, next_state) not in transition_count:
                        transition_count[(state, letter, next_state)] = 0
                    
                    #print(next_state, self.number_of_words[(next_state, length-i)], length-i)
                    if self.number_of_words[(next_state, length-i)] != 0:
                        non_sink_transitions.append((state, letter, next_state))
                        


                    count_list.append(transition_count[(state, letter, next_state)])


                num_accepted_trans = len(non_sink_transitions)
                total_count = sum(count_list)
                
                for j in range(len(self.alphabet)):
                    next_state = self.transitions[state][self.alphabet[j]]
                    if self.number_of_words[(next_state, length-i)] != 0:
                        if num_accepted_trans == 1:
                            transition_prob = 1
                        elif total_count == 0:
                            transition_prob = (1/num_accepted_trans)
                        else:
                            transition_prob = (1/num_accepted_trans)*(1-(count_list[j]/total_count))
                    
                        prob_list.append(transition_prob)
                
                
                
                prob_list = [(i/sum(prob_list)) for i in prob_list]
    
                next_transition = random.choices(non_sink_transitions, weights=prob_list)[0]
                transition_count[next_transition] += 1
                #print("Count", transition_count)
                state = next_transition[2]
                rand_word+=(next_transition[1],)
            
            word_list.append(rand_word)	

        return word_list
    


    @classmethod
    def from_RPNI(cls, RPNI_output_file_name):
        transitions = dict()
        with open(RPNI_output_file_name) as RPNI_output_file:
            mode = "general"
            for line in RPNI_output_file:
                if "alphabet size" in line:
                    size = int(line.split("=")[1].strip().strip(';'))
                    # self.alphabet = list(range(size))
                if "number of states" in line:
                    num_states = int(line.split("=")[1].strip().strip(';'))
                    # self.states = list(range(num_states))
                if "initial states" in line:
                    mode = "init"
                    continue
                if "final states" in line:
                    mode = "final"
                    continue
                if "transitions" in line:
                    mode = "transitions"
                    continue

                if mode == "init":
                    line = line.strip().strip(';')
                    listOfStates = line.split(',')
                    init_states = [int(s) for s in listOfStates]
                    if len(init_states) > 1:
                        raise ValueError("the automaton has more than 1 initial state")

                if mode == "final":
                    line = line.strip().strip(';')
                    listOfStates = line.split(',')
                    accepting_states = list()
                    for s in listOfStates:
                        if s!= '':
                            accepting_states.append(int(s))
                    if accepting_states=='':
                        accepting_states.append(int(random.choice(range(0,51))))

                if mode == "transitions":
                    line = line.strip().strip(';')
                    transition_description = line.split(',')
                    transitions[(int(transition_description[0]), int(transition_description[1]))] = int(transition_description[2])
        
        dfa = cls(init_states[0], accepting_states, transitions)
        return dfa

    def export_as_RPNI_automaton(self, output_file=sys.stdout, *,
        keep_alphabet=False,
    ):
        if isinstance(output_file, str):
            context = output_file = open(output_file, "w")
        else:
            context = open(os.devnull,"w")
        with context:
            output_file.write('[general]\n')
            output_file.write('\tis dfa = true;\n')
            output_file.write('\talphabet size = {};\n'.format(max(self.alphabet)+1 if keep_alphabet else len(self.alphabet)))
            output_file.write('\tnumber of states = {};\n'.format(len(self.states)))
            output_file.write('[initial states]\n')
            output_file.write('\t{};\n'.format(
                ', '.join(str(self.states.index(init_state)) for init_state in self.init_states)
            ))
            output_file.write('[final states]\n')
            output_file.write('\t{};\n'.format(
                ', '.join(str(self.states.index(accepting_state)) for accepting_state in self.accepting_states)
            ))
            output_file.write('[transitions]\n')
            for (state_from,letter),state_to in self.transitions.items():
                output_file.write('\t{}, {}, {};\n'.format(
                    self.states.index(state_from),
                    letter if keep_alphabet else self.alphabet.index(letter),
                    self.states.index(state_to),
                ))

    def export_dot(self, output_file=sys.stdout, *,
        keep_states=True, keep_alphabet=True,
        group_separator=r'\n',
    ):
        """
            :param group_separator: if set, group transitions between same pair of states. Usually set to ';' or r'\n'.
            :type group_separator: str or None
        """
        if isinstance(output_file, str):
            context = output_file = open(output_file, "w")
        else:
            context = open(os.devnull,"w")
        with context:
            """
                inspiration from:
                src/automata_learning_utils/lib_RPNI/libalf/src/conjecture.cpp
                line 448: string finite_automaton::visualize()
            """

            # head
            output_file.write('digraph finite_automaton {\n')
            output_file.write('\tgraph[fontsize=8];\n')
            output_file.write('\trankdir=LR;\n')
            output_file.write('\tsize=8;\n\n')

            # mark final states
            header_written = False
            final_state_count = 0
            const_iterator = {}

            if not keep_states:
                # final states
                if (len(self.accepting_states) > 0):
                    output_file.write('\tnode [shape=doublecircle, style="", color=black];')
                    for q,state in enumerate(self.states):
                        if state not in self.accepting_states: continue
                        output_file.write(' q{}'.format(q))
                    output_file.write(';\n')
                # normal states
                if (len(self.accepting_states) < len(self.states)):
                    output_file.write('\tnode [shape=circle, style="", color=black];')
                    for q,state in enumerate(self.states):
                        if state in self.accepting_states: continue
                        output_file.write(' q{}'.format(q))
                    output_file.write(';\n')
            else:
                # states
                for q,state in enumerate(self.states):
                    shape = 'doublecircle' if state in self.accepting_states else 'circle'
                    output_file.write('\tnode [shape={}, label="{}", style="", color=black]; q{};\n'.format(
                        shape,
                        state,
                        q,
                    ))

            # non-visible states for arrows to initial states
            if (len(self.init_states) > 0):
                output_file.write('\tnode [shape=plaintext, label="", style=""];')
                for iq,init_state in enumerate(self.init_states):
                    output_file.write(' iq{}'.format(iq))
                output_file.write(';\n')

            # and arrows to mark initial states
            for iq,init_state in enumerate(self.init_states):
                output_file.write('\tiq{} -> q{} [color=blue];\n'.format(
                    iq,
                    self.states.index(init_state)
                ))

            # transitions
            if group_separator is None:
                # for (state_from,letter),state_to in self.transitions.items():
                for state_from,trans in self.transitions.items():
                    for letter,state_to in trans.items():
                        output_file.write('\tq{} -> q{} [label="{}"];\n'.format(
                            self.states.index(state_from),
                            self.states.index(state_to),
                            letter if keep_alphabet else self.alphabet.index(letter),
                        ))
            else:
                grouped_transitions = {}
                # for (state_from,letter),state_to in self.transitions.items():
                for state_from,trans in self.transitions.items():
                    for letter,state_to in trans.items():
                        grouped_transitions.setdefault((state_from,state_to), set())
                        grouped_transitions[(state_from,state_to)].add(letter)
                for (state_from,state_to),letters in grouped_transitions.items():
                    # print((state_from,state_to,letter))
                    output_file.write('\tq{} -> q{} [label="{}"];\n'.format(
                        self.states.index(state_from),
                        self.states.index(state_to),
                        group_separator.join(
                            "{}".format(letter if keep_alphabet else self.alphabet.index(letter))
                            for letter in sorted(letters, key=lambda l: self.alphabet.index(l))
                        ),
                    ))

            # end
            output_file.write('}\n')

    def graphviz(self, filename=None, *args, **kwargs):
        """
            Useful in jupyter notebooks!
            See also self.export_dot(*args, **kwargs).
        """
        import io
        import graphviz
        source = io.StringIO()
        self.export_dot(source, *args, **kwargs)
        gv = graphviz.Source(source.getvalue(), filename=filename)
        if filename: gv.save()
        return gv

    def _repr_svg_(self, *args, **kwargs):
        return self.graphviz(
            keep_alphabet=True,
            group_separator=";",
        )._repr_svg_(*args, **kwargs)

    def size(self):
        return len(self.states)

    def _states(self):
        return set(self.states)

    def _initial_states(self):
        return set(self.init_states)

    def _terminal_states(self):
        return set(self.accepting_states)

    def _next_states(self, states, letter):
        # return set(self.transitions[(state,letter)] for state in states)
        return set(self.transitions[state][letter] for state in states)

    def test_word(self, word):
        current_states = self._initial_states()
        for letter in word:
            current_states = self._next_states(current_states,letter)
        return len(current_states & self._terminal_states()) != 0

    # def __str__(self):
    #     writer = io.StringIO()
    #     self.export_as_RPNI_automaton(writer)
    #     return writer.getvalue()
    def __contains__(self, word):
        return self.test_word(word)
    
    @classmethod
    def from_aalpy(cls, dfa):
        import aalpy.automata
        assert isinstance(dfa, aalpy.automata.Dfa)

        init_state = dfa.states.index(dfa.initial_state)
        final_states = [
            dfa.states.index(state)
            for state in dfa.states
            if state.is_accepting
        ]
        transitions = {
            dfa.states.index(s1): {
                l: dfa.states.index(s2)
                for l,s2 in s1.transitions.items()
            }
            for s1 in dfa.states
        }
        
        result = cls(init_state, final_states, transitions)
        return result
    
    def to_aalpy(self):
        import aalpy.automata
        # states = []
        s2state = {}
        for s in self.states:
            state = aalpy.automata.DfaState(s, s in self.final_states)
            # states.append(state)
            s2state[s] = state
        for s,state in s2state.items():
            state.transitions = {
                l: s2state[s2]
                for l,s2 in self.transitions[s].items()
            }
        dfa = aalpy.automata.Dfa(
            initial_state=s2state[self.init_state],
            states=list(s2state.values()),
        )
        return dfa



def atom2letters(atom_string, letter2pos, is_word):
    # preprocessing of atom strings
    atom_string = atom_string.replace(' ' ,'')

    alphabet = list(letter2pos.keys())

    atomlist = atom_string.split('|')
    all_letter_list= set()
    for atom_disjuncts in atomlist:
        sign = {letter:0 for letter in alphabet}
        if atom_string != 'true':
            atoms = atom_disjuncts.split('&')
            for prop in atoms:
                if prop[0]=='~':
                    sign[prop[1]] = -1
                else:
                    sign[prop[0]] = 1
        letter_list = [[]]
        for letter in alphabet:
            new_letter_list = []
            if sign[letter] == 0:
                for l in letter_list:
                    new_letter_list.append(l+[0])
                    new_letter_list.append(l+[1])
            
            if sign[letter] == 1:
                for l in letter_list:
                    new_letter_list.append(l+[1])

            if sign[letter] == -1:
                for l in letter_list:
                    new_letter_list.append(l+[0])
            letter_list = new_letter_list

        letter_list = set([tuple(l) for l in letter_list])
        all_letter_list= all_letter_list.union(letter_list)
    
    return list(all_letter_list)


def atom2letters_new(atom_string, letter2pos, is_word):
    from ltlf2dfa.parser.ltlf import LTLfParser
    
    alphabet = list(letter2pos.keys())
    
    all_letters = set([tuple()])
    for atom in alphabet:
        new_all_letters = {letter+(0,) for letter in all_letters}			
        new_all_letters = new_all_letters.union({letter+(1,) for letter in all_letters})
        all_letters = new_all_letters

    if is_word:
        all_letters = {i for i in all_letters if sum(i)==1}

    if atom_string == 'true':
        
        return all_letters

    if atom_string == 'false':

        no_letters = []
        return no_letters

    parser = LTLfParser()
    atom_formula = parser(atom_string)
    t = (atomformula2letters(atom_formula, letter2pos, all_letters, is_word))
    return t


def atomformula2letters(atom_formula, letter2pos, all_letters, is_word):

    try:
        op = atom_formula.operator_symbol
        if op == '&':
            letter_set = all_letters
            for child_atom in atom_formula.formulas:
                l = atomformula2letters(child_atom, letter2pos, all_letters, is_word)
                letter_set = letter_set.intersection(l)
            

        elif op == '|':
            letter_set = set()
            for child_atom in atom_formula.formulas:
                l = atomformula2letters(child_atom, letter2pos, all_letters, is_word)
                letter_set = letter_set.union(l)

        
        elif op == '!':
            child_atom = atom_formula.f
            l = atomformula2letters(child_atom, letter2pos, all_letters, is_word)
            letter_set = all_letters.difference(l)
            

    except:
        alphabet = list(letter2pos.keys())
        atom_list = atom_formula.find_labels()
        assert(len(atom_list)==1)
        letter_set = set([tuple()])
        for atom in alphabet:
            new_letter_set = set()
            if atom in atom_list:
                new_letter_set = new_letter_set.union({letter+(1,) for letter in letter_set})
            else:
                new_letter_set = new_letter_set.union({letter+(0,) for letter in letter_set})			
                new_letter_set = new_letter_set.union({letter+(1,) for letter in letter_set})
            letter_set = new_letter_set
        if is_word:
            letter_set = {i for i in letter_set if sum(i)==1}
    return letter_set



def ltl2dfa(formula, letter2pos, is_word):
    """convert formula into formulastring
    possiblilties to use the infix or the prefix form"""
    from ltlf2dfa.parser.ltlf import LTLfParser

    formula_str = formula.prettyPrint()

    parser = LTLfParser()
    
    formula = parser(formula_str) # returns an LTLfFormula

    #d = atom2letters(alphabet = alphabet)
    original_dfa = formula.to_dfa() #using atoms
    return dot2DFA(original_dfa, letter2pos=letter2pos, is_word=is_word)
    
    # create a map from propostitions to the corresponding digits



def dot2DFA(dot_string, *, letter2pos=None, is_word, group_separator=None):

    if isinstance(dot_string,io.TextIOBase):
        dot_string = dot_string.read()

    dfa_info = dot_string.split('\n')
    mode = ''
    transitions = {}
    for line in dfa_info:
        
        if line == '}':
            break

        if 'doublecircle' in line:
            line = line.split(']')[1]
            line = line.replace(' ', '')
            final_states = line.split(';')[1:-1]

        if '->' in line and mode != 'transitions':
            line = line.replace(' ', '')
            init_state = line.split('->')[1][:-1]
            mode = 'transitions'
            continue
        
        if mode == 'transitions':
            edge, label_info = line.split('[')

            edge = edge.replace(' ', '')
            first_state, second_state = edge.split('->')

            label = label_info.split('\"')[1]
            if letter2pos is not None:
                letters = atom2letters_new(label, letter2pos, is_word)
            elif group_separator is not None:
                letters = label.split(group_separator)
            else:
                letters = [label]
            if first_state == '3':
                #print(label, letters)
                pass
            for letter in letters:
                try:
                    transitions[first_state][letter] = second_state
                except:
                    transitions[first_state] = {letter:second_state}


    formula_dfa = DFA(init_state, final_states, transitions)

    return formula_dfa

#letter2pos = {'p':0, 'q':1, 'r':2, 's':3}
#print(atom2letters_new('~p & ~r', letter2pos))

# dfa = (ltl2dfa('dummy', letter2pos))
# dfa_c = dfa.complement()
# print(dfa_c)
# dfa_c.show()
# print(dfa_c.generate_random_word_length(10))
#print(str(dfa))

# ltl = "|(X(X(q)),&(F(p),X(q)))"
# f = Formula().convertTextToFormula(ltl)
# letter2pos = {'p':0, 'q':1}
# dfa = ltl2dfa(f, letter2pos)
# dfa1 = dfa.complement()

# # print("Started")
# l= dfa1.generate_random_words_in_batch((10,15), 100000)
# # print("Ended")
# for word in l:
#  	if dfa.is_word_in(word):
#  		print(word)

#dfa = DFA(1, [2], {1:{'a':2, 'b':2, 'c':1}, 2:{'a':1, 'b':3, 'c':3}, 3:{'a':3, 'b':3, 'c':3}})
#dfa.show()


def iter_prod(*dfas:Iterable[DFA]):
    "iterate over all reachable states of the product automata, returning the shortest word to reach each such state."
    alphabet = dfas[0].alphabet
    word = []
    queue = [
        (word, states)
        for states in itertools.product(*(dfa._initial_states() for dfa in dfas))
    ]
    visited = set()
    while queue:
        word, states = queue.pop(0)
        yield word, states
        for letter in alphabet:
            word2 = word + [letter]
            for states2 in itertools.product(*(dfa._next_states([state],letter) for dfa,state in zip(dfas,states))):
                if states2 in visited: continue
                visited.add(states2)
                queue.append((word2,states2))

def word_with_labels(dfas:Iterable[DFA], labels):
    """return a word in the product dfa which has the desired labels."""
    for word, states in iter_prod(*dfas):
        l = tuple(state in dfa._terminal_states() for dfa, state in zip(dfas, states))
        if l != labels: continue
        return word
    return None