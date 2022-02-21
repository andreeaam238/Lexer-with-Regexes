import codecs
import re
from typing import Dict, List


# State in the DFA - I have used a class as suggested on ppcarte.
class State:
    def __init__(self, state_idx):
        self.stateIdx = state_idx

    # As suggested in the DFA laboratory on ppcarte I'm defining a hash-function in order to use dictionaries over
    # states consisting of the hashing of the state's index.
    def __hash__(self):
        return hash(self.stateIdx)

    # In order to compare two states by their indices I have overridden the eq method.
    def __eq__(self, other):
        return self.stateIdx == State(other).stateIdx

    # For easier printing I have also overridden the str method to return the State's index.
    def __str__(self):
        return str(self.stateIdx)

    # Compare two States by their indexes.
    def __lt__(self, other):
        return self.stateIdx < other.stateIdx


# Configuration - tuple of State and string.
Conf = (State, str)


# The DFA.
class DFA:
    def __init__(self):
        self.name: str
        self.alphabet: set[str] = set()
        self.initialState: State = None
        self.delta: Dict[int, Dict[str, State]] = dict()
        self.states: set[State] = set()
        self.finalStates: set[State] = set()
        self.sinkStates: set[State] = set()

    def compute_sink_states(self):
        reversed_delta: Dict[int, Dict[str, List[State]]] = dict()

        for state in self.states:
            reversed_delta[hash(state)] = dict()

        for initial_state in self.delta.keys():
            for key in self.delta[initial_state].keys():
                if key in reversed_delta[hash(self.delta[initial_state][key])]:
                    reversed_delta[hash(self.delta[initial_state][key])][key].append(initial_state)
                else:
                    reversed_delta[hash(self.delta[initial_state][key])][key] = [initial_state]

        reachable_states = set()
        for state in self.finalStates:
            reachable_states = reachable_states | self.bfs(state, reversed_delta)

        self.sinkStates = self.sinkStates | (self.states - reachable_states)

    # BFS
    @staticmethod
    def bfs(src: State, reversed_delta: Dict[int, Dict[str, State]]):
        # States left to visit
        states = [src]

        # States visited
        visited = [src]

        # Reachable states
        accessible_states = set()
        accessible_states.add(src)

        # Check all the states that can be reached.
        while len(states):
            state = states.pop(0)

            # If it isn't a self-transition add it to the accesible states.
            if hash(src) != hash(state):
                accessible_states.add(state)

            # Check if the state is in the dictionary.
            if hash(state) in reversed_delta:
                # Check the transitions on each Character (key).
                for key in reversed_delta[hash(state)].keys():
                    # Check all the transitions on the current Character.
                    for adj in reversed_delta[hash(state)][key]:

                        # If it hasn't been visited already then add it to the
                        # list to visit and mark it as visited.
                        if adj not in visited:
                            visited.append(adj)
                            states.append(adj)

        return accessible_states

    # Execute one step on a Configuration.
    def step(self, conf: Conf) -> Conf:
        # I'm using repr in order not to hardcode the '\n' character.
        char = conf[1][0]

        # Check if there is any transition on the current Character from the
        # Current State in the dictionary.

        # If there isn't then the DFA will reach a Sink State, else it will
        # reach the corresponding Next State.
        if hash(conf[0]) not in self.delta or char not in self.delta[hash(conf[0])]:
            new_state = list(self.sinkStates)[0]
        else:
            new_state = self.delta[hash(conf[0])][char]

        return new_state, conf[1][1:]

    # Check if a word is accepted by the DFA (not used in the current version).
    def accept(self, word: str) -> bool:
        cur_state = self.initialState

        # Execute one step and check if a Sink State has been reached.
        while word != "":
            if cur_state in self.sinkStates:
                break
            cur_state, word = self.step((cur_state, word))

        # Check if a Final State has been reached.
        for state in self.finalStates:
            if state == cur_state:
                return True

        return False

    # Function for printing a DFA.
    def print_dfa(self):
        # Print the Alphabet
        for char in self.alphabet:
            print(char, end='')
        print()

        # Print the Number of States.
        print(len(self.states))

        # Print the Initial State.
        print(self.initialState)

        # Print the Final States
        for state in self.finalStates:
            print(state, end=' ')
        print()

        # Print the DFA's Transitions.
        for state in self.states:
            for key in self.delta[hash(state)].keys():
                print(str(state) + ",'" + key + "'," + str(self.delta[hash(state)][key]))


# The NFA.
class NFA:
    def __init__(self):
        self.alphabet: set[str] = set()
        self.initialState: State = None
        self.delta: Dict[int, Dict[str, List[State]]] = dict()
        self.finalStates: set[State] = set()
        self.states: set[State] = set()

    # Function for printing an NFA.
    def print_nfa(self):
        # Print the Alphabet.
        for char in sorted(self.alphabet):
            print(char, end='')
        print()

        # Print the number of States.
        print(len(self.states))

        # Print the Initial State.
        print(self.initialState)

        # Print the Final States.
        for state in self.finalStates:
            print(state, end=' ')
        print()

        # Print the NFA's Transitions.
        for state in self.states:
            if hash(state) in self.delta:
                for key in self.delta[hash(state)].keys():
                    for next_state in self.delta[hash(state)][key]:
                        print(str(state) + ",'" + key + "'," + str(next_state))

    # Function for computing an NFA's Epsilon Closures.
    def get_epsilon_closures(self):
        # Store the closures as a dictionary(State, List[State])
        epsilon_closures = dict()

        # Compute each state's closure.
        for state in self.states:
            # State's to visit.
            to_visit = [state]

            # The Closure.
            closure = [state]

            # Already visited States.
            visited = set()

            # While there are still states that should be visited:
            while len(to_visit) > 0:
                next_state = to_visit.pop()

                # If it has already been visited move to the next one.
                if next_state in visited:
                    continue

                visited.add(next_state)

                if hash(next_state) in self.delta:
                    # Check if the state has epsilon transitions.
                    if "ε" in self.delta[hash(next_state)].keys():
                        # Add the destination states to the closure and to the list of states to visit.
                        closure += list(self.delta[hash(next_state)]["ε"])
                        to_visit += list(self.delta[hash(next_state)]["ε"])

            # Add the closure to the closures dictionary.
            epsilon_closures[hash(state)] = (sorted(set(closure)))

        return epsilon_closures


# Regex Base Class.
class Expr:
    pass


# The Symbol.
class Symbol(Expr):
    _char: str

    def __init__(self, c: str):
        self.char = c

    def __str__(self):
        return self.char


# The Kleene Star Operator - Not used in the Current Stage.
class Star(Expr):
    _expr: Expr

    def __init__(self, expr: Expr):
        self._expr = expr

    def __str__(self):
        return "STAR" + " " + str(self._expr)


class Plus(Expr):
    _expr: Expr

    def __init__(self, expr: Expr):
        self._expr = expr

    def __str__(self):
        return "PLUS" + " " + str(self._expr)


# The Concat Operator - Not used in the Current Stage.
class Concat(Expr):
    _expr1: Expr
    _expr2: Expr

    def __init__(self, expr1: Expr, expr2: Expr):
        self._expr1 = expr1
        self._expr2 = expr2

    def __str__(self):
        return "CONCAT" + " " + str(self._expr1) + " " + str(self._expr2)


# The Union Operator - Not used in the Current Stage.
class Union(Expr):
    _expr1: Expr
    _expr2: Expr

    def __init__(self, expr1: Expr, expr2: Expr):
        self._expr1 = expr1
        self._expr2 = expr2

    def __str__(self):
        return "UNION" + " " + str(self._expr1) + " " + str(self._expr2)


operators = "*+|()"


# Function for converting an infix regex to a prefix one.
def to_prefix(tokens):
    stack = []

    # Process each token.
    while tokens:
        token = tokens.pop()

        # Check if the token is an operator or not and process it adequately.
        if token not in operators:
            stack.append(Symbol(token))
        elif token == "|":
            stack.append(Union(stack.pop(), to_prefix(tokens)))
            while len(stack) > 1:
                elem1 = stack.pop()
                elem2 = stack.pop()
                stack.append(Concat(elem2, elem1))
            return stack.pop()
        elif token == "*":
            stack.append(Star(stack.pop()))
        elif token == "+":
            stack.append(Plus(stack.pop()))
        elif token == "(":
            stack.append(to_prefix(tokens))
        elif token == ")":
            while len(stack) > 1:
                elem1 = stack.pop()
                elem2 = stack.pop()
                stack.append(Concat(elem2, elem1))
            return stack.pop()
        else:
            while len(stack) > 1:
                elem1 = stack.pop()
                elem2 = stack.pop()
                stack.append(Concat(elem2, elem1))
            return stack.pop()

    while len(stack) > 1:
        elem1 = stack.pop()
        elem2 = stack.pop()
        stack.append(Concat(elem2, elem1))

    return stack.pop()


# Function used for reducing the Stack in order to generate the equivalent NFA for the Regex given as input.
def reduce_stack(stack: list, index: List[int]):
    # Check if there are any elements in the stack.
    while len(stack) > 1:
        curr_elem = stack[-1]

        # If the top of the stack is an NFA check if the stack can be reduced.
        if isinstance(curr_elem, NFA):
            prev_elem = stack[-2]

            # Reduce the Stack by building the equivalent STAR NFA.
            if prev_elem == "STAR":
                stack.pop()
                stack.pop()
                stack.append(star_nfa(curr_elem, index))
            # Reduce the Stack by building the equivalent PLUS NFA.
            elif prev_elem == "PLUS":
                stack.pop()
                stack.pop()
                stack.append(plus_nfa(curr_elem, index))
            # Reduce the Stack by building the equivalent CONCAT/UNION NFA.
            elif isinstance(prev_elem, NFA):
                stack.pop()
                stack.pop()
                op = stack.pop()

                # Check if the operator is CONCAT or UNION and build the equivalent NFA.
                if op == "CONCAT":
                    stack.append(concat_nfa(prev_elem, curr_elem))
                elif op == "UNION":
                    stack.append(union_nfa(prev_elem, curr_elem, index))
            else:
                break
        else:
            break

    # Return the reduced stack.
    return stack


# Function used for converting a Regex to an NFA - I started my implementation based on the one from the Regex
# Laboratory, but instead of pushing Mini Regexes to the Stack, I push mini NFAs.
def regex_to_nfa(s: str, index: [int]):
    tokens = []
    if len(s) > 1:
        aux_tokens = re.split('(?<! ) ', s)

        for token in aux_tokens:
            if len(token) > 1:
                tokens.append(re.split(' (?! )', token))
            else:
                tokens.append([token])

        tokens = sum(tokens, [])
    else:
        tokens = s
    stack = []

    for token in tokens:
        # If the token is a Symbol push the corresponding Symbol NFA to the stack, else it is an operator and should
        # be pushed directly to the stack.
        if token != "CONCAT" and token != "UNION" and token != "STAR" and token != "PLUS":
            stack.append(symbol_nfa(Symbol(token), index))
        else:
            stack.append(token)

        # Reduce the stack.
        stack = reduce_stack(stack, index)

    # Return the corresponding NFA for the Regex.
    return stack.pop()


# Function for creating a Symbol NFA, implemented using the algorithm from the lecture.
# Base case: c E alphabet, initial state --c--> final state
def symbol_nfa(symbol: Symbol, index: List[int]):
    nfa = NFA()

    # Add the character to the alphabet.
    nfa.alphabet.add(symbol.char)

    # Create the initial and final states.
    initial_state = State(index[0])
    final_state = State(index[0] + 1)
    index[0] += 2

    nfa.states.add(initial_state)
    nfa.states.add(final_state)

    nfa.initialState = initial_state
    nfa.finalStates = {final_state}

    # Add the transition from the initial state to the final state via the character.
    nfa.delta[hash(initial_state)] = dict()
    nfa.delta[hash(initial_state)][symbol.char] = [final_state]

    return nfa


# Function for creating a STAR NFA, implemented using the algorithm from the lecture.
#                              _____________e______________
#                              |                          |
#                              v                          |
# new initial state --e--> NFA's initial state -...-> NFA's final state --e--> new final state
#        |                                                                          ^
#        |                                                                          |
#        ----------------------------------e-----------------------------------------
def star_nfa(nfa: NFA, index: List[int]):
    # Crete the new initial and final states.
    initial_state = State(index[0])
    final_state = State(index[0] + 1)
    index[0] += 2

    nfa_final_state, *_ = nfa.finalStates

    # Add the Epsilon transitions necessary for the Star NFA.
    nfa.delta[hash(initial_state)] = dict()
    nfa.delta[hash(initial_state)]["ε"] = [nfa.initialState]

    nfa.delta[hash(initial_state)]["ε"].append(final_state)

    nfa.delta[hash(nfa_final_state)] = dict()
    nfa.delta[hash(nfa_final_state)]["ε"] = [nfa.initialState]

    nfa.delta[hash(nfa_final_state)]["ε"].append(final_state)

    nfa.initialState = initial_state
    nfa.finalStates = {final_state}

    nfa.states.add(initial_state)
    nfa.states.add(final_state)

    return nfa


# Function for creating a PLUS NFA, implemented by creating a copy of the initial NFA. After that I create a STAR NFA
# from the copy of the initial NFA and concatenate it with the initial NFA.
def plus_nfa(nfa: NFA, index: List[int]):
    nfa1 = NFA()

    # Create a copy of the NFA and keep a state Map for renaming the States in te NFA's copy.
    state_map: Dict[int, State] = dict()

    # Clone the NFA and change the states' indexes.
    for state in nfa.states:
        if hash(state) not in state_map:
            state_map[hash(state)] = State(index[0])
            index[0] += 1

        new_state = state_map[hash(state)]
        nfa1.delta[hash(new_state)] = dict()
        nfa1.states.add(new_state)

        if hash(state) in nfa.delta:
            for key in nfa.delta[hash(state)].keys():
                nfa1.delta[hash(new_state)][key] = []
                for next_state in nfa.delta[hash(state)][key]:
                    if hash(next_state) not in state_map:
                        state_map[hash(next_state)] = State(index[0])
                        index[0] += 1

                    corresponding_next_state = state_map[hash(next_state)]
                    nfa1.delta[hash(new_state)][key].append(corresponding_next_state)

    nfa1.initialState = state_map[hash(nfa.initialState)]

    for final_state in nfa.finalStates:
        nfa1.finalStates.add(state_map[hash(final_state)])

    nfa1.alphabet = nfa.alphabet.copy()

    # Create a star NFA from the clone.
    nfa2 = star_nfa(nfa1, index)

    # Concatenate the initial NFA with the STAR NFA in order to build the PLUS NFA.
    return concat_nfa(nfa, nfa2)


# Function for creating an UNION NFA, implemented using the algorithm from the lecture.
# new initial state --e--> NFA1's initial state -...-> NFA1's final state --e--> new final state
#        |                                                                             ^
#        |                                                                             |
#        ------e-----> NFA2's initial state -...-> NFA2's final state --------e---------
def union_nfa(nfa1: NFA, nfa2: NFA, index: List[int]):
    # Create the new initial and final states.
    initial_state = State(index[0])
    final_state = State(index[0] + 1)
    index[0] += 2

    nfa1_final_state, *_ = nfa1.finalStates
    nfa2_final_state, *_ = nfa2.finalStates

    # Add the necessary Epsilon transitions.
    nfa1.delta[hash(initial_state)] = dict()
    nfa1.delta[hash(initial_state)]["ε"] = [nfa1.initialState]
    nfa1.delta[hash(initial_state)]["ε"].append(nfa2.initialState)

    nfa1.delta[hash(nfa1_final_state)] = dict()
    nfa1.delta[hash(nfa1_final_state)]["ε"] = [final_state]

    nfa2.delta[hash(nfa2_final_state)] = dict()
    nfa2.delta[hash(nfa2_final_state)]["ε"] = [final_state]

    nfa1.initialState = initial_state
    nfa1.finalStates = {final_state}

    nfa1.states.add(initial_state)
    nfa1.states.add(final_state)

    # Combine the two NFAs.
    nfa1 = combine_nfas(nfa1, nfa2)

    return nfa1


# Function for creating an UNION NFA, implemented using the algorithm from the lecture.
# NFA1's initial state -...-> NFA1's final state --e--> NFA2's initial state -...-> NFA2's final state
def concat_nfa(nfa1: NFA, nfa2: NFA):
    nfa1_final_state, *_ = nfa1.finalStates

    # Add the necessary Epsilon transition.
    nfa1.delta[hash(nfa1_final_state)] = dict()
    nfa1.delta[hash(nfa1_final_state)]["ε"] = [nfa2.initialState]

    # Combine the two NFAs.
    nfa1 = combine_nfas(nfa1, nfa2)

    # Update the NFA's new Final State.
    nfa1.finalStates = nfa2.finalStates.copy()

    return nfa1


# Function for combining two NFA's.
def combine_nfas(nfa1: NFA, nfa2: NFA):
    # Join the states sets.
    nfa1.states.update(nfa2.states)

    # Join the delta functions.
    nfa1.delta.update(nfa2.delta)

    # Join the alphabets sets.
    nfa1.alphabet.update(nfa2.alphabet)
    return nfa1


# Function for creating a DFA based on input generated from an NFA.
def create_dfa(delta: Dict[int, Dict[str, State]], states, alphabet, final_states):
    dfa = DFA()

    # Set the alphabet, the initial state and the final states.
    dfa.alphabet = sorted(alphabet)
    dfa.initialState = State(0)
    dfa.finalStates = final_states

    # Create a possible Sink State.
    sink_state = State(len(states))

    # Check if transitions to the Sink State should be added for each State in the DFA.
    for i in range(len(states)):
        state = State(i)
        dfa.states.add(state)

        # The State has no transitions in the delta function, transitions to the Sink State via any character in the
        # alphabet should be added.
        if hash(state) not in delta:
            delta[hash(state)] = dict()
            for key in alphabet:
                delta[hash(state)][key] = sink_state

        # Check if there are any characters in the alphabet that don't have a transition from the current state via it
        # in the delta function and add them with the Sink State as the destination State.
        else:
            for key in alphabet:
                if key not in delta[hash(state)].keys():
                    delta[hash(state)][key] = sink_state

    # Add the Sink State transitions to self on any character in the alphabet if necessary.
    delta[hash(sink_state)] = dict()
    for key in alphabet:
        delta[hash(sink_state)][key] = sink_state

    dfa.states.add(sink_state)
    dfa.sinkStates.add(sink_state)

    # Finally set the delta function.
    dfa.delta = delta

    return dfa


# Function for converting an NFA to a DFA, implementation based on the algorithm from the lecture.
def nfa_to_dfa(nfa: NFA):
    # Compute the NFA's Epsilon Transitions.
    epsilon_closures = nfa.get_epsilon_closures()

    closures = [epsilon_closures[hash(nfa.initialState)]]
    visited_closures: List[List[State]] = []
    state_index = 0

    # DFA's components.
    delta: Dict[int, Dict[str, State]] = dict()
    final_states: set[State] = set()
    alphabet = nfa.alphabet.copy()

    # Compute the DFA's transitions.
    while len(closures) > 0:
        transitions: Dict[str, List[State]] = {}

        # Check if the current closure has been reached before and get its corresponding state in the DFA.
        closure = closures.pop()
        if closure in visited_closures:
            new_state = State(visited_closures.index(closure))
        else:
            new_state = State(state_index)
            delta[hash(new_state)] = dict()
            visited_closures.append(closure)
            state_index += 1

        # Check if the corresponding state should be final or not.
        for state in closure:
            if state in nfa.finalStates:
                final_states.add(new_state)
                break

        # Save all the transitions from states in the closure on characters != "ε" in the transitions dictionary.
        for state in closure:
            if hash(state) in nfa.delta:
                for key in nfa.delta[hash(state)].keys():
                    if key != "ε":
                        for next_state in nfa.delta[hash(state)][key]:
                            if key not in transitions:
                                transitions[key] = []

                            transitions[key].append(next_state)

        # Compute the next closures that can be reached from the current closure.
        for key in transitions.keys():
            new_closure = []

            # Add to the closure all the states that can be reached from the current closure via the current key.
            for state in transitions[key]:
                new_closure.append(epsilon_closures[hash(state)])

            # Remove duplicates and check if the new closure has been reached before.
            new_closure = list(set(sum(new_closure, [])))
            if new_closure not in visited_closures:
                visited_closures.append(new_closure)
                closures.append(new_closure)

            # Add the transition from the state corresponding to the initial closure to the one corresponding to the
            # new closure.
            if hash(new_state) not in delta:
                delta[hash(new_state)] = dict()
            delta[hash(new_state)][key] = State(visited_closures.index(new_closure))

    # Create the equivalent DFA.
    return create_dfa(delta, visited_closures, alphabet, final_states)


class Lexer:
    def __init__(self, dfas, output):
        self.dfas: list = dfas
        self.output: str = output

        # I used this list to store all the DFAs' current states.
        self.states: list = list()

        for dfa in self.dfas:
            self.states.append(dfa.initialState)

    def print_lexemes(self, lexemes, word, sinking_idx, sinked_dfas):
        with open(self.output, "w") as output:
            # The word has been tokenized successfully.
            if sinked_dfas != len(self.dfas):
                output.write(lexemes)
            else:
                # Find the line where all the DFAs sinked.
                line = 0
                line_breaks = [i for i, char in enumerate(word) if char == "\n"]

                for i in line_breaks:
                    if sinking_idx > i:
                        line += 1

                # Print the character's index and line on which all the DFAs have sinked.
                if sinking_idx == len(word):
                    output.write("No viable alternative at character EOF, line " + str(line))
                else:
                    output.write("No viable alternative at character " + str(sinking_idx) + ", line " + str(line))

    # Get the lexemes from a word using the DFAs.
    def get_lexemes(self, word):
        lexemes = ""
        left = 0
        right = 1

        # While the word hasn't been completely split in tokens.
        while left <= right <= len(word):
            # Start and End of the longest Accepted Token and the DFA which
            # accepts it.
            max_left = max_right = -1
            max_dfa = None

            # Number of DFAs which have reached a Sink State and the character's index
            # on which the last DFA has sinked.
            sinked_dfas = 0
            sinking_idx = right - 1

            # Try to get the longest accepted token starting from left by each
            # DFA.

            # If the character does not make the DFA reach a Sink State proceed
            # to test the next Character.
            for dfa in self.dfas:
                aux_left = left
                aux_right = right

                # While the word's end hasn't been reached.
                while aux_right <= len(word):
                    # Execute one step.
                    new_state, _ = dfa.step((self.states[self.dfas.index(dfa)], word[aux_right - 1]))

                    # Check if a Sink State has been reached and update the
                    # number of Sinked DFAs and the Sinking Index if necessary.
                    if new_state in dfa.sinkStates:
                        sinked_dfas += 1
                        sinking_idx = max(aux_right - 1, sinking_idx)
                        break

                    # Check if the Character made the DFA accept the word and
                    # update the vars regarding the longest accepted word
                    # adequately.
                    if aux_right > max_right and new_state in dfa.finalStates:
                        max_left = aux_left
                        max_right = aux_right
                        max_dfa = dfa

                    # Update the DFA's state and move to the next Character.
                    self.states[self.dfas.index(dfa)] = new_state
                    aux_right += 1

                # If the word's end has been reached and neither a Final State,
                # nor a Sink State has been reached update the number of Sinked
                # DFAs and the Sinking Index.
                if aux_right > len(word) and new_state not in (dfa.finalStates | dfa.sinkStates):
                    sinked_dfas += 1
                    sinking_idx = len(word)

                self.states[self.dfas.index(dfa)] = dfa.initialState

            # Update the Lexemes if possible, or check if all the DFAs have
            # sinked and the word can't be tokenized.
            if max_dfa:
                lexemes += max_dfa.name + " " + repr(word[max_left:max_right])[1:-1] + "\n"
                left = max_right
                right = max_right + 1
            elif sinked_dfas == len(self.dfas):
                break

        self.print_lexemes(lexemes, word, sinking_idx, sinked_dfas)


def runparser(parserfinput, parserfoutput):
    with open(parserfoutput, "w") as output:
        output.write("")


def runcompletelexer(lexerfinput, finput, foutput):
    # Read the Lexer
    with open(lexerfinput, "r") as input:
        dfas = []
        regexes = input.readlines()

    for regex in regexes:
        # Convert the Infix Regex to a Prefix one.
        regex = regex.replace("'", '')
        regex = codecs.decode(regex, 'unicode-escape')
        regex = regex[:-2]
        parsed = regex.split(" ", 1)
        prefix = to_prefix(list(parsed[1][::-1]))

        # Convert the Regex to an NFA.
        nfa = regex_to_nfa(str(prefix), [0])

        # Convert the NFA to a DFA.
        dfa = nfa_to_dfa(nfa)
        dfa.compute_sink_states()
        dfa.name = parsed[0]
        dfas.append(dfa)

    # Initialise the Lexer.
    lexer = Lexer(dfas, foutput)

    with open(finput, "r") as input:
        words = input.readlines()
        word = ''.join(words)

        # Split the word into lexemes.
        lexer.get_lexemes(word)
