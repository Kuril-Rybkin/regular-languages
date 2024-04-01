#ifndef __PROGTEST__

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iostream>
#include <list>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <variant>
#include <vector>

using State = unsigned int;
using Symbol = uint8_t;

struct NFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, std::set<State>> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;
};

struct DFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, State> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;
};

#endif

//compares state with first element in a set of equivalent states
bool equivalentWithSet(State state, const std::set<State> & set, std::map<State, State> & map, DFA & automaton) {
    State first = *set.begin();

    if (state == first) {
        return true;
    }

    for (auto symbol : automaton.m_Alphabet) {
        if (map[automaton.m_Transitions[{state, symbol}]] != map[automaton.m_Transitions[{first, symbol}]]) {
            return false;
        }
    }

    return true;
}

DFA minimize(DFA original) {
    DFA result;

    //create set of non-final states by using {States}\{FinalStates} (difference of sets)
    std::set<State> Q1;
    std::set_difference(original.m_States.begin(), original.m_States.end(),
                        original.m_FinalStates.begin(), original.m_FinalStates.end(),
                        std::inserter(Q1, Q1.begin()));

    //create set of final states
    std::set<State> Q2 = original.m_FinalStates;

    //create a map which maps the state to the equivalency set it is in
    std::map<State, State> stateSetID;
    for (auto i : Q1) {
        stateSetID[i] = 0;
    }
    for (auto i : Q2) {
        stateSetID[i] = 1;
    }

    //create 2 vectors of sets. Each set will be a set of equivalent states. The algorithm stops when they are equal
    std::vector<std::set<State>> currSet = {Q1, Q2};
    std::vector<std::set<State>> prevSet;

    while (currSet != prevSet) {
        //set the previous set to the current set, since we will be modifying the current set now.
        prevSet = currSet;

        for (size_t i = 0; i < currSet.size(); i++) {
            //create temporary equivalence set where all states that do not match current equivalence set will go
            std::set<State> tmpEquivalenceSet;

            //check every state in the equivalence set and compare it with the first element in the equivalence set
            for (auto state = currSet[i].begin(); state != currSet[i].end();) {
                //move all states that are not equivalent with the head of the set into their own new set
                if (!equivalentWithSet(*state, currSet[i], stateSetID, original)) {
                    tmpEquivalenceSet.insert(*state);
                    state++;
                }
                else {
                    state++;
                }
            }

            if (!tmpEquivalenceSet.empty()) {
                for (auto j : tmpEquivalenceSet) {
                    stateSetID[j] = currSet.size();
                    currSet[i].erase(j);
                }
                currSet.push_back(tmpEquivalenceSet);
            }
        }
    }

    //give states new state IDs based on their equivalency set
    //(states in the same equivalency set have the same ID)
    std::map<State, State> newStateMapping;
    std::map<std::set<State>, State> setMapping;
    State counter = 0;
    for (auto & set : currSet) {
        setMapping[set] = counter;
        for (auto state : set) {
            newStateMapping[state] = counter;
        }
        ++counter;
    }

    for (auto & set : currSet) {
        if (set.find(original.m_InitialState) != set.end()) {
            result.m_InitialState = setMapping[set];
        }

        result.m_States.insert(setMapping[set]);

        if (original.m_FinalStates.find(*set.begin()) != original.m_FinalStates.end()) {
            result.m_FinalStates.insert(setMapping[set]);
        }

        for (auto symbol : original.m_Alphabet) {
            auto findTransition = original.m_Transitions.find({*set.begin(), symbol});
            if (findTransition != original.m_Transitions.end()) {
                result.m_Transitions[{setMapping[set], symbol}] = newStateMapping[findTransition->second];
            }
        }
    }

    result.m_Alphabet = original.m_Alphabet;

    for (auto i : result.m_States) {
        bool isSink = true;

        for (auto j : result.m_Alphabet) {
            if (result.m_Transitions[{i, j}] != i || result.m_FinalStates.find(i) != result.m_FinalStates.end()) {
                isSink = false;
                break;
            }
        }

        if (isSink) {
            result.m_States.erase(i);
            auto transition = result.m_Transitions.begin();
            while (transition != result.m_Transitions.end()) {
                if (transition->first.first == i || transition->second == i) {
                    transition = result.m_Transitions.erase(transition);
                }
                else {
                    transition++;
                }
            }
            break;
        }
    }

    if (result.m_States.find(result.m_InitialState) == result.m_States.end()) {
        result.m_InitialState = *result.m_States.begin();
    }

    bool restInaccessible = true;
    for (auto symbol : result.m_Alphabet) {
        auto tr = result.m_Transitions.find({result.m_InitialState, symbol});
        if (tr != result.m_Transitions.end() && tr->second != result.m_InitialState) {
            restInaccessible = false;
        }
    }

    if (restInaccessible) {
        result.m_States = {result.m_InitialState};
        auto i = result.m_Transitions.begin();
        while (i != result.m_Transitions.end()) {
            if (i->first.first != result.m_InitialState) {
                i = result.m_Transitions.erase(i);
            }
            else {
                i++;
            }
        }
    }

    return result;
}

//removes unreachable states, adds sink state if necessary
DFA determine(const NFA & nfa) {
    DFA result;

    //copy alphabet and initial state, since they will always be the same
    result.m_Alphabet = nfa.m_Alphabet;
    result.m_InitialState = 0;

    //map of set of states to their new state ID
    std::map<std::set<State>, unsigned int> map;
    //stack of states which need to be added
    std::queue<std::set<State>> queue;

    //counter of total new states
    size_t stateCounter = 0;

    //manually add 1st state
    result.m_States.insert(0);
    map[{nfa.m_InitialState}] = 0;

    //check if manually inserted first state is final, and add it to final states set
    if (nfa.m_FinalStates.find(nfa.m_InitialState) != nfa.m_FinalStates.end()) {
        result.m_FinalStates.insert(0);
    }
    ++stateCounter;

    bool sinkStateAdded = false;

    //get all transitions for start state and write them down as a grouped transition
    for (auto & symbol : nfa.m_Alphabet) {
        //find transition with starting state 0 and symbol i (i cycles through entire alphabet)
        auto startState = nfa.m_Transitions.find({nfa.m_InitialState, symbol});

        //if matching transition is found
        if (startState != nfa.m_Transitions.end()) {
            //if this exact transition did not exist before
            if (map.find(startState->second) == map.end()) {
                //add this transition to stack so that it can be reviewed again
                queue.push(startState->second);

                //remember this transition with it's unique ID being the current stateCounter
                map[startState->second] = stateCounter;
                //increase the total number of states (and help assign new IDs)
                ++stateCounter;

                //assign ID to this new transition in the result DFA
                result.m_States.insert(map[startState->second]);
            }
            result.m_Transitions[{0, symbol}] = map[startState->second];
        }
        else {
            if (!sinkStateAdded) {
                queue.push({});
                map[{}] = stateCounter;

                result.m_States.insert(stateCounter);
                result.m_Transitions[{0, symbol}] = stateCounter;
                stateCounter++;
                sinkStateAdded = true;
            }
            else {
                result.m_Transitions[{0, symbol}] = map[{}];
            }
        }
    }

    //while there are still transitions left to review
    while (!queue.empty()) {
        //get next element in queue of non-computed transitions
        auto nextInQueue = queue.front();

        //set flag to determine if state is accepting or not
        bool flag = false;

        //for every state inside the current state set at the top of the stack
        //this basically makes it so that all the states in the set behave like 1 state by unifying their transitions
        for (auto symbol : nfa.m_Alphabet) {
            //create a temporary set to store states transitioned to, from the nextInQueue
            std::set<State> tmp;

            for (auto state : nextInQueue) {
                //check if this state we are checking is an accepting state and set the flag accordingly
                if (flag != true && nfa.m_FinalStates.find(state) != nfa.m_FinalStates.end()) {
                    flag = true;
                }

                //find transitions with current state and every symbol in the alphabet and determine if they exist
                auto transitionSet = nfa.m_Transitions.find({state, symbol});

                if (transitionSet != nfa.m_Transitions.end()) {
                    tmp.insert(transitionSet->second.begin(), transitionSet->second.end());
                }
            }

            //if this newly created state wasn't looked at before, add it to the queue of states to be checked.
            //also, make it into a new state and add it.
            if (map.find(tmp) == map.end()) {
                //remember this transition with it's unique ID being the current stateCounter
                map[tmp] = stateCounter;
                //increase the total number of states (and help assign new IDs)
                ++stateCounter;

                //add newly created transition to queue
                queue.push(tmp);
            }

            //assign ID to this new transition in the result DFA
            result.m_Transitions[{map[nextInQueue], symbol}] = map[tmp];
            //insert state ID into result set of states
            result.m_States.insert(map[tmp]);

            //if the state was determined to be accepting by the flag previously, add it as an accepting state now.
            if (flag) {
                result.m_FinalStates.insert(map[nextInQueue]);
            }
        }
        queue.pop();
    }

    return result;
}

NFA unifyNFA(const NFA & a, const NFA & b) {
    //create new temporary result NFA as copy of a
    NFA result = a;
    result.m_Alphabet.insert(b.m_Alphabet.begin(), b.m_Alphabet.end());

    //add all states from b and offset them by the size of a because the states are now concurrent
    for (auto state : b.m_States) {
        result.m_States.insert(state + a.m_States.size());
        if (b.m_FinalStates.find(state) != b.m_FinalStates.end()) {
            result.m_FinalStates.insert(state + a.m_States.size());
        }

        for (auto symbol : b.m_Alphabet) {
            //check if transition for this state and symbol exists
            auto transition = b.m_Transitions.find({state, symbol});

            if (transition != b.m_Transitions.end()) {
                //offset all elements in resulting transition to account for states in NFA a
                for (auto & elem : transition->second) {
                    //add resulting state for this transition from b and offset result as well since all states
                    //in b are offset
                    result.m_Transitions[{state + a.m_States.size(), symbol}]
                            .insert(elem + a.m_States.size());
                }
            }
        }
    }

    //create new start state for union of languages
    result.m_InitialState = result.m_States.size();
    result.m_States.insert(result.m_InitialState);

    if (a.m_FinalStates.find(a.m_InitialState) != a.m_FinalStates.end() || b.m_FinalStates.find(b.m_InitialState) != b.m_FinalStates.end()) {
        result.m_FinalStates.insert(result.m_InitialState);
    }

    //check all transitions from initial states for every symbol in the alphabet
    for (auto symbol : result.m_Alphabet) {
        //do not forget to offset states in NFA b
        auto trA = a.m_Transitions.find({a.m_InitialState, symbol});
        auto trB = b.m_Transitions.find({b.m_InitialState, symbol});

        if (trA != a.m_Transitions.end()) {
            result.m_Transitions[{result.m_InitialState, symbol}] = trA->second;
        }

        if (trB != b.m_Transitions.end()) {
            for (auto state : trB->second) {
                result.m_Transitions[{result.m_InitialState, symbol}].insert(state + a.m_States.size());
            }
        }
    }

    return result;
}

DFA unify(const NFA& a, const NFA& b) {
    return minimize(determine(unifyNFA(a, b)));
}

DFA parallelRun(const DFA & a, const DFA & b) {
    DFA result;
    result.m_Alphabet.insert(a.m_Alphabet.begin(), a.m_Alphabet.end());
    result.m_Alphabet.insert(b.m_Alphabet.begin(), b.m_Alphabet.end());

    std::map<std::pair<std::vector<State>, Symbol>, std::vector<State>> tempTransitions;
    std::map<std::vector<State>, State> pairID;
    std::queue<std::vector<State>> queue;

    //state with ID 0 will always be sink state.
    pairID[{}] = 0;

    //add sink state to the resulting DFA.
    result.m_States.insert(0);

    //sink state will always transition to itself.
    for (auto symbol : result.m_Alphabet) {
        tempTransitions[{{}, symbol}] = {};
    }

    //since initial states are pushed first, resulting DFA initial state will always be 1
    result.m_InitialState = 1;

    State stateCounter = 1;
    queue.push({a.m_InitialState, b.m_InitialState});

    while (!queue.empty()) {
        auto next = queue.front();
        queue.pop();

        for (auto symbol : result.m_Alphabet) {
            if (next.size() == 2) {
                auto transitionA = a.m_Transitions.find({next[0], symbol});
                auto transitionB = b.m_Transitions.find({next[1], symbol});

                if (transitionA != a.m_Transitions.end() && transitionB != b.m_Transitions.end()) {
                    tempTransitions[{{next[0], next[1]}, symbol}] = {transitionA->second, transitionB->second};

                    if (pairID.find({next[0], next[1]}) == pairID.end()) {
                        pairID[{next[0], next[1]}] = stateCounter;

                        result.m_States.insert(stateCounter);

                        if (a.m_FinalStates.find({next[0]}) != a.m_FinalStates.end()
                            && b.m_FinalStates.find({next[1]}) != b.m_FinalStates.end()) {
                            result.m_FinalStates.insert(stateCounter);
                        }

                        stateCounter++;
                    }

                    if (pairID.find({transitionA->second, transitionB->second}) == pairID.end()) {
                        queue.push({transitionA->second, transitionB->second});
                    }
                }
                else {
                    tempTransitions[{{next[0], next[1]}, symbol}] = {};
                }
            }
        }
    }

    for (auto transition : tempTransitions) {
        result.m_Transitions[{pairID[transition.first.first], transition.first.second}] = pairID[transition.second];
    }

    return result;
}

DFA intersect(const NFA& a, const NFA& b) {
    return minimize(parallelRun(determine(a), determine(b)));
}

#ifndef __PROGTEST__

// You may need to update this function or the sample data if your state naming strategy differs.
bool operator==(const DFA& a, const DFA& b)
{
    return std::tie(a.m_States, a.m_Alphabet, a.m_Transitions, a.m_InitialState, a.m_FinalStates) == std::tie(b.m_States, b.m_Alphabet, b.m_Transitions, b.m_InitialState, b.m_FinalStates);
}

int main()
{
    NFA a1{
            {0, 1, 2},
            {'a', 'b'},
            {
                    {{0, 'a'}, {0, 1}},
                    {{0, 'b'}, {0}},
                    {{1, 'a'}, {2}},
            },
            0,
            {2},
    };
    NFA a2{
            {0, 1, 2},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{1, 'a'}, {2}},
                    {{2, 'a'}, {2}},
                    {{2, 'b'}, {2}},
            },
            0,
            {2},
    };
    DFA a{
            {0, 1, 2, 3, 4},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{1, 'a'}, {2}},
                    {{2, 'a'}, {2}},
                    {{2, 'b'}, {3}},
                    {{3, 'a'}, {4}},
                    {{3, 'b'}, {3}},
                    {{4, 'a'}, {2}},
                    {{4, 'b'}, {3}},
            },
            0,
            {2},
    };
    DFA aa = intersect(a1, a2);

    NFA b1{
            {0, 1, 2, 3, 4},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{0, 'b'}, {2}},
                    {{2, 'a'}, {2, 3}},
                    {{2, 'b'}, {2}},
                    {{3, 'a'}, {4}},
            },
            0,
            {1, 4},
    };
    NFA b2{
            {0, 1, 2, 3, 4},
            {'a', 'b'},
            {
                    {{0, 'b'}, {1}},
                    {{1, 'a'}, {2}},
                    {{2, 'b'}, {3}},
                    {{3, 'a'}, {4}},
                    {{4, 'a'}, {4}},
                    {{4, 'b'}, {4}},
            },
            0,
            {4},
    };
    DFA b{
            {0, 1, 2, 3, 4, 5, 6, 7, 8},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{0, 'b'}, {2}},
                    {{2, 'a'}, {3}},
                    {{2, 'b'}, {4}},
                    {{3, 'a'}, {5}},
                    {{3, 'b'}, {6}},
                    {{4, 'a'}, {7}},
                    {{4, 'b'}, {4}},
                    {{5, 'a'}, {5}},
                    {{5, 'b'}, {4}},
                    {{6, 'a'}, {8}},
                    {{6, 'b'}, {4}},
                    {{7, 'a'}, {5}},
                    {{7, 'b'}, {4}},
                    {{8, 'a'}, {8}},
                    {{8, 'b'}, {8}},
            },
            0,
            {1, 5, 8},
    };
    DFA bb = unify(b1, b2);

    NFA c1{
            {0, 1, 2, 3, 4},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{0, 'b'}, {2}},
                    {{2, 'a'}, {2, 3}},
                    {{2, 'b'}, {2}},
                    {{3, 'a'}, {4}},
            },
            0,
            {1, 4},
    };
    NFA c2{
            {0, 1, 2},
            {'a', 'b'},
            {
                    {{0, 'a'}, {0}},
                    {{0, 'b'}, {0, 1}},
                    {{1, 'b'}, {2}},
            },
            0,
            {2},
    };
    DFA c{
            {0},
            {'a', 'b'},
            {},
            0,
            {},
    };
    DFA cc = intersect(c1, c2);

    NFA d1{
            {0, 1, 2, 3},
            {'i', 'k', 'q'},
            {
                    {{0, 'i'}, {2}},
                    {{0, 'k'}, {1, 2, 3}},
                    {{0, 'q'}, {0, 3}},
                    {{1, 'i'}, {1}},
                    {{1, 'k'}, {0}},
                    {{1, 'q'}, {1, 2, 3}},
                    {{2, 'i'}, {0, 2}},
                    {{3, 'i'}, {3}},
                    {{3, 'k'}, {1, 2}},
            },
            0,
            {2, 3},
    };
    NFA d2{
            {0, 1, 2, 3},
            {'i', 'k'},
            {
                    {{0, 'i'}, {3}},
                    {{0, 'k'}, {1, 2, 3}},
                    {{1, 'k'}, {2}},
                    {{2, 'i'}, {0, 1, 3}},
                    {{2, 'k'}, {0, 1}},
            },
            0,
            {2, 3},
    };
    DFA d{
            {0, 1, 2, 3},
            {'i', 'k', 'q'},
            {
                    {{0, 'i'}, {1}},
                    {{0, 'k'}, {2}},
                    {{2, 'i'}, {3}},
                    {{2, 'k'}, {2}},
                    {{3, 'i'}, {1}},
                    {{3, 'k'}, {2}},
            },
            0,
            {1, 2, 3},
    };
    DFA dd = intersect(d1, d2);

    NFA e1{
            {0, 1},
            {'a', 'b'},
            {
                    {{1, 'a'}, {0}},
                    {{1, 'b'}, {1}}
            },
            0,
            {0, 1}
    };

    NFA e2{
            {0, 1},
            {'a', 'b'},
            {
                    {{1, 'a'}, {0}},
                    {{1, 'b'}, {1}}
            },
            0,
            {0, 1}
    };

    DFA ee = unify(e1, e2);

    NFA f1{
            {0, 1},
            {'a'},
            {
                    {{1, 'a'}, {1}}
            },
            0,
            {1}
    };

    NFA f2{
            {0, 1},
            {'a', 'b'},
            {
                    {{1, 'a'}, {0}},
                    {{1, 'b'}, {1}}
            },
            0,
            {0, 1}
    };

    DFA ff = unify(f1, f2);

    NFA g1{
            {0, 1, 2, 3},
            {'a', 'b'},
            {
                    {{0, 'a'}, {0, 1, 2, 3}}
            },
            0,
            {0, 1, 2, 3}
    };

    NFA g2 {
            {0, 1, 2, 3, 4},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{1, 'b'}, {2}},
                    {{2, 'a'}, {3}},
                    {{3, 'b'}, {4}}
            },
            0,
            {4}
    };

    DFA gg = unify(g1, g2);

    NFA h1 {
            {0,1,2,3,4,5,6,7,8,9,10,11,12},
            {'G', 't'},
            {
                    {{0, 'G'},{0,2,3}},
                    {{0, 't'},{0,1,2,8}},
                    {{1, 'G'},{2,4,9}},
                    {{1, 't'},{0,2,10}},
                    {{2, 'G'},{9,10}},
                    {{2, 't'},{0,2,9}},
                    {{3, 'G'},{1,4,10}},
                    {{3, 't'},{1,2}},
                    {{4, 'G'},{0,8,11}},
                    {{4, 't'},{0,1,4,12}},
                    {{5, 'G'},{0,4,6,7,11}},
                    {{5, 't'},{1,5,9,10}},
                    {{6, 'G'},{2,5,8}},
                    {{6, 't'},{0,2,4,6,7}},
                    {{7, 'G'},{0, 1}},
                    {{7, 't'}, {0,2,5,6,9}},
                    {{9, 'G'}, {1,4,10}},
                    {{9, 't'}, {1,2}},
                    {{10, 'G'}, {0,8,12}},
                    {{10, 't'}, {0,1,4,11}}

            },
            1,
            {0,1,2,5,7}
    };

    NFA h2 {
            {0,1,2,3,4,5,6,7,8,9,10,11},
            {'G', 't'},
            {
                    {{0, 'G'}, {2, 3, 4, 8, 10, 11}},
                    {{0, 't'}, {0, 3, 8}},
                    {{1, 't'}, {1, 4, 7, 10}},
                    {{2, 'G'}, {0, 1, 3, 7, 10}},
                    {{2, 't'}, {2, 3, 4, 9}},
                    {{3, 'G'}, {1, 2, 3}},
                    {{3, 't'}, {0, 1, 2}},
                    {{4, 'G'}, {0, 1, 2, 3, 4, 9, 10}},
                    {{4, 't'}, {1, 8, 9, 11}},
                    {{5, 'G'}, {2, 7}},
                    {{5, 't'}, {2, 3, 5, 6}},
                    {{6, 'G'}, {0, 2, 3, 4, 7, 8}},
                    {{6, 't'}, {1, 4, 5, 7, 10}},
                    {{7, 'G'}, {11}},
                    {{7, 't'}, {9, 10}},
                    {{8, 'G'}, {8, 9}},
                    {{9, 'G'}, {10}},
                    {{9, 't'}, {8, 10}},
                    {{10, 'G'}, {9}},
                    {{10, 't'}, {8, 10}},
                    {{11, 'G'}, {7}},
                    {{11, 't'}, {9, 10}}
            },
            2,
            {1,2,3,4,5,6}
    };

    DFA hh = unify(h1, h2);

    return 0;
}
#endif
