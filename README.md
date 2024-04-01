# regular-languages
## Task specification

The goal of this task is to implement algorithms for finding a minimal deterministic finite automaton that accepts intersection or union of two languages defined by two finite automata. These functions will have the following C++ signatures:
- `DFA unify(const NFA&, const NFA&);`, and
- `DFA intersect(const NFA&, const NFA&);`.

Both of these functions must not only find the intersection (or union) but the finite automaton must also be minimal.
