---- MODULE BinSearch3 ----
EXTENDS Integers, Sequences, Apalache

\* $ apalache-mc check --inv=ReturnValueIsCorrect MC3_8.tla
\* fails because that condition is only true after termination; _apalache-out/**/violation*tla contains a counterexample
\* $ apalache-mc check --inv=Postcondition MC3_8.tla
\* passes

CONSTANTS
    \* the input sequence
    \* @type: Seq(Int);
    INPUT_SEQ,
    \* the key to search for
    \* @type: Int;
    INPUT_KEY,
    \* bit-width of machine integers
    \* @type: Int;
    INT_WIDTH

\* largest unsigned integer
MAX_UINT == 2^INT_WIDTH
\* largest signed integer
MAX_INT == 2^(INT_WIDTH - 1) - 1
\* smallest signed integer
MIN_INT == -2^(INT_WIDTH - 1)

VARIABLES
    \* lower bound of search interval (incl)
    \* @type: Int;
    low,
    \* upper bound of search interval (incl)
    \* @type: Int;
    high,
    \* terminated?
    \* @type: Bool;
    isTerminated,
    \* return value?
    \* @type: Int;
    returnValue

Init ==
    /\ low = 0
    /\ high = Len(INPUT_SEQ) - 1
    /\ isTerminated = FALSE
    /\ returnValue = 0

Next ==
    IF ~isTerminated THEN
        IF low <= high THEN
            \* TODO
            UNCHANGED <<low, high, isTerminated, returnValue>>
        ELSE
            /\ isTerminated' = TRUE
            /\ returnValue' = -(low + 1)
            /\ UNCHANGED <<low, high>>
    ELSE
        UNCHANGED <<low, high, isTerminated, returnValue>>

\* relates input sequence to return value according to the java
\* spec for the binary search function
\* "guarantees that the return value will be >= 0 iff key is found"
ReturnValueIsCorrect ==
    LET MatchingIndices ==
        { i \in DOMAIN INPUT_SEQ: INPUT_SEQ[i] = INPUT_KEY }
    IN
    IF MatchingIndices /= {} THEN
        returnValue + 1 \in MatchingIndices
    ELSE
        returnValue < 0

Postcondition ==
    isTerminated => ReturnValueIsCorrect

====
