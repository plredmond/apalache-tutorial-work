---- MODULE BinSearch5 ----
EXTENDS Integers, Sequences, Apalache

\* run with symbolic inputs:
\* apalache-mc check --cinit=ConstInit --inv=Postcondition MC5_8.tla

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
            LET mid == (low + high) \div 2 IN \* OOF integer division; rounding which way?
            LET midVal == INPUT_SEQ[mid + 1] IN \* OOF `+ 1` because TLA sequences are 1-indexed
                \//\ midVal < INPUT_KEY
                 /\ low' = mid + 1 \* OOF what about overflow?
                 /\ UNCHANGED <<high, isTerminated, returnValue>>
                \//\ midVal > INPUT_KEY
                 /\ high' = mid - 1
                 /\ UNCHANGED <<low, isTerminated, returnValue>>
                \//\ midVal = INPUT_KEY
                 /\ returnValue' = mid
                 /\ isTerminated' = TRUE
                 /\ UNCHANGED <<low, high>>
                \* OOF no help with case coverage
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
        returnValue + 1 \in MatchingIndices \* OOF `+ 1` because TLA sequences are 1-indexed
    ELSE
        returnValue < 0

Postcondition ==
    isTerminated => ReturnValueIsCorrect

====