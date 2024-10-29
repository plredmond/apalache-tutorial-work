---- MODULE BinSearch2 ----
EXTENDS Integers, Sequences, Apalache

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
    low,
    \* upper bound of search interval (incl)
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

====
