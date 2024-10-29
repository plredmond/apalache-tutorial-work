---- MODULE BinSearch1 ----
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

Init == TRUE

Next == TRUE
====
