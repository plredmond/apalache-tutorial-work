---- MODULE MC7_8 ----
EXTENDS Apalache

\* fix 8 bits
INT_WIDTH == 8

\* reason about all sequences wiht "ConstInit"
CONSTANTS \* (parameters)
    \* @type: Seq(Int);
    INPUT_SEQ,
    \* @type: Int;
    INPUT_KEY

VARIABLES \* (state)
    \* @type: Int;
    low,
    \* @type: Int;
    high,
    \* @type: Bool;
    isTerminated,
    \* @type: Int;
    returnValue,
    \* @type: Int;
    nSteps

INSTANCE BinSearch7

ConstInit ==
    /\ INPUT_KEY \in Gen(1)
    /\ INPUT_SEQ \in Gen(MAX_INT)
    \* QQQ these "Gen(…)" wrappers are sometimes optional; when?

====
