---- MODULE MC2_8 ----

\* fix 8 bits
INT_WIDTH == 8

\* input sequence to try
\* @type: Seq(Int);
INPUT_SEQ == << >>

\* element to search for
INPUT_KEY == 10

VARIABLES
    \* @type: Int;
    low,
    \* @type: Int;
    high,
    \* @type: Bool;
    isTerminated,
    \* @type: Int;
    returnValue

INSTANCE BinSearch2

====
