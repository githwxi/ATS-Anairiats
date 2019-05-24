\begin{figure}[thp]
\begin{verbatim}
abstype rat // a boxed abstract type for rational numbers

exception DenominatorIsZeroException // an exception constructor

// rat_make_int (p) = p / 1
fun rat_make_int (numer: int): rat

// rat_make_int_int (p, q) = p / q
fun rat_make_int_int (numer: int, denom: int): rat

symintr rat_make // [rat_make] is introduced for overloading
overload rat_make with rat_make_int
overload rat_make with rat_make_int_int

fun add_rat_rat (r1: rat, r2: rat): rat and sub_rat_rat (r1: rat, r2: rat): rat
fun mul_rat_rat (r1: rat, r2: rat): rat and div_rat_rat (r1: rat, r2: rat): rat

overload + with add_rat_rat; overload - with sub_rat_rat
overload * with mul_rat_rat; overload / with div_rat_rat

fun fprint_rat (out: FILEref, r: rat): void

// the symbol [fprint] is already introduced elsewhere
overload fprint with fprint_rat
\end{verbatim}
\caption{The content of rational.sats}
\label{figure:rational.sats}
\end{figure}
