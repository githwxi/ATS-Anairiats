//
//
// code for illustration in linear-arrays.html
//
//

(* ****** ****** *)

// function style
fn fact_val (x: int): int = loop (x, 1) where {
  fun loop (x: int, res: int): int =
    if x > 0 then loop (x-1, x * res) else res
  // end of [loop]
} // end of [fact_val]

// imperative style
fn fact_var (x: int): int = let
  var x: int = x; var res: int = 1
  val () = while (x > 0) (res := x * res; x := x - 1)
in
  res  
end // end of [fact_var]

(* ****** ****** *)

// imperative style based on persistent references, which looks
// awkward and runs inefficiently (in terms of both time and space)
fn fact_ref (x: int): int = let
  val x = ref<int> (x); val res = ref<int> (1)
  val () = while (!x > 0) (!res := !x * !res; !x := !x - 1)
in
  !res
end // end of [fact_ref]

(* ****** ****** *)

fun loop {x,res:addr}
  (pf_x: !int @ x, pf_res: !int @ res | p_x: ptr x, p_res: ptr res): void =
  if !p_x > 0 then begin
    !p_res := !p_x * !p_res; !p_x := !p_x - 1; loop (pf_x, pf_res | p_x, p_res)
  end // end of [loop]
// end of [loop]

fn fact_var2 (x: int): int = let
  var x: int = x; var res: int = 1
in
  loop (view@ x, view@ res | &x, &res); res
end // end of [fact_var2]

(* ****** ****** *)

(* end of [val-and-var.dats] *)

