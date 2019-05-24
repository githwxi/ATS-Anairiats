\begin{verbatim}
typedef complex = @{real=double, imag=double}

// extracting out record fields by pattern matching
fn magnititute_complex (z: complex): double = let
  val @{real= r, imag= i} = z // the @ symbol cannot be omitted
in
  sqrt (r * r + i * i)
end

// extracting out record fields by field selection
fn add_complex_complex (z1: complex, z2: complex): complex = begin
  @{real= z1.real + z2.real, imag= z1.imag + z2.imag}
end
\end{verbatim}
