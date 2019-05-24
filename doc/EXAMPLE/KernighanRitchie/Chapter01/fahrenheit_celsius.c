//
// K&R, 2nd edition, page 15
//

#define LOWER 0
#define UPPER 300
#define STEP 20

main () {
  int fahr;
  for (fahr = LOWER; fahr <= UPPER; fahr += STEP) {
    printf ("%3d %6.1f\n", fahr, (5.0/9.0) * (fahr - 32)) ;
  } // end of [for]

} /* end of [main] */

/* ****** ****** */

/* end of [fahrenheit_celsius.c] */
