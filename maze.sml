(* REPRESENTATION CONVENTION: TODO
REPRESENTATION INVARIANT: none *)

datatype mazeSection = WALL | OPEN | PATH

(* LCG (a, c, m, seed)
TYPE: int * int * int -> int
PRE:	0 < m, 
		0 < a < m, 
		0 <= c < m, 
		0 <= seed < m, 
		c and m are relatively prime, 
		a - 1 is divisible by all m's prime factors, 
		a - 1 is divisible by 4 if m is divisible by 4
POST: a psuedorandom number based on seed.
EXAMPLE: LCG (32845, 1573, 229908, 123) = 133072 *)

fun LCG (a, c, m, seed) = (a * seed + c) mod m

(* RNG seed
TYPE: int -> int
PRE: true
POST: An LCG random int based on seed.
EXAMPLE: RNG () = 37792 *)

fun RNG (seed) = LCG (32845, 1573, 229908, seed)

(* TRNG ()
TYPE: unit -> int
PRE: true
POST: a random int
EXAMPLE: RNG () = 37792
time dependent, will give the same number if called multiple times too fast, (more than once per function call) *)

fun TRNG () = LCG (32845, 1573, 229908, Time.toMicroseconds(Time.now ()))

(* chance (seed, c)
TYPE: int * int -> bool
PRE: none
POST: has a c % chance of returning true
EXAMPLE: chance (121213, 30) = false
*)

fun chance (seed, c) = (RNG (seed) mod 100) <= c

(* randint (start, stop)
TYPE: int * int -> int
PRE: start < stop
POST: returns an int >= start and <= stop
EXAMPLE: randint (1, 10) = 2 *)

fun randint (start, stop) = ((TRNG ()) - start) mod stop + start

(* toList v
TYPE: 'a vector -> 'a list
PRE: true
POST: a list consisting of v's elements in the same order as in the vector
EXAMPLE: toList (Vector.fromList [1, 2, 3]) = [1, 2, 3]*)

fun toList v =
let
	val l = Vector.length(v)
	fun toList' (v, n) = if n = l then [] else Vector.sub(v, n) :: toList' (v, n + 1)
in
	toList' (v, 0)
end

(* validPath (maze, x, y)
TYPE: mazeSection vector vector * int * int -> bool
PRE: y > 0
POST: false if the two mazeSections above and the one to the left are OPEN, true otherwise
EXAMPLE: ##  ##				## ##
		 ## ¤## -> false 	## ¤# -> true		 # is wall, ¤ is current position *)

fun validPath (maze, x, y) = not (Vector.sub(Vector.sub(maze, y - 1), x - 1) = OPEN andalso Vector.sub(Vector.sub(maze, y - 1), x) = OPEN andalso Vector.sub(Vector.sub(maze, y), x - 1) = OPEN)

(* firstRow maze
TYPE: mazeSection vector vector -> mazeSection vector
PRE: x > 2
POST: returns the first vector in maze with a random element that isn't on either end changed to OPEN *)

fun firstRow row = 
let
	val vectorLength = Vector.length row
in
	Vector.update(row, randint(1, vectorLength - 2), OPEN)
end

(*  (rows, density)
TYPE: mazeSection vector vector
PRE: rows is nonempty
POST: Rows with a density chance of having holes punched where they satisfy the validPath predicate. 
*)

(* holepuncher (maze)
TYPE: mazeSection vector vector * int -> unit
PRE:
POST:
*)

(* fun holepuncher (maze, seed, x, y, density) = 
	let
		val mazeHeight = Vector.length(maze)
	in
		firstRow(Vector.sub(maze, 0))

(* mazeGen (x, y, density)
TYPE: int * int * int -> mazeSection vector vector
PRE: x > 0, y > 0, density > 0
POST: a maze with no paths wider than 1 and a path to the end *)

fun mazeGen (x, y, density) = 
let
	val row = Vector.tabulate (x, (fn a => WALL))
in
	Vector.tabulate (y, (fn a => row))
end

fun printrow row = (Vector.app (fn x => if x = WALL then print "#" else if x = OPEN then print " " else print "%") row; print ("\n"))

(* mazePrinter maze
TYPE: mazeSection vector vector -> unit
PRE: true
POST: none
SIDE-EFFECTS: prints maze to the standard output
VARIANT: |maze|
*)

fun mazePrinter maze = List.app printrow maze

fun power (b, e) =
let  
	fun power' (b, 0, ack) = ack
	  | power' (b, e, ack) = power' (b, e - 1, b * ack)
in
	power' (b, e, 1)
end

val m = 229908
val a = 32845
val c = 1573

val arr = Array.tabulate (10, (fn x => 0))

fun LCGtest (seed, 0) = ()
  | LCGtest (seed, n) = (Array.update(arr, LCG(a, c, m, seed) mod 10, Array.sub(arr, LCG(a, c, m, seed) mod 10) + 1); LCGtest (LCG(a, c, m, seed), n - 1))