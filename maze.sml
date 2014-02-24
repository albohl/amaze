(* REPRESENTATION CONVENTION: NOTE!
REPRESENTATION INVARIANT: none *)

datatype mazeSection = WALL | OPEN | PATH

(* LCG (a, c, m, seed, n)
TYPE: int * int * int * int -> int
PRE:	0 < m, 
		0 < a < m, 
		0 <= c < m, 
		0 <= seed < m, 
		c and m are relatively prime, 
		a - 1 is divisible by all m's prime factors, 
		a - 1 is divisible by 4 if m is divisible by 4
POST: the n:th int from the linear congruence generator using a, c, m and seed.
EXAMPLE:
m = 2 * 2 * 3 * 7 * 7 * 17 * 23 = 229908
c = 11 * 11 * 13 = 1573
a = 2 * 2 * 3 * 7 * 17 * 23 + 1 = 32845
*)

fun LCG (a, c, m, seed) = (a * seed + c) mod m

(* validatePath (maze, x, y)
TYPE: mazeSection vector vector * int * int -> bool
PRE: y > 0
POST: false if the two mazeSections above and the one to the left are OPEN, true otherwise
EXAMPLE: ##  ##				## ##
		 ## ¤## -> false 	## ¤# -> true 
		 
		 # is wall, ¤ is current position
*)

fun validatePath x = 1

(* firstRow maze
TYPE: mazeSection vector vector -> mazeSection vector
PRE: x > 2
POST: returns the first vector in maze with a random element that isn't on either end changed to OPEN
*)

fun firstRow maze = 
let
	val vectorLength = Vector.length(Vector.sub(maze, 0))
in
	Vector.update(Vector.sub(maze, 0), ((LCG (32845, 1573, 229908, Time.toMicroseconds(Time.now ())) - 1) mod (vectorLength - 1)) + 1, OPEN)
end

(* toList v
TYPE: 'a vector -> 'a list
PRE: true
POST:
EXAMPLE:
*)

fun toList v =
let
	val l = Vector.length(v)
	fun toList' (v, n) = if n = l then [] else Vector.sub(v, n) :: toList' (v, n + 1)
in
	toList' (v, 0)
end

(* holepuncher (maze, seed)
TYPE: mazeSection vector list * int -> unit
PRE:
POST:
*)

(* fun holepuncher (maze, seed) = Vector.sub(Vector.sub(maze, y), x) *)

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
  (*
fun testlcg (seed, n) = (LCG (a, c, m, seed, n)) mod 10

val arr = Vector.fromList (List.tabulate (10, (fn x => 0)))

fun testerthingy (arr, 0) = ()
  | testerthingy (arr, n) = (Vector.update(arr, testlcg ((Time.toMicroseconds(Time.now ())), n), 1 + Vector.sub(arr, testlcg ((Time.toMicroseconds(Time.now ())), n))); testerthingy (arr, n - 1))

fun testlcgtester 0 = print (Int.toString (testlcg ((Time.toMicroseconds(Time.now ())), 0))^"\n")
  | testlcgtester n = (print (Int.toString (testlcg ((Time.toMicroseconds(Time.now ())), n))^"\n"); testlcgtester (n - 1))
  *)