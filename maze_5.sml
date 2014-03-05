(*
REPRESENTATION CONVENTION: Queue([x1,x2,...,xn],[y1,y2,...,ym]) represents the queue x1,x2,...,xn,ym,...,y2,y1 with head x1 and last element y1
REPRESENTATION INVARIANT: a non-empty queue is never represented by Queue([],[y1,y2,...,ym])
*)
datatype 'a queue = Queue of 'a list * 'a list;

(*
REPRESENTATION CONVENTION: mazeSection represents a coordinate in a maze, where WALL are impenetrable walls, OPEN is open space, PATH is passed open space, START is the beginning of the maze, END is the goal of the maze and PLAYER is the player.
REPRESENTATION INVARIANT: NOTE! Tillsvidare: There can only exist one START and one END
*)

datatype mazeSection = WALL | OPEN | PATH | START | END | PLAYER;

(*
REPRESENTATION CONVENTION: A move represents movement in a maze. Each constructor represents an obvious movement counterpart.
REPRESENTATION INVARIANT: none 
*)

datatype move = UP | DOWN | LEFT | RIGHT | STOP

(*
REPRESENTATION CONVENTION: Each constructor represents the status of the player in each step of the automatic maze-solver, where STOPPED represents the player having stopped, FINISHED represents the player having finished and OTW represents the player being on the way.. NOTE! vad är OTW?
REPRESENTATION INVARIANT: none
*)

datatype Status = STOPPED | FINISHED | OTW

(*
REPRESENTATION CONVENTION: If pTree is empty it is defined by emptyPtree. If pTree is non empty it is defined by pTree (position, status, Up, Down, Left, Right, partsolution, movecounter), where position is the current position in the maze, status is the current status of the player, Up, Down, Left and Right are the subtrees in corresponding direction, partsolution is the solution up until the current position and movecounter are the number of moves to the current position.
REPRESENTATION INVARIANT: none
*)

datatype pathTree = pTree of (int * int) * Status * pathTree * pathTree * pathTree * pathTree * mazeSection vector vector * int | emptyPtree

(*  TCG (a, c, m, seed)
    TYPE: int * int * int * int -> int
    PRE: 0 < m,
         0 < a < m,
         0 <= c < m,
         0 <= seed < m,
         c and m are relatively prime,
         a - 1 is divisible by all m's prime factors,
         a - 1 is divisible by 4 if m is divisible by 4
    POST: a pseudo-random number based on seed.
    EXAMPLE: LCG (32845, 1573, 229908, 123) = 133072
*)
fun LCG (a, c, m, seed) =
    (a * seed + c) mod m;

(*	power (b, e)
	TYPE: int * int -> int	
	PRE: e >= 0
	POST: b to the e:th power
	EXAMPLE: power(2, 3) = 8
*)
fun power(b, e) = 
	let
		fun power'(b, 0, a) = a
		| power'(b, e, a) = power'(b, e - 1, a * b)
	in
		power'(b, e, 1)
	end;

val a = 1664525
val c = 1013904223
val m = power(2, 32)

(*  RNG (seed)
    TYPE: int -> int
    PRE: true
    POST: A linear congruency generated int based on seed.
    EXAMPLE: RNG () = 37792
*)
fun RNG (seed) =
    LCG (a32845, c1573, m229908, seed);


(*  chance (seed, c)
    TYPE: int * int -> bool
    PRE: true
    POST: has a c % chance of returning true
    EXAMPLE: chance (121213, 30) = (false, 1251231)
*)
fun chance (seed, c) =
    (RNG (seed) mod 100) <= c;

(*  randint (start, stop, seed)
    TYPE: int * int -> int
    PRE: start < stop
    POST: returns a random int >= start and <= stop based on seed
    EXAMPLE: randint (1, 10, 1231) = 2 NOTE!
*)
fun randint (start, stop, seed) =
    ((RNG (seed)) - start) mod stop + start;

(*  toList v
    TYPE: 'a vector -> 'a list
    PRE: true
    POST: the elements of v in a list put in the same order as in v.
    EXAMPLE: toList (Vector.fromList [1, 2, 3]) = [1, 2, 3]
*)
fun toList v =
    Vector.foldr (fn(a,x) => a::x) [] v;

(*  toQueue lst
    TYPE: ‘a list -> ‘a queue
    PRE: true
    POST: returns lst as a queue
    EXAMPLE: toQueue [1,2,3,4,5] = Queue ([1, 2, 3, 4, 5], [])
*)
fun toQueue lst = Queue(lst, []);

(*  emptyQueue ()
    TYPE: unit -> ‘a queue
    PRE: true
    POST: an empty queue
    EXAMPLE: emptyQueue () = Queue([], [])
*)
fun emptyQueue () = Queue([], []);

(*  normalize (Q)
    TYPE: ’a queue -> ’a queue
    PRE: (none)
    POST: if Q is of the form Queue([],[y1,y2,...,ym]), then Queue([ym,...,y2,y1],[]), else Q
    EXAMPLE: normalize (Queue ([], [1, 2, 3, 4, 5])) = Queue ([5, 4, 3, 2, 1], []
*)
fun normalize (Queue([], back)) = Queue(rev back, [])
    | normalize (Queue(front, back)) = (Queue(front, back));
 
(*  enQueue (Q, e)
    TYPE: ’a queue * ’a -> ’a queue
    PRE: (none)
    POST: the queue Q with e added as new tail element
    EXAMPLE: enQueue (Queue ([1, 2, 3, 4, 5], []), 6) = Queue ([1, 2, 3, 4, 5], [6]
*)
fun enQueue (Queue(front, back), e) =
    normalize (Queue(front, e::back));

(*  dequeue (Q)
    TYPE: ’a queue -> ’a queue
    PRE: Q is nonempty
    POST: Q without its head element
    EXAMPLE: deQueue  (Queue ([1, 2, 3, 4, 5], [6])) = Queue ([2, 3, 4, 5], [6]
*)
fun deQueue (Queue(front, back)) =
    normalize (Queue(tl front, back));

(*  head (Q)
    TYPE: ’a queue -> ’a
    PRE: Q is nonempty
    POST: the head element of Q
    EXAMPLE: Queue  (Queue ([1, 2, 3, 4, 5], [6])) = 1
*)
fun hdQueue (Queue(front, back)) = hd front;

(*  existsQueue (Q, e)
    TYPE: ‘’a queue * ‘’a -> bool
    PRE: true
    POST: true if e exists in Q, false otherwise
    EXAMPLE: existsQueue  (Queue ([1, 2, 3, 4, 5], [6,7,8]), 6) = true
*)
fun existsQueue (Queue(front, back), e) =
    List.exists (fn x => x = e) (front @ back);

(*  isEmptyQueue (Q)
    TYPE: ‘a queue -> bool
    PRE: true
    POST: true if Q is empty, false if it is non-empty
    EXAMPLE: isEmptyQueue (Queue ([], [])) = true
*)
fun isEmptyQueue (Queue(front, back)) = List.null(front);

(*  getBlock (maze, (x, y))
    TYPE: mazeSection vector vector * (int * int) -> mazeSection
    PRE: 0 <= x < |row|, 0 <= y < |maze|
    POST: The mazeSection found at (x,  y)
    EXAMPLE: NOTE!
*)
fun getBlock (maze, (x,y)) = Vector.sub(Vector.sub(maze,y),x);

(*  getBlockOption (maze, (x, y))
    TYPE: mazeSection vector vector * (int * int) -> mazeSection option
    PRE:  true
    POST: SOME mazeSection at (x, y), or NONE if x or y is out of bounds
    EXAMPLE: NOTE!
*)
fun getBlockOption (maze, (x,y)) =
    SOME (getBlock (maze, (x,y))) handle Subscript => NONE
    
(*  findBlocks (maze, block) NOTE!
    TYPE: ''a vector vector * ''a -> (int * int) list
    PRE: true
    POST: a list of coordinates for any and all block
    EXAMPLE:findBlocks (testmaze, START) = [(1, 0)]: (int * int) list NOTE!
    VARIANT: |maze|
*)
fun findBlocks(maze, block) =
    let (* Build list of coords for all blocks that matches in x-direction *)     
        fun foldx (yi, y, coordlist) =
            Vector.foldli (fn (i, x, l) => if x = block then (i,yi)::l else l) coordlist y
    in
        Vector.foldli (fn (i, y , coordlist) => foldx(i, y, coordlist)) [] maze
    end;

(*	lookAround (maze, x, y)
    TYPE: mazeSection vector vector * int * int -> (int * int) option list
    PRE: true
    POST: A list of the coordinates of the adjacent OPEN mazeSections.
    EXAMPLE: NOTE!
*)
fun lookAround (maze, (x, y)) =
	let
		val adj = [(x, y + 1), (x, y - 1), (x + 1, y), (x - 1, y)]
	in
		map Option.valOf (List.filter (fn x => x <> NONE) (map (fn x => if getBlockOption (maze, x) <> NONE andalso (getBlockOption (maze, x) = SOME OPEN orelse getBlockOption (maze, x) = SOME END) then SOME x else NONE) adj))
	end;


(*  queueAdder (queue, donelist, coordlist)
    TYPE: ''a queue * ''a list * ''alist -> ''a queue
    PRE: true
    POST: queue with all elements of coordlist that aren’t found in queue or donelist added
    EXAMPLE: queueAdder (Queue([1,2], [3]), [4], [3, 4, 5]) = Queue([1, 2], [5, 3])
*)
fun queueAdder (queue, donelist, []) = queue
    | queueAdder (queue, donelist, coordlist) =
        if not (List.exists (fn x => x = hd coordlist) donelist) andalso not (existsQueue(queue, hd coordlist)) then
            queueAdder(enQueue (queue, hd coordlist), donelist, tl coordlist)
        else
            queueAdder(queue, donelist, tl coordlist);

(*  indexOf (vec, e)
    TYPE: 'a vector * 'a -> int
    PRE:
    POST: the index of the first e in vec
    SIDE-EFFECTS: Raises Option Empty if e isn't in vec.
    EXAMPLE: indexOf([1, 2, 3], 3) = 2
*)
fun indexOf (vec, e) =
	#1 (Option.valOf (Vector.findi (fn (i, x) => x = e) vec))

(*  pathcheck maze
    TYPE: mazeSection vector vector -> bool
    PRE: true
    POST: true if there is a path from start to end, false otherwise.
    EXAMPLE: ## ##            ## ##
             ## ##            ## ##
             ## ##            #####
             ## ## = true     ## ## =false
    
*)
fun pathcheck maze =
    let
        val startpos = (indexOf (Vector.sub(maze, 0), START), 0)
        val mazeheight = Vector.length(maze)
        fun mazeTraverse (maze, pos, donelist, queue) =
            if isEmptyQueue queue then
                false
            else if (fn (x, y) => y) (hdQueue queue) = mazeheight - 1 then
                true
            else
                mazeTraverse (maze, hdQueue queue, pos::donelist, deQueue (queueAdder(queue, pos::donelist, lookAround(maze, (hdQueue queue)))))
    in
        mazeTraverse(maze, startpos, [], queueAdder(emptyQueue (), [], lookAround (maze, startpos)))
    end;


(*  validPath (prevRow, currRow, x)
    TYPE: mazeSection vector * ‘a * int -> bool
    PRE: y > 0
    POST: false if prevRow and currRow coincide so that any OPEN makes a square shape, true otherwise
    EXAMPLE: ##  ##                ## ##
             ## ¤## -> false       ## ¤# -> true         # is wall, ¤ is current position
*)
fun validPath (prevRow, currRow, x) =
    not ((Vector.sub(prevRow, x - 1) = OPEN) andalso (Vector.sub(prevRow, x) = OPEN) andalso (Vector.sub(currRow, x - 1) = OPEN));

(*  singleRow (row, seed, mazeSec, n)
    TYPE: mazeSection vector -> mazeSection vector
    PRE: |row| >= 3, n >= 1
    POST: returns row with up to n random elements, based on seed, between the first and last element in row changed to mazeSec
    EXAMPLE: NOTE!
*)
fun singleRow (row, seed, mazeSec, n) =
    let
        val vectorLength = Vector.length row
    in
        if n = 1 then
            Vector.update(row, randint(1, vectorLength - 2, seed), mazeSec)
        else
            singleRow (Vector.update(row, randint(1, vectorLength - 2, seed), mazeSec), RNG(seed), mazeSec, n - 1)
    end;

(*  rowMaker (prevRow, currRow, x, density)
    TYPE: mazeSection vector * mazeSection vector * int
    PRE: x >= 1
    POST: returns currRow with some WALLs changed to OPEN
    EXAMPLE: NOTE!
*)
fun rowMaker (prevRow, currRow, x, density, seed) =
    let
        val lastx = Vector.length(currRow) - 1
    in
        if x < lastx then
            if validPath(prevRow, currRow, x) andalso chance(seed, density) then
                rowMaker(prevRow, Vector.update(currRow, x, OPEN), x + 1, density, RNG(seed))
            else
                rowMaker(prevRow, currRow, x + 1, density, RNG(seed))
        else
            currRow
    end;

(*  mazePather (maze, density, seed)
    TYPE: mazeSection vector vector * int * int  -> mazeSection vector vector
    PRE: 0< density < 100 NOTE!
    POST: maze with WALLs changed to OPEN depending on density (and if it satisfies the validPath predicate) NOTE!.
    EXAMPLE: NOTE!
*)
fun mazePather (maze, density, seed, starts, ends) =
    let
        val mazeLength = Vector.length(maze)
        (*  mazePather' (maze, prevRows, n, density, seed)
            TYPE: mazeSection vector vector * mazeSection vector list * int * int * int -> mazeSection vector vector
            PRE: 0< density < 100
            POST: NOTE!
            EXAMPLE: NOTE!
        *)
        fun mazePather' (maze, prevRows, n, density, seed) =
            if n = 0 then
                mazePather' (maze, [singleRow(Vector.sub(maze, n), seed, START, starts)], n + 1, density, RNG (seed))
            else if n = mazeLength - 1 then
                    if pathcheck (Vector.fromList(prevRows @ [singleRow(Vector.sub(maze, n), seed, END, ends)])) then
                        Vector.fromList(prevRows @ [singleRow(Vector.sub(maze, n), seed, END, ends)])
                    else
                        mazePather'(maze, prevRows, n, density, RNG(seed))                        
            else if pathcheck (Vector.fromList (prevRows @ [rowMaker(List.hd(List.rev(prevRows)), Vector.sub(maze, n), 1, density, seed)])) then
                mazePather' (maze, (prevRows @ [rowMaker(List.hd(List.rev(prevRows)), Vector.sub(maze, n), 1, density, seed)]), n + 1, density, RNG(seed))
            else
                mazePather' (maze, prevRows, n, density, RNG(seed))
    in
        mazePather' (maze, [], 0, density, seed)
    end;


(*  mazeGen (x, y, density)
    TYPE: int * int -> mazeSection vector vector
    PRE: x > 2, y > 2, 0 < density < 100
    POST: a randomized maze with no paths wider than 1 and a path to the end
*)
fun mazeGen (x, y, density) =
    let
        val row = Vector.tabulate (x, (fn a => WALL))
        val maze = Vector.tabulate (y, (fn a => row))
    in
        mazePather(maze, density, Time.toMicroseconds(Time.now ()), 1, 1)
    end;
    
(*  printRow row
    TYPE: maseSection vector -> unit
    PRE: true
    POST: ()
    SIDE-EFFECTS: prints an ASCII representation of row to the standard output where WALL = “#”, OPEN " " etc NOTE!
    EXAMPLE: NOTE!
*)
fun printRow row =
    (Vector.app
        (fn x =>
            if x = WALL then print "#"
            else if x = OPEN then print " "
            else if x = PATH then print "%"
            else if x = PLAYER then print "O"
            else if x = START then print "S"
            else if x = END then print "E"
            else print "?") row;
            print ("\n"));

(*  mazePrinter maze
    TYPE: mazeSection vector vector -> unit
    PRE: true
    POST: ()
    SIDE-EFFECTS: prints maze to the standard output represented by ASCII where WALL = “#”, OPEN = “ “, PATH = “%”, PLAYER = “O”, START = “S” and END = “E”  NOTE!
    VARIANT: |maze|
*)
fun mazePrinter maze = 
	(print (foldr op^ "" (List.tabulate(50,(fn x => "\n")))); Vector.app printrow maze );

(*	readLine ()
    TYPE: unit -> string
    PRE: true
    POST: the current line of input from stdIn
    SIDE-EFFECTS: advances the stream position of stdIn
*)
fun readLine () =
    valOf (TextIO.inputLine TextIO.stdIn);

(*	readKey ()
    TYPE: unit -> move
    PRE: true
    POST: a move depending on user input, w = UP, a = LEFT, s = DOWN, d = RIGHT, anything else = STOP.
    SIDE-EFFECTS: prints the maze (NOTE! - No it doesn’t…)
*)
fun readKey () =
(   case readLine () of
        "w\n" => UP
      | "W\n" => UP
      | "a\n" => LEFT
      | "A\n" => LEFT
      | "s\n" => DOWN
      | "S\n" => DOWN
      | "d\n" => RIGHT
      | "D\n" => RIGHT
      | r => STOP
);

(*  addToMaze (maze, buildingblock, coordinates) NOTE!
    TYPE: 'a vector vector * 'a * int list -> 'a vector vector
    PRE: true
    POST: maze with the block at coordinates replaced with buildingblock
    EXAMPLE: NOTE!
*)
fun addToMaze(maze,buildingblock,(column,row)) =
    Vector.update(maze,row,Vector.update(Vector.sub(maze,row),column,buildingblock));

(* 	possibleMoves (maze, (column, row)
	TYPE: mazeSection vector vector * int list -> bool
	PRE: true
	POST: a list of four bools, corresponding to the directions up, down, left, right, true for any direction there is a possible move towards (column, row), false if not NOTE!
	EXAMPLE: possibleMoves (testmaze,(0,0)) = [false, false, false, true] NOTE!
*)
fun possibleMoves (maze,(column,row)) =
	let
		val position = (column,row)
		val up = 	if row = 0 then
						false
					else
						not (getBlock(maze,(column,row-1)) = WALL orelse getBlock(maze,(column,row-1)) = PATH)
		val down = 	if row = Vector.length(maze)-1 then
						false
					else
						not (getBlock(maze,(column,row+1)) = WALL orelse getBlock(maze,(column,row+1)) = PATH)
		val left = 	if column = 0 then
						false
					else
						not (getBlock(maze,(column-1,row)) = WALL orelse getBlock(maze,(column-1,row)) = PATH)
		val right = if column = Vector.length(Vector.sub(maze,0))-1 then
						false
					else
						not (getBlock(maze,(column+1,row)) = WALL orelse getBlock(maze,(column+1,row)) = PATH)
	in
		[up,down,left,right]
	end;

(*  manualSolve maze
    TYPE: mazeSection vector vector -> unit
    PRE: true
    POST: ()
    SIDE-EFFECTS: prints the current state of the maze, if completed it also prints number of moves made
    EXAMPLE: NOTE!
*)
fun manualSolve maze =
	let
		val startposition = hd(findBlocks(maze,START))
		val moves = 0
		(* 	manualSolve' (currentMaze,movement,(column,row),moves
			TYPE: mazeSection vector vector * move * (int*int) * int -> unit
			PRE: currentMaze is not empty
			POST: unit
			SIDE-EFFECTS: prints the current state of the maze, if completed it also prints number of moves made.
			EXAMPLE: NOTE!
		*) 
		(*VARIANT: ??? NOTE! Styr själv? Men anropar funktionen?*)
		fun manualSolve' (currentMaze,movement,(column,row),moves) =
			let
				val previousMaze = currentMaze
				val currentMaze = addToMaze(currentMaze,PATH,(column,row))
				val position =
					(case movement of
						UP => 	if not (getBlock(currentMaze,(column,row-1)) = WALL) then
									(column,row-1)
								else
									(column,row)
						| LEFT => 	if not (getBlock(currentMaze,(column-1,row)) = WALL) then
										(column-1,row)
									else 
										(column,row)
						| DOWN => 	if not (getBlock(currentMaze,(column,row+1)) = WALL) then
										(column,row+1)
									else
										(column,row)
						| RIGHT => 	if not (getBlock(currentMaze,(column+1,row)) = WALL) then
										(column+1,row)
									else
										(column,row)
						| _ => (column,row)
						)
				val currentMaze = addToMaze(currentMaze,PLAYER,position)
			in
				if getBlock(previousMaze,position) = END then
					(mazePrinter currentMaze; print "CONGRATULATIONS!\nYou solved the maze in "; print (Int.toString(moves)); print " moves.\n")
				else 
					(mazePrinter currentMaze; manualSolve' (currentMaze,readKey(),position,moves+1)) (* NOTE! man får fler moves när man går in i en vägg.*)
			end;
	in	
		manualSolve' (maze,readKey(),startposition,moves)
	end;

(* getPath tree
    TYPE: pathTree -> pathTree
    PRE: pathTree is a valid pathTree and not emptyPtree
    POST: a pathTree with each node representing a position and all possible moves from a position stored as subtrees to that node.
    EXAMPLE: NOTE! (I dont feel like doing this ]:)
*)
(* VARIANT: |maze| NOTE! *)
fun getPath (pTree ((column,row),status,uptree,downtree,leftree,righttree,maze,moves)) =
	let
		val pMs = possibleMoves(maze,(column,row))
		val up = if List.nth(pMs,0) then
					(if Vector.sub((Vector.sub(maze,row-1)),column) = END then
						pTree((column,row-1),FINISHED,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(addToMaze(maze,PLAYER,(column,row-1)),PATH,(column,row)),moves+1)
					 else
						getPath(pTree((column,row-1),OTW,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(maze,PATH,(column,row)),moves+1))
					)
				 else
					pTree((column,row),STOPPED,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(maze,PLAYER,(column,row)),moves)
		val down =  if List.nth(pMs,1) then
						(if Vector.sub((Vector.sub(maze,row+1)),column) = END then
							pTree((column,row+1),FINISHED,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(addToMaze(maze,PLAYER,(column,row+1)),PATH,(column,row)),moves+1)
						 else
							getPath(pTree((column,row+1),OTW,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(maze,PATH,(column,row)),moves+1))
						)
					else
						pTree((column,row),STOPPED,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(maze,PLAYER,(column,row)),moves)
		val left = 	if List.nth(pMs,2) then
						(if Vector.sub((Vector.sub(maze,row)),column-1) = END then
							pTree((column-1,row),FINISHED,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(addToMaze(maze,PLAYER,(column-1,row)),PATH,(column,row)),moves+1)
						else
							getPath(pTree((column-1,row),OTW,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(maze,PATH,(column,row)),moves+1))
						)
					else 
						pTree((column,row),STOPPED,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(maze,PLAYER,(column,row)),moves)
		val right = if List.nth(pMs,3) then
						(if Vector.sub((Vector.sub(maze,row)),column+1) = END then
							pTree((column+1,row),FINISHED,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(addToMaze(maze,PLAYER,(column+1,row)),PATH,(column,row)),moves+1)
						else
							getPath(pTree((column+1,row),OTW,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(maze,PATH,(column,row)),moves+1))
						)
					else
						pTree((column,row),STOPPED,emptyPtree,emptyPtree,emptyPtree,emptyPtree,addToMaze(maze,PLAYER,(column,row)),moves)
	in
		pTree((column,row),OTW,up,down,left,right,maze,moves)
	end;

(*  traverseTree Ptree
    TYPE: pTree -> (mazeSection vector vector * int) list
    PRE: pTree is not emptyPtree
    POST: list of tuples each containing a solved maze and the number of moves used to solve it. Returns ()
    EXAMPLE: NOTE!
*)
fun traverseTree (pTree(position,status,uptree,downtree,lefttree,righttree,maze,moves)) =
    let
       (* 	traverseTree' Ptree, accumulator
			TYPE: pTree * (mazeSection vector vector * int) list -> (mazeSection vector vector * int) list
			PRE: pTree is not emptyPtree
			POST: list of tuples each containing a partially/wholly solved maze and the number of moves used to get to the current position.
			EXAMPLE: NOTE!
		*)
		(* VARIANT: |Ptree| *)
 
		fun traverseTree' (pTree(position,status,uptree,downtree,lefttree,righttree,maze,moves), a) =
            if status = FINISHED then
                (maze,moves)::a
            else if status = OTW then
                traverseTree'(uptree,traverseTree'(downtree,traverseTree'(lefttree,traverseTree'(righttree,a))))
            else
				a
				| traverseTree' (_,a) = a
    in
        if status = OTW then
            traverseTree'((uptree,traverseTree'((downtree,traverseTree'((lefttree,traverseTree'((righttree,[]))))))))
        else if status = FINISHED then
            [(maze,moves)]
        else
            [(maze,~1)]
    end;

(* solveMaze maze
    TYPE: maze -> unit
    PRE: maze has a start, an ending and at least one solution.
    POST: unit
    SIDE-EFFECTS: prints the solved maze.
    EXAMPLE: NOTE!
*)
fun solveMaze maze =
	let
		val starttree = pTree(hd(findBlocks(maze,START)),OTW,emptyPtree, emptyPtree, emptyPtree, emptyPtree, maze,0)
		val solution = hd(traverseTree(getPath (starttree))) (* NOTE! Här ska ändras så att den väljer den kortaste vägen*)
		val solvedMaze = (fn (x,y) => x) solution
		val moves = (fn (x,y) => y) solution
	in
		(mazePrinter solvedMaze;print ("Moves: "^(Int.toString(moves))^".\n"))
	end;

val frstrow = Vector.fromList([WALL, WALL, OPEN, WALL, WALL, WALL, OPEN, WALL, OPEN, WALL]);
val scndrow = Vector.fromList([WALL, WALL, WALL, WALL, WALL, WALL, WALL, WALL, WALL, WALL]);

val testmaze = Vector.fromList([
(Vector.fromList[WALL, START, WALL, WALL, WALL, WALL, WALL, WALL, WALL, WALL]),
(Vector.fromList[WALL, OPEN, WALL, OPEN, OPEN, OPEN, OPEN, OPEN, OPEN, WALL]),
(Vector.fromList[WALL, OPEN, OPEN, OPEN, WALL, OPEN, WALL, WALL, OPEN, WALL]),
(Vector.fromList[WALL, WALL, WALL, WALL, WALL, OPEN, OPEN, OPEN, OPEN, WALL]),
(Vector.fromList[WALL, WALL, WALL, WALL, OPEN, OPEN, WALL, WALL, WALL, WALL]),
(Vector.fromList[WALL, WALL, WALL, WALL, OPEN, WALL, WALL, WALL, WALL, WALL]),
(Vector.fromList[WALL, WALL, WALL, WALL, END, WALL, WALL, WALL, WALL, WALL])]);


