use "bst";
use "avl";
use "rand";

structure Node : ORDERED = struct
	type element = int;
	fun lt (a,b) = if a < b then true else false;
end;

structure IntBST = AVLcreate(Node);

val max =  10000000;
val nodes = 1000000;

fun rand m = let
	val r = Rand.srand (Time.toSeconds (Time.now()));
in
	fn () => r() mod m
end;

val nrand = rand max;

local
	fun insertloop rnd m t i =
		if i < m then
			insertloop rnd m (IntBST.insert (t,rnd())) (i+1)
		else t
in
	fun inserts t = let
		val theloop = insertloop nrand nodes;
		val timer = Timer.startCPUTimer();
		val t = theloop t 0;
		val {nongc={usr=usertime, ...}, ...} = Timer.checkCPUTimes timer;
	in
		(t,Time.toMilliseconds usertime)
	end
end;

local
	fun lookuploop rnd m t i l =
		if i < m then
			case IntBST.lookup (t,rnd()) of
				SOME _ =>  lookuploop rnd m t (i+1) (l+1)
			|	NONE => lookuploop rnd m t (i+1) l
		else l
in
	fun lookups t = let
		val theloop = lookuploop nrand nodes;
		val timer = Timer.startCPUTimer();
		val l = theloop t 0 0;
		val {nongc={usr=usertime, ...}, ...} = Timer.checkCPUTimes timer;
	in
		(l,Time.toMilliseconds usertime)
	end
end;

local
	fun deleteloop rnd m t i l =
		if i < m then
			case IntBST.delete (t,rnd()) of
				(true,t) =>  deleteloop rnd m t (i+1) (l+1)
			|	(false,t) => deleteloop rnd m t (i+1) l
		else (t,l)
in
	fun deletes t = let
		val theloop = deleteloop nrand nodes;
		val timer = Timer.startCPUTimer();
		val (t,l) = theloop t 0 0;
		val {nongc={usr=usertime, ...}, ...} = Timer.checkCPUTimes timer;
	in
		(t,l,Time.toMilliseconds usertime)
	end
end;

fun main () = let
	val (t,inserttime) = inserts IntBST.create;
	val (l,lookuptime) = lookups t;
in
	print ("Inserts took " ^ (Int.toString inserttime) ^ "ms.\n");
	IntBST.test t;
	print "Tree is balanced\n";
	print ("Lookups took " ^ (Int.toString lookuptime) ^ "ms.\n");
	print ("There were " ^ (Int.toString l) ^ " successful lookups.\n")
end;
