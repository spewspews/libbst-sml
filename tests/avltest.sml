use "../bst.sml";
use "../avl.sml";
use "../util/rand.sml";

structure Node : ORDERED = struct
	type element = int;
	fun lt (a,b) = if a < b then true else false;
end;

structure IntBST = AVLcreate(Node);

val max =   1000000;
val nodes = 1000000;

fun rand m = let
	val r = Rand.srand (Time.toSeconds (Time.now()));
in
	fn () => r() mod m
end;

val nrand = rand max;

fun inserts t = let
	fun theloop (t,i) = if i < nodes
		then let val t = IntBST.insert (t,nrand())
		in theloop (t,i+1)
		end else t;
	val timer = Timer.startCPUTimer();
	val t = theloop (t,0);
	val {nongc={usr=usertime, ...}, ...} = Timer.checkCPUTimes timer;
in
	(t,Time.toMilliseconds usertime)
end;

fun lookups t = let
	fun theloop (t,i,l) = if i < nodes
		then case IntBST.lookup (t,nrand()) of
			SOME _ => theloop (t,i+1,l+1)
		|	NONE => theloop (t,i+1,l)
		else l;
	val timer = Timer.startCPUTimer();
	val l = theloop (t,0,0);
	val {nongc={usr=usertime, ...}, ...} = Timer.checkCPUTimes timer
in
	(l,Time.toMilliseconds usertime)
end;

fun deletes t = let
	fun theloop (t,i,l) = if i < nodes
		then case IntBST.delete (t,nrand()) of
			(true,t) => theloop (t,i+1,l+1)
		|	(false,t) => theloop (t,i+1,l)
		else (t,l);
	val timer = Timer.startCPUTimer();
	val (t,l) = theloop (t,0,0);
	val {nongc={usr=usertime, ...}, ...} = Timer.checkCPUTimes timer
in
	(t,l,Time.toMilliseconds usertime)
end;

(*
fun main () = let
	val (t,inserttime) = inserts IntBST.create;
	val (l,lookuptime) = lookups t;
	val (t1,ld,deletetime) = deletes t;
	val (l1,lookuptime1) = lookups t1
in
	print ("Inserts took " ^ (LargeInt.toString inserttime) ^ "ms.\n");

	IntBST.test t;
	print "Tree is balanced\n";

	print ("Lookups took " ^ (LargeInt.toString lookuptime) ^ "ms.\n");
	print ("There were " ^ (Int.toString l) ^ " successful lookups.\n");

	print ("Deletions took " ^ (LargeInt.toString deletetime) ^ "ms.\n");
	print ("There were " ^ (Int.toString ld) ^ " successful deletions.\n");

	IntBST.test t1;
	print "Tree after deletions is balanced\n";

	print ("Lookups took " ^ (LargeInt.toString lookuptime1) ^ "ms.\n");
	print ("There were " ^ (Int.toString l1) ^ " successful lookups.\n")
end;
*)

fun main () = let
	val (t,time) = inserts IntBST.create;
	val _ = print ("Inserts took " ^ (LargeInt.toString time) ^ "ms.\n")

	val _ = IntBST.test t;
	val _ = print("Tree is balanced\n");

	val (n,time) = lookups t;
	val _ = print ("Lookups took " ^ (LargeInt.toString time) ^ "ms.\n");
	val _ = print ("There were " ^ (Int.toString n) ^ " successful lookups.\n");

	val (t,n,time) = deletes t;
	val _ = print ("Deletions took " ^ (LargeInt.toString time) ^ "ms.\n");
	val _ = print ("There were " ^ (Int.toString n) ^ " successful deletions.\n");

	val _ = IntBST.test t;
	val _ = print "Tree after deletions is balanced\n";

	val (n,time) = lookups t
	val _ = print ("Lookups took " ^ (LargeInt.toString time) ^ "ms.\n");
	val _ = print ("There were " ^ (Int.toString n) ^ " successful lookups.\n")
in
	()
end;
