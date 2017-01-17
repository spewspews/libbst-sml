use "../bst.sml";
use "../avl.sml";
use "../util/rand.sml";

structure Node : ORDERED = struct
	type element = int;
	fun lt (a,b) = if a < b then true else false;
end;

structure IntBST = AVLcreate(Node);

val max =    1000000;
val nodes =  1000000;

fun rand m = let
	val r = Rand.srand (Time.toSeconds (Time.now()));
in
	fn () => r() mod m
end;

val maxrand = rand max;

fun inserts t = let
	fun theloop (t,i) = if i < nodes
		then let val t = IntBST.insert (t,maxrand())
		in theloop (t,i+1)
		end else t;
	val timer = Timer.startCPUTimer();
	val t = theloop (t,0);
	val {nongc={usr=usertime, ...}, ...} = Timer.checkCPUTimes timer;
in
	(t,Time.toMilliseconds usertime)
end;

fun lookups t = let
	fun theloop (t,l,i) = if i < nodes
		then case IntBST.lookup (t,maxrand()) of
			SOME _ => theloop (t,l+1,i+1)
		|	NONE => theloop (t,l,i+1)
		else l;
	val timer = Timer.startCPUTimer();
	val l = theloop (t,0,0);
	val {nongc={usr=usertime, ...}, ...} = Timer.checkCPUTimes timer
in
	(l,Time.toMilliseconds usertime)
end;

fun deletes t = let
	fun theloop (t,l,i) =  let
			val r = maxrand()
		in
			if i < nodes
			then case IntBST.delete (t,maxrand()) of
				(true,t) => theloop (t,r::l,i+1)
			|	(false,t) => theloop (t,l,i+1)
			else (t,l)
		end
	val timer = Timer.startCPUTimer()
	val (t,l) = theloop (t,[],0)
	val {nongc={usr=usertime, ...}, ...} = Timer.checkCPUTimes timer
in
	(t,l,Time.toMilliseconds usertime)
end;

fun main () = let
	val (t,time) = inserts IntBST.create
	val _ = (
		print ("Inserts took " ^ (LargeInt.toString time) ^ "ms.\n");
		IntBST.test t;
		print("Tree is balanced\n")
	)

(*
 *	val inorder = IntBST.map (fn i => i) (NONE,NONE) t;
 *	val _ = (
 *		List.app (fn i => print (Int.toString i ^ " ")) inorder;
 *		print "\n"
 *	)
 *)

	val (n,time) = lookups t
	val _ = (
		print ("Lookups took " ^ (LargeInt.toString time) ^ "ms.\n");
		print ("There were " ^ (Int.toString n) ^ " successful lookups.\n")
	)

	val (t,d,time) = deletes t

	val _ = (
		print ("Deletions took " ^ (LargeInt.toString time) ^ "ms.\n");
		print ("There were " ^ (Int.toString (List.length d)) ^ " successful deletions.\n");
		IntBST.test t;
(*
 *		List.app (fn i => print (Int.toString i ^ " ")) d;
 *		print "\n";
 *)
		print "Tree after deletions is balanced\n"
	)

(*
 *	val inorder = IntBST.map (fn i => i) (NONE,NONE) t;
 *	val _ = (
 *		List.app (fn i => print (Int.toString i ^ " ")) inorder;
 *		print "\n"
 *	)
 *)
	val (n,time) = lookups t

	val _ = (
		print ("Lookups took " ^ (LargeInt.toString time) ^ "ms.\n");
		print ("There were " ^ (Int.toString n) ^ " successful lookups.\n")
	)
in
	()
end;
