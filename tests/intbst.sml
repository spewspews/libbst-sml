use "../bst.sml";
use "../avl.sml";

structure Node : ORDERED = struct
	type element = int;
	fun lt (a,b) = if a < b then true else false;
end;

structure IntBST = AVLcreate(Node);

open IntBST;

val bstToString = toString Int.toString;
val t = create;
