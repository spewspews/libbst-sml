functor AVLcreate(O: ORDERED) = struct
	structure Ordered = O;

	type elt = Ordered.element;

	datatype 'k btree = 
		Empty
	|	Node of {value : 'k, child : 'k btree vector, balance : int};

	datatype compare = LESS|GREATER|EQUAL;

	fun assert (b,s) = if b then () else raise Fail ("Assertion failed: " ^ s);

	fun	cmp (x,y) =
		if Ordered.lt(x,y) then LESS
		else if Ordered.lt(y,x) then GREATER
		else EQUAL;

	val create = Empty;

	fun flip 0 = 1
	|	flip _ = 0;

	fun	rotate (a,{child=c, balance=b, value=v}) = 
	let
		open Vector;
		val a = (a+1) div 2;
		val a' = flip a;
		val {child=cc, balance=cb, value=cv} =
			case sub (c,a) of
				Node h => h
			|	_ => raise Fail "Tried to rotate a bad node";
		val s = {
			child = update (c,a,sub (cc,a')),
			value = v,
			balance = b
		}
	in
		{
			child = update (cc,a',Node s),
			value = cv,
			balance = cb
		}
	end;
end
