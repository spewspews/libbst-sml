functor AVLcreate(O: ORDERED) = struct
	structure Ordered = O;

	type elt = Ordered.element;

	datatype 'k btree = 
		Empty
	|	Node of {
			balance : int,
			left : 'k btree,
			right : 'k btree,
			value : 'k
		};

	datatype compare = LESS|GREATER|EQUAL;

	fun assert (b,s) = if b then () else raise Fail ("Assertion failed: " ^ s);

	fun	cmp (x,y) =
		if Ordered.lt(x,y) then LESS
		else if Ordered.lt(y,x) then GREATER
		else EQUAL;

	val create = Empty;

	fun child (~1,{left=l, ...}) = l
	|	child (1,{right=r, ...}) = r
	|	child (_,_) = raise Fail "fun child: Invalid child";

	fun setchild (~1, {right=r, balance=b, value=v, ...}, n) =
			{left=n, right=r, balance=b, value=v}
	|	setchild (1, {left=l, balance=b, value=v, ...}, n) =
			{right=n, left=l, balance=b, value=v}
	|	setchild (_,_,_) = raise Fail "fun setchild: Invalid child";

	fun rotate (a,s) = 
		let
			val c = case child(a,s) of
				Node h => h
			|	_ => raise Fail "Tried to rotate on a bad node";
			val s = setchild (a,s,child (~a,c))
		in
			setchild(~a,c,Node s)
		end;

	fun singlerot (a,{left=l, right=r, balance=b, value=v}) =
		let
			val s = {balance=0, left=l, right=r, value=v};
			val {left=l, right=r, balance=b, value=v} = rotate (a,s);
		in
			{balance=0, left=l, right=r, value=v}
		end;

	fun rebalance (a,p as {balance=b, ...}) =
		let
			val {left=sl, right=sr, value=sv, ...} = case child(~a,p) of
				Node h => h
			|	_ => raise Fail "fun rebalance: bad node";
			val {left=rl, right=rr, value=rv, ...} = case child(a,p) of
				Node h => h
			|	_ => raise Fail "fun rebalance: bad node";
			val (sb,rb) = if b = a then
				(~a,0)
			else if b = ~a then
				(0,a)
			else
				(0,0);
			val s = {balance=sb, left=sl, right=sr, value=sv};
			val r = {balance=rb, left=rl, right=rr, value=rv};
			val p = setchild (~a,p,Node s);
			val p as {left=l, right=r, value=v, ...} = setchild (a,p,Node r);
		in
			{balance=0, left=l, right=r, value=v}
		end;

	fun doublerot (a,s) =
		let
			val c = case child(a,s) of
				Node h => h
			|	_ => raise Fail "fun doublerot: bad node";
			val c = rotate (~a,c);
			val s = setchild(a,s,Node c);
			val s = rotate(a,s);
		in
			rebalance (a,s)
		end;

	fun insertfix (a,{balance=0, left=l, right=r, value=v}) =
			(true,{balance=a, left=l, right=r, value=v})
	|	insertfix (a,s as {balance=b, left=l, right=r, value=v}) =
			if b = ~a then
				(false,{balance=0, left=l, right=r, value=v})
			else let
				val {balance=b, ...} = case child(a,s) of
					Node h => h
				|	_ => raise Fail "fun insertfix: bad node"
			in
				if b = a then
					(false,singlerot(a,s))
				else
					(false,doublerot(a,s))
			end;

	fun insert1 (Empty,k) = (false,{value=k, left=Empty, right=Empty, balance=0})
	|	insert1 (Node{left=l, right=r, balance=b, value=v},k) =
		let
			val (a,fix,s) = case cmp(k,v) of
				LESS => let val (fix,l) = insert1(l,k)
				in
					(~1,fix,{left=Node l, right=r, balance=b, value=v})
				end
			|	GREATER => let val (fix,r) = insert1(r,k) in
					(1,fix,{right=Node r, left=l, balance=b, value=v})
				end
			|	EQUAL => (0,false,{value=k, left=l, right=r, balance=b})
		in
			if fix then
				insertfix(a,s)
			else
				(false,s)
		end;

	fun insert (t,k) = let val (fix,t) = insert1(t,k) in Node t end;
end
