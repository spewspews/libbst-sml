functor AVLcreate(O : ORDERED) : BST = struct
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

	fun lookup (Empty,k) = NONE
	|	lookup (Node{left=l,right=r,value=v,...},k) = case cmp(k,v) of
			LESS => lookup(l,k)
		|	GREATER => lookup(r,k)
		|	EQUAL => SOME v;

	fun child ({left=l, ...},~1) = l
	|	child ({right=r, ...},1) = r
	|	child (_,_) = raise Fail "fun child: Invalid child";

	fun setone ({right=r, balance=b, value=v, ...},~1,c) =
			{left=c, right=r, balance=b, value=v}
	|	setone ({left=l, balance=b, value=v, ...},1,c) =
			{right=c, left=l, balance=b, value=v}
	|	setone (_,_,_) = raise Fail "fun setone: Invalid child";

	fun setboth ({value=v, balance=b,...},~1,r,l) = {left=l, right=r, value=v, balance=b}
	|	setboth ({value=v, balance=b,...},1,l,r) = {left=l, right=r, value=v, balance=b}
	|	setboth (_,_,_,_) = raise Fail "fun setboth: Invalid direction";

	fun rotate (s,a) =
		let
			val c = case child (s,a) of
				Node n => n
			|	_ => raise Fail "Tried to rotate on a bad node";
			val s = setone (s,a,child (c,~a))
		in
			setone(c,~a,Node s)
		end;

	fun singlerot ({left=l, right=r, balance=b, value=v},a) = 
		let
			val s = {balance=0, left=l, right=r, value=v};
			val {left=l, right=r, balance=b, value=v} = rotate (s,a);
		in
			{balance=0, left=l, right=r, value=v}
		end;

	fun doublebal (t as {balance=b, ...},a) =
		let
			val {left=sl, right=sr, value=sv, ...} = case child(t,~a) of
				Node n => n
			|	_ => raise Fail "fun rebalance: bad node";
			val {left=rl, right=rr, value=rv, ...} = case child(t,a) of
				Node n => n
			|	_ => raise Fail "fun rebalance: bad node";
			val (sb,rb) = if b = a then
				(~a,0)
			else if b = ~a then
				(0,a)
			else
				(0,0);
			val s = {balance=sb, left=sl, right=sr, value=sv};
			val r = {balance=rb, left=rl, right=rr, value=rv};
			val {left=l, right=r, value=v, ...} = setboth(t,a,Node s,Node r)
		in
			{balance=0, left=l, right=r, value=v}
		end;

	fun doublerot (s,a) =
		let
			val r = case child(s,a) of
				Node n => n
			|	_ => raise Fail "fun doublerot: bad node";
			val p = rotate (r,~a);
			val s = setone(s,a,Node p);
			val t = rotate(s,a);
		in
			doublebal (t,a)
		end;

	fun insertfix ({balance=0, left=l, right=r, value=v},a) =
			(true,{balance=a, left=l, right=r, value=v})
	|	insertfix (s as {balance=b, left=l, right=r, value=v},a) =
			if b = ~a then
				(false,{balance=0, left=l, right=r, value=v})
			else let
				val {balance=b, ...} = case child(s,a) of
					Node n => n
				|	_ => raise Fail "fun insertfix: Impossible"
			in
				if b = a then (false,singlerot(s,a))
				else (false,doublerot(s,a))
			end;

	fun insert1 (Empty,k) = (true,{value=k, left=Empty, right=Empty, balance=0})
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
				insertfix(s,a)
			else
				(false,s)
		end;

	fun insert (t,k) = let val (fix,t) = insert1(t,k) in Node t end;

	fun deletefix ({balance=0,left=l,right=r,value=v},a) =
			(false,Node {balance=a,left=l,right=r,value=v})
	|	deletefix (s as {balance=b,left=l,right=r,value=v},a) =
			if(b = ~a) then
				(true,Node {balance=0,left=l,right=r,value=v})
			else let
				val {balance=cb,...} = case child(s,a) of
					Node n => n
				|	_ => raise Fail "fun deletefix: Impossible"
			in
				if cb = 0 then let
					val {value=v,left=l,right=r,...} = rotate (s,a);
					val s = {balance= ~a,left=l,right=r,value=v}
				in
					(false,Node s)
				end else if cb = a then (true,Node (singlerot (s,a)))
				else (true,Node (doublerot (s,a)))
			end;

	fun deletemin Empty = raise Fail "fun deletemin: Called on empty node"
	|	deletemin (Node {left=Empty,right=r,value=v,...}) =	(true,r,v)
	|	deletemin (Node {left=l,right=r,value=v,balance=b}) =
		let
			val (fix,newl,minv) = deletemin(l);
			val q = {left=newl,right=r,value=v,balance=b};
			val (fix,q) = if not fix then (false,Node q) else deletefix(q,1);
		in
			(fix,q,minv)
		end;

	fun delete1 (Empty,_) = (false,false,Empty)
	|	delete1 (Node {left=l,right=r,balance=b,value=v},k) =
		let
			val c = cmp(k,v)
		in case (c,r) of
			(EQUAL,Empty) => (true,true,l)
		|	_ => let
				val (found,a,fix,q) = case c of
					EQUAL => let
						val (fix,newr,newv) = deletemin(r);
						val q = {right=newr,value=newv,left=l,balance=b}
					in
						(true,~1,fix,q)
					end
				|	GREATER => let
						val (found,fix,newr) = delete1(r,k);
						val q = {right=newr,left=l,balance=b,value=v}
					in
						(found,~1,fix,q)
					end
				|	LESS => let
						val (found,fix,newl) = delete1(l,k);
						val q = {left=newl,right=r,balance=b,value=v}
					in
						(found,1,fix,q)
					end
			in if fix then
				let
					val (fix,q) = deletefix(q,a)
				in
					(found,fix,q)
				end
			else
				(found,false,Node q)
			end
		end;

	fun delete (Empty,k) = (false,Empty)
	|	delete (t,k) = let val (found,fix,t) = delete1(t,k) in (found,t) end;

	fun map _ (_,_) _ = [];

	fun app _ (_,_) _ = ();

	fun longest Empty = 0
	|	longest (Node{left=l, right=r,...}) =
		let
			val ln = longest(l);
			val rn = longest(r);
			val m = if ln > rn then ln else rn
		in
			m+1
		end;

	fun checkbalance Empty = ()
	|	checkbalance (Node{left=l, right=r, balance=b,...}) =
		let
			val ln = longest(l);
			val rn = longest(r);
		in
			assert(rn-ln = b,(
				"AVL tree is not balanced b left right " ^
				(Int.toString b) ^ " " ^
				(Int.toString ln) ^ " " ^
				(Int.toString rn)
			));
			checkbalance(l);
			checkbalance(r)
		end;

	val test = checkbalance;

	fun toString sfn Empty = ""
	|	toString sfn (Node {left=l, right=r, value=v, balance=b}) = (
			(sfn v) ^ " " ^
			(case l of
				Empty => "-"
			|	Node {value=v, ...} => (sfn v)) ^
			" " ^
			(case r of
				Empty => "-"
			|	Node{value=v, ...} => (sfn v)) ^
			" " ^ (Int.toString b) ^ "\n" ^
			(toString sfn l) ^
			(toString sfn r)
		);
end
