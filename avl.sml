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

	fun cmp (x,y) =
		if Ordered.lt(x,y) then LESS
		else if Ordered.lt(y,x) then GREATER
		else EQUAL;

	val create = Empty;

	fun lookup (Empty,k) = NONE
	|	lookup (Node {left=l,right=r,value=v,...},k) = case cmp(k,v) of
			LESS => lookup(l,k)
		|	GREATER => lookup(r,k)
		|	EQUAL => SOME v;

	fun child ({left=l, ...},~1) = l
	|	child ({right=r, ...},1) = r

	fun setone ({right=r, balance=b, value=v, ...},~1,c) =
			{left=c, right=r, balance=b, value=v}
	|	setone ({left=l, balance=b, value=v, ...},1,c) =
			{right=c, left=l, balance=b, value=v}

	fun setboth ({value=v, balance=b,...},~1,r,l) = {left=l, right=r, value=v, balance=b}
	|	setboth ({value=v, balance=b,...},1,l,r) = {left=l, right=r, value=v, balance=b}

	fun rotate (s,a) =
		let
			val Node c = child (s,a);
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
			val Node {left=sl, right=sr, value=sv, ...} = child(t,~a);
			val Node {left=rl, right=rr, value=rv, ...} = child(t,a);
			val (sb,rb) = if b = a then (~a,0)
				else if b = ~a then (0,a)
				else (0,0);
			val s = {balance=sb, left=sl, right=sr, value=sv};
			val r = {balance=rb, left=rl, right=rr, value=rv};
			val {left=l, right=r, value=v, ...} = setboth(t,a,Node s,Node r)
		in
			{balance=0, left=l, right=r, value=v}
		end;

	fun doublerot (s,a) =
		let
			val Node r = child(s,a);
			val p = rotate (r,~a);
			val s = setone(s,a,Node p);
			val t = rotate(s,a);
		in
			doublebal (t,a)
		end;

	fun insertfix ({balance=0, left=l, right=r, value=v},a) =
			(true,Node {balance=a, left=l, right=r, value=v})
	|	insertfix (s as {balance=b, left=l, right=r, value=v},a) =
			if b = ~a
			then (false,Node {balance=0, left=l, right=r, value=v})
			else let
				val Node {balance=b, ...} = child(s,a);
			in
				if b = a then (false,Node (singlerot (s,a)))
				else (false,Node (doublerot (s,a)))
			end;

	fun insert1 (Empty,k) = (true,Node {value=k, left=Empty, right=Empty, balance=0})
	|	insert1 (Node {left=l, right=r, balance=b, value=v},k) =
		let
			val (a,fix,s) = case cmp(k,v) of
				LESS => let val (fix,newl) = insert1(l,k)
				in
					(~1,fix,{left=newl, right=r, balance=b, value=v})
				end
			|	GREATER => let val (fix,newr) = insert1(r,k) in
					(1,fix,{right=newr, left=l, balance=b, value=v})
				end
			|	EQUAL => (0,false,{value=k, left=l, right=r, balance=b})
		in
			if fix then insertfix (s,a)
			else (false,Node s)
		end;

	fun insert (t,k) = let val (fix,t) = insert1(t,k) in t end;

	fun deletefix ({balance=0,left=l,right=r,value=v},a) =
			(false,Node {balance=a,left=l,right=r,value=v})
	|	deletefix (s as {balance=b,left=l,right=r,value=v},a) =
			if b = ~a
			then (true,Node {balance=0,left=l,right=r,value=v})
			else let
				val Node {balance=cb,...} = child(s,a);
			in
				if cb = 0 then let
					val {value=v,left=l,right=r,...} = rotate (s,a);
					val s = {balance= ~a,left=l,right=r,value=v}
				in
					(false,Node s)
				end else if cb = a then (true,Node (singlerot (s,a)))
				else (true,Node (doublerot (s,a)))
			end;

	fun deletemin (Node {left=Empty,right=r,value=v,...}) =	(true,r,v)
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
				val (found,fix,a,q) = case c of
					EQUAL => let
						val (fix,newr,newv) = deletemin(r);
						val q = {right=newr,value=newv,left=l,balance=b}
					in
						(true,fix,~1,q)
					end
				|	GREATER => let
						val (found,fix,newr) = delete1(r,k);
						val q = {right=newr,left=l,balance=b,value=v}
					in
						(found,fix,~1,q)
					end
				|	LESS => let
						val (found,fix,newl) = delete1(l,k);
						val q = {left=newl,right=r,balance=b,value=v}
					in
						(found,fix,1,q)
					end
			in
				if fix then let
					val (fix,q) = deletefix(q,a)
				in
					(found,fix,q)
				end
				else (found,false,Node q)
			end
		end;

	fun delete (Empty,k) = (false,Empty)
	|	delete (t,k) = let val (found,fix,t) = delete1(t,k) in (found,t) end;

	fun	optcmp (x,NONE) = EQUAL
	|	optcmp (x,SOME y) = cmp(x,y);

	fun	map _ _ Empty = []
	|	map f (min,max) (Node {left=l, right=r, value=v, ...}) =
		let
			val llist = map f (min,max) l;
			val rlist = map f (min,max) r
		in
			if optcmp (v,min) = LESS orelse optcmp (v,max) = GREATER
			then llist @ rlist
			else llist @ (f v)::rlist
		end;

	fun	app _ _ Empty = ()
	|	app f (min,max) (Node{left=l, right=r, value=v, ...}) = (
			app f (min,max) l;
			if optcmp(v,min) = LESS orelse optcmp(v,max) = GREATER
			then ()
			else f v;
			app f (min,max) r
		);

	fun longest Empty = 0
	|	longest (Node {left=l, right=r,...}) =
		let
			val ln = longest(l);
			val rn = longest(r);
			val m = if ln > rn then ln else rn
		in
			m+1
		end;

	fun checkbalance Empty = ()
	|	checkbalance (Node {left=l, right=r, balance=b,...}) =
		let
			val ln = longest(l);
			val rn = longest(r)
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
			|	Node {value=v, ...} => (sfn v)) ^
			" " ^ (Int.toString b) ^ "\n" ^
			(toString sfn l) ^
			(toString sfn r)
		);
end
