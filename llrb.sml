signature ORDERED = sig
	type element;
	val lt: element * element -> bool
end;

signature BST = sig
	type 'k btree;
	type elt;
	structure Ordered : ORDERED;
	sharing type elt = Ordered.element;
	val create : 'k btree;
	val lookup : elt * elt btree -> elt option;
	val insert : elt * elt btree -> elt btree;
end;

functor LLRBcreate(O: ORDERED) : BST = struct
	structure Ordered = O;

	type elt = Ordered.element;

	datatype color = RED|BLACK;

	datatype 'k btree = 
		Empty
	|	Node of {value : 'k, left : 'k btree, right : 'k btree, color : color};

	datatype compare = LESS|GREATER|EQUAL;

	fun	cmp(x,y) =
		if Ordered.lt(x,y) then
			LESS
		else if Ordered.lt(y,x) then
			GREATER
		else
			EQUAL;

	val create = Empty;

	fun	rotateleft(Node{
		right = x as Node{left=xl, right=xr, value=xv, color=RED},
		left = l,
		value = v,
		color = c
	}) =
		let
			val h = Node{right=xl, left=l, value=v, color=RED}
		in
			Node{left=h, right=xr, color=c, value=xv}
		end
	|	rotateleft(_) = raise Match;

	fun	rotateright(Node{
		left = x as Node{left=xl, right=xr, value=xv, color=RED},
		right = r,
		value = v,
		color = c
	}) =
		let
			val h = Node{left=xr, right=r, value=v, color=RED}
		in
			Node{right=h, left=xl, color=c, value=xv}
		end
	|	rotateright(_) = raise Match;

	fun flip(Node {
		color = c,
		left = Node{color=lc, value=lv, left=ll, right=lr},
		right = Node{color=rc, value=rv, left=rl, right=rr},
		value = v
	}) =
	let
		fun flipcolor(RED) = BLACK
		|	flipcolor(BLACK) = RED
	in
		Node {
			color = flipcolor(c),
			left = Node{color=flipcolor(lc), value=lv, left=ll, right=lr},
			right = Node{color=flipcolor(rc), value=rv, left=rl, right=rr},
			value = v
		}
	end
	|	flip(_) = raise Match

	fun	isred(Empty) = false
	|	isred(Node{color = RED, ...}) = true
	|	isred(Node{color = BLACK, ...}) = false;

	fun	left(Node{left, ...}) = left
	|	left(Empty) = raise Match

	fun	right(Node{right, ...}) = right
	|	right(Empty) = raise Match

	fun	fixup(x) =
		if isred(right(x)) andalso not(isred(left(x))) then
			rotateleft(x)
		else if isred(left(x)) andalso isred(left(left(x))) then
			flip(rotateright(x))
		else if isred(left(x)) andalso isred(right(x)) then
			flip(x)
		else x;

	fun	lookup(x,Empty) = NONE
	|	lookup(x,Node{value = y, left, right, ...}) = case cmp(x,y) of
			LESS => lookup(x,left)
		|	GREATER => lookup(x,right)
		|	EQUAL => SOME y;

	fun	insert(x, y) =
	let
		fun	insert1(x,Empty) = Node{value=x, left=Empty, right=Empty, color=RED}
		|	insert1(x, y as Node{value=v, left=l, right=r, color=c}) =
			let
				val h = case cmp(x,v) of
					LESS => Node{value=v, left=insert1(x, l), right=r, color=c}
				|	GREATER => Node{value=v,left=l,right=insert1(x, r),color=c}
				|	EQUAL => Node{value=x, left=l, right=r, color=c};
				val h = fixup(h)
			in
				h
			end;
		val t = insert1(x, y)
	in
		case t of
			Node{color=BLACK, ...} => t
		|	Node{color=RED, left=l, right=r, value=v} =>
				Node{color=BLACK, left=l, right=r, value=v}
		|	Empty => raise Match
	end;

	fun moveredleft(h) =
	let
		val h = flip(h)
	in
		case h of
			Node{left=l, right=r, value=v, color=c} =>
				if isred(left(r)) then
					let
						val h = Node{left=l, right=rotateright(r), color=c, value=v};
						val h = rotateleft(h)
						val h = flip(h)
					in
						h
					end
				else
					h
		|	Empty => raise Match
	end;

	fun deletemin(Empty) = Empty
	|	deletemin(h as Node{left=l, ...}) =
		case l of
			Empty => Empty
		|	Node{left=ll, ...} =>
				let
					val h = if not(isred(l)) andalso not(isred(ll))
					then
						moveredleft(h)
					else
						h
				in
					case h of
						Node{left=l, right=r, color=c, value=v} => 
							let
								val h = Node{left=deletemin(l), right=r, color=c, value=v};
								val h = fixup(h)
							in
								h
							end
					|	Empty => raise Match
				end;
end;
