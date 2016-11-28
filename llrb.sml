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
	val delete : elt * elt btree -> bool * elt btree;
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

	fun	rotateleft {
		right = x as Node{left=xl, right=xr, value=xv, color=RED},
		left = l,
		value = v,
		color = c
	} =
		let
			val h = Node{right=xl, left=l, value=v, color=RED}
		in
			{left=h, right=xr, color=c, value=xv}
		end
	|	rotateleft(_) = raise Fail("Tried to rotateleft on a bad node.");

	fun	rotateright {
		left = x as Node{left=xl, right=xr, value=xv, color=RED},
		right = r,
		value = v,
		color = c
	} =
		let
			val h = Node{left=xr, right=r, value=v, color=RED}
		in
			{right=h, left=xl, color=c, value=xv}
		end
	|	rotateright(_) = raise Fail("Tried to rotateright on a bad node.");

	fun	flip {
		color = c,
		left = Node{color=lc, value=lv, left=ll, right=lr},
		right = Node{color=rc, value=rv, left=rl, right=rr},
		value = v
	} =
	let
		fun	flipcolor RED = BLACK
		|	flipcolor BLACK = RED
	in
		{
			color = flipcolor(c),
			left = Node{color=flipcolor(lc), value=lv, left=ll, right=lr},
			right = Node{color=flipcolor(rc), value=rv, left=rl, right=rr},
			value = v
		}
	end
	|	flip(_) = raise Fail("Tried to flip on a bad node.")

	fun	isred Empty = false
	|	isred(Node{color = BLACK, ...}) = false
	|	isred(Node{color = RED, ...}) = true;

	fun	fixup(h as {left=l, right=r, ...}) =
	if isred(r) andalso not(isred(l)) then
		rotateleft(h)
	else if isred(l) andalso (
		case l of
			Node l => isred(#left(l))
		|	Empty => raise Fail("Impossible.")
	) then
		flip(rotateright(h))
	else if isred(l) andalso isred(r) then
		flip(h)
	else
		h;

	fun	lookup(x,Empty) = NONE
	|	lookup(x,Node{value = y, left, right, ...}) = case cmp(x,y) of
			LESS => lookup(x,left)
		|	GREATER => lookup(x,right)
		|	EQUAL => SOME y;

	fun	insert1(x,Empty) = Node{value=x, left=Empty, right=Empty, color=RED}
	|	insert1(x, y as Node{value=v, left=l, right=r, color=c}) =
		let
			val h = case cmp(x,v) of
				LESS => {value=v, left=insert1(x, l), right=r, color=c}
			|	GREATER => {value=v,left=l,right=insert1(x, r),color=c}
			|	EQUAL => {value=x, left=l, right=r, color=c};
			val h = fixup(h)
		in
			Node(h)
		end;

	fun	insert(x, y) =
	let
		val t = insert1(x, y)
	in
		case t of
			Node{color=BLACK, ...} => t
		|	Node{color=RED, left=l, right=r, value=v} =>
				Node{color=BLACK, left=l, right=r, value=v}
		|	_ => raise Fail("Result of insertion was Empty.")
	end;

	fun	moveredleft(h) =
	let
		val h = flip(h)
	in
		case h of
			{right=Node(r), left=l, value=v, color=c} =>
				if isred(#left(r)) then
					let
						val r = rotateright(r)
						val h = {left=l, right=Node(r), color=c, value=v};
					in
						flip(rotateleft(h))
					end
				else
					h
		|	_ => raise Fail("Tried to moveredleft on a bad node.")
	end;

	fun	moveredright(h) =
	let
		val h = flip(h)
	in
		case h of
			{left=Node{left=ll, ...}, ...} =>
				if isred(ll) then
					flip(rotateright(h))
				else
					h
		|	_ => raise Fail("Tried to moveredright on a bad node.")
	end;

	fun	deletemin(Empty) = (false, Empty)
	|	deletemin(Node(h as {left=l, ...})) =
		case l of
			Empty => (true, Empty)
		|	Node{left=ll, ...} =>
			let
				val {left=l, right=r, color=c, value=v} = if not(isred(l)) andalso not(isred(ll))
				then
					moveredleft(h)
				else
					h
				val (suc, dl) = deletemin(l)
				val h = {left=dl, right=r, color=c, value=v}
			in
				(suc, Node(fixup(h)))
			end;


	fun	delete1(x, Empty) = (false,Empty)
	|	delete1(x, Node(h as {value=v, left=l, ...})) =
		let
			val (suc, h) = case cmp(x,v) of
				LESS => dless(x, h)
			|	_ => dgeq(x, h)
		in
			case h of
				Empty => (suc, h)
			|	Node h => (suc, Node(fixup(h)))
		end
	and dless(x, h as {left=l, ...}) =
	        case l of
	            Empty => (false, Node h)
	        |	Node{left=ll, ...} =>
	            let
	                val {left=l, right=r, color=c, value=v} =
	                if not(isred(l)) andalso not(isred(ll)) then
	                    moveredleft(h)
	                else
	                    h;
	                val (suc, dl) = delete1(x, l)
	            in
	                (suc, Node{left=dl, right=r, value=v, color=c})
	            end
	and dgeq(x, h as {left=l, ...}) = 
	let
		val {left=l, right=r, value=v, color=c} =
			if isred(l) then
				rotateright(h)
			else
				h
	in
		case r of
			Empty =>
				if cmp(x, v) = EQUAL then
					(true, Empty)
				else
					let
						val (suc, dr) = delete1(x, r)
					in
						(suc, Node{right=dr, left=l, value=v, color=c})
					end
		|	Node {left=rl, ...} =>
			let
				val {left=l, right=r, value=v, color=c} =
					if not(isred(r)) andalso not(isred(rl)) then
						moveredright(h)
					else
						h
				val (suc, dr) = case cmp(x, v) of
					EQUAL => deletemin(r)
				|	_ => delete1(x, r)
			in
				(suc, Node{right=dr, left=l, value=v, color=c})
			end
	end

	fun	delete(x, t) =
	let
		val (suc,t) = delete1(x,t)
	in
		case t of
			Node{color=BLACK, ...} => (suc, t)
		|	Node{color=RED, left=l, right=r, value=v} =>
				(suc, Node{color=BLACK, left=l, right=r, value=v})
		|	Empty => (false, Empty)
	end;
end;
