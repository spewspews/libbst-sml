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
    |   Node of {value : 'k, left : 'k btree, right : 'k btree, color : color};

    datatype compare = LESS|GREATER|EQUAL;

    fun cmp(x,y) =
        if Ordered.lt(x,y) then
            LESS
        else if Ordered.lt(y,x) then
            GREATER
        else
            EQUAL;

    val create = Empty;

    fun rotateleft(Node{
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
    |   rotateleft(_) = raise Fail("Tried to rotateleft on a bad node.");

    fun rotateright(Node{
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
    |   rotateright(_) = raise Fail("Tried to rotateright on a bad node.");

    fun flip(Node {
        color = c,
        left = Node{color=lc, value=lv, left=ll, right=lr},
        right = Node{color=rc, value=rv, left=rl, right=rr},
        value = v
    }) =
    let
        fun flipcolor(RED) = BLACK
        |   flipcolor(BLACK) = RED
    in
        Node {
            color = flipcolor(c),
            left = Node{color=flipcolor(lc), value=lv, left=ll, right=lr},
            right = Node{color=flipcolor(rc), value=rv, left=rl, right=rr},
            value = v
        }
    end
    |   flip(_) = raise Fail("Tried to flip a bad node.");

    fun isred(Empty) = false
    |   isred(Node{color = BLACK, ...}) = false
    |   isred(Node{color = RED, ...}) = true;

    fun fixup(h as Node{left=l, right=r, ...}) =
    let
        val h = if isred(r) andalso not(isred(l)) then
                rotateleft(h)
            else h;
        val h = case l of
                Node{left=ll, ...} => if isred(l) andalso isred(ll) then
                    rotateright(h)
                else h
            |   Empty => h;
        val h = if isred(l) andalso isred(r) then
                flip(h)
            else
                h;
    in
        h
    end
    |   fixup(_) = raise Fail("Tried to fixup a bad node.");

    fun lookup(x,Empty) = NONE
    |   lookup(x,Node{value = y, left, right, ...}) = case cmp(x,y) of
            LESS => lookup(x,left)
        |   GREATER => lookup(x,right)
        |   EQUAL => SOME y;

    fun insert(x, y) =
    let
        fun insert1(x,Empty) = Node{value=x, left=Empty, right=Empty, color=RED}
        |   insert1(x, y as Node{value=v, left=l, right=r, color=c}) =
            let
                val h = case cmp(x,v) of
                    LESS => Node{value=v, left=insert1(x, l), right=r, color=c}
                |   GREATER => Node{value=v,left=l,right=insert1(x, r),color=c}
                |   EQUAL => Node{value=x, left=l, right=r, color=c};
                val h = fixup(h)
            in
                h
            end;
        val t = insert1(x, y)
    in
        case t of
            Node{color=BLACK, ...} => t
        |   Node{color=RED, left=l, right=r, value=v} =>
                Node{color=BLACK, left=l, right=r, value=v}
        |   _ => raise Fail("Result of insertion was Empty.")
    end;

    fun moveredleft(h) =
    let
        val h = flip(h)
    in
        case h of
            Node{right=r as Node{left=rl, ...}, left=l, value=v, color=c} =>
                if isred(rl) then
                    let
                        val h = Node{left=l, right=rotateright(r), color=c, value=v};
                    in
                        flip(rotateleft(h))
                    end
                else
                    h
        |   _ => raise Fail("Tried to moveredleft on a bad node.")
    end;

    fun deletemin(Empty) = Empty
    |   deletemin(h as Node{left=l, ...}) =
        case l of
            Empty => Empty
        |   Node{left=ll, ...} =>
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
                        in
                            fixup(h)
                        end
                |   Empty => raise Fail("Cannot happen.")
            end;
end;
