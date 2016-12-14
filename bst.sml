signature ORDERED = sig
	type element;
	val lt: element * element -> bool
end;

signature BST = sig
	structure Ordered : ORDERED;
	type 'k btree;
	type elt;
	sharing type elt = Ordered.element;
	val create : elt btree;
	val lookup : elt btree * elt -> elt option;
	val insert : elt btree * elt -> elt btree;
	val delete : elt btree * elt -> bool * elt btree;
	val map : (elt -> 'e) -> elt option * elt option -> elt btree -> 'e list;
	val app : (elt -> unit) -> elt option * elt option -> elt btree -> unit;
end;
