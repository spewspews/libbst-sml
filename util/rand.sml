(* srand returns a function that returns pseudo-random numbers 0 <= x < 2^31 *)

signature RAND = sig
	val srand: int -> unit -> int;
end

structure Rand: RAND = struct
	val len = 607;
	val tap = 273;
	val mask = 0wx7fffffff;
	val a = 48271;
	val m = 2147483647;
	val q = 44488;
	val r = 3399;

	fun srand seed =
	let
		val rng_vec = Array.array (len,Word32.fromInt 0);
		val rng_tap = ref 0;
		val rng_feed = ref 0;
		fun loop (i,x) =
		let
			val hi = x div q;
			val lo = x mod q;
			val x = a*lo - r*hi;
			val x = if x >= 0 then x else x+m
		in
			if i < len then (
				if i < 0 then () else
					Array.update (rng_vec,i,Word32.fromInt x);
				loop (i+1,x)
			) else ()
		end;
	in
		rng_tap := 0;
		rng_feed := len - tap;
		let
			val seed = seed mod m;
			val seed = if seed > 0 then seed else 89482311;
		in
			loop (~20,seed)
		end;
		fn () => (
			rng_tap := (
				let val new = !rng_tap - 1
				in
					if new >= 0 then new else new + len
				end
			);
			rng_feed := (
				let val new = !rng_feed - 1
				in
					if new >= 0 then new else new + len
				end
			);
			let
				val x = Array.sub (rng_vec,!rng_feed) + Array.sub (rng_vec,!rng_tap);
				val x = Word32.andb (x,mask)
			in (
				Array.update (rng_vec,!rng_feed,x);
				Word32.toInt x
			) end
		)
	end;

	fun rand () = 0;
end
