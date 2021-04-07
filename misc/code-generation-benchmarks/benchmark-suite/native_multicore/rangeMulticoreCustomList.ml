effect Fetch : unit -> int

type int_list = Nil | Cons of int * int_list

let test n = 
	let rec range n =
		match n with
		| 0 -> Nil
		| _ ->
			 Cons((perform (Fetch ()), (range (n - 1))))
	in	
  match		
	  range n 
  with
	| effect (Fetch _) k -> (continue k 42)
  | x -> x
