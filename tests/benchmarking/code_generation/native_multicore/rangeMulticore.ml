effect Fetch : unit -> int


let test n = 
	let rec range n =
		match n with
		| 0 -> []
		| _ ->
			 (perform (Fetch ()):: (range (n - 1)))
	in	
  try		
	  range n 
  with
	| effect (Fetch _) k -> (continue k 42)
