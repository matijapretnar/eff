include Stdlib.Option

let default_map default f = function None -> default | Some x -> f x
