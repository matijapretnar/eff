module Ty = struct
  include Symbol.Make (Symbol.Parameter (struct
    let ascii_symbol = "ty"

    let utf8_symbol = "\207\132"
  end))

  let print_type_param t ppf = fold (fun _ n -> Format.fprintf ppf "'t%d" n) t

  let print_old ?(poly= []) k ppf =
    let c = if List.mem k poly then "'" else "'_" in
    fold
      (fun _ k ->
        if 0 <= k && k <= 25 then
          Format.fprintf ppf "%s%c" c (char_of_int (k + int_of_char 'a'))
        else Format.fprintf ppf "%sty%i" c (k - 25) )
      k
end

