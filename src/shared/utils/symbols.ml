let handler_arrow () = if !Config.ascii then "=>" else "\226\159\185 "

let short_arrow () = if !Config.ascii then "->" else "\226\134\146"

let times () = if !Config.ascii then " * " else " \195\151 "

let subscript sub =
  match sub with
  | None -> ""
  | Some i ->
      if !Config.ascii then string_of_int i
      else
        let rec sub i =
          let last =
            List.nth
              [
                "\226\130\128";
                "\226\130\129";
                "\226\130\130";
                "\226\130\131";
                "\226\130\132";
                "\226\130\133";
                "\226\130\134";
                "\226\130\135";
                "\226\130\136";
                "\226\130\137";
              ]
              (i mod 10)
          in
          if i < 10 then last else sub (i / 10) ^ last
        in
        sub i

let param ascii_symbol utf8_symbol index poly ppf =
  let prefix = if poly then "_" else ""
  and symbol = if !Config.ascii then ascii_symbol else utf8_symbol in
  Print.print ppf "%s%s%s" prefix symbol (subscript (Some (index + 1)))

let ty_param = param "ty" "\207\132"
