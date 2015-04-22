let fprintf = Format.fprintf

let print ?(max_level=9999) ?(at_level=0) ppf =
  if max_level < at_level then
    begin
      Format.fprintf ppf "(@[";
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@])") ppf
    end
  else
    begin
      Format.fprintf ppf "@[";
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]") ppf
    end

let rec sequence sep pp vs ppf =
  match vs with
  | [] -> ()
  | [v] -> pp v ppf
  | v :: vs -> Format.fprintf ppf "%t%s@,%t" (pp v) sep (sequence sep pp vs)


let variable (_, x) ppf = print ppf "%s" x

and field pp (f, v) ppf = fprintf ppf "%s = %t" f (pp v)

let tuple pp lst ppf =
  print ppf "(@[<hov>%t@])" (sequence ", " pp lst)

let record pp lst ppf =
  print ppf "{@[<hov>%t@]}" (sequence "; " (field pp) lst)

let to_string m =
  (Format.kfprintf (fun _ -> Format.flush_str_formatter ()) Format.str_formatter) m


let message ?loc msg_type v =
  if v <= !Config.verbosity then
    begin
      begin match loc with
      | None -> Format.eprintf "@[%s: " msg_type
      | Some loc -> Format.eprintf "@[%s (%t): " msg_type (Location.print loc)
      end;
      Format.kfprintf (fun ppf -> fprintf ppf "@]@.") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let error (loc, err_type, msg) = message ?loc err_type 1 "%s" msg
let check ~loc = message ~loc "Check" 2
let warning ~loc = message ~loc "Warning" 3
let info ?loc = message ?loc "Info" 4
let debug ?loc = message ?loc "Debug" 5
