module Assoc = Assoc
module Config = Config
module Error = Error
module List = List
module Location = Location
module Print = Print
module Symbol = Symbol
module Symbols = Symbols

type 'a located = { it : 'a; at : Location.t }

let unlocated x = { it = x; at = Location.unknown }
