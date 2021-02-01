module Assoc = Assoc
module Config = Config
module Error = Error
module List = List
module Location = Location
module Option = Option
module Print = Print
module Symbol = Symbol
module Symbols = Symbols

type 'a located = { it : 'a; at : Location.t }

type ('trm, 'ty) typed = { term : 'trm; ty : 'ty }

let unlocated x = { it = x; at = Location.unknown }
