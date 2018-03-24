open Abstract_syntax_tree
open Value_reduction
open Parity_domain
open Interval_domain

module ParityIntervalsReduction =(struct

module A = Parity
module B = Intervals
type t = A.t * B.t
let reduce ((a,b):t) : t = a,b


end : VALUE_REDUCTION)