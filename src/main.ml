(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Antoine Miné 2015
*)


module ConcreteAnalysis =
  Interpreter.Interprete(Concrete_domain.Concrete)
    
module ConstantAnalysis =
  Interpreter.Interprete
    (Non_relational_domain.NonRelational
       (Constant_domain.Constants))

(*interval module added*)
module IntervalAnalysis =
  Interpreter.Interprete
    (Non_relational_domain.NonRelational
       (Interval_domain.Intervals))

(*disjonctive interval analysis*)
module DisjonctiveAnalysis =
  Interpreter.Interprete
    (Non_relational_domain.NonRelational
       (Disjonctive_domain.DisjunctiveIntervals))

(*parity interval reduction*)
module ParityIntervalsAnalysis =
 Interpreter.Interprete
   (Non_relational_domain.NonRelational
     (Value_reduced_product.ReducedProduct
       (Parity_interval_reduction.ParityIntervalsReduction)))   
    
(* parse and print filename *)
let doit filename =
  let prog = File_parser.parse_file filename in
  Abstract_syntax_printer.print_prog Format.std_formatter prog

    
(* default action: print back the source *)
let eval_prog prog =
  Abstract_syntax_printer.print_prog Format.std_formatter prog

(* entry point *)
let main () =
  let action = ref eval_prog in
  let files = ref [] in
  (* parse arguments *)
  Arg.parse
    (* handle options *)
    ["-trace",
     Arg.Set Interpreter.trace,
     "Show the analyzer state after each statement";

     "-concrete",
     Arg.Unit (fun () -> action := ConcreteAnalysis.eval_prog),
     "Use the concrete domain";

     "-constant",
     Arg.Unit (fun () -> action := ConstantAnalysis.eval_prog),
     "Use the constant abstract domain";

     (* options to add *)
     "-interval",
     Arg.Unit (fun () -> action := IntervalAnalysis.eval_prog),
     "Use the interval abstract domain";

    "-delay", Arg.Set_int Interpreter.widen_delay,"Use the loop delay";
     "-unroll", Arg.Set_int Interpreter.loop_unroll,"Use the loop unrool";

      "-parity-interval",
      Arg.Unit (fun () -> action := ParityIntervalsAnalysis.eval_prog),
     "Use the parity-interval abstract domain";

 "-disjonctive",
      Arg.Unit (fun () -> action := DisjonctiveAnalysis.eval_prog),
     "Use the disjonctive -interval abstract domain";
    ]
    (* handle filenames *)
    (fun filename -> files := (!files)@[filename])
    "";
  List.iter
    (fun filename ->
      let prog = File_parser.parse_file filename in
      !action prog
    )
    !files
    
let _ = main ()
