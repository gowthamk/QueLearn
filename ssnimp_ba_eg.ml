
open Z3
open Z3.SMT
open Z3.Sort
open Z3.Expr
open Z3.Optimize
open Z3.Solver
open Z3.Symbol
open Z3.Datatype
open Z3.FuncDecl
open Z3.Boolean
open Z3.Arithmetic 
open Z3.Arithmetic.Integer
open Z3.Quantifier
module Solver = Z3.Solver
module Model = Z3.Model
module Symbol = Z3.Symbol
module Optimize = Z3.Optimize
module Int = Z3.Arithmetic.Integer
module Bool = Z3.Boolean
module Quantifier = Z3.Quantifier

let fromJust = function
  | Some x -> x
  | None -> failwith "Got None when Some was expected."

(* Returns [f(i), f(i-1), ... , f(1)]*)
let rec list_init i f = if i <= 0 then [] else (f i)::(list_init (i-1) f)

let hd = List.hd

let _ = 
  if not (Log.open_ "z3.log") then
    failwith "Log couldn't be opened."
  else (
    Printf.printf "Running Z3 version %s\n" Version.to_string ;
    let cfg = [("model", "true"); ("proof", "false")] in
    let ctx = (mk_context cfg) in
    let solver = mk_solver ctx None in 
    let sym = Symbol.mk_string ctx in
    let nullary_const cons = mk_app ctx 
                   (Constructor.get_constructor_decl cons) [] in
    let s_true = mk_true ctx in
    let s_Int = Int.mk_sort ctx in
    let s_Bool = Bool.mk_sort ctx in
    let s_0 = Int.mk_numeral_i ctx 0 in
    (* (declare-datatypes () ((Oper GB WD DP NOP)))*)
    let s_GB = mk_constructor_s ctx "GB" (sym "isGB") [] [] [] in
    let s_WD = mk_constructor_s ctx "WD" (sym "isWD") [] [] [] in
    let s_DP = mk_constructor_s ctx "DP" (sym "isDP") [] [] [] in
    let s_NOP = mk_constructor_s ctx "NOP" (sym "isNOP") [] [] [] in
    let s_Oper = mk_sort_s ctx "Oper" [s_GB; s_WD; s_DP; s_NOP] in
    (* (declare-datatypes () ((Eff e1 e2 e3 e4 e5)))*)
    let s_e1 = mk_constructor_s ctx "e1" (sym "isE1") [] [] [] in
    let s_e2 = mk_constructor_s ctx "e2" (sym "isE2") [] [] [] in
    let s_e3 = mk_constructor_s ctx "e3" (sym "isE3") [] [] [] in
    let s_e4 = mk_constructor_s ctx "e4" (sym "isE4") [] [] [] in
    let s_e5 = mk_constructor_s ctx "e5" (sym "isE5") [] [] [] in
    let s_Eff = mk_sort_s ctx "Eff" [s_e1; s_e2; s_e3; s_e4; s_e5] in
    (* (declare-fun oper (Eff) Oper) *)
    let s_oper = mk_func_decl_s ctx "oper" [s_Eff] s_Oper in
    (* (declare-fun rval (Eff) Int) *)
    let s_rval = mk_func_decl_s ctx "rval" [s_Eff] s_Int in
    (* (assert (forall ((e Eff)) (=> (or (= (oper e) DP) (= (oper e) WD)) 
                              (>= (rval e) 0)))) *)
    let typs = [s_Eff] in
    let names = [sym "e"] in
    let vars = [mk_bound ctx 0 s_Eff] in 
    let opere = mk_app ctx s_oper vars in
    let rvale = mk_app ctx s_rval vars in
    let body = mk_implies ctx 
                 (mk_or ctx [mk_eq ctx opere (nullary_const s_DP);
                             mk_eq ctx opere (nullary_const s_WD)])
                  (mk_ge ctx rvale s_0) in
    let asn1 = mk_forall ctx typs names body None [] [] None None in
    let _ = Printf.printf "Quantifier asn1: %s\n" 
              (Quantifier.to_string asn1) in
    let _ = Solver.add solver [expr_of_quantifier asn1] in
    (* (declare-fun vis (Eff Eff) Bool) *)
    let s_vis = mk_func_decl_s ctx "vis" [s_Eff; s_Eff] s_Bool in
    (* (assert (forall ((e Eff)) (not (vis e e)))) *)
    let body = mk_not ctx @@ mk_app ctx s_vis [hd vars; hd vars] in
    let asn2 = mk_forall ctx typs names body None [] [] None None in
    let _ = Printf.printf "Quantifier asn2: %s\n" 
              (Quantifier.to_string asn2) in
    let _ = Solver.add solver [expr_of_quantifier asn2] in
    (* (declare-const a1 Int) (declare-const a2 Int) *)
    let s_a1 = Int.mk_const ctx @@ sym "a1" in
    let s_a2 = Int.mk_const ctx @@ sym "a2" in
    (* (assert (>= a1 0)) (assert (>= a2 0)) *)
    let asn3 = mk_ge ctx s_a1 s_0 in
    let asn4 = mk_ge ctx s_a2 s_0 in
    let _ = Solver.add solver [asn3; asn4] in
    (* (define-fun sel ((a Eff)(n Eff)) Int
        (if (and (vis a n) (= (oper a) DP)) (rval a) 
          (if (and (vis a n) (= (oper a) WD)) (- 0 (rval a)) 0))) *)
    let s_sel = mk_func_decl_s ctx "sel" [s_Eff; s_Eff] s_Int in
    let typs = [s_Eff; s_Eff] in
    let names = [sym "a"; sym "n"] in
    let vars = [mk_bound ctx 0 s_Eff; mk_bound ctx 1 s_Eff] in 
    let visan = mk_app ctx s_vis vars in
    let opera = mk_app ctx s_oper [hd vars] in
    let rvala = mk_app ctx s_rval [hd vars] in
    let grd1 = mk_and ctx [visan; 
                           mk_eq ctx opera @@ nullary_const s_DP] in
    let grd2 = mk_and ctx [visan;
                           mk_eq ctx opera @@ nullary_const s_WD] in
    let rhs = mk_ite ctx grd1 rvala @@
                 mk_ite ctx grd2 (mk_unary_minus ctx rvala) s_0 in
    let lhs = mk_app ctx s_sel vars in
    let body = mk_eq ctx lhs rhs in
    let asn5 = mk_forall ctx typs names body None [] [] None None in
    let _ = Solver.add solver [expr_of_quantifier asn5] in
    let model = match check solver []  with
      | SATISFIABLE -> fromJust (get_model solver)
      | _ -> failwith "Unsat!" in
    Printf.printf "Model: \n%s\n" (Model.to_string model);
    Printf.printf "Disposing...\n";
    Gc.full_major ())
