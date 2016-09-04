
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
module OptSolver = Z3.Optimize
module Model = Z3.Model
module Symbol = Z3.Symbol
module Optimize = Z3.Optimize
module Int = Z3.Arithmetic.Integer
module Bool = Z3.Boolean
module Quantifier = Z3.Quantifier
module Expr = Z3.Expr

let fromJust = function
  | Some x -> x
  | None -> failwith "Got None when Some was expected."

type oper = GB | WD | DP | NOP
type exec = {opers: oper array; visees: bool array array}

(* Returns [f(i), f(i-1), ... , f(1)]*)
let rec list_init i f = if i <= 0 then [] else (f i)::(list_init (i-1) f)

let hd = List.hd

let oper_of_expr expr = match Expr.to_string expr with 
  | "GB" -> GB | "WD" -> WD | "DP" -> DP | "NOP" -> NOP
  | _ -> failwith "Unexpected Expr.expr"

let string_of_oper = function GB -> "GB" 
  | WD -> "WD" | DP -> "DP" | NOP -> "NOP"

let print_exec {opers; visees} = 
  begin
    for i = 0 to 4 do
      Printf.printf "%s," (string_of_oper opers.(i)) 
    done;
    for i=0 to 4 do
      for j=0 to 4 do
        let value = if visees.(i).(j) then "1" else "0" in
        let sep = if i=4 && j=4 then "" else "," in
          Printf.printf "%s%s" value sep
      done
    done;
    Printf.printf "\n"
  end

let _ = 
  if not (Log.open_ "z3.log") then
    failwith "Log couldn't be opened."
  else (
    Printf.printf "Running Z3 version %s\n" Version.to_string ;
    let cfg = [("model", "true"); ("proof", "false")] in
    let ctx = (mk_context cfg) in
    let sym = Symbol.mk_string ctx in
    let nullary_const cons = mk_app ctx 
                   (Constructor.get_constructor_decl cons) [] in
    (* let s_true = mk_true ctx in *)
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
    (* (declare-fun vis (Eff Eff) Bool) *)
    let s_vis = mk_func_decl_s ctx "vis" [s_Eff; s_Eff] s_Bool in
    (* (assert (forall ((e Eff)) (not (vis e e)))) *)
    let body = mk_not ctx @@ mk_app ctx s_vis [hd vars; hd vars] in
    let asn2 = mk_forall ctx typs names body None [] [] None None in
    let _ = Printf.printf "Quantifier asn2: %s\n" 
              (Quantifier.to_string asn2) in
    (* (declare-const a1 Int) (declare-const a2 Int) *)
    let s_a1 = Int.mk_const ctx @@ sym "a1" in
    let s_a2 = Int.mk_const ctx @@ sym "a2" in
    (* (assert (>= a1 0)) (assert (>= a2 0)) *)
    let asn3 = mk_ge ctx s_a1 s_0 in
    let asn4 = mk_ge ctx s_a2 s_0 in
    (* (define-fun sel ((a Eff)(n Eff)) Int
        (if (and (vis a n) (= (oper a) DP)) (rval a) 
          (if (and (vis a n) (= (oper a) WD)) (- 0 (rval a)) 0))) *)
    let s_sel = mk_func_decl_s ctx "sel" [s_Eff; s_Eff] s_Int in
    let typs = [s_Eff; s_Eff] in
    let names = [sym "a"; sym "n"] in
    let vars = [mk_bound ctx 1 s_Eff; mk_bound ctx 0 s_Eff] in 
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
    let _ = Printf.printf "Quantifier asn5: %s\n" 
              (Quantifier.to_string asn5) in
    (* (define-fun getBalance ((n Eff)) Int
          (+ (sel e1 n) (sel e2 n) (sel e3 n) (sel e4 n) (sel e5 n))) *)
    let s_getBalance = mk_func_decl_s ctx "getBalance" [s_Eff] s_Int in
    let typs = [s_Eff] in
    let names = [sym "n"] in
    let vars = [mk_bound ctx 0 s_Eff] in 
    let sele1n = mk_app ctx s_sel [nullary_const s_e1; hd vars] in
    let sele2n = mk_app ctx s_sel [nullary_const s_e2; hd vars] in
    let sele3n = mk_app ctx s_sel [nullary_const s_e3; hd vars] in
    let sele4n = mk_app ctx s_sel [nullary_const s_e4; hd vars] in
    let sele5n = mk_app ctx s_sel [nullary_const s_e5; hd vars] in
    let rhs = mk_add ctx [sele1n; sele2n; sele3n; sele4n; sele5n] in
    let lhs = mk_app ctx s_getBalance vars in
    let body = mk_eq ctx lhs rhs in
    let asn6 = mk_forall ctx typs names body None [] [] None None in
    let _ = Printf.printf "Quantifier asn6: %s\n" 
              (Quantifier.to_string asn6) in
    (* (assert (= (oper e3) GB)) (assert (= (rval e3) (getBalance e3))) *)
    let opere3 = mk_app ctx s_oper [nullary_const s_e3] in
    let asn7 = mk_eq ctx opere3 @@ nullary_const s_GB in
    let rvale3 = mk_app ctx s_rval [nullary_const s_e3] in
    let asn8 = mk_eq ctx rvale3 @@ mk_app ctx s_getBalance 
                                     [nullary_const s_e3] in
    (* (assert (if (>= (getBalance e4) a1) 
                  (and (= (oper e4) WD) (= (rval e4) a1)) 
                  (and (= (oper e4) NOP))))*)
    let grd = mk_ge ctx (mk_app ctx s_getBalance 
                           [nullary_const s_e4]) s_a1 in
    let opere4 = mk_app ctx s_oper [nullary_const s_e4] in
    let rvale4 = mk_app ctx s_rval [nullary_const s_e4] in
    let thene = mk_and ctx [mk_eq ctx opere4 @@ nullary_const s_WD;
                            mk_eq ctx rvale4 s_a1] in
    let elsee = mk_eq ctx opere4 @@ nullary_const s_NOP in
    let asn9 = mk_ite ctx grd thene elsee in
    (* (assert (if (>= (getBalance e5) a2) 
                  (and (= (oper e5) WD) (= (rval e5) a2)) 
                  (and (= (oper e5) NOP))))*)
    let grd = mk_ge ctx (mk_app ctx s_getBalance 
                           [nullary_const s_e5]) s_a2 in
    let opere5 = mk_app ctx s_oper [nullary_const s_e5] in
    let rvale5 = mk_app ctx s_rval [nullary_const s_e5] in
    let thene = mk_and ctx [mk_eq ctx opere5 @@ nullary_const s_WD;
                            mk_eq ctx rvale5 s_a2] in
    let elsee = mk_eq ctx opere5 @@ nullary_const s_NOP in
    let asn10 = mk_ite ctx grd thene elsee in
    (* (assert (>= (+ (sel e1 e3) (sel e2 e3)) 0))*)
    let sele1e3 = mk_app ctx s_sel [nullary_const s_e1; 
                                    nullary_const s_e3] in
    let sele2e3 = mk_app ctx s_sel [nullary_const s_e2; 
                                    nullary_const s_e3] in
    let asn11 = mk_ge ctx (mk_add ctx [sele1e3; sele2e3]) s_0 in
    (* (declare-const inv Bool) (assert (= inv (>= (rval e3) 0))) *)
    let s_inv = Boolean.mk_const ctx @@ sym "inv" in
    let asn12 = mk_eq ctx s_inv @@ mk_ge ctx rvale3 s_0 in
    (* assert soft constraints *)
    let opt_solver = mk_opt ctx in
    let _ = OptSolver.add opt_solver [expr_of_quantifier asn1; 
                                      expr_of_quantifier asn2; 
                                      asn3; asn4; 
                                      expr_of_quantifier asn5; 
                                      expr_of_quantifier asn6;
                                      asn7; asn8; asn9; asn10; 
                                      asn11; asn12] in
    let e_consts = Array.of_list @@ List.map nullary_const 
                                      [s_e1; s_e2; s_e3; s_e4; s_e5] in
    let (visees : Expr.expr array array) = Array.mapi 
                   (fun i row -> 
                      Array.mapi
                        (fun j x -> mk_app ctx s_vis 
                                      [e_consts.(i); e_consts.(j)]) row) 
                   (Array.make 5 @@ Array.make 5 0) in
    let opere1 = mk_app ctx s_oper [nullary_const s_e1] in
    let opere2 = mk_app ctx s_oper [nullary_const s_e2] in
    let opers = Array.of_list [opere1; opere2; opere3; opere4; opere5] in
    let _ = 
      for i = 0 to 4 do
        for j = 0 to 4 do
          let str = "soft"^(string_of_int @@ i+1)^(string_of_int @@ j+1) in
          let visee = visees.(i).(j) in
          let soft_asn = mk_not ctx visee in
            ignore @@ OptSolver.add_soft opt_solver soft_asn "1" @@ sym str
        done
      done in
    let _ = OptSolver.push opt_solver in 
    (* (assert (not inv)) *)
    let neg_inv_asn = mk_not ctx s_inv in
    let _ = OptSolver.add opt_solver [neg_inv_asn] in
    let _ = Printf.printf "Opt Ctx:\n %s \n" @@ OptSolver.to_string opt_solver in
    let model = match OptSolver.check opt_solver with
      | SATISFIABLE -> fromJust (OptSolver.get_model opt_solver)
      | _ -> failwith "Unsat!" in
    let _ = OptSolver.pop opt_solver in
    (*Printf.printf "Model: \n%s\n" (Model.to_string model);*)
    let opers_mod = Array.map 
                      (fun opere -> oper_of_expr @@ fromJust @@ 
                                    Model.eval model opere true)
                      opers in
    let visees_mod = Array.map 
                       (fun row -> Array.map 
                          (fun visee -> is_true @@ fromJust @@
                               Model.eval model visee true) row) 
                       visees in
    let exec = {opers=opers_mod; visees=visees_mod} in 
    let _ = print_exec exec in 
    let _ = Printf.printf "oper(e1) = %s\n" @@ Expr.to_string @@ 
            fromJust @@ Model.eval model opere1 true in
    let _ = Printf.printf "oper(e2) = %s\n" @@ Expr.to_string @@ 
            fromJust @@ Model.eval model opere2 true in
    let _ = Printf.printf "oper(e3) = %s\n" @@ Expr.to_string @@ 
            fromJust @@ Model.eval model opere3 true in
    let _ = Printf.printf "oper(e4) = %s\n" @@ Expr.to_string @@ 
            fromJust @@ Model.eval model opere4 true in
    let _ = Printf.printf "oper(e5) = %s\n" @@ Expr.to_string @@ 
            fromJust @@ Model.eval model opere5 true in
    let _ = Printf.printf "%s = %s\n"  (Expr.to_string visees.(0).(2))
              (Expr.to_string @@ fromJust @@ 
               Model.eval model visees.(0).(2) true) in
    Printf.printf "Disposing...\n";
    Gc.full_major ())
