
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

module Array :
sig
  include module type of Array
  val map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map3 : ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array
end = 
struct
  include Array
  let map2 f arr1 arr2 = 
    let _ = if Array.length arr1 = Array.length arr2 then ()
            else failwith "Array.map2 exception" in
      Array.mapi (fun i e1 -> f e1 @@ arr2.(i)) arr1

  let map3 f arr1 arr2 arr3 = 
    let _ = if Array.length arr1 = Array.length arr2 &&
               Array.length arr2 = Array.length arr3 then ()
            else failwith "Array.map2 exception" in
      Array.mapi (fun i e1 -> f e1 arr2.(i) arr3.(i)) arr1
end

let mkUidGen idBase =
  let count = ref 0 in
    fun () -> 
      let id = idBase ^ (string_of_int !count) in
      let _ = count := !count + 1 in
        id
let freshDotFileName = 
  let f = mkUidGen @@ "cex"^(string_of_float @@ Unix.time ()) in
    fun () -> (f ())^".dot"

let fromJust = function
  | Some x -> x
  | None -> failwith "Got None when Some was expected."

type oper = GB | WD | DP | NOP
type exec = {opers: oper array; visees: bool array array}
exception Return 

(* Returns [f(i), f(i-1), ... , f(1)]*)
let rec list_init i f = if i <= 0 then [] else (f i)::(list_init (i-1) f)

let hd = List.hd

let oper_of_expr expr = match Expr.to_string expr with 
  | "GB" -> GB | "WD" -> WD | "DP" -> DP | "NOP" -> NOP
  | _ -> failwith "Unexpected Expr.expr"

let string_of_oper = function GB -> "GB" 
  | WD -> "WD" | DP -> "DP" | NOP -> "NOP"


(* 
 * Execution graphs
 *)
module ExecGraph : 
sig
  type t
  type node = int * oper
  val create : unit -> t
  val add_vertex : t -> node -> unit
  val remove_vertex : t -> node -> unit
  val add_edge : t -> (node*node) -> unit
  val fold_edges : (node*node -> 'a -> 'a) -> t -> 'a -> 'a
  val output_graph : out_channel -> t -> unit
end= 
struct
  type node = int * oper
  module Vertex = struct
    type t = node
    let compare (a1,_) (a2,_) = Pervasives.compare a1 a2
    let hash = Hashtbl.hash
    let equal (a1,_) (a2,_) = a1 = a2
  end 
  module DiGraph = Graph.Imperative.Digraph.ConcreteBidirectional(Vertex)
  module Dot = Graph.Graphviz.Dot
    (struct
       include DiGraph
       let edge_attributes _ = []
       let default_edge_attributes _ = [`Label "vis"]
       let get_subgraph _ = None
       let vertex_name (a,op_tag) = "e"^(string_of_int a)^"_"
              ^(string_of_oper op_tag)
       let vertex_attributes v = [`Label (vertex_name v)]
       let default_vertex_attributes _ = []
       let graph_attributes _ = []
     end)
  include DiGraph
  include Dot
  let create () = create ()
  let add_edge t (v1,v2) = add_edge t v1 v2
  let fold_edges f = fold_edges (fun v1 v2 acc -> f (v1,v2) acc)
end

let graph_of_exec {opers=opers_mod; visees=visees_mod} = 
  let open ExecGraph in
  let g = create () in
  let add_vertex = add_vertex g in
  let add_edge = add_edge g in
    begin
      for i=0 to 4 do
        for j=0 to 4 do
          if visees_mod.(i).(j) then
            begin
              let node1 = (i+1,opers_mod.(i)) in
              let node2 = (j+1,opers_mod.(j)) in
              add_vertex node1;
              add_vertex node2;
              add_edge (node1,node2)
            end
          else
            ()
        done
      done;
      g
    end

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
    let expr_of_oper = function 
      | GB -> nullary_const s_GB 
      | WD -> nullary_const s_WD
      | DP -> nullary_const s_DP
      | NOP -> nullary_const s_NOP in
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
    let s_hb = mk_func_decl_s ctx "hb" [s_Eff; s_Eff] s_Bool in
    (* assert (forall ((a Eff) (b Eff)) (=> (vis a b) (hb a b)) *)
    let typs = [s_Eff; s_Eff] in
    let names = [sym "a"; sym "b"] in
    let vars = [mk_bound ctx 1 s_Eff; mk_bound ctx 0 s_Eff] in 
    let visab = mk_app ctx s_vis vars in
    let hbab = mk_app ctx s_hb vars in
    let body = mk_implies ctx visab hbab in
    let asn2a = mk_forall ctx typs names body None [] [] None None in
    let _ = Printf.printf "Quantifier asn2a: %s\n" 
              (Quantifier.to_string asn2a) in
    (* assert (forall ((a Eff) (b Eff) (c Eff)) 
          (=> (and (hb a b) (hb b c)) (hb a c)) *)
    let typs = [s_Eff; s_Eff; s_Eff] in
    let names = [sym "a"; sym "b"; sym "c"] in
    let vars = [mk_bound ctx 2 s_Eff; mk_bound ctx 1 s_Eff; 
                mk_bound ctx 0 s_Eff] in 
    let hbab = mk_app ctx s_hb [List.nth vars 0; List.nth vars 1] in
    let hbbc = mk_app ctx s_hb [List.nth vars 1; List.nth vars 2] in
    let hbac = mk_app ctx s_hb [List.nth vars 0; List.nth vars 2] in
    let body = mk_implies ctx (mk_and ctx [hbab; hbbc]) hbac in
    let asn2b = mk_forall ctx typs names body None [] [] None None in
    let _ = Printf.printf "Quantifier asn2b: %s\n" 
              (Quantifier.to_string asn2b) in
    (* (assert (forall ((e Eff)) (not (hb e e)))) *)
    let typs = [s_Eff] in
    let names = [sym "e"] in
    let vars = [mk_bound ctx 0 s_Eff] in 
    let body = mk_not ctx @@ mk_app ctx s_hb [hd vars; hd vars] in
    let asn2c = mk_forall ctx typs names body None [] [] None None in
    let _ = Printf.printf "Quantifier asn2c: %s\n" 
              (Quantifier.to_string asn2c) in
    (* (assert (not (vis (e_i,e_j))) where i \in {3,4,5} and 
    * j \in {1,2}) *)
    (* (declare-const a1 Int) (declare-const a2 Int) *)
    let s_a1 = Int.mk_const ctx @@ sym "a1" in
    let s_a2 = Int.mk_const ctx @@ sym "a2" in
    (* (assert (>= a1 0)) (assert (>= a2 0)) *)
    let asn3 = mk_gt ctx s_a1 s_0 in
    let asn4 = mk_gt ctx s_a2 s_0 in
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
    (* (assert (not inv)) *)
    let neg_inv_asn = mk_not ctx s_inv in
    (* Create opt_solver and  assert all hard contraints.*)
    let opt_solver = mk_opt ctx in
    let _ = OptSolver.add opt_solver [expr_of_quantifier asn1; 
                                      expr_of_quantifier asn2a; 
                                      expr_of_quantifier asn2b; 
                                      expr_of_quantifier asn2c; 
                                      asn3; asn4; 
                                      expr_of_quantifier asn5; 
                                      expr_of_quantifier asn6;
                                      asn7; asn8; asn9; asn10; 
                                      asn11; asn12;
                                      neg_inv_asn] in
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
    (* assert soft constraints *)
    let _ = 
      for i = 0 to 4 do
        for j = 0 to 4 do
          let visee = visees.(i).(j) in
          let soft_asn = mk_not ctx visee in
            ignore @@ OptSolver.add_soft opt_solver soft_asn "1" @@ sym "soft"
        done
      done in
    (*
     *  Encode (relevant part of) the given execution as a big conjunction.
     *)
    let encode_exec ({opers=opers_mod; visees=visees_mod}:exec) : Expr.expr = 
      let relevant = Array.make 5 false in
      let _ = 
        for i=0 to 4 do
          for j=0 to 4 do
              if visees_mod.(i).(j) then
                begin
                    relevant.(i) <- true;
                    relevant.(j) <- true;
                end
              else
                ()
          done
        done in
      let oper_eqs = Array.to_list @@ Array.map3 
                       (fun is_rel opere op_tag -> 
                          if is_rel then mk_eq ctx opere @@ 
                                         expr_of_oper op_tag
                          else s_true)
                       relevant opers opers_mod in
      let vis_preds = ref [] in
      let _ =
        for i=4 downto 0 do
          for j=4 downto 0 do
            let vis_pred = if visees_mod.(i).(j) 
                           then Some visees.(i).(j)
                           else if i!=j && (relevant.(i) || relevant.(j)) 
                           then Some (mk_not ctx visees.(i).(j))
                           else None in
              match vis_pred with 
                | None -> ()
                | Some vis_pred -> vis_preds := vis_pred :: (!vis_preds)
          done
        done in
      let conj = mk_and ctx @@ oper_eqs @ !vis_preds in
      let _ = Printf.printf "Conjunction:\n %s \n" @@ Expr.to_string conj in
        conj in
    (*
     * Main CEGAR loop.
     *)
    let cexs = ref [] in
    let rec cegar_loop iter = 
      let _ = if iter > 20 then raise Return else () in
      let _ = OptSolver.push opt_solver in 
      let _ = if iter = -1 then 
                begin
                  Printf.printf "*****  CONTEXT ******\n";
                  print_string @@ OptSolver.to_string opt_solver;
                  Printf.printf "\n*********************\n"
                end
              else () in
      let model = match OptSolver.check opt_solver with
        | SATISFIABLE -> fromJust (OptSolver.get_model opt_solver)
        | UNSATISFIABLE -> (print_string "UNSAT\n"; raise Return)
        | UNKNOWN -> (print_string "UNKNOWN\n"; raise Return) in
      let _ = OptSolver.pop opt_solver in
      (* Printf.printf "Model: \n%s\n" (Model.to_string model);*)
      let opers_mod = Array.map 
                        (fun opere -> oper_of_expr @@ fromJust @@ 
                                      Model.eval model opere true)
                        opers in
      let visees_mod = Array.map 
                         (fun row -> Array.map 
                            (fun visee -> is_true @@ fromJust @@
                                 Model.eval model visee true) row) 
                         visees in
      let cex = {opers=opers_mod; visees=visees_mod} in 
        begin
          cexs:= cex :: !cexs; 
          Printf.printf "%d. " iter; 
          print_exec cex; 
          flush_all ();
          OptSolver.add opt_solver [mk_not ctx @@ encode_exec cex];
          cegar_loop (iter + 1);
        end in
    begin
      try cegar_loop 1 with 
        | Return -> ();
      List.iteri
        (fun i cex -> 
           let g = graph_of_exec cex in
           let fpath = "./Graphs/"^(string_of_int i)^".dot" in
           let out_channel = open_out_bin fpath in
           let _ = ExecGraph.output_graph out_channel g in
           let _ = close_out out_channel in
             ()) 
        @@ List.rev !cexs;
      let fpath = "Graphs/"^(freshDotFileName()) in
      ignore @@ Sys.command @@ Printf.sprintf 
                       "gvpack -gu Graphs/[0-9]*.dot > %s" fpath ;
      ignore @@ Sys.command "rm Graphs/[0-9]*.dot";
      Printf.printf "Execution graph: %s\n" fpath;
      Printf.printf "Disposing...\n";
      Gc.full_major ()
    end)

