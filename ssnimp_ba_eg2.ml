
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

module List:
sig
  include module type of List
  val keep_some : 'a option list -> 'a list
  val tabulate : int -> (int -> 'a) -> 'a list 
  val unzip : ('a*'b) list -> 'a list * 'b list
end = 
struct
  include List
  let rec keep_some l = match l with
    | [] -> []
    | (Some x)::xs -> x::(keep_some xs)
    | None::xs -> keep_some xs
  let tabulate n f = 
    let l = Array.to_list @@ Array.make n () in
      List.mapi (fun i _ -> f i) l

  let rec unzip l = match l with
    | [] -> ([],[])
    | (x,y)::l' -> (fun (xs,ys) -> (x::xs,y::ys)) @@ unzip l'
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
exception Return of exec list

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
  let n = Array.length opers_mod in 
    begin
      for i=0 to n-1 do
        for j=0 to n-1 do
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
  let n = Array.length opers in 
  begin
    for i=0 to n-1 do
      for j=0 to n-1 do
        let value = if visees.(i).(j) then "1" else "0" in
        let sep = if i=n-1 && j=n-1 then "" else "," in
          Printf.printf "%s%s" value sep
      done
    done;
    Printf.printf "\n"
  end

let mine_a_contract n_effs_S cexss ctrts = 
  let n_effs = n_effs_S + 2 in
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
  let expr_of_oper = function 
    | GB -> nullary_const s_GB 
    | WD -> nullary_const s_WD
    | DP -> nullary_const s_DP
    | NOP -> nullary_const s_NOP in
  (* (declare-datatypes () ((Eff e1 e2 e3 e4 e5)))*)
  let s_e = mk_constructor_s ctx "e" (sym "isE") [] [] [] in
  let s_eb = mk_constructor_s ctx "eb" (sym "isEb") [] [] [] in
  let effs_S = List.tabulate n_effs_S 
                 (fun i -> 
                    let iStr = string_of_int i in
                    let estr = "e"^iStr in
                    let esym = sym ("isE"^iStr) in
                      mk_constructor_s ctx estr esym [] [] []) in
  let effs = effs_S@[s_e;s_eb] in
  let s_Eff = mk_sort_s ctx "Eff" effs in
  (* (declare-fun oper (Eff) Oper) *)
  let s_oper = mk_func_decl_s ctx "oper" [s_Eff] s_Oper in
  (* (declare-fun rval (Eff) Int) *)
  let s_rval = mk_func_decl_s ctx "rval" [s_Eff] s_Int in
  (* (declare-fun vis (Eff Eff) Bool) *)
  let s_vis = mk_func_decl_s ctx "vis" [s_Eff; s_Eff] s_Bool in
  (* (declare-fun hb (Eff Eff) Bool) *)
  let s_hb = mk_func_decl_s ctx "hb" [s_Eff; s_Eff] s_Bool in

  (*
   *  Encode (relevant part of) the given execution as a big conjunction.
   *)
  let encode_exec n_S ({opers=opers_mod; visees=visees_mod}:exec) opers visees = 
    let oper_eqs = Array.to_list @@ Array.map2
                     (fun opere op_tag -> 
                        mk_eq ctx opere @@ 
                                       expr_of_oper op_tag) 
                      opers opers_mod in
    let vis_preds = ref [] in
    let n = Array.length opers in
    let _ =
      if n_S < n then ()
      else failwith "n_S < n invariant violated";
      for i=0 to n-1  do
        for j=0 to n-1 do
          let vis_pred = if visees_mod.(i).(j) 
                         then Some visees.(i).(j)
                         else if i!=j && not (i<n_S && j<n_S) 
                                  && not visees_mod.(j).(i)
                         then Some (mk_not ctx visees.(i).(j)) 
                         else None in
            match vis_pred with 
              | None -> ()
              | Some vis_pred -> vis_preds := vis_pred :: (!vis_preds)
        done
      done in
    let conj = mk_and ctx @@ oper_eqs @ List.rev !vis_preds in
    (* let _ = Printf.printf "Conjunction:\n %s \n" @@ Expr.to_string conj in *)
      conj in

  (*
   * Given a list of counterexamples, all having same number of effects, return
   * a contract that negates these counterexamples.
   *)
  let get_ctrt n_S cexs = 
    let n = n_S + 2 in
    let typs = List.tabulate n (fun _ -> s_Eff) in
    let names = List.tabulate n (fun i -> sym @@ "n_"^(string_of_int i)) in
    let vars = List.rev @@ List.tabulate n (fun i -> mk_bound ctx i s_Eff) in 
    let opers = Array.of_list @@ List.map (fun c -> 
                              mk_app ctx s_oper [c]) vars in
    let visees = Array.mapi 
                   (fun i row -> Array.mapi
                        (fun j x -> mk_app ctx s_vis 
                                      [List.nth vars i; 
                                       List.nth vars j]) row) 
                   (Array.make n @@ Array.make n 0) in
    let conjs = List.map (fun cex -> mk_not ctx @@ 
                                     encode_exec n_S cex opers visees) cexs in
    let body = mk_and ctx conjs in
    let ctrt = mk_forall ctx typs names body None [] [] None None in
    (* let _ = Printf.printf "Quantifier ctrt: %s\n" 
              (Quantifier.to_string ctrt) in *)
      expr_of_quantifier ctrt in

  (* (declare-fun in_S (Eff) Bool)*)
  let s_in_S = mk_func_decl_s ctx "in_S" [s_Eff] s_Bool in
  (* (assert (forall ((x Eff)) (<=> (not (in_S x)) 
   *           (or (= x s_e) (= x s_eb))))) *)
  let typs = [s_Eff] in
  let names = [sym "x"] in
  let var_x = mk_bound ctx 0 s_Eff in
  let vars = [var_x] in 
  let body = mk_iff ctx 
               (mk_not ctx @@ mk_app ctx s_in_S vars)
               (mk_or ctx [mk_eq ctx var_x (nullary_const s_e);
                           mk_eq ctx var_x (nullary_const s_eb)]) in
  let asn0 = mk_forall ctx typs names body None [] [] None None in
  (* let _ = Printf.printf "Quantifier asn0: %s\n" 
            (Quantifier.to_string asn0) in *)
  (* (assert (forall ((x Eff)) (=> (or (= (oper x) DP) (= (oper x) WD)) 
                            (>= (rval x) 0)))) *)
  let typs = [s_Eff] in
  let names = [sym "x"] in
  let vars = [mk_bound ctx 0 s_Eff] in 
  let opere = mk_app ctx s_oper vars in
  let rvale = mk_app ctx s_rval vars in
  let body = mk_implies ctx 
               (mk_or ctx [mk_eq ctx opere (nullary_const s_DP);
                           mk_eq ctx opere (nullary_const s_WD)])
                (mk_ge ctx rvale s_0) in
  let asn1 = mk_forall ctx typs names body None [] [] None None in
  (* let _ = Printf.printf "Quantifier asn1: %s\n" 
            (Quantifier.to_string asn1) in *)
  (* assert (forall ((a Eff) (b Eff)) (=> (vis a b) (hb a b)) *)
  let typs = [s_Eff; s_Eff] in
  let names = [sym "a"; sym "b"] in
  let vars = [mk_bound ctx 1 s_Eff; mk_bound ctx 0 s_Eff] in 
  let visab = mk_app ctx s_vis vars in
  let hbab = mk_app ctx s_hb vars in
  let body = mk_implies ctx visab hbab in
  let asn2a = mk_forall ctx typs names body None [] [] None None in
  (* let _ = Printf.printf "Quantifier asn2a: %s\n" 
            (Quantifier.to_string asn2a) in *)
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
  (* let _ = Printf.printf "Quantifier asn2b: %s\n" 
            (Quantifier.to_string asn2b) in *)
  (* (assert (forall ((e Eff)) (not (hb e e)))) *)
  let typs = [s_Eff] in
  let names = [sym "e"] in
  let vars = [mk_bound ctx 0 s_Eff] in 
  let body = mk_not ctx @@ mk_app ctx s_hb [hd vars; hd vars] in
  let asn2c = mk_forall ctx typs names body None [] [] None None in
  (* let _ = Printf.printf "Quantifier asn2c: %s\n" 
            (Quantifier.to_string asn2c) in *)
  (* (assert (forall ((x Eff)(y Eff)) 
   *      (=> (in_S y) (not (vis x y))))) *)
  let typs = [s_Eff; s_Eff] in
  let names = [sym "x"; sym "y"] in
  let [var_x; var_y] as vars = [mk_bound ctx 1 s_Eff; 
                                mk_bound ctx 0 s_Eff] in 
  let body = mk_implies ctx 
               (mk_app ctx s_in_S [var_y])
               (mk_not ctx @@ mk_app ctx s_vis vars) in
  let asn2d = mk_forall ctx typs names body None [] [] None None in
  (* let _ = Printf.printf "Quantifier asn2d: %s\n" 
            (Quantifier.to_string asn2d) in *)
  (* (declare-const a1 Int)*)
  let s_a1 = Int.mk_const ctx @@ sym "a1" in
  (* (assert (>= a1 0)) *)
  let asn3 = mk_gt ctx s_a1 s_0 in
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
  (* let _ = Printf.printf "Quantifier asn5: %s\n" 
            (Quantifier.to_string asn5) in *)
  (* We define a new type called State *)
  let s_State = mk_uninterpreted_s ctx "State" in
  (* State S0 is the common state present on all replicas *)
  let s_S0 = Expr.mk_const_s ctx "S0" s_State in 
  (* State S is the state before the execution of the withdraw operation *)
  let s_S = Expr.mk_const_s ctx "S" s_State in 
  (* State S1 is the state after the execution of the withdraw operation *)
  let s_S1 = Expr.mk_const_s ctx "S1" s_State in 
  (* Define getBalance as a function that, given a state and and effect,
   * computes the balance w.r.t to the part of the state visible to that 
   * effect *)
  let s_getBalance = mk_func_decl_s ctx "getBalance" [s_State; s_Eff] s_Int in
  (* For the common state S0, getBalance returns the same value for any effect.
   * (assert (forall ((a Eff)(b Eff)) 
   *      (= (getBalance S0 a) (getBalance S0 b)))) *)
  let typs = [s_Eff; s_Eff] in
  let names = [sym "a"; sym "b"] in
  let [var_a; var_b] as vars = [mk_bound ctx 1 s_Eff; 
                                mk_bound ctx 0 s_Eff] in 
  let body = mk_eq ctx (mk_app ctx s_getBalance [s_S0; var_a]) 
                       (mk_app ctx s_getBalance [s_S0; var_b]) in
  let asn6 = mk_forall ctx typs names body None [] [] None None in
  (* (assert (forall ((n Eff)) 
  *     (= (getBalance S n) (+ (getBalance S0 n) (sel e1 n) .. (sel ek n)))))*)
  let typs = [s_Eff] in
  let names = [sym "n"] in
  let vars = [mk_bound ctx 0 s_Eff] in 
  let sels_S = List.map (fun s_ei -> 
                         mk_app ctx s_sel 
                           [nullary_const s_ei; hd vars]) effs_S in
  let gbS0n = mk_app ctx s_getBalance (s_S0::vars) in
  let rhs = mk_add ctx @@ gbS0n::sels_S in
  let lhs = mk_app ctx s_getBalance (s_S::vars) in
  let body = mk_eq ctx lhs rhs in
  let asn6a = mk_forall ctx typs names body None [] [] None None in
  (* let _ = Printf.printf "Quantifier asn6: %s\n" 
            (Quantifier.to_string asn6) in *)
  (* Balance is initially non-negative *)
  (* (forall ((n Eff)) (=> (not (in_S n)) (>= (getBalance S n) 0))) *)
  let typs = [s_Eff] in
  let names = [sym "n"] in
  let vars = [mk_bound ctx 0 s_Eff] in 
  let body = mk_implies ctx 
               (mk_not ctx (mk_app ctx s_in_S vars))
               (mk_ge ctx (mk_app ctx s_getBalance (s_S::vars)) s_0) in
  let asn6b = mk_forall ctx typs names body None [] [] None None in
  (* let _ = Printf.printf "Quantifier asn6a: %s\n" 
            (Quantifier.to_string asn6a) in *)
  (* (assert (forall ((n Eff)) 
   *    (= (getBalance S1 n) (+ (getBalance S0 n) (sel e1 n) ...
   *                            (sel ek n) (sel e n) (sel eb n))))) *)
  let typs = [s_Eff] in
  let names = [sym "n"] in
  let vars = [mk_bound ctx 0 s_Eff] in 
  let s_sele = mk_app ctx s_sel [nullary_const s_e; hd vars] in
  let s_seleb = mk_app ctx s_sel [nullary_const s_eb; hd vars] in
  let gbS0n = mk_app ctx s_getBalance (s_S0::vars) in
  let rhs = mk_add ctx @@ gbS0n::s_sele::s_seleb::sels_S in
  let lhs = mk_app ctx s_getBalance (s_S1::vars) in
  let body = mk_eq ctx lhs rhs in
  let asn6c = mk_forall ctx typs names body None [] [] None None in
  (* let _ = Printf.printf "Quantifier asn6b: %s\n" 
            (Quantifier.to_string asn6b) in *)
  (* (assert (= (oper eb) GB)) (assert (= (rval eb) (getBalance S1 eb))) *)
  let opereb = mk_app ctx s_oper [nullary_const s_eb] in
  let asn7 = mk_eq ctx opereb @@ nullary_const s_GB in
  let rvaleb = mk_app ctx s_rval [nullary_const s_eb] in
  let asn8 = mk_eq ctx rvaleb @@ mk_app ctx s_getBalance
                                   [s_S1; nullary_const s_eb] in
  (* (assert (if (>= (getBalance S e) a1) 
                (and (= (oper e) WD) (= (rval e) a1)) 
                (and (= (oper e) NOP))))*)
  let grd = mk_ge ctx (mk_app ctx s_getBalance
                         [s_S; nullary_const s_e]) s_a1 in
  let opere = mk_app ctx s_oper [nullary_const s_e] in
  let rvale = mk_app ctx s_rval [nullary_const s_e] in
  let thene = mk_and ctx [mk_eq ctx opere @@ nullary_const s_WD;
                          mk_eq ctx rvale s_a1] in
  let elsee = mk_eq ctx opere @@ nullary_const s_NOP in
  let asn9 = mk_ite ctx grd thene elsee in
  (* (declare-const inv Bool) (assert (= inv (>= (rval eb) 0))) *)
  let s_inv = Boolean.mk_const ctx @@ sym "inv" in
  let asn12 = mk_eq ctx s_inv @@ mk_ge ctx rvaleb s_0 in
  (* 
   * Create opt_solver and  assert all the constraints generated from symbolic
   * execution.
   *)
  let opt_solver = mk_opt ctx in
  let _ = OptSolver.add opt_solver [expr_of_quantifier asn0; 
                                    expr_of_quantifier asn1; 
                                    expr_of_quantifier asn2a; 
                                    expr_of_quantifier asn2b; 
                                    expr_of_quantifier asn2c; 
                                    expr_of_quantifier asn2d; 
                                    asn3; 
                                    expr_of_quantifier asn5; 
                                    expr_of_quantifier asn6;
                                    expr_of_quantifier asn6a;
                                    expr_of_quantifier asn6b;
                                    expr_of_quantifier asn6c;
                                    asn7; asn8; asn9; asn12] in
  (* assert any existing contracts *)
  let _ = Array.iteri 
            (fun i cexs -> if List.length cexs = 0 then () else
              let ctrt = get_ctrt i cexs in
              let _ = if ctrts.(i) = "" 
                      then ctrts.(i) <- Expr.to_string ctrt else () in
                OptSolver.add opt_solver [ctrt]) 
            cexss in
  (* assert soft constraints *)
  let (e_consts,e_eqs) = List.unzip @@ List.map 
                            (fun (s_ei:Constructor.constructor) -> 
                               let s_ei_exp = nullary_const s_ei in
                               let str = "n_"^(Expr.to_string s_ei_exp) in
                               let c = Expr.mk_const_s ctx str s_Eff in
                               let eq = mk_eq ctx c @@ s_ei_exp in
                                (c,eq)) effs in
  let _ = OptSolver.add opt_solver e_eqs in
  let (visees : Expr.expr array array) = Array.mapi 
                 (fun i row -> Array.mapi
                      (fun j x -> mk_app ctx s_vis 
                                    [List.nth e_consts i; 
                                     List.nth e_consts j]) row) 
                 (Array.make n_effs @@ Array.make n_effs 0) in
  let _ = 
    for i = 0 to n_effs-1 do
      for j = 0 to n_effs-1 do
        let visee = visees.(i).(j) in
        let soft_asn = mk_not ctx visee in
          ignore @@ OptSolver.add_soft opt_solver soft_asn "1" @@ sym "soft"
      done
    done in
  (* Model evaluation stuff *)
  let opers = Array.of_list @@ List.map (fun c -> 
                            mk_app ctx s_oper [c]) e_consts in
  (*
   * Main CEGAR loop.
   *)
  let rec cegar_loop (cexs : exec list) iter = 
    (* let _ = if iter > 10 then raise (Return cexs) else () in *)
    (* Assert the last conjunct inferred *)
    let _ = match cexs with
      | [] -> () 
      | cex::_ -> OptSolver.add opt_solver 
                    [mk_not ctx @@ encode_exec n_effs_S cex opers visees] in
    (*
     * PUSH.
     *)
    let _ = OptSolver.push opt_solver in 
    (* (assert (not inv)) *)
    let neg_inv_asn = mk_not ctx s_inv in
    let _ = OptSolver.add opt_solver [neg_inv_asn] in
    let _ = if iter = -1 then 
              begin
                Printf.printf "*****  CONTEXT ******\n";
                print_string @@ OptSolver.to_string opt_solver;
                Printf.printf "\n*********************\n"
              end
            else () in
    let model = match OptSolver.check opt_solver with
      | SATISFIABLE -> fromJust (OptSolver.get_model opt_solver)
      | UNSATISFIABLE -> (print_string "UNSAT\n"; raise (Return cexs))
      | UNKNOWN -> (print_string "UNKNOWN\n"; raise (Return cexs)) in
    (* Printf.printf "Model: \n%s\n" (Model.to_string model);*)
    let _ = OptSolver.pop opt_solver in
    (* 
     * POP. 
     * Read counter example.
     *)
    let opers_mod = Array.map 
                      (fun opere -> oper_of_expr @@ fromJust @@ 
                                    Model.eval model opere true)
                      opers in
    let visees_mod = Array.map 
                       (fun row -> Array.map 
                          (fun visee -> is_true @@ fromJust @@
                               Model.eval model visee true) row) 
                       visees in
    let cex = { opers=opers_mod; visees=visees_mod} in 
    (* 
     * Infer new conjunct
     *)
      begin
        Printf.printf "%d. " iter; 
        print_exec cex; 
        flush_all ();
        cegar_loop (cex::cexs) (iter + 1);
      end in
  let cexs = try cegar_loop [] 1 with 
      | Return cexs -> cexs in 
  begin
    Printf.printf "Disposing...\n";
    Gc.full_major ();
    cexs
  end

let _ = 
  if not (Log.open_ "z3.log") then
    failwith "Log couldn't be opened."
  else
    let k = 100 in
    let cexss = Array.make (k+1) [] in 
    let ctrts = Array.make (k+1) "" in 
      begin
        for i = 1 to k do
          let cexs = mine_a_contract i cexss ctrts in
            cexss.(i) <- cexs;
          flush_all ();
        done;
        print_string "Successful! Contracts inferred:\n";
        Array.iteri 
          (fun i s -> if not (s="") then Printf.printf "%d. %s\n" i s) ctrts;
      end

