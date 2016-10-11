open Utils
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
module Constructor = Z3.Datatype.Constructor

type oper = NT | GT | NTTL | GTTL | NTUL | GTUL | NOP
type fn = ADD_NEW_TWEET | GET_USERLINE 
type exec = {opers: oper array; fns: fn array; sobjees: bool array array;
             soees: bool array array; visees: bool array array}
exception Return of exec list

(* Returns [f(i), f(i-1), ... , f(1)]*)
let rec list_init i f = if i <= 0 then [] else (f i)::(list_init (i-1) f)

let hd = List.hd

let oper_of_expr expr = match Expr.to_string expr with 
  | "NT" -> NT | "GT" -> GT | "NTTL" -> NTTL | "GTTL" -> GTTL 
  | "NTUL" -> NTUL | "GTUL" -> GTUL | "NOP" -> NOP
  | _ -> failwith "Unexpected Expr.expr"

let string_of_oper = function NT -> "NT" 
  | NT -> "NT" | GT -> "GT" | NTTL -> "NTTL" | GTTL -> "GTTL" 
  | NTUL -> "NTUL" | GTUL -> "GTUL" | NOP -> "NOP"

let fn_of_expr expr = match Expr.to_string expr with
  | "ADD_NEW_TWEET" -> ADD_NEW_TWEET
  | "GET_USERLINE" -> GET_USERLINE

let string_of_fn = function 
    ADD_NEW_TWEET -> "ADD_NEW_TWEET"
  | GET_USERLINE -> "GET_USERLINE"

let print_exec_hdr to_s opers fns soees visees =
  let n = Array.length opers in 
  begin
    for i=0 to n-1 do
      let s = (if i/3 = 0 then "ea" else "eb")^(string_of_int @@ i mod 3) in
      Printf.printf "%s, " s
    done;
    for i=0 to n-1 do
      for j=0 to n-1 do
        let l = (if i/3 = 0 then "ea" else "eb")^(string_of_int @@ i mod 3) in
        let r = (if j/3 = 0 then "ea" else "eb")^(string_of_int @@ j mod 3) in
        let sep = if i=n-1 && j=n-1 then "" else ", " in
          Printf.printf "(%s%s)%s" l r sep
      done
    done;
    Printf.printf "\n"
  end
 
let print_exec {opers; fns; sobjees; soees; visees} = 
  let n = Array.length opers in 
  begin
    for i=0 to n-1 do
      Printf.printf "%s, " (string_of_oper opers.(i))
    done;
    for i=0 to n-1 do
      for j=0 to n-1 do
        let value = if visees.(i).(j) then "1" else "0" in
        let sep = if i=n-1 && j=n-1 then "" else ", " in
          Printf.printf "%s%s" value sep
      done
    done;
    Printf.printf "\n"
  end

let mine_a_contract n_effs_S cexss ctrts = 
  let n_effs = n_effs_S + 5 in
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = (mk_context cfg) in
  let sym = Symbol.mk_string ctx in
  let cons_decl = Constructor.get_constructor_decl in
  let nullary_const cons = mk_app ctx (cons_decl cons) [] in
  let nary_const cons = mk_app ctx (cons_decl cons) in
  (* let s_true = mk_true ctx in *)
  let s_Int = Int.mk_sort ctx in
  let s_Bool = Bool.mk_sort ctx in
  let s_0 = Int.mk_numeral_i ctx 0 in
  (* (declare-sort Id) *)
  let s_Id = mk_uninterpreted_s ctx "Id" in
  (* (declare-const none_id) *)
  let s_none_id = Expr.mk_const_s ctx "none_id" s_Id in
  (* (declare-sort Stringe) *)
  let s_Stringe = mk_uninterpreted_s ctx "Stringe" in
  (* (declare-const none_stringe) *)
  let s_none_stringe = Expr.mk_const_s ctx "none_stringe" s_Stringe in
  (* (declare-datatypes () ((Fn ADD_NEW_TWEET GET_USERLINE))) *)
  let s_Fn = mk_sort_s ctx "Fn" @@ 
             [mk_constructor_s ctx "ADD_NEW_TWEET" (sym "isANT") [] [] [];
              mk_constructor_s ctx "GET_USERLINE" (sym "isGU") [] [] []] in
  let [s_ADD_NEW_TWEET; s_GET_USERLINE] = List.map (fun f -> mk_app ctx f []) 
                                            (Datatype.get_constructors s_Fn) in
  (* (declare-datatypes () ((Eff e1 e2 e3 e4 e5)))*)
  let mk_ith_e = (fun suf i -> let sufi = suf^(string_of_int i) in 
                     mk_constructor_s ctx ("e"^sufi) 
                       (sym @@ "isE"^sufi) [] [] []) in
  let [s_ea0; s_ea1; s_ea2] as eas = List.tabulate 3 (mk_ith_e "a") in
  let [s_eb0; s_eb1] as ebs = List.tabulate 2 (mk_ith_e "b") in
  let effs_S = List.tabulate n_effs_S (mk_ith_e "") in
  let effs = List.concat [effs_S; eas; ebs] in
  let s_Eff = mk_sort_s ctx "Eff" effs in
  (* (declare-datatypes () ((Oper (NT Id{-userid-} Stringe{-content-}) (GT) 
  *                               (NTTL Id{-tweetId-}) (GTTL) 
  *                               (NTUL Id{-tweetId-}) (GTUL) (NOP))))*)
  let s_NT = mk_constructor_s ctx "NT" (sym "isNT") [] [] [] in
  let s_GT = mk_constructor_s ctx "GT" (sym "isGT") [] [] [] in
  let s_NTTL = mk_constructor_s ctx "NTTL" (sym "isNTTL") [] [] [] in
  let s_GTTL = mk_constructor_s ctx "GTTL" (sym "isGTTL") [] [] [] in
  let s_NTUL = mk_constructor_s ctx "NTUL" (sym "isNTUL") [] [] [] in
  let s_GTUL = mk_constructor_s ctx "GTUL" (sym "isGTUL") [] [] [] in
  let s_NOP = mk_constructor_s ctx "NOP" (sym "isNOP") [] [] [] in
  let s_Oper = mk_sort_s ctx "Oper" [s_NT; s_GT; s_NTTL; s_GTTL; 
                                     s_NTUL; s_GTUL; s_NOP] in
  let [s_NT; s_GT; s_NTTL; s_GTTL; 
       s_NTUL; s_GTUL; s_NOP] = Datatype.get_constructors s_Oper in
  (*
   * Define accessors as stand-alone functions.
   *)
  let s_userId = mk_func_decl_s ctx "userId" [s_Eff] s_Id in
  let s_content = mk_func_decl_s ctx "content" [s_Eff] s_Stringe in
  let s_tweetIdB = mk_func_decl_s ctx "tweetId" [s_Eff] s_Id in
  (* let accessors = Datatype.get_accessors s_Oper in
  let _ = List.iteri (fun i xs -> 
                       List.iteri (fun j x -> Printf.printf "%d.%d %s\n" 
                                   i j (FuncDecl.to_string x)) xs) accessors in
  let _ = print_string "---------------------- \n" in
  let s_content = List.nth (List.nth accessors 0) 1 in
  let s_tweetIdB = List.nth (List.nth accessors 4) 0 in *)
  let recognizers = Datatype.get_recognizers s_Oper in
  (* let _ = List.iteri (fun i x -> Printf.printf "%d. %s\n"
                                i (FuncDecl.to_string x)) recognizers in *)
  let s_isNT = List.nth recognizers 0 in
  let s_isNTUL = List.nth recognizers 4 in
  (* let _ = print_string "---------------------- \n" in
  let _ = Printf.printf "%s\n" (FuncDecl.to_string s_content) in
  let _ = Printf.printf "%s\n" (FuncDecl.to_string s_isNT) in
  let _ = Printf.printf "%s\n" (FuncDecl.to_string s_tweetIdB) in
  let _ = Printf.printf "%s\n" (FuncDecl.to_string s_isNTUL) in *)
  (* ----- Sorts and Relations ---- *)
  (* (declare-fun objid (Eff) Id) *)
  let s_objid = mk_func_decl_s ctx "objid" [s_Eff] s_Id in
  (* (declare-fun fn (Eff) Fn) *)
  let s_fn = mk_func_decl_s ctx "fn" [s_Eff] s_Fn in
  (* (declare-const ADD_NEW_TWEET Fn)
  let s_ADD_NEW_TWEET = Expr.mk_const_s ctx "ADD_NEW_TWEET" s_Fn in
  (*(declare-const GET_USERLINE Fn) *)
  let s_GET_USERLINE = Expr.mk_const_s ctx "GET_USERLINE" s_Fn in *)
  (* (declare-fun oper (Eff) Oper) *)
  let s_oper = mk_func_decl_s ctx "oper" [s_Eff] s_Oper in
  (* (declare-fun rval (Eff) Int) *)
  let s_rval = mk_func_decl_s ctx "rval" [s_Eff] s_Int in
  (* (declare-fun vis (Eff Eff) Bool) *)
  let s_vis = mk_func_decl_s ctx "vis" [s_Eff; s_Eff] s_Bool in
  (* (declare-fun so (Eff Eff) Bool) *)
  let s_so = mk_func_decl_s ctx "so" [s_Eff; s_Eff] s_Bool in
  (* (declare-fun hb (Eff Eff) Bool) *)
  let s_hb = mk_func_decl_s ctx "hb" [s_Eff; s_Eff] s_Bool in
  (* (declare-fun sameobj (Eff Eff) Bool) *)
  let s_sameobj = mk_func_decl_s ctx "sameobj" [s_Eff; s_Eff] s_Bool in
  let expr_of_oper = function
    | NT -> mk_app ctx s_NT []
    | GT -> mk_app ctx s_GT []
    | NTTL -> mk_app ctx s_NTTL []
    | GTTL -> mk_app ctx s_GTTL []
    | NTUL -> mk_app ctx s_NTUL []
    | GTUL -> mk_app ctx s_GTUL []
    | NOP -> mk_app ctx s_NOP [] in
  let expr_of_fn = function
    | ADD_NEW_TWEET -> s_ADD_NEW_TWEET
    | GET_USERLINE -> s_GET_USERLINE in
  (*
   * Accumulator for assertions.
   *)
  let asns = ref [] in
  (*
   *  Encode (relevant part of) the given execution as a big conjunction.
   *)
  let encode_exec n_S ({opers=opers_mod; fns=fns_mod; sobjees=sobjees_mod;
                        soees=soees_mod; visees=visees_mod}:exec) 
                      opers fns sobjees soees visees = 
    let oper_eqs = Array.to_list @@ Array.map2
                     (fun opere op_tag -> 
                        mk_eq ctx opere @@ 
                                       expr_of_oper op_tag) 
                      opers opers_mod in
    let fn_eqs = Array.to_list @@ Array.map2
                     (fun fne fn_tag -> 
                        mk_eq ctx fne @@ 
                                       expr_of_fn fn_tag) 
                      fns fns_mod in
    let n = Array.length opers in
    let sobj_preds = ref [] in
    let _ =
      for i=0 to n-1  do
        for j=0 to n-1 do
          let sobj_pred = if i < j && sobjees_mod.(i).(j) 
                           then Some sobjees.(i).(j)
                           else None in
            match sobj_pred with 
              | None -> ()
              | Some sobj_pred -> sobj_preds := sobj_pred :: (!sobj_preds)
        done
      done in
    let vis_preds = ref [] in
    let _ =
      if n_S < n then ()
      else failwith "n_S < n invariant violated";
      for i=0 to n-1  do
        for j=0 to n-1 do
          let vis_pred = if visees_mod.(i).(j) 
                         then Some visees.(i).(j)
                         else if i!=j && not (i<n_S && j<n_S) 
                                  && not visees_mod.(j).(i)
                                  && sobjees_mod.(i).(j)
                         then Some (mk_not ctx visees.(i).(j)) 
                         else None in
            match vis_pred with 
              | None -> ()
              | Some vis_pred -> vis_preds := vis_pred :: (!vis_preds)
        done
      done in
    let so_preds = ref [] in
    let _ =
      for i=0 to n-1  do
        for j=0 to n-1 do
          let so_pred = if soees_mod.(i).(j) 
                         then Some soees.(i).(j)
                         else None in
            match so_pred with 
              | None -> ()
              | Some so_pred -> so_preds := so_pred :: (!so_preds)
        done
      done in
    let conj = mk_and ctx @@ oper_eqs @ fn_eqs @ List.rev !sobj_preds
                                @ List.rev !so_preds @ List.rev !vis_preds in
    (* let _ = Printf.printf "Conjunction:\n %s \n" @@ Expr.to_string conj in *)
      conj in

  (*
   * Given a list of counterexamples, all having same number of effects, return
   * a contract that negates these counterexamples.
   *)
  let get_ctrt n_S cexs = 
    let n = n_S + 5 in
    let typs = List.tabulate n (fun _ -> s_Eff) in
    let names = List.tabulate n (fun i -> sym @@ "n_"^(string_of_int i)) in
    let vars = List.rev @@ List.tabulate n (fun i -> mk_bound ctx i s_Eff) in 
    let opers = Array.of_list @@ List.map (fun c -> 
                              mk_app ctx s_oper [c]) vars in
    let fns = Array.of_list @@ List.map (fun c -> 
                              mk_app ctx s_fn [c]) vars in
    let sobjees = Array.mapi 
                   (fun i row -> Array.mapi
                        (fun j x -> mk_app ctx s_sameobj 
                                      [List.nth vars i; 
                                       List.nth vars j]) row) 
                   (Array.make n @@ Array.make n 0) in
    let soees = Array.mapi 
                   (fun i row -> Array.mapi
                        (fun j x -> mk_app ctx s_so 
                                      [List.nth vars i; 
                                       List.nth vars j]) row) 
                   (Array.make n @@ Array.make n 0) in
    let visees = Array.mapi 
                   (fun i row -> Array.mapi
                        (fun j x -> mk_app ctx s_vis 
                                      [List.nth vars i; 
                                       List.nth vars j]) row) 
                   (Array.make n @@ Array.make n 0) in
    let conjs = List.map 
                  (fun cex -> mk_not ctx @@ 
                               encode_exec n_S cex opers fns sobjees 
                                 soees visees) cexs in
    let body = mk_and ctx conjs in
    let ctrt = mk_forall ctx typs names body None [] [] None None in
    (* let _ = Printf.printf "Quantifier ctrt: %s\n" 
              (Quantifier.to_string ctrt) in *)
      expr_of_quantifier ctrt in

  (* (declare-fun in_S (Eff) Bool)*)
  let s_in_S = mk_func_decl_s ctx "in_S" [s_Eff] s_Bool in
  (* (assert (forall ((x Eff)) (<=> (not (in_S x)) 
   *           (or (= x s_a1) .. (= x s_eb1) ..)))) *)
  let typs = [s_Eff] in
  let names = [sym "x"] in
  let var_x = mk_bound ctx 0 s_Eff in
  let vars = [var_x] in
  let eqs = List.map (fun e -> mk_eq ctx var_x (nullary_const e))
            @@ List.append eas ebs in
  let body = mk_iff ctx 
               (mk_not ctx @@ mk_app ctx s_in_S vars)
               (mk_or ctx eqs) in
  let asn0 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn0)::(!asns) in

(*
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
*)

  (* so is transitive *)
  (* (assert (forall ((a Eff) (b Eff) (c Eff)) 
   *     (=> (and (so a b) (so b c)) (so a c))))*)
  let typs = [s_Eff; s_Eff; s_Eff] in
  let names = [sym "a"; sym "b"; sym "c"] in
  let [var_a; var_b; var_c] as vars = [mk_bound ctx 2 s_Eff; 
                                       mk_bound ctx 1 s_Eff;
                                       mk_bound ctx 0 s_Eff] in 
  let soab = mk_app ctx s_so [var_a; var_b] in
  let sobc = mk_app ctx s_so [var_b; var_c] in
  let soac = mk_app ctx s_so [var_a; var_c] in
  let body = mk_implies ctx 
               (mk_and ctx [soab; sobc]) soac in
  let asn2 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn2)::(!asns) in
  (* hb is (vis U so)+ *)
  (* (assert (forall ((a Eff) (b Eff)) 
   *      (=> (or (vis a b) (so ab)) (hb a b)))) *)
  let typs = [s_Eff; s_Eff] in
  let names = [sym "a"; sym "b"] in
  let vars = [mk_bound ctx 1 s_Eff; mk_bound ctx 0 s_Eff] in 
  let visab = mk_app ctx s_vis vars in
  let soab = mk_app ctx s_so vars in
  let hbab = mk_app ctx s_hb vars in
  let body = mk_implies ctx (mk_or ctx [visab; soab]) hbab in
  let asn3 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn3)::(!asns) in
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
  let asn4 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn4)::(!asns) in
  (* let _ = Printf.printf "Quantifier asn2b: %s\n" 
            (Quantifier.to_string asn2b) in *)
  (* (assert (forall ((e Eff)) (not (hb e e)))) *)
  let typs = [s_Eff] in
  let names = [sym "e"] in
  let vars = [mk_bound ctx 0 s_Eff] in 
  let body = mk_not ctx @@ mk_app ctx s_hb [hd vars; hd vars] in
  let asn5 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn5)::(!asns) in
  (* (assert (forall ((a Eff)(b Eff)) 
   *      (<=> (sameobj a b) (= (objid a) (objid b))))) *)
  let typs = [s_Eff; s_Eff] in
  let names = [sym "a"; sym "b"] in
  let [var_a; var_b] as vars = [mk_bound ctx 1 s_Eff; 
                                mk_bound ctx 0 s_Eff] in 
  let sameobjab = mk_app ctx s_sameobj vars in
  let objida = mk_app ctx s_objid[var_a] in
  let objidb = mk_app ctx s_objid [var_b] in
  let body = mk_iff ctx sameobjab @@ mk_eq ctx objida objidb in
  let asn6 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn6)::(!asns) in
  (* (assert (forall ((a Eff)(b Eff)) 
          (=> (vis a b) (sameobj a b))))*)
  let typs = [s_Eff; s_Eff] in
  let names = [sym "a"; sym "b"] in
  let [var_a; var_b] as vars = [mk_bound ctx 1 s_Eff; 
                                mk_bound ctx 0 s_Eff] in 
  let visab = mk_app ctx s_vis vars in
  let sameobjab = mk_app ctx s_sameobj vars in
  let body = mk_implies ctx visab sameobjab in
  let asn7 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn7)::(!asns) in
  (* let _ = Printf.printf "Quantifier asn2c: %s\n" 
            (Quantifier.to_string asn2c) in *)
  (*
   * Proscribe invalid sameobj relations. This can be generalized by 
   * ascribing types for Ids.
   *)
  let [n_ea0; n_ea1; n_ea2] as n_eas = List.map nullary_const 
                                         [s_ea0; s_ea1; s_ea2] in 
  let [n_eb0; n_eb1] = List.map nullary_const [s_eb0; s_eb1] in
  let invalid_sameobjs = List.map (fun (x,y) -> mk_app ctx s_sameobj [x; y])
                           [(n_ea0,n_eb0); (n_ea1,n_eb1); 
                            (n_ea2,n_eb0); (n_ea2,n_eb1)] in
  let asn7a = mk_not ctx @@ mk_or ctx invalid_sameobjs in
  let _ = asns := (asn7a)::(!asns) in
  (* (assert (forall ((x Eff)(y Eff)) 
   *      (=> (in_S y) (not (or (vis x y) (so x y)))))) *)
  let typs = [s_Eff; s_Eff] in
  let names = [sym "x"; sym "y"] in
  let [var_x; var_y] as vars = [mk_bound ctx 1 s_Eff; 
                                mk_bound ctx 0 s_Eff] in 
  let body = mk_implies ctx 
               (mk_app ctx s_in_S [var_y])
               (mk_not ctx @@ 
                  mk_or ctx [mk_app ctx s_vis vars; mk_app ctx s_so vars]) in
  let asn8 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn8)::(!asns) in
  (* We define a new type called State *)
  let s_State = mk_uninterpreted_s ctx "State" in
  (* State S0 is the common state present on all replicas *)
  let s_S0 = Expr.mk_const_s ctx "S0" s_State in 
  (* State S is the state before the execution of the withdraw operation *)
  let s_S = Expr.mk_const_s ctx "S" s_State in 
  (* State S1 is the state after the execution of the withdraw operation *)
  let s_S1 = Expr.mk_const_s ctx "S1" s_State in 
  (* (declare-fun getTweet (State Eff{-witness-} Id{-TweetId-}) Stringe)*)
  let s_getTweet = mk_func_decl_s ctx "getTweet" [s_State; s_Eff; s_Id] s_Stringe in
  (* Since S0 is the common prefix, 
      (assert (forall ((n1 Eff)(n2 Eff)(t Id)) 
          (= (getTweet S0 n1 t) (getTweet S0 n2 t)))) *)
  let typs = [s_Eff; s_Eff; s_Id] in
  let names = [sym "n1"; sym "n2"; sym "t"] in
  let [var_n1; var_n2; var_t] as vars = [mk_bound ctx 2 s_Eff;
                                         mk_bound ctx 1 s_Eff; 
                                         mk_bound ctx 0 s_Id] in 
  let body = mk_eq ctx (mk_app ctx s_getTweet @@ [s_S0; var_n1; var_t])
                       (mk_app ctx s_getTweet @@ [s_S0; var_n2; var_t]) in
  let asn8a = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn8a)::(!asns) in
  (* Define getTweet in pre-state (S) *)
  (* (assert (forall ((a Eff)(b Id)) 
   *    (ite (and (vis e1 a) (isNT (oper e1) (= (objid e1) b))) 
   *      (= (getTweet S a b) content (oper e1))
   *      (ite ...
   *        ...
   *         (= (getTweet S a b) (getTweet S0 a b)) ..)))) *)
  let typs = [s_Eff; s_Id] in
  let names = [sym "a"; sym "b"] in
  let [var_a; var_b] as vars = [mk_bound ctx 1 s_Eff; 
                                mk_bound ctx 0 s_Id] in 
  let grde e = mk_and ctx [mk_app ctx s_vis [e; var_a]; 
                           mk_app ctx s_isNT [mk_app ctx s_oper [e]];
                           mk_eq ctx (mk_app ctx s_objid [e]) var_b] in
  let thene e = mk_eq ctx (mk_app ctx s_getTweet @@ s_S::vars) 
                          (mk_app ctx s_content [e]) in
  let body = List.fold_right 
               (fun c elsee -> let e = nullary_const c in 
                  mk_ite ctx (grde e) (thene e) elsee) 
               effs_S 
               (mk_eq ctx (mk_app ctx s_getTweet @@ s_S::vars)
                          (mk_app ctx s_getTweet @@ s_S0::vars)) in
  let asn9 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn9)::(!asns) in
  (* (declare-fun getTweetsInUL (State Eff{-witness-} Id{-UserId-}) 
   *                                 Id{-TweetId-}}) Bool *)
  let s_getTweetsInUL = mk_func_decl_s ctx "getTweetsInUL" 
                          [s_State; s_Eff; s_Id; s_Id] s_Bool in
  (* Since S0 is the common prefix, 
      (assert (forall ((n1 Eff)(n2 Eff)(uid Id)(tid Id)) 
          (= (getTweetsInUL S0 n1 uid tid) (getTweetsInUL S0 n2 uid tid)))) *)
  let typs = [s_Eff; s_Eff; s_Id; s_Id] in
  let names = [sym "n1"; sym "n2"; sym "u"; sym "t"] in
  let [var_n1; var_n2; var_u; var_t] as vars = [mk_bound ctx 3 s_Eff;
                                                mk_bound ctx 2 s_Eff; 
                                                mk_bound ctx 1 s_Id;
                                                mk_bound ctx 0 s_Id] in 
  let body = mk_eq ctx (mk_app ctx s_getTweetsInUL @@ 
                                [s_S0; var_n1; var_u; var_t])
                       (mk_app ctx s_getTweetsInUL @@ 
                                [s_S0; var_n2; var_u; var_t]) in
  let asn9a = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn9a)::(!asns) in
  (* Define getTweetsInUL in pre-state (S) *)
  (* (assert (forall ((e Eff)(u Id)(t Id)) 
   *    (= (getTweetsInUL S e u t)
           (or (and (vis e1 e) (is-NTUL (oper e1)) 
                    (= (objid e1) u) (= (tweetIdB (oper e1)) t))
               (and ... )
               (getTweetsInUL S0 e u t))))) *)
  let typs = [s_Eff; s_Id; s_Id] in
  let names = [sym "e"; sym "u"; sym "t"] in
  let [var_e; var_u; var_t] as vars = [mk_bound ctx 2 s_Eff;
                                       mk_bound ctx 1 s_Id; 
                                       mk_bound ctx 0 s_Id] in 
  let conj ei = mk_and ctx [mk_app ctx s_vis [ei; var_e]; 
                            mk_app ctx s_isNTUL [mk_app ctx s_oper [ei]];
                            mk_eq ctx (mk_app ctx s_objid [ei]) var_u;
                            mk_eq ctx (mk_app ctx s_tweetIdB [ei]) var_t] in
  let conjs = List.map (conj << nullary_const) effs_S in 
  let lhs = mk_app ctx s_getTweetsInUL @@ s_S::vars in
  let rhs = mk_or ctx @@ 
            conjs@[mk_app ctx s_getTweetsInUL @@ s_S0::vars] in
  let body = mk_eq ctx lhs rhs in
  let asn10 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn10)::(!asns) in
  (* eb0 and eb1 are GTUL and GT witness effects *)
  (*(assert (= (oper eb0) GTUL)) *)
  (*(assert (= (oper eb1) GT)) *) 
  let asn10a = mk_eq ctx (mk_app ctx s_oper [n_eb0]) 
                         (mk_app ctx s_GTUL []) in
  let asn10b = mk_eq ctx (mk_app ctx s_oper [n_eb1]) 
                         (mk_app ctx s_GT []) in
  (*; They are in so *)
  (*(assert (so eb0 eb1)) *)
  let asn10c = mk_app ctx s_so [n_eb0; n_eb1] in
  (*; Their function is GET_USERLINE *)
  (*(assert (= (fn eb0) GET_USERLINE)) *)
  let asn10d = mk_eq ctx (mk_app ctx s_fn [n_eb0]) s_GET_USERLINE in
  (*(assert (= (fn eb1) GET_USERLINE)) *)
  let asn10e = mk_eq ctx (mk_app ctx s_fn [n_eb1]) s_GET_USERLINE in
  (* Invariant is valid in the pre-state (S) w.r.t witness effects *)
  (* (assert (forall ((u Id)(t Id)) 
        (=> (getTweetsInUL S eb0 u t)
            (not (= (getTweet S eb1 t) none_stringe))))) *)
  let _ = asns := asn10a::asn10b::asn10c::asn10d::asn10e::(!asns) in
  let inv st = 
    let typs = [s_Id; s_Id] in
    let names = [sym "u"; sym "t"] in
    let [var_u; var_t] as vars = [mk_bound ctx 1 s_Id; 
                                  mk_bound ctx 0 s_Id] in 
    let ante = mk_and ctx [mk_eq ctx (mk_app ctx s_objid [n_eb0]) var_u;
                           mk_app ctx s_getTweetsInUL @@ st::n_eb0::vars;
                           mk_eq ctx (mk_app ctx s_objid [n_eb1]) var_t] in
    let conseq = mk_not ctx @@ 
                    mk_eq ctx (mk_app ctx s_getTweet [st; n_eb1; var_t])
                              s_none_stringe in
    let body = mk_implies ctx ante conseq in
      mk_forall ctx typs names body None [] [] None None in
  let asn10f = inv s_S in
  let _ = asns := (expr_of_quantifier asn10f)::(!asns) in
  (* Execute newTweet Fn *)
  (* (declare-const uid0 Id) *)
  let s_uid0 = Expr.mk_const_s ctx "uid0" s_Id in
  (* Define a string that is not none_stringe *)
  (* (declare-const stringe0 Stringe) 
     (assert (not (= stringe0 none_stringe))) *)
  let s_stringe0 = Expr.mk_const_s ctx "stringe0" s_Stringe in
  let asn11 = mk_not ctx @@ mk_eq ctx s_stringe0 s_none_stringe in
  let _ = asns := (asn11)::(!asns) in
  (* (declare-const tid0 Id) *)
  let s_tid0 = Expr.mk_const_s ctx "tid0" s_Id in
  (* (assert (not (= tid0 uid0))) *)
  let asn11a = mk_not ctx @@ mk_eq ctx s_tid0 s_uid0 in
  (* (assert (= (oper ea0) NT))
     (assert (= (userId ea0) uid0))
     (assert (= (content ea0) stringe0))
     (assert (= (objid ea0) tid0))
     (assert (= (fn ea0) ADD_NEW_TWEET)) *)
  let asn12 = mk_eq ctx (mk_app ctx s_oper [n_ea0])
                        (mk_app ctx s_NT []) in 
  let asn12a = mk_eq ctx (mk_app ctx s_userId [n_ea0]) s_uid0 in
  let asn12b = mk_eq ctx (mk_app ctx s_content [n_ea0]) s_stringe0 in
  let asn13 = mk_eq ctx (mk_app ctx s_objid [nullary_const s_ea0]) s_tid0 in
  let asn14 = mk_eq ctx (mk_app ctx s_fn [nullary_const s_ea0]) 
                s_ADD_NEW_TWEET in
  (* (declare-const ulid0 Id) *)
  let s_ulid0 = Expr.mk_const_s ctx "ulid0" s_Id in
  (* (assert (not (or (= ulid0 uid0) (= ulid0 tid0)))) *)
  let asn14a = mk_not ctx @@ mk_or ctx [mk_eq ctx s_ulid0 s_uid0;
                                        mk_eq ctx s_ulid0 s_tid0] in
  (* (assert (= (oper ea1) NTUL))
     (assert (= (tweetIdB ea1) tid0))
     (assert (= (objid ea1) ulid0))
     (assert (= (fn ea1) ADD_NEW_TWEET)) *)
  let asn15 = mk_eq ctx (mk_app ctx s_oper [n_ea1])
                        (mk_app ctx s_NTUL []) in 
  let asn15a = mk_eq ctx (mk_app ctx s_tweetIdB [n_ea1]) s_tid0 in 
  let asn16 = mk_eq ctx (mk_app ctx s_objid [nullary_const s_ea1]) s_ulid0 in
  let asn17 = mk_eq ctx (mk_app ctx s_fn [nullary_const s_ea1]) 
                s_ADD_NEW_TWEET in
  (*(declare-const tlid0 Id) *)
  let s_tlid0 = Expr.mk_const_s ctx "tlid0" s_Id in
  (* (assert (not (or (=tlid0 ulid0) (= tlid0 uid0) (= tlid0 tid0)))) *)
  let asn17a = mk_not ctx @@ mk_or ctx [mk_eq ctx s_tlid0 s_ulid0;
                                        mk_eq ctx s_tlid0 s_uid0;
                                        mk_eq ctx s_tlid0 s_tid0] in
  (* (assert (= (oper ea2) NTTL))
     (assert (= (tweetIdB ea2) tid0))
     (assert (= (objid ea2) tlid0))
     (assert (= (fn ea2) ADD_NEW_TWEET)) *)
  let asn18 = mk_eq ctx (mk_app ctx s_oper [n_ea2])
                        (mk_app ctx s_NTTL []) in 
  let asn18a = mk_eq ctx (mk_app ctx s_tweetIdB [n_ea2]) s_tid0 in
  let asn19 = mk_eq ctx (mk_app ctx s_objid [nullary_const s_ea2]) s_tlid0 in
  let asn20 = mk_eq ctx (mk_app ctx s_fn [nullary_const s_ea2]) 
                s_ADD_NEW_TWEET in
  (* (assert (and (so ea0 ea1) (so ea1 ea2))) *)
  let asn21 = mk_and ctx [mk_app ctx s_so [n_ea0; n_ea1];
                          mk_app ctx s_so [n_ea1; n_ea2]] in
  let _ = asns := asn11a::asn12::asn12a::asn12b::asn13::asn14::
                  asn14a::asn15::asn15a::asn16::asn17::asn17a::
                  asn18::asn18a:: asn19::asn20::asn21::(!asns) in
    (* S1 is S U {ea0,ea1,ea2}.
       Define getTweet under S1. *)
  let typs = [s_Eff; s_Id] in
  let names = [sym "a"; sym "b"] in
  let [var_a; var_b] as vars = [mk_bound ctx 1 s_Eff; 
                                mk_bound ctx 0 s_Id] in 
  let grde e = mk_and ctx [mk_app ctx s_vis [e; var_a]; 
                           mk_app ctx s_isNT [mk_app ctx s_oper [e]];
                           mk_eq ctx (mk_app ctx s_objid [e]) var_b] in
  let thene e = mk_eq ctx (mk_app ctx s_getTweet @@ s_S1::vars) 
                          (mk_app ctx s_content [e]) in
  let body = List.fold_right 
               (fun e elsee -> mk_ite ctx (grde e) (thene e) elsee) 
               n_eas
               (mk_eq ctx (mk_app ctx s_getTweet @@ s_S1::vars)
                          (mk_app ctx s_getTweet @@ s_S::vars)) in
  let asn22 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn22)::(!asns) in
  (* Define getTweetsInUL under S1 *)
  let typs = [s_Eff; s_Id; s_Id] in
  let names = [sym "e"; sym "u"; sym "t"] in
  let [var_e; var_u; var_t] as vars = [mk_bound ctx 2 s_Eff;
                                       mk_bound ctx 1 s_Id; 
                                       mk_bound ctx 0 s_Id] in 
  let conj ei = mk_and ctx [mk_app ctx s_vis [ei; var_e]; 
                            mk_app ctx s_isNTUL [mk_app ctx s_oper [ei]];
                            mk_eq ctx (mk_app ctx s_objid [ei]) var_u;
                            mk_eq ctx (mk_app ctx s_tweetIdB [ei]) var_t] in
  let conjs = List.map conj n_eas in 
  let lhs = mk_app ctx s_getTweetsInUL @@ s_S1::vars in
  let rhs = mk_or ctx @@ 
            conjs@[mk_app ctx s_getTweetsInUL @@ s_S::vars] in
  let body = mk_eq ctx lhs rhs in
  let asn23 = mk_forall ctx typs names body None [] [] None None in
  let _ = asns := (expr_of_quantifier asn23)::(!asns) in
  (* (assert (not inv)) *)
  let asn24 = mk_not ctx (expr_of_quantifier @@ inv s_S1) in
  let _ = asns := (asn24)::(!asns) in
  (* 
   * Create opt_solver and  assert all the constraints generated from symbolic
   * execution.
   *)
  let opt_solver = mk_opt ctx in
  let _ = OptSolver.add opt_solver @@ List.rev !asns in
  (*let _ = 
    begin
      Printf.printf "*****  CONTEXT ******\n";
      print_string @@ OptSolver.to_string opt_solver;
      Printf.printf "\n*********************\n"
    end in
  let model = match OptSolver.check opt_solver with
    | SATISFIABLE -> fromJust (OptSolver.get_model opt_solver)
    | UNSATISFIABLE -> (failwith "UNSAT\n")
    | UNKNOWN -> (failwith "UNKNOWN\n") in
  let _ = Printf.printf "Model: \n%s\n" (Model.to_string model) in *)
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
  let (soees : Expr.expr array array) = Array.mapi 
                 (fun i row -> Array.mapi
                      (fun j x -> mk_app ctx s_so
                                    [List.nth e_consts i; 
                                     List.nth e_consts j]) row) 
                 (Array.make n_effs @@ Array.make n_effs 0) in
  let (sobjees : Expr.expr array array) = Array.mapi 
                 (fun i row -> Array.mapi
                      (fun j x -> mk_app ctx s_sameobj
                                    [List.nth e_consts i; 
                                     List.nth e_consts j]) row) 
                 (Array.make n_effs @@ Array.make n_effs 0) in
  let opers = Array.of_list @@ List.map (fun c -> 
                            mk_app ctx s_oper [c]) e_consts in
  let fns = Array.of_list @@ List.map (fun c -> 
                            mk_app ctx s_fn [c]) e_consts in
  (*
   * Main CEGAR loop.
   *)
  let rec cegar_loop (cexs : exec list) iter = 
    let _ = if iter > 10 then raise (Return cexs) else () in
    (* Assert the last conjunct inferred *)
    let _ = match cexs with
      | [] -> () 
      | cex::_ -> OptSolver.add opt_solver 
                    [mk_not ctx @@ 
                     encode_exec n_effs_S cex opers fns sobjees 
                       soees visees] in
    (*
     * PUSH.
     *)
    let _ = OptSolver.push opt_solver in 
    (* (assert (not inv))
    let neg_inv_asn = mk_not ctx s_inv in
    let _ = OptSolver.add opt_solver [neg_inv_asn] in *)
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
    let fns_mod = Array.map 
                      (fun fne -> fn_of_expr @@ fromJust @@ 
                                    Model.eval model fne true)
                      fns in
    let visees_mod = Array.map 
                       (fun row -> Array.map 
                          (fun visee -> is_true @@ fromJust @@
                               Model.eval model visee true) row) 
                       visees in
    let sobjees_mod = Array.map 
                       (fun row -> Array.map 
                          (fun sobjee -> is_true @@ fromJust @@
                               Model.eval model sobjee true) row) 
                       sobjees in
    let soees_mod = Array.map 
                       (fun row -> Array.map 
                          (fun soee -> is_true @@ fromJust @@
                               Model.eval model soee true) row) 
                       soees in
    let cex = {opers=opers_mod; fns=fns_mod; sobjees=sobjees_mod; 
               soees=soees_mod; visees=visees_mod} in 
    (* 
     * Infer new conjunct
     *)
      begin
        if iter = 1 then print_exec_hdr Expr.to_string 
                           opers fns soees visees ;
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
    (* mine_a_contract 1 (Array.make 1 []) (Array.make 1 []) *)
    let k = 10 in
    let cexss = Array.make (k+1) [] in 
    let ctrts = Array.make (k+1) "" in 
      begin
        for i = 0 to k do
          let cexs = mine_a_contract i cexss ctrts in
            cexss.(i) <- cexs;
          flush_all ();
        done;
        print_string "Successful! Contracts inferred:\n";
        Array.iteri 
          (fun i s -> if not (s="") then Printf.printf "%d. %s\n" i s) ctrts;
      end

