(*
  Algorithm W with support for exception handling
*)

datatype prim = Add | Neg | Mult | Div | And | Or | Not | Eq | Lt | Gt

fun prim_to_str Prim(Add) = "add"
  | prim_to_str Prim(Neg) = "neg"
  | prim_to_str Prim(Mult) = "mult"
  | prim_to_str Prim(Div) = "div"
  | prim_to_str Prim(And) = "and"
  | prim_to_str Prim(Or) = "or"
  | prim_to_str Prim(Not) = "not"
  | prim_to_str Prim(Eq) = "eq"
  | prim_to_str Prim(Lt) = "lt"
  | prim_to_str Prim(Gt) = "gt"

datatype milner = Var of string
  | Abs of string * milner
  | App of milner * milner
  | If of milner * milner * milner
  | Let of string * milner * milner
  | Fix of string * milner
  | Int of int
  | Bool of bool
  | Prim of prim
  | Letex of string * milner
  | Raise of milner
  | Handle of milner * milner * milner

datatype mtype = TInt | TBool
  | TVar of string
  | Arrow of mtype * mtype
  | TException

val counter = ref 0
fun newtype() =
  "Z" ^ Int.toString(!counter before counter := !counter + 1)

fun pptype (Arrow(x, y)) = "(" ^ pptype x ^ " -> " ^ pptype y ^ ")"
  | pptype (TVar x) = "'" ^ x
  | pptype TInt = "int"
  | pptype TBool = "bool"
  | pptype TException = "exception"

type scheme = (string list * mtype)
type env = (string * scheme) list

val initenv = [
    ("add", ([], Arrow(TInt, Arrow(TInt, TInt)))),
    ("neg", ([], Arrow(TInt, TInt))),
    ("mult", ([], Arrow(TInt, Arrow(TInt, TInt)))),
    ("div", ([], Arrow(TInt, Arrow(TInt, TInt)))),
    ("and", ([], Arrow(TBool, Arrow(TBool, TBool)))),
    ("or", ([], Arrow(TBool, Arrow(TBool, TBool)))),
    ("not", ([], Arrow(TBool, TBool))),
    ("eq", ([], Arrow(TInt, Arrow(TInt, TBool)))),
    ("lt", ([], Arrow(TInt, Arrow(TInt, TBool)))),
    ("gt", ([], Arrow(TInt, Arrow(TInt, TBool)))),
    ("raise", ([], Arrow(TException, TVar("raise"))))
]
val emptyenv = []:env

(* helpers *)
fun ppquan [] = ""
  | ppquan (s::rest) = "FA(" ^ s ^")." ^ ppquan rest

fun ppenv [] = ""
  | ppenv ((x, (q, e))::rest) = "" ^ x ^ ": " ^ (ppquan q) ^ (pptype e) ^ "\n" ^ (ppenv rest)

fun ppexpr (Var x) = "Var " ^ x
  | ppexpr (Abs(x, e)) = "Abs(" ^ x ^ ", " ^ (ppexpr e) ^ ")"
  | ppexpr (App(e1, e2)) = "App(" ^ (ppexpr e1) ^ ", " ^ (ppexpr e2) ^ ")"
  | ppexpr (If(e1, e2, e3)) = "If(" ^ (ppexpr e1) ^ ", " ^ (ppexpr e2) ^ ", " ^ (ppexpr e3) ^ ")"
  | ppexpr (Let(x, e1, e2)) = "Let(" ^ x ^ ", " ^ (ppexpr e1) ^ ", " ^ (ppexpr e2) ^ ")"
  | ppexpr (Fix(x, e)) = "Fix(" ^ x ^ ", " ^ (ppexpr e) ^ ")"
  | ppexpr (Int(x)) = "Int(" ^ Int.toString(x) ^ ")"
  | ppexpr (Bool(x)) = "Bool(" ^ (if x then "true" else "false") ^ ")"
  | ppexpr (Prim(x)) = "Prim(" ^ (prim_to_str Prim(x)) ^ ")"
  | ppexpr (Letex(x, y)) = "Letex(" ^ x ^ ", " ^ (ppexpr y) ^ ")"
  | ppexpr (Raise(x)) = "Raise(" ^ (ppexpr x) ^ ")"
  | ppexpr (Handle(x, y, z)) = "Handle(" ^ (ppexpr x) ^ ", " ^ (ppexpr y) ^ ", " ^ (ppexpr z) ^ ")"

fun is_in_list (a : string) [] = false
  | is_in_list (a : string) (s::rest) = if (a = s) then true else is_in_list a rest

fun rm_from_list (a : string) [] = []
  | rm_from_list (a : string) (s::rest) = (if s = a then [] else [a]) @ (rm_from_list a rest)

fun remove_duplicates_from_list l =
  let
      fun iter [] f = f
        | iter (s::rest) f = if is_in_list s f then (iter rest f) else (iter rest (f @ [s]))
  in
    iter l []
  end

(* subtitutions *)
fun sub (Arrow(t1, t2)) s = (Arrow(sub t1 s, sub t2 s))
  | sub (TVar t) (tau, (TVar alpha)) = if t = alpha then tau else (TVar t)
  | sub term _ = term

fun subs term [] = term
  | subs term (s::rest) = subs (sub term s) rest

fun env_sub (e:env) nil = e
  | env_sub nil _ = nil
  | env_sub ((x, (q, t))::rest) s = ((x, (q, (subs t s)))::(env_sub rest s))

(* occurs check *)
fun occurs_check (a as TVar _) t = (a = t)
  | occurs_check (Arrow(x, y)) t = (occurs_check x t) orelse (occurs_check y t)
  | occurs_check _ _ = false

(* unification *)
exception Unify
fun unify (Arrow(t1, t2)) (Arrow(t3, t4)) =
    let
      val s1 = unify t1 t3
      val s2 = unify (subs t2 s1) (subs t4 s1)
    in
      s1 @ s2
    end
  | unify (TVar a) t = if occurs_check t (TVar a) then raise Unify else [(t, (TVar a))]
  | unify t (TVar a) = if occurs_check t (TVar a) then raise Unify else [(t, (TVar a))]
  | unify t (Arrow(_)) = raise Unify
  | unify (Arrow(_)) t = raise Unify
  | unify t1 t2 = if t1 = t2 then [] else raise Unify

(* quantification *)
fun mark (t : mtype) (A : env) =
  let
    fun free_vars_of_expr (TVar a) q = if is_in_list a q then [] else [a]
      | free_vars_of_expr (Arrow(x, y)) q = (free_vars_of_expr x q) @ (free_vars_of_expr y q)
      | free_vars_of_expr _ _ = []

    fun free_vars_of_env [] = []
      | free_vars_of_env ((x, (q, t))::rest) = (free_vars_of_expr t q) @ (free_vars_of_env rest)

    fun get_vars_to_mark (TVar a) free_vars = if is_in_list a free_vars then [] else [a]
      | get_vars_to_mark (Arrow(x, y)) free_vars = (get_vars_to_mark x free_vars) @ (get_vars_to_mark y free_vars)
      | get_vars_to_mark _ _ = []

    val A_free = free_vars_of_env A
    val q = remove_duplicates_from_list(get_vars_to_mark t A_free)
  in
    (q, t)
  end

fun unmark t q =
  let
    fun get_new_name a [] = ""
      | get_new_name a ((old : string, new : string)::rest) = if (a = old) then new else get_new_name a rest

    fun unmark_inner (TVar a) list =
        let
          val new_name = get_new_name a list
        in
          if new_name = "" then (TVar a) else (TVar new_name)
        end
      | unmark_inner (Arrow(x, y)) list = Arrow(unmark_inner x list, unmark_inner y list)
      | unmark_inner a _ = a

    val new_names = (map (fn x => (x, newtype())) q)
  in
    unmark_inner t new_names
  end

(* lookup *)
exception Lookup
fun lookup (nil : env) _ = raise Lookup
  | lookup ((s, (q, t))::rest) x = if x = s then unmark t q else lookup rest x

(* algorithm W *)
fun W (Var x) A = ([], (lookup A x))
  | W (Abs(x, e)) A =
    let
      val alpha = TVar(newtype())
      val (s, t) = W e ((x, ([], alpha))::A)
    in
      (s, Arrow(subs alpha s, t))
    end
  | W (App(e1, e2)) A =
    let
      val alpha = TVar(newtype())
      val (s1, t1) = W e1 A
      val (s2, t2) = W e2 (env_sub A s1)
      val s3 = unify (subs t1 s2) (Arrow(t2, alpha))
    in
      (s1 @ s2 @ s3, (subs alpha s3))
    end
  | W (If(e1, e2, e3)) A =
    let
      val (s1, t1) = W e1 A
      val s2 = unify t1 TBool
      val (s3, t3) = W e2 (env_sub A (s1 @ s2))
      val (s4, t4) = W e3 (env_sub A (s1 @ s2 @ s3))
      val s5 = unify (subs t3 s4) t4
    in
      (s1 @ s2 @ s3 @ s4 @ s5, (subs t4 s5))
    end
  | W (Fix(x, e)) A =
    let
      val alpha = TVar(newtype())
      val (s1, t1) = W e ((x, ([], alpha))::A)
      val s2 = unify (subs alpha s1) t1
    in
      (s1 @ s2, (subs t1 s2))
    end
  | W (Let(x, e1, e2)) A =
    let
      val (s1, t1) = W e1 A
      val s1_env = env_sub A s1
      val (s2, t2) = W e2 ((x, (mark t1 s1_env))::s1_env)
    in
      (s1 @ s2, t2)
    end
  | W (Int(_)) A = ([], TInt)
  | W (Bool(_)) A = ([], TBool)
  | W (Prim(x)) A = W (Var(prim_to_str Prim(x))) A
  | W (Letex(x, y)) A = W y ((x, ([], TException))::A) (* PART E *)
  | W (Raise(x)) A = W (App(Var "raise", x)) A (* PART E *)
  | W (Handle(e1, e2, e3)) A = (* PART E *)
    let
      val (s1, t1) = W e1 A
      val s2 = unify TException  t1
      val (s3, t3) = W e2 (env_sub A (s1 @ s2))
      val (s4, t4) = W e3 (env_sub A (s1 @ s2 @ s3))
      val s5 = unify (subs t3 s4) t4
    in
      (s1 @ s2 @ s3 @ s4 @ s5, (subs t4 s5))
    end

(* Tests *)
(*
;W (Var "a") initenv;
W (App(Int 1, Int 2)) initenv;
W (If(Int(0), Int(1), Int(2))) initenv;
W (Abs ("x", App(Var "x", Var "x"))) initenv;
W (Let("f", (Abs("x", Var("x"))),
  If(App(Var("f"), Bool(true)),
    App(Var("f"), Int(1)),
    Int(0))
  )) initenv;
W (Letex("divzero",
   Let("safediv", Abs("x", Abs("y",
           If(App(App(Prim Eq, Var "y"), Int 0),
               Raise(Var "divzero"),
               App(App(Prim Div, Var "x"), Var "y")
             )
        )),
        Handle(Var "divzero",
               App(App(Prim Add, App(App(Var "safediv", Int 8), Int 4)),
                                 App(App(Var "safediv", Int 3), Int 0)),
               Int 0)
        )
    )) initenv;
*)
