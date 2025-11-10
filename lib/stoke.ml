open Core
open Z3

type reg = string

type instr =
  | Add of reg * reg * reg
  | Mul of reg * reg * reg
  | Mov of reg * reg
  | IAdd of reg * reg * int
  | IMul of reg * reg * int
  | Load of reg * int
  (*| And of reg * reg * reg
  | Xor of reg * reg * reg
  | AndI of reg * reg * int*)

type program = instr list

let string_of_instr = function
  | Add (d, r1, r2) -> sprintf "add %s,%s,%s" d r1 r2
  | Mul (d, r1, r2) -> sprintf "mul %s,%s,%s" d r1 r2
  | Mov (d, s) -> sprintf "mov %s,%s" d s
  | IAdd (d, r, c) -> sprintf "addi %s,%s,%d" d r c
  | IMul (d, r, c) -> sprintf "muli %s,%s,%d" d r c
  | Load (d, c) -> sprintf "li %s,%d" d c 
  (*| And (d, r1, r2) -> sprintf "and %s,%s,%s" d r1 r2
  | Xor (d, r1, r2) -> sprintf "or %s,%s,%s" d r1 r2
  | AndI (d, r1, c) -> sprintf "andi %s,%s,%d" d r1 c*)

let string_of_program prog =
  String.concat ~sep:"; " (List.map prog ~f:string_of_instr)

let eval_program prog (init_env : (string, int) Hashtbl.t) =
  let env = Hashtbl.copy init_env in
  List.iter prog ~f:(function
    | Add (d,r1,r2) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env r1 + Hashtbl.find_exn env r2)
    | Mul (d,r1,r2) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env r1 * Hashtbl.find_exn env r2)
    | Mov (d,s) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env s)
    | IAdd (d,r,c) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env r + c)
    | IMul (d,r,c) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env r * c)
    | Load (d,c) -> Hashtbl.set env ~key:d ~data:c
  );
  env


let run_program prog (init_env : (string,int) Hashtbl.t) ~out_reg = 
  Hashtbl.find_exn (eval_program prog init_env) out_reg


let check_equiv prog1 prog2 regs =
  let ctx = mk_context [] in
  let int_sort = Arithmetic.Integer.mk_sort ctx in
  let env1 = Hashtbl.of_alist_exn (module String)
      (List.map regs ~f:(fun r -> r, Expr.mk_const ctx (Symbol.mk_string ctx r) int_sort)) in
  let env2 = Hashtbl.copy env1 in

  let exec ctx prog env =
    List.iter prog ~f:(function
      | Add (d,r1,r2) -> Hashtbl.set env ~key:d ~data:(Arithmetic.mk_add ctx [Hashtbl.find_exn env r1; Hashtbl.find_exn env r2])
      | Mul (d,r1,r2) -> Hashtbl.set env ~key:d ~data:(Arithmetic.mk_mul ctx [Hashtbl.find_exn env r1; Hashtbl.find_exn env r2])
      | Mov (d,s) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env s)
      | IAdd (d,r,c) -> Hashtbl.set env ~key:d ~data:(Arithmetic.mk_add ctx [Hashtbl.find_exn env r; Arithmetic.Integer.mk_numeral_i ctx c])
      | IMul (d,r,c) -> Hashtbl.set env ~key:d ~data:(Arithmetic.mk_mul ctx [Hashtbl.find_exn env r; Arithmetic.Integer.mk_numeral_i ctx c])
      | Load (d,c) -> Hashtbl.set env ~key:d ~data:(Arithmetic.Integer.mk_numeral_i ctx c)
    );
    env
  in

  let env1 = exec ctx prog1 env1 in
  let env2 = exec ctx prog2 env2 in

  let neq =
    List.map regs ~f:(fun r -> Boolean.mk_not ctx (Boolean.mk_eq ctx (Hashtbl.find_exn env1 r) (Hashtbl.find_exn env2 r)))
    |> Boolean.mk_or ctx
  in

  let solver = Solver.mk_simple_solver ctx in
  Solver.add solver [neq];
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE -> true
  | _ -> false


let used_regs prog =
  let regs_of_instr = function
    | Add (r1,r2,r3) | Mul (r1,r2,r3) -> [r1; r2; r3]
    | IAdd (r1,r2,_) | IMul(r1, r2, _)  -> [r1; r2]
    | Mov (r1,r2) -> [r1; r2]
    | Load (r1, _) -> [r1]
  in
  prog
  |> List.concat_map ~f:regs_of_instr
  |> List.dedup_and_sort ~compare:String.compare

let rand_choice lst =
  List.nth_exn lst (Random.int (List.length lst))

let random_instr_used_regs regs =
  match Random.int 6 with
  | 0 -> Add (rand_choice regs, rand_choice regs, rand_choice regs)
  | 1 -> Mul (rand_choice regs, rand_choice regs, rand_choice regs)
  | 2 -> IAdd (rand_choice regs, rand_choice regs, Random.int 10)
  | 3 -> Mov (rand_choice regs, rand_choice regs)
  | 4 -> IMul (rand_choice regs, rand_choice regs, Random.int 10)
  | 5 -> Load (rand_choice regs, Random.int 10)
  | _ -> failwith "unreachable"

let perturb prog =
  let regs = used_regs prog in
  if List.is_empty regs then prog
  else
    match Random.int 3 with
    | 0 ->
        let i = Random.int (List.length prog) in
        List.mapi prog ~f:(fun j ins ->
          if j = i then random_instr_used_regs regs else ins)
    | 1 ->
        prog @ [ random_instr_used_regs regs ]
    | 2 ->
      if List.length prog > 1 then
        let i = Random.int (List.length prog) in
        List.filteri prog ~f:(fun j _ -> j <> i)
      else prog
    | _ -> prog

let cost prog =
  Core.List.fold prog ~init:0.0 ~f:(fun acc inst ->
    match inst with
    | Add _ -> acc +. 1.0
    | Mul _ -> acc +. 4.0
    | Mov _ -> acc +. 1.0
    | IAdd _ -> acc +. 1.0
    | IMul _ -> acc +. 4.0
    | Load _ -> acc +. 4.0
  )


let test_equiv_random prog1 prog2 regs trials =
  let same = ref 0 in
  for _ = 1 to trials do
    let env = Hashtbl.of_alist_exn (module String)
      (List.map regs ~f:(fun r -> (r, Random.int 10)))
    in
    let out_reg = "rax" in (* should this be made general? *)
    let r1 = run_program prog1 env ~out_reg in
    let r2 = run_program prog2 env ~out_reg in
    if r1 = r2 then incr same
  done;
  !same

let score_candidate prog_orig prog_candidate regs =
  let random_matches = test_equiv_random prog_orig prog_candidate regs 10 in
  let prop = float_of_int random_matches /. 10.0 in
  if Float.(prop <> 1.0) then
    0.1 +. prop
  else if check_equiv prog_orig prog_candidate regs then
    2.0 +. 2.0 ** (-1.0 *. (cost prog_candidate))
  else 0.1 +. prop

let run_equiv_optimizer ~iterations prog0 regs =
  Random.self_init ();
  printf "Initial program: %s\n" (string_of_program prog0);

  let current_prog = ref prog0 in
  let current_score = ref (score_candidate prog0 prog0 regs) in
  let visited = ref [(!current_prog, !current_score)] in

  for iter = 1 to iterations do
    let candidate = perturb !current_prog in
    let score = score_candidate prog0 candidate regs in

    let accept_ratio = score /. !current_score in
    let r = Random.float 1.0 in
    if Float.(r < accept_ratio) then begin
      current_prog := candidate;
      current_score := score;
    end;

    visited := (candidate, score) :: !visited;

    if iter mod 100 = 0 then
      printf "Iter %-5d | Current score: %.5f | Program: %s\n"
        iter !current_score (string_of_program !current_prog)
  done;

  let visited_sorted =
    List.dedup_and_sort !visited ~compare:(fun (_, s1) (_, s2) -> Float.compare s2 s1)
  in

  (!current_prog, !current_score, visited_sorted)

let run () =
  let prog0 = [Load("rax", 1); IAdd("rax", "rax", 1); IMul("rax", "rax", 2)] in
  let regs = ["rax"] in

  let x = run_program prog0 (Hashtbl.of_alist_exn (module String) [("rax",0); ("rbx",0)]) ~out_reg:"rax" in
  printf "Result of running %s \n" (string_of_program prog0);
  printf "Is === %d === \n" x;

  let _,_, visited = run_equiv_optimizer ~iterations:10000 prog0 regs in

  printf "\n Original program: %s\n" (string_of_program prog0);

  printf "\nTop 5 visited programs:\n";
  List.iter (List.take visited 5) ~f:(fun (prog, score) ->
    let env = Hashtbl.of_alist_exn (module String) [("rax",0); ("rbx",0)] in
    printf "Score %.5f -- result: %d --- %s\n" score (run_program prog env ~out_reg:"rax") (string_of_program prog) 
  )
;;
