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

type program = instr list

let string_of_instr = function
  | Add (d, r1, r2) -> sprintf "add %s,%s,%s" d r1 r2
  | Mul (d, r1, r2) -> sprintf "mul %s,%s,%s" d r1 r2
  | Mov (d, s) -> sprintf "mov %s,%s" d s
  | IAdd (d, r, c) -> sprintf "iadd %s,%s,%d" d r c
  | IMul (d, r, c) -> sprintf "imul %s,%s,%d" d r c
  | Load (d, c) -> sprintf "load %s,%d" d c 

let string_of_program prog =
  String.concat ~sep:"; " (List.map prog ~f:string_of_instr)


let eval_program prog (x:int) (y:int) =
  let env = Hashtbl.of_alist_exn (module String) [("rax",x);("rbx",y)] in
  List.iter prog ~f:(function
    | Add (d,r1,r2) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env r1 + Hashtbl.find_exn env r2)
    | Mul (d,r1,r2) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env r1 * Hashtbl.find_exn env r2)
    | Mov (d,s) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env s)
    | IAdd (d,r,c) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env r + c)
    | IMul (d,r,c) -> Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env r * c)
    | Load (d, c) -> Hashtbl.set env ~key:d ~data:c
  );
  env


let run_program prog (x, y) = Hashtbl.find_exn (eval_program prog x y) "rax"


let check_equiv prog1 prog2 =
  let ctx = mk_context [] in
  let int_sort = Arithmetic.Integer.mk_sort ctx in
  let x = Expr.mk_const ctx (Symbol.mk_string ctx "rax") int_sort in
  let y = Expr.mk_const ctx (Symbol.mk_string ctx "rbx") int_sort in
  let init_env () =
    Hashtbl.of_alist_exn (module String) [ ("rax", x); ("rbx", y) ]
  in
  let exec ctx prog env =
    List.iter prog ~f:(function
      | Add (d, r1, r2) ->
          let v = Arithmetic.mk_add ctx [ Hashtbl.find_exn env r1;
                                          Hashtbl.find_exn env r2 ] in
          Hashtbl.set env ~key:d ~data:v
      | Mul (d, r1, r2) ->
          let v = Arithmetic.mk_mul ctx [ Hashtbl.find_exn env r1;
                                          Hashtbl.find_exn env r2 ] in
          Hashtbl.set env ~key:d ~data:v
      | Mov (d, s) ->
          Hashtbl.set env ~key:d ~data:(Hashtbl.find_exn env s)
      | IAdd (d,r,c) ->
        let v = Arithmetic.mk_add ctx [Hashtbl.find_exn env r; Arithmetic.Integer.mk_numeral_i ctx c] in
        Hashtbl.set env ~key:d ~data:v
      | IMul (d, r, c) ->
        let v = Arithmetic.mk_mul ctx [Hashtbl.find_exn env r; Arithmetic.Integer.mk_numeral_i ctx c] in 
        Hashtbl.set env ~key:d  ~data:v
      | Load (d, c) -> 
        Hashtbl.set env ~key:d ~data:(Arithmetic.Integer.mk_numeral_i ctx c));
    env
  in
  let env1 = exec ctx prog1 (init_env ()) in
  let env2 = exec ctx prog2 (init_env ()) in
  let out1 = Hashtbl.find_exn env1 "rax" in
  let out2 = Hashtbl.find_exn env2 "rax" in
  let neq = Boolean.mk_not ctx (Boolean.mk_eq ctx out1 out2) in
  let solver = Solver.mk_simple_solver ctx in
  Solver.add solver [neq];
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE -> true
  | _ -> false
;;

let used_regs prog =
  let regs_of_instr = function
    | Add (r1,r2,r3) | Mul (r1,r2,r3) -> [r1; r2; r3]
    | IAdd (r1,r2,_) | IMul(r1, r2, _) -> [r1; r2]
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
  | 5 -> Load ("rax", Random.int 10)
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
;;


let test_equiv_random prog1 prog2 trials =
  let same = ref 0 in
  for _ = 1 to trials do
    let x = 0 in
    let y = Random.int 5 in
    let r1 = run_program prog1 (x, y) in
    let r2 = run_program prog2 (x, y) in
    if r1 = r2 then incr same
  done;
  !same
;;

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
;;


let score_candidate prog_orig prog_candidate =
  let random_matches = test_equiv_random prog_orig prog_candidate 10 in
  let prop = float_of_int random_matches /. 10.0 in
  if Float.(prop <> 1.0) then
    0.1 +. prop
  else if check_equiv prog_orig prog_candidate then
    2.0 +. 2.0 ** (-1.0 *. (cost prog_candidate))
  else 0.1 +. prop
;;

let run_equiv_optimizer ~iterations prog0 =
  Random.self_init ();
  printf "Initial program: %s\n" (string_of_program prog0);

  let current_prog = ref prog0 in
  let current_score = ref (score_candidate prog0 prog0) in
  let visited = ref [(!current_prog, !current_score)] in

  for iter = 1 to iterations do
    let candidate = perturb !current_prog in
    let score = score_candidate prog0 candidate in

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
;;




let run () =
  let const_folding = [Load("rax",2); IAdd("rax","rax",3); IMul("rax", "rax", 1)] in
  (*let reductions =
    [
      IMul("x", "x", 2);
    ]
  in*)

  let x = run_program const_folding (0, 0) in
  printf "Result of running %s \n" (string_of_program const_folding);
  printf "Is === %d === \n" x;

  let best_prog, best_score, visited = run_equiv_optimizer ~iterations:10000 const_folding in

  printf "\nFinal best program: %s\n" (string_of_program best_prog);
  printf "Score: %.2f\n" best_score;

  printf "\n Original program: %s\n" (string_of_program const_folding);

  printf "\nTop 5 visited programs:\n";
  List.iter (List.take visited 5) ~f:(fun (prog, score) ->
    printf "Score %.5f -- result: %d --- %s\n" score ((run_program prog) (0,0)) (string_of_program prog) 
  )
;;

