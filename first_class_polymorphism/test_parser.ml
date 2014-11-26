open OUnit2
open Expr

type result =
	| OK of texpr
	| Fail

let bound i = TVar (ref (Bound i))
let unbound = TVar (ref (Unbound(-1, 0)))

let test_cases = [
	("", Fail);
	("a", OK (Var "a", unbound));
	("f(x, y)", OK (Call((Var "f",unbound), [(Var "x",unbound); (Var "y",unbound)]),unbound));

	("f(x)(y)", OK (Call((Call((Var "f", unbound), [Var "x", unbound]), unbound), [Var "y", unbound]), unbound));
	("let f = fun x y -> g(x, y) in f(a, b)",
		OK (Let("f", (Fun([("x", None); ("y", None)], (Call((Var "g", unbound), [(Var "x", unbound); (Var "y", unbound)]), unbound)), unbound),
			(Call((Var "f", unbound), [(Var "a", unbound); (Var "b", unbound)]), unbound)), unbound));
	("let x = a in " ^
	 "let y = b in " ^
	 "f(x, y)", OK (Let("x", (Var "a",unbound), (Let("y", (Var "b", unbound), (Call((Var "f", unbound), [(Var "x", unbound); (Var "y", unbound)]), unbound)), unbound)), unbound));
	("f x", Fail);
	("let a = one", Fail);
	("a, b", Fail);
	("a = b", Fail);
	("()", Fail);
	("fun x, y -> y", Fail);
	("fun -> y", OK (Fun([], (Var "y", unbound)), unbound));
	("id : forall[a] a -> a", OK (Ann((Var "id", unbound), ([], TForall([0], TArrow([bound 0], bound 0)))), unbound));
	("magic : forall[a b] a -> b",
		OK (Ann((Var "magic", unbound), ([], TForall([0; 1], TArrow([bound 0], bound 1)))), unbound));
	("magic : forall[x int] x -> int",
		OK (Ann((Var "magic", unbound), ([], TForall([0; 1], TArrow([bound 0], bound 1)))), unbound));
	("magic : forall[w x y z] y -> x",
		OK (Ann((Var "magic", unbound), ([], TForall([0; 1], TArrow([bound 0], bound 1)))), unbound));
	("a : forall[a] forall[b] b", Fail);
	("a : (forall[int] int -> int) -> int",
		OK (Ann((Var "a", unbound), ([], TArrow([TForall([0], TArrow([bound 0], bound 0))], TConst "int"))), unbound));
	("f : int -> int -> int",
		OK (Ann((Var "f", unbound), ([], TArrow([TConst "int"], TArrow([TConst "int"], TConst "int")))), unbound));
	("f : some[a b] forall[c d] (int, int) -> int",
		OK (Ann((Var "f", unbound), ([], TArrow([TConst "int"; TConst "int"], TConst "int"))), unbound));
	("fun (x : some[a] a -> a) y (z : (list[forall[t] t -> int])) -> m : int",
		OK (Fun([("x", Some ([0], TArrow([bound 0], bound 0))); ("y", None);
			("z", Some ([], TApp(TConst "list", [TForall([1], TArrow([bound 1], TConst "int"))])))],
			(Ann((Var "m", unbound), ([], TConst "int")), unbound)), unbound));
	]



let string_of_result = function
	| Fail -> "Fail"
	| OK (expr, _) -> "OK (" ^ string_of_expr expr ^ ")"

let make_single_test_case (code, expected_result) =
	String.escaped code >:: fun _ ->
		Infer.reset_id () ;
		let result =
			try
				OK (Parser.expr_eof Lexer.token (Lexing.from_string code))
			with Parsing.Parse_error ->
				Fail
		in
		assert_equal ~printer:string_of_result expected_result result ;
		match result with
			| OK (expr,_) ->
					let expr_str = string_of_expr expr in
					Infer.reset_id () ;
					let new_result = OK (Parser.expr_eof Lexer.token (Lexing.from_string expr_str)) in
					assert_equal ~printer:string_of_result ~msg:"string_of_expr error"
						expected_result new_result
			| Fail -> ()

let suite =
	"test_parser" >::: List.map make_single_test_case test_cases


