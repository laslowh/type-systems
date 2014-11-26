(*
	Parts of this file are based on code from Daan Leijen's
	reference implementation of HMF, available at (as of 2014/04/04)
	http://research.microsoft.com/en-us/um/people/daan/download/hmf-prototype-ref.zip
*)

open Expr
open Infer


type generalized = Generalized | Instantiated


let rec should_generalize expected_ty = match expected_ty with
	| TForall _ -> Generalized
	| TVar {contents = Link ty} -> should_generalize ty
	| _ -> Instantiated

let maybe_generalize generalized level ty = match generalized with
	| Instantiated -> ty
	| Generalized -> generalize level ty

let maybe_instantiate generalized level ty = match generalized with
	| Instantiated -> instantiate level ty
	| Generalized -> ty

let generalize_or_instantiate generalized level ty = match generalized with
	| Instantiated -> instantiate level ty
	| Generalized -> generalize level ty


let rec infer env level maybe_expected_ty generalized e = 
	match e with 
	| Var name -> begin
			try
				(e, maybe_instantiate generalized level (Env.lookup env name))
			with Not_found -> error ("variable " ^ name ^ " not found")
		end
	| Fun(param_list, (body_expr, _)) ->
			let expected_param_list, maybe_expected_return_ty, body_generalized =
				match maybe_expected_ty with
					| None -> param_list, None, Instantiated
					| Some expected_ty -> begin
							match instantiate (level + 1) expected_ty with
								| TArrow(expected_param_ty_list, expected_return_ty) ->
										List.map2
											(fun (param_name, maybe_param_ty_ann) expected_param_ty ->
												param_name, if maybe_param_ty_ann = None then Some ([], expected_param_ty) else maybe_param_ty_ann)
											param_list expected_param_ty_list, Some expected_return_ty, should_generalize expected_return_ty
								| _ -> param_list, None, Instantiated
						end
			in

			let fn_env_ref = ref env in
			let var_list_ref = ref [] in
			let param_ty_list = List.map
				(fun (param_name, maybe_param_ty_ann) ->
					let param_ty = match maybe_param_ty_ann with
						| None -> (* equivalent to `some[a] a` *)
								let var = new_var (level + 1) in
								var_list_ref := var :: !var_list_ref ;
								var
						| Some ty_ann ->
								let var_list, ty = instantiate_ty_ann (level + 1) ty_ann in
								var_list_ref := var_list @ !var_list_ref ;
								ty
					in
					fn_env_ref := Env.extend !fn_env_ref param_name param_ty ;
					param_ty)
				expected_param_list
			in

			let (body_expr, return_ty) =
				infer !fn_env_ref (level + 1) maybe_expected_return_ty body_generalized body_expr
			in
			if not (List.for_all is_monomorphic !var_list_ref) then
				error ("polymorphic parameter inferred: "
					^ String.concat ", " (List.map string_of_ty !var_list_ref))
			else
				(Fun(param_list, (body_expr, return_ty)), maybe_generalize generalized level (TArrow(param_ty_list, return_ty)))
	| Let(var_name, (value_expr,_), (body_expr,_)) ->
			let (v, var_ty) = infer env (level + 1) None Generalized value_expr in
			let (b, inferred_type) = infer (Env.extend env var_name var_ty) level maybe_expected_ty generalized body_expr in
			((Let (var_name, (v, var_ty), (b, inferred_type))), inferred_type)
	| Call((fn_expr, _), arg_list) ->
			let (fn_expr, fn_ty) = infer env (level + 1) None Instantiated fn_expr in
			let fn_ty = instantiate (level + 1) fn_ty in
			let param_ty_list, return_ty = match_fun_ty (List.length arg_list) fn_ty in
			let instantiated_return_ty = instantiate (level + 1) return_ty in
			begin match maybe_expected_ty, instantiated_return_ty with
				| None, _ | _, TVar {contents = Unbound _} -> ()
				| Some expected_ty, _ ->
					unify (instantiate (level + 1) expected_ty) instantiated_return_ty ;
			end ;
			let inferred_args = infer_args env (level + 1) param_ty_list arg_list in 
			let ty = generalize_or_instantiate generalized level instantiated_return_ty in
			((Call ((fn_expr, fn_ty), inferred_args)), ty)
	| Ann((expr, _), ty_ann) ->
			let _, ty = instantiate_ty_ann level ty_ann in
			let (expr, expr_ty) = infer env level (Some ty) (should_generalize ty) expr in
			subsume level ty expr_ty ;
			((Ann ((expr, ty), ty_ann)), ty)

and infer_args env level param_ty_list arg_list =
	let pair_list = List.combine param_ty_list (List.map fst arg_list) in
	let get_ordering ty arg =
		(* subsume annotated arguments first, type variables last *)
		if is_annotated arg then 0
		else match unlink ty with
				| TVar {contents = Unbound _ } -> 2
				| _ -> 1
	in
	let sorted_pair_list = List.fast_sort
		(fun (ty1, arg1) (ty2, arg2) -> compare (get_ordering ty1 arg1) (get_ordering ty2 arg2))
		pair_list
	in
	let infer_arg (param_ty, arg_expr) =
		let (arg_expr, arg_ty) = infer env level (Some param_ty) (should_generalize param_ty) arg_expr in
			if is_annotated arg_expr then
				unify param_ty arg_ty
			else
			subsume level param_ty arg_ty;
		(arg_expr, param_ty)
	in
	List.map infer_arg sorted_pair_list
