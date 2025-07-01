val import_ty : Types.span -> Types.ty -> Ast.Rust.ty
val import_trait_ref : Types.span -> Types.trait_ref -> Ast.Rust.trait_goal

val import_clause :
  Types.span -> Types.clause -> Ast.Rust.generic_constraint option

val import_item :
  drop_body:bool ->
  Types.item_for__decorated_for__expr_kind ->
  Concrete_ident.t * (Ast.Rust.item list * Diagnostics.t list)
