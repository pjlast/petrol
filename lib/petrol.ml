module Schema = Schema
module Query = Query
module Expr = Expr

module Type = struct
  include Type

  let pp fmt vl = Format.fprintf fmt "%s" (show vl)
end

type table_name = Types.table_name
type ('ret_ty, 'query_kind) query = ('ret_ty, 'query_kind) Types.query
type ('res, 'multiplicity) request = ('res, 'multiplicity) Request.t

module Request = Request

module Sqlite3 = struct
  module Request = Request

  module Expr = struct
    type 'a t = 'a Expr.t

    type 'a expr_list = 'a Expr.expr_list =
      | [] : unit expr_list
      | ( :: ) : ('a t * 'b expr_list) -> ('a * 'b) expr_list

    type wrapped_assign = Types.wrapped_assign

    include Expr.Sqlite3
  end

  module Type = struct
    type 'a t = 'a Type.t

    let int = Type.int
    let real = Type.real
    let text = Type.text
    let bool = Type.bool
    let null_ty = Type.null_ty

    include Type.Sqlite3
    module Numeric = Type.Numeric
  end
end

module Postgres = struct
  module Request = Request

  module Expr = struct
    type 'a t = 'a Expr.t

    type 'a expr_list = 'a Expr.expr_list =
      | [] : unit expr_list
      | ( :: ) : ('a t * 'b expr_list) -> ('a * 'b) expr_list

    type wrapped_assign = Types.wrapped_assign

    include Expr.Postgres
  end

  module Type = struct
    type 'a t = 'a Type.t

    let int = Type.int
    let real = Type.real
    let text = Type.text
    let bool = Type.bool
    let null_ty = Type.null_ty

    include Type.Postgres
    module Numeric = Type.Numeric
  end
end

let exec :
    (module Caqti_lwt.CONNECTION) ->
    (unit, [< `Zero ]) Request.t ->
    (unit, [> Caqti_error.call_or_retrieve ]) result Lwt.t =
 fun (module DB : Caqti_lwt.CONNECTION)
     ((MkCaqti (inps, req), wrapp_value) : (unit, _) Request.t) ->
  let data = Request.unwrap (inps, wrapp_value) in
  DB.exec req data

let find :
      'a.
      (module Caqti_lwt.CONNECTION) ->
      ('a, [< `One ]) Request.t ->
      ('a, [> Caqti_error.call_or_retrieve ]) result Lwt.t =
 fun (module DB : Caqti_lwt.CONNECTION) (type a)
     ((MkCaqti (inps, req), wrapp_value) : (a, _) Request.t) ->
  let data = Request.unwrap (inps, wrapp_value) in
  DB.find req data

let find_opt :
      'a.
      (module Caqti_lwt.CONNECTION) ->
      ('a, [< `One | `Zero ]) Request.t ->
      ('a option, [> Caqti_error.call_or_retrieve ]) result Lwt.t =
 fun (module DB : Caqti_lwt.CONNECTION) (type a)
     ((MkCaqti (inps, req), wrapp_value) : (a, _) Request.t) ->
  let data = Request.unwrap (inps, wrapp_value) in
  DB.find_opt req data

let collect_list :
      'a.
      (module Caqti_lwt.CONNECTION) ->
      ('a, [< `Many | `One | `Zero ]) Request.t ->
      ('a list, [> Caqti_error.call_or_retrieve ]) result Lwt.t =
 fun (module DB : Caqti_lwt.CONNECTION) (type a)
     ((MkCaqti (inps, req), wrapp_value) : (a, _) Request.t) ->
  let data = Request.unwrap (inps, wrapp_value) in
  DB.collect_list req data
