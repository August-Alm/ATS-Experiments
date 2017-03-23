#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include "linstate.hats"
staload M = "libats/SATS/linmap_avltree.sats"
staload _(*M*) = "libats/DATS/linmap_avltree.dats"
#include "contrib/atscntrb-hx-intinf/mylibies.hats"
//#include "contrib/atscntrb-libgmp/CATS/gmp.cats"

(* We'll need the Either type. *)

datavtype 
  Either_bool(a: vt0ype+, b: vt0ype+, bool) 
  = Left(a, b, true) of a | Right(a, b, false) of b

stadef 
  Either_bool = Either_bool

vtypedef 
  Either(a: vt0ype+, b: vt0ype+) = [p: bool] Either_bool(a, b, p)

(* Why is not fold for linear lists in Prelude?? *)

fun {res: vt0p}{a: t0p}
  list_vt_foldleft 
  ( xs: List0_vt(INV(a))
  , init: res
  , fopr: (res, a) -> res
  ) : res 
  = case xs of
    | ~list_vt_nil() => init
    | ~list_vt_cons(x0, xs1) =>
      let val init = fopr(init, x0)
          val xs1 = xs1
      in list_vt_foldleft(xs1, init, fopr)
      end

(* Here we go! *)

abstype 
  input_type  
typedef 
  input = input_type 

abstype 
  output_type 
typedef 
  output = output_type 

(* After the following assumption we can [reassume monad_vtype]
 * as the linear state monad with [state = Map].
 *)
assume state_vtype = $M.map(input, output)

typedef
  Recur = input -> Either( output
                         , ( List0_vt(input)
                           , List0_vt(output) -> output
                           )
                         )

fun 
  memoize 
  ( t: cfun(input, M(output)) -<cloref1> 
       cfun(input, M(output))
  , x: input
  ) : output
  = let (* We now want [state] State-monad! *)
      reassume monad_vtype

      fnx 
        foo(x: input):<cloref1> M(output)
        = llam(s) => let val y_opt = $M.linmap_search_opt(s, x)
                     in case y_opt of
                        | ~None_vt()  => bar(x)(s)
                        | ~Some_vt(y) => return_vt(y)(s)
                     end
  
      and 
        bar(x: input):<cloref1> M(output)
        = llam(s) => let val (s1, y1) = ((t foo)(x))(s)
                         var s1 = s1
                     in $M.linmap_insert_any(s1, x, y1)
                      ; (s1, y1)
                     end
    in
      state_eval(foo(x), $M.linmap_nil())
    end
  
  fun (* This one works for any monad! *) 
    distr
    (go: Recur): cfun(input, M(output)) -<cloref1> 
                 cfun(input, M(output)) 
    = lam(u) => ( lam(x) =<cloref1> 
        case go(x) of
        | ~Left(y)         => return_vt(y)
        | ~Right(@(xs, h)) => bind_vt
                              ( mapM_vt(xs, u)
                              , lam(ys) => return_vt(h(ys))
                              )
      )

  fun
    conquer(go: Recur): cfun(input, output)
    = lam(x) => memoize(distr(go), x) 

(* ****** Examples ****** *) //Horrendous notation to follow...

local assume input_type = $INTINF_t.Intinf
      assume output_type = $INTINF_t.Intinf
in
  fun
    list_vt_sum_intinf(xs: List0_vt(output)): output
    = list_vt_foldleft<output><output>
      ( xs
      , $INTINF_t.intinf_make_int(0)
      , lam(y1, y2) => $INTINF_t.add_intinf_intinf(y1, y2)
      )

  fun 
    divide_fib_fun
    (x: input): Either(output, @(List0_vt(output), List0_vt(output) -> output))
    = let val cmp = $INTINF_t.compare_int_intinf(2, x) 
                in if cmp > 0 then Left(x)
                   else Right @( $list_vt( $INTINF_t.sub_intinf_int(x, 1)
                                         , $INTINF_t.sub_intinf_int(x, 2)
                                         )
                               , list_vt_sum_intinf
                               )
                end
 
  val divide_fib: Recur = divide_fib_fun

  fun
    fib(x: input): output = conquer(divide_fib)(x)
end  

implement 
  main0() = print($UN.cast{int}(fib($UN.cast{input}(100000))))
