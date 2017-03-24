(*
 * How to compile:
 * patscc -I${PATSHOME}/contrib -o divideandconquer divideandconquer.dats 
 * -DATS_MEMALLOC_LIBC -lgmp
*)

#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include "linstate.hats" (* For linear state monad! *)
staload M = "libats/SATS/linmap_avltree.sats"
staload _(*M*) = "libats/DATS/linmap_avltree.dats"
#include "contrib/atscntrb-hx-intinf/mylibies.hats"
#staload I = $INTINF_t (* For very large integers. *)

(* Function in [linmap_avltree] that used to miss implementation. *)

implement{key, itm}
  $M.linmap_insert_any
  (map, k0, x0) = () 
  where
    val- ~None_vt() 
      = $M.linmap_insert_opt<key, itm>(map, k0, x0)
  end

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

abst@ype 
  input_type  
typedef 
  input = input_type 

abstype 
  output_type 
typedef 
  output = output_type 

(* A recursive definition of a function [f: input -> output] is an
 * element [div_f: Recur]. Note that it does not have to be recursive
 * per se. We just say that for some [x: input] we "know" [y = f(x)],
 * and set [div_f(x) = Left(y)]. For other inputs we assume that we can
 * divide into a list of inputs [xs: List0_vt(input)] and a function
 * [h: List0_vt(output) -> output] for combining lists of output values;
 * and set [div_f(x) = Right(xs, h)]. Note that [h] depends on [x]!
 * Writing down a [div_f] for a specific problem is the "divide" part
 * of a divide-and-conquer strategy.
 *)
typedef
  Recur = input -> Either( output
                         , ( List0_vt(input)
                           , List0_vt(output) -> output
                           )
                         )

(* There is a naive way to "conquer" and write down a function
 * [conq: Recur -> (input -> output)], namely by:
 * [
 *   conq(div_f) = lam(x) => 
 *   case div_f(x) of
 *   | Left(y) => y
 *   | Right(xs, h) => h(list_vt_map(xs, conq(div_f)))
 * ]
 * This is however terribly inefficient. A more abstract and fruitful
 * perspective is to note that [div_f] defines a distribution
 * [distr_f: (input -> output) -> (input -> output)]
 * and that a sought solution [f = conq(div_f)] must be a fixed point
 * of [distr_f]. Below we note that the distribution can be done over
 * an arbitrary monad and use memoization based on a state monad with
 * AVL-backed maps to find such a fixed point.
 *)

(* After the following assumption we can [reassume monad_vtype]
 * as the linear state monad with [state = map(input, output)].
*)
assume state_vtype = $M.map(input, output)

fun{} (* Only works for [state] State-monad! *)
  memoize 
  ( t: cfun(input, M(output)) -<cloref1> 
       cfun(input, M(output))
  , x: input
  ) : output
  = let (* Reassume State-monad! *)
      reassume monad_vtype

      fun 
        foo(x: input):<cloref1> M(output)
        = llam(s) => let val y_opt = $M.linmap_search_opt(s, x)
                     in case y_opt of
                        | ~None_vt()  => bar(x)(s)
                        | ~Some_vt(y) => return_vt<output>(y)(s)
                     end
  
      and 
        bar(x: input):<cloref1> M(output)
        = llam(s) => let val (s1, y1) = ((t foo)(x))(s)
                         var s1 = s1
                     in 
                         $M.linmap_insert_any(s1, x, y1); (s1, y1)
                     end
    in
      state_eval(foo(x), $M.linmap_nil())
    end
  
fun{} (* This one works for any monad! *) 
  distr
  (go: Recur): cfun(input, M(output)) -<cloref1> 
               cfun(input, M(output)) 
  = lam(u) => lam(x) =<cloref1> 
    case go(x) of
    | ~Left(y)         => return_vt(y)
    | ~Right(@(xs, h)) => bind_vt
                          ( mapM_vt(xs, u)
                          , lam(ys) => return_vt(h(ys))
                          )

fun{} (* "Universal" way to conquer recursion. *)
  conquer
  (go: Recur): cfun(input, output) 
  = lam(x) => memoize(distr(go), x) 

(* Example *)

assume input_type = intGte(0)
assume output_type = $I.Intinf

implement
  gcompare_val_val<input>(x, y) = $I.compare(x, y)

fun
  list_vt_sum_intinf
  (xs: List0_vt(output)): output
  = list_vt_foldleft<output><output>
    ( xs
    , $I.intinf_make_int(0)
    , lam(y1, y2) => $I.add_intinf_intinf(y1, y2)
    )

fun 
  divide_fib_fun
  (x: input): Either(output, @(List0_vt(input), List0_vt(output) -> output))
  = let val cmp = compare(2, x) 
    in if cmp > 0 then Left($I.intinf_make_int(x))
       else Right @( $list_vt{input}( x-1 , x-2 )
                   , list_vt_sum_intinf
                   )
    end
 
val 
  divide_fib: Recur = divide_fib_fun

fun
  fib(x: input): output = conquer(divide_fib)(x)

implement 
  main0() = $I.fprint(stdout_ref, fib(10000))
