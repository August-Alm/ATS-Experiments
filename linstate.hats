(* ****** ****** ****** *)

// Linear state monads //

(* ****** ****** ****** *)

staload "libats/ML/SATS/basis.sats"
staload UN = "prelude/SATS/unsafe.sats"

(* Template(s) for a linear monad. To use in a file, add
 * [assume monad_vtype(a) = ...] and implement [bind_vt]
 * and [return_vt].
 *)
absvtype
  monad_vtype(a: vt0ype+) = ptr

vtypedef
  M(a: vt0ype) = monad_vtype(a)

extern fun{a: vt0ype}
  return_vt(x: a): M(a)

extern fun{a, b: vt0ype}
  bind_vt
  (mx: M(a), fopr: cfun(a, M(b))): M(b)

symintr >>=
infix >>=
overload >>= with bind_vt

#define nil list_vt_nil
#define :: list_vt_cons

extern fun{a, b: vt0ype}
  mapM_vt$fopr(a): M(b)

fun{a, b: vt0ype}
  mapM_vt_aux(xs: List0_vt(a)): M(List0_vt(b))
  = case xs of
    | ~nil()      => return_vt<List0_vt(b)>(nil())
    | ~(x :: xs1) => let 
        val xs1 = $UN.castvwtp0{ptr}(xs1)
        val fx = mapM_vt$fopr<a, b>(x) 
      in bind_vt<b, List0_vt(b)>
         ( fx
         , lam(y: b) => let
             val y = $UN.castvwtp0{ptr}(y)
             val xs1 = $UN.castvwtp0{List0_vt(a)}(xs1)
           in bind_vt<List0_vt(b), List0_vt(b)>
              ( mapM_vt_aux(xs1)
              , lam(ys: List0_vt(b)) => let
                  val y = $UN.castvwtp0{b}(y) 
                in return_vt<List0_vt(b)>(y :: ys)
                end
              ) 
           end
         )
      end
 
fun{a, b: vt0ype}
  mapM_vt
  ( xs: List0_vt(a)
  , fopr: a -<cloref1> M(b)
  ) : M(List0_vt(b))
  = let val () = $tempenver(fopr)
        implement mapM_vt$fopr<a, b>(x) = fopr(x)
    in mapM_vt_aux<a, b>(xs) 
    end

(* Template of linear state monads. To use in a file, add 
 * [assume state_vtype = ...] and, whenever in a function body 
 * or definition that the template monad [M(a)] needs to be 
 * instantiated as the state monad based on [state_vtype], just
 * add [reassume monad_vtype].
 *)
absvtype 
  state_vtype = ptr
vtypedef 
  state = state_vtype

fun{a: vt0ype}
  state_action_free(mx: M(a))
  = cloptr_free($UN.castvwtp0{cloptr(void)}(mx))

overload free with state_action_free

extern fun{}
  state_init(): state

extern fun{}
  state_destroy(state): void

extern fun{a: vt0ype}
  state_run(M(a), state): @(state, a)

fun{a: vt0ype}
  state_exec(mx: M(a), s: state): state
  = let val (s', _) = state_run(mx, s) in s' end

fun{a: vt0ype}
  state_eval(mx: M(a), s: state): a
  = let val (_, x') = state_run(mx, s) in x' end
  
local assume
  monad_vtype(a) = state -<lincloptr1> (state, a)
in

  implement{a}
    return_vt(x) = llam s => (s, x)
  
  implement{a, b}
    bind_vt(mx, fopr) 
    = let val mx = $UN.castvwtp0{ptr}(mx)
      in llam s => let
           val mx = $UN.castvwtp0{M(a)}(mx) 
           val (s', x) = mx(s)
        in cloptr_free($UN.castvwtp0{cloptr(void)}(mx))
         ; fopr(x)(s') 
        end
      end
  
  implement{a}
    state_run(mx, s) = sx where
      val sx = mx(s)
      val () = cloptr_free($UN.castvwtp0{cloptr(void)}(mx)) 
    end

end (* of local assume *)

(* ****** ****** ****** *)

(* End of [linstate.hats]. *)
