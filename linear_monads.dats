(* ****** ****** ****** *)

// First steps at  a template-based 
// implementation of linear (viewtype)
// monads, following Hongwei Xi.

// Compile:
// $ patscc -DATS_MEMALLOC_LIBC -o 
// linear_monads linear_monads.dats

(* ****** ****** ******* *)

#include "share/atspre_staload.hats"
#staload UN = "prelude/SATS/unsafe.sats"
#staload "libats/SATS/qlist.sats"
#staload "libats/DATS/qlist.dats"

(* ****** ****** ****** *)

macdef 
freehom(h) = cloptr_free($UN.castvwtp0{cloptr(void)} ,(h))

vtypedef
hom(a: vt0ype, b: vt0ype) = a -<lincloptr1> b

sortdef 
fvtype = vt0ype -> vtype

(* ****** ****** ****** *)

// Template-based linear functors.

(* ****** ****** ****** *)

absprop 
FUNCTOR(f_name: type, f: fvtype) 

dataprop
EQ_fvtype(fvtype, fvtype) = {f: fvtype} Eq_fvtype(f, f)

extern fun{f_name: type}{a, b: vt0ype}
functor_map
{f: fvtype}
(FUNCTOR(f_name, f)| hom(a, b)): hom(f(a), f(b))

praxi{f_name: type}
trust_me_this_is_the_functor
{f: fvtype}.<f>.(): FUNCTOR(f_name, f) = 
  $UN.proof_assert{FUNCTOR(f_name, f)}()

(* ****** ****** ****** *)

// Template-based linear monads.

(* ****** ****** ****** *)
absprop 
MONAD(m_name: type, m: fvtype)

extern fun{m_name: type}{a: vt0ype}
monad_return
{m: fvtype}
(MONAD(m_name, m)| a): m(a)

extern fun{m_name: type}{a, b: vt0ype}
monad_bind
{m: fvtype}
(MONAD(m_name, m)| m(a), hom(a, m(b))): m(b)

fun{m_name: type}{a, b: vt0ype}
monad_bind_const
{m: fvtype}
(pfm: MONAD(m_name, m)| mx: m(a), my: m(b)): m(b) =
  monad_bind<m_name><a, b>(pfm| mx, llam(_) => my)

fun{m_name: type}{a: vt0ype}
monad_join
{m: fvtype}
(pfm: MONAD(m_name, m)| mmx: m(m(a))): m(a) =
  monad_bind<m_name><m(a), a>(pfm| mmx, llam(mx) => mx)

praxi{m_name: type}
trust_me_this_is_the_monad
{m: fvtype}.<m>.(): MONAD(m_name, m) = 
  $UN.proof_assert{MONAD(m_name, m)}()

extern praxi{t_name: type}
monad_is_functor
{t: fvtype}
(MONAD(t_name, t)): FUNCTOR(t_name, t)

symintr bind return join
overload bind with monad_bind
overload bind with monad_bind_const
overload return with monad_return
overload join with monad_join

(* ****** ****** ****** *)

// General functions involving
// monads and [list_vt].

(* ****** ****** ****** *)

// mapM

extern fun{a, s: vt0ype}
mapM_list_vt$fopr(a): s    // [s = m(b)] in implementation!

(* Our definition of mapM is in would-be tail-recursive style.
 * Compile with aggressive inlining and hope for the best.
 *)
fun{m_name: type}{a, b: vt0ype} 
mapM_list_vt$aux
{m: fvtype}
{n: int}
( pfm: MONAD(m_name, m)
| xs: list_vt(INV(a), n) ): 
m(list_vt(b, n)) =
  let
    prval () = lemma_list_vt_param(xs)

    fun loop
    {m: fvtype}
    {n: nat}.<n>.
    {k: nat}
    ( pfm: MONAD(m_name, m)
    | xs: list_vt(a, n)
    , acc: qlist(INV(b), k) ):
    m(list_vt(b, k+n)) =
      case xs of
      | ~list_vt_nil() => 
          let val ys = qlist_takeout_list{b}{k}(acc)   // takeout is O(1) 
          in qlist_free_nil{b}(acc)
           ; monad_return<m_name><list_vt(b, k+n)>(pfm| ys) 
          end
      | ~list_vt_cons(x, xs1) => 
          monad_bind<m_name><b, list_vt(b, k+n)>
             ( pfm
             | mapM_list_vt$fopr<a, m(b)>(x)
             , llam(y: b) => ( qlist_insert<b>{k}(acc, y)
                             ; loop(pfm| xs1, acc) ) )
    
    val acc = qlist_make_nil{b}()
  in
    loop{m}{n}(pfm| xs, acc)
  end

fun{m_name: type}{a, b: vt0ype}
mapM_list_vt_fun
{m: fvtype}
{n: int}
( pfm: MONAD(m_name, m)
| xs: list_vt(INV(a), n) 
, fopr: a -<fun1> m(b) ):
m(list_vt(b, n)) = 
  let implement(a, s) mapM_list_vt$fopr<a, s>(x) = 
        let val x = $UN.castvwtp0(x) in $UN.castvwtp0(fopr(x)) end 
  in mapM_list_vt$aux<m_name><a, b>{m}{n}(pfm| xs) end

fun{m_name: type}{a, b: vt0ype}
mapM_list_vt_cloref
{m: fvtype}
{n: int}
( pfm: MONAD(m_name, m)
| xs: list_vt(INV(a), n) 
, fopr: a -<cloref1> m(b) ):
m(list_vt(b, n)) = 
  let implement(a, s) mapM_list_vt$fopr<a, s>(x) = 
        let val x = $UN.castvwtp0(x) in $UN.castvwtp0(fopr(x)) end 
  in mapM_list_vt$aux<m_name><a, b>{m}{n}(pfm| xs) end

fun{m_name: type}{a, b: vt0ype}
mapM_list_vt_cloptr
{m: fvtype}
{n: int}
( pfm: MONAD(m_name, m)
| xs: list_vt(INV(a), n) 
, fopr: !hom(a, m(b)) ):  // Note, [fopr] is not freed!
m(list_vt(b, n)) =   
    let val foo = $UN.castvwtp1{a -<cloref1> m(b)}(fopr)
  in mapM_list_vt_cloref<m_name><a, b>{m}{n}(pfm| xs, foo) end


(* ****** ****** ****** *)

// sequence

fun{m_name: type}{a: vt0ype}
sequence_list_vt
{m: fvtype}
{n: int}
( pfm: MONAD(m_name, m)
| mxs: list_vt(m(a), n) ):
m(list_vt(a, n)) =
  let prval () = lemma_list_vt_param(mxs)
  in case mxs of
  | ~list_vt_nil() =>
      monad_return<m_name><list_vt(a, n)>(pfm| list_vt_nil{a}())
  | ~list_vt_cons(mx, mxs1) =>
      monad_bind<m_name><a, list_vt(a, n)>
      ( pfm
      | mx
      , llam(x) => 
          let prval () = lemma_list_vt_param(mxs1)
          in monad_bind<m_name><list_vt(a, n-1), list_vt(a, n)>
             ( pfm
             | sequence_list_vt(pfm| mxs1)
             , llam(xs) => 
                 let prval () = lemma_list_vt_param(xs)
                 in monad_return<m_name><list_vt(a, n)>
                    (pfm| list_vt_cons(x, xs)) end ) end ) end

(* ****** ****** ***** *)

// Example: The Option ("Maybe") monad.

abstype
Option_vt_name

prval 
pfoptm = trust_me_this_is_the_monad<Option_vt_name>{Option_vt}()

extern praxi
MONAD_Option_vt_elim
{m: fvtype}
(pfm: MONAD(Option_vt_name, m)): EQ_fvtype(Option_vt, m)

implement(a: vt0ype)
monad_return<Option_vt_name><a>(pfm| x) = 
  let prval Eq_fvtype() = MONAD_Option_vt_elim(pfm)
  in Some_vt(x) end

implement(a, b: vt0ype)
monad_bind<Option_vt_name><a, b>(pfm| x_opt, fopr) = 
  let prval Eq_fvtype() = MONAD_Option_vt_elim(pfm) 
  in case x_opt of
     | ~Some_vt(x) => fx where 
           val fx = fopr(x) 
           val () = freehom(fopr) 
         end
     | ~None_vt()  => (freehom(fopr); None_vt())
  end 

(* ****** ****** ****** *)

implement
main0() = let 
    val xs = $list_vt{int}(1, 2, 3)
   
    val fopr = 
      llam(x: int): Option_vt(int) =<cloptr1> return(pfoptm| x)
    
    val xsopt = mapM_list_vt_cloptr(pfoptm| xs, fopr)
    
    val () = freehom(fopr)

    val yopts = 
      $list_vt{Option_vt(int)}(Some_vt(4), Some_vt(5), Some_vt(6))

    val- ~Some_vt(xs) = xsopt

    val- ~Some_vt(ys) = sequence_list_vt(pfoptm| yopts)

    fun printout{n: int}(ks: list_vt(int, n)): void =
      case ks of
      | ~list_vt_nil()        => ()
      | ~list_vt_cons(k, ks1) => (println!(k); printout(ks1))
  in 
    printout(xs); printout(ys) 
  end

(* Valgrind says:
 * ==2312== HEAP SUMMARY:
 * ==2312==     in use at exit: 0 bytes in 0 blocks
 * ==2312==   total heap usage: 34 allocs, 34 frees, 472 bytes allocated
 * ==2312== 
 * ==2312== All heap blocks were freed -- no leaks are possible
 *) 
