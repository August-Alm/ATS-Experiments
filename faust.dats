(* ****** ****** ****** *)

#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** ****** *)

// General definitions and macros

implement(a:vt0ype)
gfree_val<a>(z) = strptr_free($UN.castvwtp0{Strptr1}(z))

macdef
evcloptr(f, x) = y where
    val f = ,(f)
    val y = f(,(x))
    val () = cloptr_free($UN.castvwtp0{cloptr(void)}(f))
  end

absvtype
hom(a: vt0ype-, b: vt0ype+)

extern fun{a, b: vt0ype}
hom_defn(a -<lincloptr1> b): hom(a, b)

symintr defn
overload defn with hom_defn

extern fun{a, b: vt0ype}
hom_eval(hom(a, b), a): b

overload [] with hom_eval

extern fun{a, b: vt0ype}
hom_free(hom(a, b)): void

overload free with hom_free of 20

extern fun{a, b, c: vt0ype}
hom_compose(hom(b, c), hom(a, b)): hom(a, c)

symintr o
infix o
overload o with hom_compose

local 
  assume hom(a, b) = 
    {i: bool} option_vt(a, i) -<lincloptr1> option_vt(b, i)
in
  implement{a, b} hom_defn(f) = 
    llam(z) =<cloptr1> 
      case z of
      | ~None_vt() => None_vt() where
            val () = cloptr_free($UN.castvwtp0(f))
          end
      | ~Some_vt(x) => Some_vt(y) where
            val y = evcloptr(f, x)
          end
  
  implement{a, b} hom_eval(f, x) = 
    let val+ ~Some_vt(y) = f(Some_vt(x)) in y end

  implement{a, b} hom_free(f) =
    let val+ ~None_vt() = f(None_vt()) in (*void*) end

  implement{a, b, c} hom_compose(f, g) = 
    llam(z) =<cloptr1> z''
      where val z' = g(z)
            val z'' = f(z') end
end

(* ****** ****** ****** *)

// Signals

(* A "signal" is a stream of "as". For modularity we
 * leave the value type [a] unspecified; but note that 
 * it can be unboxed. To help the typechecker we also 
 * make [signal] abstract in the scope of all functions 
 * that do not depend on it being a type of streams.
 *)

extern fun{a: vt0ype}  // For implementing "delay"/[mem], later.
mem$zero(): a

absvtype 
signal(a: vt0ype)

local  // To [reassume] when needed. 
  assume signal(a) = stream_vt(a)
in end

fun{a: vt0ype}  // Requires [mem$zero] to be implemented.
mem_one(u: signal(a)): signal(a) =
  let reassume signal
  in $ldelay(stream_vt_cons(mem$zero<a>(), u), ~u)
  end

absvtype
signals(a: vt0ype, n: int) 

local
  assume signals(a, n) = list_vt(signal(a), n)
in end

fun{a: vt0ype}
signals_free{n: int}(us: signals(a, n)): void =
  let reassume signal
      reassume signals
      implement list_vt_freelin$clear<signal(a)>(u) =
        stream_vt_free<a>(u)
  in list_vt_freelin<signal(a)>(us) end

overload free with signals_free of 20

fun{a: vt0ype}
signals_map_fun
{n: int}
( us: signals(a, n)
, fopr: signal(a) -<fun1> signal(a) ):
signals(a, n) =
  let reassume signals
      implement list_vt_mapfree$fopr<signal(a)><signal(a)>(u) = fopr(u)
  in list_vt_mapfree<signal(a)><signal(a)>(us) end

fun{a: vt0ype}
signals_map_hom
{n: int}
(us: signals(a, n), f: hom(signal(a), signal(a))):
signals(a, n) =
  let val () = $tempenver(f)
      val f = $UN.castvwtp0{ptr}(f)
      implement list_vt_mapfree$fopr<signal(a)><signal(a)>(u) =
        let val f = $UN.castvwtp0{hom(signal(a), signal(a))}(f) in f[u]
        end
  in list_vt_mapfree<signal(a)><signal(a)>(us)
  end

fun{a: vt0ype}
signals_lift_fun
{n: int}
(us: signals(a, n), fopr: a -<fun1> a): signals(a, n) =
  let reassume signal
      fun{} gopr(u: signal(a)): signal(a) = 
        stream_vt_map_fun<a><a>(u, $UN.castvwtp0(fopr))
      implement list_vt_mapfree$fopr<signal(a)><signal(a)>(u) = gopr(u)
  in list_vt_mapfree<signal(a)><signal(a)>(us)
  end

fun{a: vt0ype}
signals_lift_hom
{n: int}
(us: signals(a, n), f: hom(a, a)): signals(a, n) =
  let reassume signal
      reassume signals
      val () = $tempenver(f)
      val f = $UN.castvwtp0{ptr}(f)
      implement list_vt_mapfree$fopr<signal(a)><signal(a)>(u) =
        let implement stream_vt_map$fopr<a><a>(x) = 
            let val f = $UN.castvwtp0{hom(a, a)}(f) in f[x]
            end
        in stream_vt_map<a><a>(u)
        end
  in list_vt_mapfree<signal(a)><signal(a)>(us)
  end

fun{a: vt0ype}
signals_split_at
{n: int}
{k: int |0 <= k; k <= n}
(us: signals(a, n), k: int k): 
@(signals(a, k), signals(a, n-k)) =
  let reassume signals in list_vt_split_at<signal(a)>(us, k)
  end
   
fun{a: vt0ype}
signals_take
{n: int}
{k: int| 0 <= k; k <= n}
(us: signals(a, n), k: int k): signals(a, k) =
  let val (us1, us2) = signals_split_at<a>{n}(us, k)
  in (signals_free<a>(us2); us1)
  end

fun{a: vt0ype} 
signals_append
{n1, n2: int}
(us1: signals(a, n1), us2: signals(a, n2)):
signals(a, n1+n2) =
  let reassume signals
  in list_vt_append<signal(a)>(us1, us2)
  end      

fun{a: vt0ype}
signals_mem
{n: int}(us: signals(a, n)): signals(a, n) =
  let implement 
      list_vt_mapfree$fopr<signal(a)><signal(a)>(u) = 
        mem_one<a>(u)
  in list_vt_mapfree<signal(a)><signal(a)>(us)
  end

(* ****** ****** ****** *)

// Processors

datavtype
processor(a: vt0ype, m: int, n: int) = 
  PROC of @{ hom  = hom(signals(a, m), signals(a, n))
           , ins  = int(m)
           , outs = int(n) }

fn{a: vt0ype}
processor_free
{m, n: int}(pr: processor(a, m, n)): void =
  let val+ ~PROC(p) = pr
      val f = p.hom
  in hom_free(f)
  end

overload free with processor_free

extern praxi{a: vt0ype}
lemma_processor_param
{m, n: int}(!processor(a, m, n)): [m >= 1; n >= 1] void

fn{a: vt0ype}
apply_processor
{m, n: nat}
( pr: processor(a, m, n)
, us: signals(a, m) ): 
signals(a, n) = f[us]
  where val ~PROC(p) = pr
        val f = p.hom
      end

(* So we can write " pr[us] " to apply a processor
 * to signals:
 *)
overload [] with apply_processor of 20

(* ****** ****** ****** *)

// Composing processors

fun{a: vt0ype}  // <+>
parallel_composition
{m1, n1, m2, n2: int}
(pr1: processor(a, m1, n1), pr2: processor(a, m2, n2)):
processor(a, m1+m2, n1+n2) = 
  let 
    val ~PROC(p1) = pr1
    val ~PROC(p2) = pr2
    val f1 = p1.hom
    val f2 = p2.hom
    val f = defn(llam(us) =<cloptr1> 
      signals_append<a>{n1, n2}(f1[us1], f2[us2])
      where
        prval () = __trustme1(p1.ins) where
             extern praxi
             __trustme1{n: int}(n: int n): [n >= 1] void
          end
        prval () = __trustme2(p2.ins) where
             extern praxi 
            __trustme2{n: int}(n: int n): [n >= 1] void
          end
        val (us1, us2) = signals_split_at<a>{m1+m2}{m1}(us, p1.ins)
      end)  // end of [val f = defn ...] 
  in
    PROC @{ hom  = f
          , ins  = p1.ins + p2.ins
          , outs = p1.outs + p2.outs }
  end

symintr <+>
infix <+>
overload <+> with parallel_composition

fun{a: vt0ype}  // <:>
sequential_composition
{m, k, n: int}
(pr1: processor(a, m, k), pr2: processor(a, k, n)):
processor(a, m, n) =
  let val ~PROC(p1) = pr1
      val ~PROC(p2) = pr2
  in PROC @{ hom  = f2 o f1 
             where val f1 = p1.hom and f2 = p2.hom
             end
           , ins  = p1.ins
           , outs = p2.outs }
   end 

symintr <:>
infix <:>
overload <:> with sequential_composition

fun{a: vt0ype}  // <^>
recursive_composition
{m1, n1, m2, n2: int| n1 >= m2; m1 > n2; m2 > 0}
(pr1: processor(a, m1, n1), pr2: processor(a, m2, n2)):
processor(a, m1-n2, n1) =
  let 
    val ~PROC(p1) = pr1
    val ~PROC(p2) = pr2
    val m2 = p2.ins
    val n2 = p2.outs
    val f1 = p1.hom
    val f2 = p2.hom
    val f = fix 
      f(us: signals(a, m1-n2)): signals(a, n1) =<lincloptr1> let
          val us' = dataget(us)
          val us' = $UN.castvwtp0{signals(a, m1-n2)}(us')
        in 
          f1[signals_append<a>{n2, m1-n2}
             ( f2[signals_mem<a>{m2}(signals_take<a>{n1}(f(us), m2))]
             , us' )]: signals(a, n1)
        end
    val phi = defn(f)
  in
    PROC @{ hom = phi
          , ins = p1.ins - p2.outs
          , outs = p1.outs }
  end
(*
 Discarding ins and outs (pun intended!):

  (pr1 <^> pr2)[us] = 
    pr1[append( pr2[mem(take((pr1 <^> pr2)[us], m2))]
              , us )]
*)
symintr <^>
infix <^>
overload <^> with recursive_composition

extern fun{a: vt0ype}  // <<>
split_composition
{m1, n1, k, n2: nat| k > 0}
(p1: processor(a, m1, n1), p2: processor(a, k*n1, n2)):
processor(a, m1, n2)

extern fun{a: vt0ype}  // <>>
merge_composition
{m1, k, m2, n2: nat| k > 0}
(p1: processor(a, m1, k*m2), p2: processor(a, m2, n2)):
processor(a, m1, n2)

(* ****** ****** ****** *)

implement
main0() = let
    reassume signal
    
    val id1: processor(int, 1, 1) = 
      PROC @{ hom = defn(llam(u) =<cloptr1> u) 
            , ins  = 1
            , outs = 1 }

    val id2: processor(int, 1, 1) = 
      PROC @{ hom = defn(llam(u) =<cloptr1> u)
            , ins  = 1
            , outs = 1 }

    (* Parallel composition; uses [signals_split_at] and
     * [signals_append]: 
     *)
    val f = id1 <+> id2 
    
    (* Recursive composition, requires [mem$zero]:
     *)
    implement mem$zero<int>() = 0
    val id3: processor(int, 1, 1) = 
      PROC @{ hom = defn(llam(u) =<cloptr1> u)
            , ins  = 1
            , outs = 1 }
 
    val pr: processor(int, 2, 1) =
      PROC @{ hom = defn<signals(int, 2), signals(int, 1)>(
                llam(us) =<cloptr1> let
               //  val u0 = list_vt_takeout_at<signal>(us, 0)
                 var us = us
                 val u1 = list_vt_takeout_at<signal(int)>(us, 1)
                 val u1 = $list_vt{signal(int)}(u1)
                 val () = signals_free<int>(us)
               in u1 end)
            , ins = 2
            , outs = 1 }

     
    val g = pr <^> id3
    //val () = processor_free<int>(g)

    fun{} from(n: int): stream_vt(int) =
      let implement stream_vt_tabulate$fopr<int>(i) = n + i
      in stream_vt_tabulate<int>() end
 
    val us: signals(int, 2) = $list_vt{signal(int)}(from(0), from(1))
    
    val res: signals(int, 2) = f[us]
    var res = res
    val secondsgnl = list_vt_takeout_at<signal(int)>(res, 1)
    val () = signals_free<int>(res)
    val h = stream_vt_head_exn(secondsgnl)
    val () = println!(h: int)
    
    val vs: signals(int, 1) = $list_vt{signal(int)}(from(5))
    val vs' = g[vs]
    val () = free(vs')
    (* Just testing homomorphisms; ordinary lincloptr's would
     * leak memory if composed analogously unless [psi] was
     * actually applied:
     *)
    val phi = defn<int, int>(llam(x) =<cloptr1> 5 + x)
    val id_int = defn<int, int>(llam(x) =<cloptr1> x)
    val psi = phi o id_int
    
    (* Testing "delay"/[mem]: *)
    val ws: signal(int) = from(4)
    val ws = mem_one<int>(ws)
    val w = stream_vt_head_exn(ws)
    val () = println!(w: int)

     (* Testing [signal_lift_hom]: *)
     val zs: signals(int, 2) = $list_vt{signal(int)}(from(0), from(1))
     val alpha = defn<int, int>(llam(n) =<cloptr1> succ(n))
     val zs' = signals_lift_hom{2}(zs, alpha)
     var zs' = zs'
     val sndsgnl = list_vt_takeout_at<signal(int)>(zs', 1)
     val z' = stream_vt_head_exn(sndsgnl)
     val () = free(zs')
     val () = println!(z': int)
  in
    println!("The heart of the poodle!"); free(psi)
    //; println!(psi[4]: int)
  end
