#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"

(* ****** ****** ****** *)

// This file gives a primitive implementation of lenses in ATS
// and shows an exemplifying use case. Lenses are a functional
// way of doing "dot notation with updates" on immutable tuples
// and records. It can be regarded as a functorial dot notation.

// Compile with:
// $ patscc -O2 -D_GNU_SOURCE -DATS_MEMALLOC_GCBDW -lgc -o lens lens.dats

(* ****** ****** ****** *)

(* We will be doing typical functional programming and mostly use
 * boxed data. Functions will be closures by default.
 *)
typedef
cfun(a: t0p, b: t0p) = a -<cloref1> b

(* A "lens" from [a] to [b] is a "get" and a "set" function, 
 * abstracting the idea that [a] is a record with a field of
 * type [b].
 *)
typedef
Lens(a: t0p, b: t0p) = '{get = cfun(a, b), set = cfun(a, cfun(b, a))}

(* Functions can be applied "over" a lens, abstracting the idea
 * that a function can be applied to a single field in a record.
 *)
fn{a, b: t0p}
over
( ln: Lens(a, b)
, f: cfun(b, b) ):<cloref1>
cfun(a, a) =
  lam(x) => ln.set(x)(f(ln.get(x)))

(* Lenses compose, like functions. Note that the order is the
 * order of dot notation!
 *)
fn{a, b, c: t0p}
lens_compose
( ln1: Lens(a, b)
, ln2: Lens(b, c) ):
Lens(a, c) =
  let val (get1, set1) = (ln1.get, ln1.set)
      val (get2, set2) = (ln2.get, ln2.set)
  in '{ get = lam(x) => get2(get1(x))
      , set = lam(x) => lam(z) => set1(x)(set2(get1(x))(z)) } end

(* To make notation a bit nicer: *)
symintr ::
infix ::
overload :: with lens_compose

(* Now we're ready to see an example! First, let's introduce a 
 * nested record type. 
 *)
typedef
Address = '{_street = string, _zip = int}
typedef
Person = '{_name = string, _age = int, _address = Address}

(* Next: two lenses. Note that their definition is purely
 * boilerplate that it should be possible automatically
 * generate, somehow.
 *)
val
address: Lens(Person, Address) =
  let val address_get: cfun(Person, Address) =
        lam(p: Person) =<cloref1> p._address
      val address_set: cfun(Person, cfun(Address, Person)) =
        lam(p: Person) =<cloref1>
          lam(a) =<cloref1> '{ _name = p._name
                             , _age = p._age
                             , _address = a }
  in '{get = address_get, set = address_set} end

val
zip: Lens(Address, int) =
  let val zip_get: cfun(Address, int) =
        lam(a: Address) =<cloref1> a._zip
      val zip_set: cfun(Address, cfun(int, Address)) =
        lam(a: Address) =<cloref1>
          lam(x: int) =<cloref1> '{ _street = a._street
                                  , _zip = x }
  in '{get = zip_get, set = zip_set} end

(* We now apply a function over a composite lens: *)
val
john = '{ _name = "John"
        , _age = 23
        , _address = '{ _street = "venusbergstrasse"
                      , _zip = 123 }}: Person

fn
add3(x: int):<cloref1> int = x + 3

val
john = over<Person, int>(address::zip, add3)(john)

(* Lenses are much more general and flexible than the above example
 * showcases. In particular, they interplay nicely with functors, as 
 * implemented in the following code:
 *
 * typedef
 * Fun(F: t0p -> t0p) = {a, b: t0p} cfun(a, b) -<cloref1> cfun(F(a), F(b))
 * typedef
 * Fun = [F: t0p -> t0p] Fun(F)
 * 
 * fn{a, b: t0p}{F: t0p -> t0p}
 * over_functor
 * ( ln: Lens(a, b)
 * , F_map: Fun(F)
 * , f: cfun(b, F(b)) ):<cloref1>
 * cfun(a, F(a)) =
 *   lam(x) => F_map(ln.set(x))(f(ln.get(x)))
 *)
implement
main0() = println!(john._address._zip)
