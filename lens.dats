#include "share/atspre_staload.hats"
#staload "libats/ML/SATS/basis.sats"

(* ****** ****** ****** *)

// This file gives a primitive implementation of lenses in ATS
// and shows an exemplifying use case. Lenses are a functional
// way of doing "dot notation with updates" on immutable tuples
// and records. It can be regarded as a functorial dot notation.

// Compile with:
// $ patscc -O2 -D_GNU_SOURCE -DATS_MEMALLOC_GCBDW -lgc -o lens lens.dats

(* ****** ****** ****** *)

(* A "lens" from [a] to [b] is a "get" and a "set" function, 
 * abstracting the idea that [a] is a record with a field of
 * type [b]. 
 *)
abstype
Lens_type(a: t0p, b: t0p)

typedef
Lens(a: t0p, b: t0p) = Lens_type(a, b) 

extern fun{a, b: t0p}
lens_get(Lens(a, b), a): b

extern fun{a, b: t0p}
lens_set(Lens(a, b), a, b): a

extern fun{a, b: t0p}
lens_make(get: cfun(a, b), set: cfun(a, b, a)): Lens(a, b)

local 
  assume 
  Lens_type(a: t0p, b: t0p) = '(cfun(a, b), cfun(a, b, a))
in
  implement{a, b}
  lens_get(lns, x) = lns.0(x)

  implement{a, b}
  lens_set(lns, x, y) = lns.1(x, y)

  implement{a, b}
  lens_make(get, set) = '(get, set)
end

overload .get with lens_get
overload .set with lens_set

(* Functions can be applied "over" a lens, abstracting the idea
 * that a function can be applied to a single field in a record.
 *)
fn{a, b: t0p}
over
( lns: Lens(a, b)
, fopr: cfun(b, b) ):
cfun(a, a) =
  lam(x) => lns.set(x, fopr(lns.get(x)))

(* Lenses compose, like functions. Note that the order is the
 * order of dot notation!
 *)
fn{a, b, c: t0p}
lens_compose
( lns1: Lens(a, b)
, lns2: Lens(b, c) ):
Lens(a, c) =
  lens_make
  ( lam(x) => lns2.get(lns1.get(x))
  , lam(x, z) => lns1.set(x, lns2.set(lns1.get(x), z)) )

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
      val address_set: cfun(Person, Address, Person) =
        lam(p: Person, a: Address) =<cloref1> '{ _name = p._name
                                               , _age = p._age
                                               , _address = a }
  in lens_make(address_get, address_set) end

val
zip: Lens(Address, int) =
  let val zip_get: cfun(Address, int) =
        lam(a: Address) =<cloref1> a._zip
      val zip_set: cfun(Address, int, Address) =
        lam(a: Address, x: int) =<cloref1> '{ _street = a._street
                                            , _zip = x }
  in lens_make(zip_get, zip_set) end

(* We now apply a function over a composite lens: *)
val
john = '{ _name = "John"
        , _age = 23
        , _address = '{ _street = "Venusbergstrasse"
                      , _zip = 123 }}: Person

val
john = over(address::zip, lam(x) => x + 3)(john)

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
 * ( lns: Lens(a, b)
 * , F_map: Fun(F)
 * , fopr: cfun(b, F(b)) ):
 * cfun(a, F(a)) =
 *   lam(x) => F_map(lam(y) => lns.set(x, y))(fopr(lns.get(x)))
 *)
implement
main0() = println!((address::zip).get(john))
