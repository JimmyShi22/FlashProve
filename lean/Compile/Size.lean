-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Size.lean: parts of the serialization of a compiled proof as a string of bits, and upper
bounds on their lengths (words of this library: lean/GLOSSARY.md).

  `EntR`, `EntS`, `EntE`         Opened positions with their openings.
  `serEntR`, `serEntS`, `serPlains`
                                 The serializers of `EntR`, `EntS` and of the plain parts; an opened
                                 position is encoded as (position, symbol), salt, path.
  `entriesE`                     The list of the opened external positions (`mem_entriesE`,
                                 `entriesE_injective`: under `we.OK` the list determines the
                                 openings).
  `FitsEnt`                      In each round: at most o_r opened positions, each with a salt of at
                                 most sMT bits and a path of at most depth_r digests.
  `ExtNums`                      The numbers of the external openings: how many at most; the bits of
                                 (position, symbol); the depth of the trees.
  `length_put_serBits_le`, `length_put_serDigs_le`, `length_put_serEntR_le`,
  `length_put_serPlains_le`, `length_put_option_le`
                                 Bounds on the lengths of these encodings, in bits. Lists and
                                 strings of bits have a length prefix (`lenList`, `natG`,
                                 Iop/Ser.lean).

Notation: o_r, depth_r (the row of `FitsEnt`): in Lean the round's number n of the `OpenList`
(Iop/SerS.lean: "For each round a number: how many positions of its oracle are opened at most.") and
`w.depth` of the round's `WireR` (Iop/Wire.lean); external: of an `ExtSpec` (Iop/InteractiveOracleProof.lean):
"External strings: oracles that are fixed before the first message."; the plain parts: `Plains`
(Iop/Shape.lean): "The plain parts of all prover messages."; `sMT`: a natural number: the most bits
of a salt (`FitsEnt`); `K`: a natural number; "how K hash blocks give its challenge" (`WireR`,
Iop/Wire.lean).

Limits: it does not define the serialization of a verification key or of a proof, and does not bound
their sizes.
-/
import Compile.Ser
import Compile.Star
import Iop.Sizes

set_option autoImplicit false

namespace Compile
open Iop Rom

variable {I X : Type} {lam K : ℕ}

/-! ## Part 1. The serializers -/

/-- an opened position of a round, with its opening -/
abbrev EntR (lam : ℕ) (r : Round) : Type := Σ p : r.Pos, Opening lam (r.Sym p)

def serEntR (lam : ℕ) {r : Round} (a : Ser (Σ p : r.Pos, r.Sym p)) : Ser (EntR lam r) :=
  Ser.ofEquiv (β := (Σ p : r.Pos, r.Sym p) × Bits × List (Dig lam))
    ⟨fun e => (⟨e.1, e.2.sym⟩, e.2.salt, e.2.path),
      fun y => ⟨y.1.1, ⟨y.1.2, y.2.1, y.2.2⟩⟩,
      fun _ => rfl, fun _ => rfl⟩
    (Ser.prod a (Ser.prod serBits (serDigs lam)))

/-- for each round the list of its opened positions -/
def EntS (lam : ℕ) : Shape → Type
  | [] => Unit
  | r :: s => List (EntR lam r) × EntS lam s

def serEntS (lam : ℕ) : (s : Shape) → SerS s → Ser (EntS lam s)
  | [], _ => Ser.unit
  | _ :: s, ((a, _), e) => Ser.prod (Ser.lenList (serEntR lam a)) (serEntS lam s e)

def serPlains : (s : Shape) → SerS s → Ser (Plains s)
  | [], _ => Ser.unit
  | _ :: s, ((_, b), e) => Ser.prod b (serPlains s e)


/-- an opened external position, with its opening -/
abbrev EntE (lam : ℕ) (E : ExtSpec) : Type := E.Pos × Opening lam E.Sym

def entriesE {E : ExtSpec} (we : WireE E) (g : E.Pos → Option (Opening lam E.Sym)) :
    List (EntE lam E) :=
  we.all.filterMap fun p => (g p).map fun op => (p, op)

/-! ### Under `we.OK` the list determines the openings -/


theorem mem_entriesE {E : ExtSpec} {we : WireE E} (hw : we.OK)
    (g : E.Pos → Option (Opening lam E.Sym)) (p : E.Pos) (op : Opening lam E.Sym) :
    ((p, op) : EntE lam E) ∈ entriesE we g ↔ g p = some op := by
  unfold entriesE
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p', -, hp'⟩
    obtain ⟨op', hop, he⟩ := Option.map_eq_some_iff.1 hp'
    cases he
    exact hop
  · intro h
    exact ⟨p, hw.complete p, by rw [h, Option.map_some]⟩

theorem entriesE_injective {E : ExtSpec} {we : WireE E} (hw : we.OK)
    {g g' : E.Pos → Option (Opening lam E.Sym)} (h : entriesE we g = entriesE we g') : g = g' := by
  funext p
  refine Option.ext fun op => ?_
  rw [← mem_entriesE hw g, ← mem_entriesE hw g', h]

/-! ## Part 2. What fits, and the bounds -/

open Ser (gam)


/-- In each round: at most o_r opened positions, each with a salt of at most sMT bits and a path of
at most depth_r digests. -/
def FitsEnt (sMT : ℕ) : (s : Shape) → WireS lam K s → OpenList s → EntS lam s → Prop
  | [], _, _, _ => True
  | _ :: s, (w, W), (n, o), (l, e) =>
      l.length ≤ n ∧
      (∀ x ∈ l, x.2.salt.length ≤ sMT ∧ x.2.path.length ≤ w.depth) ∧
      FitsEnt sMT s W o e

theorem length_put_serBits_le {b : Bits} {n : ℕ} (h : b.length ≤ n) :
    (serBits.put b).length ≤ gam n + n * 1 :=
  Ser.length_put_lenList_le_gam Ser.bool h fun _ _ => le_rfl

theorem length_put_serDigs_le {l : List (Dig lam)} {n : ℕ} (h : l.length ≤ n) :
    ((serDigs lam).put l).length ≤ gam n + n * lam :=
  Ser.length_put_lenList_le_gam (serDig lam) h fun v _ => le_of_eq (Ser.length_put_bits lam v)

theorem length_put_serEntR_le {r : Round} (a : Ser (Σ p : r.Pos, r.Sym p))
    {x sMT d : ℕ} (ha : ∀ z, (a.put z).length ≤ x) (e : EntR lam r)
    (h1 : e.2.salt.length ≤ sMT) (h2 : e.2.path.length ≤ d) :
    ((serEntR lam a).put e).length ≤ entBits lam sMT d x := by
  unfold serEntR entBits
  rw [Ser.length_put_ofEquiv, Ser.length_put_prod, Ser.length_put_prod]
  exact Nat.add_le_add (ha _) (Nat.add_le_add (length_put_serBits_le h1) (length_put_serDigs_le h2))

theorem length_put_serPlains_le :
    ∀ (s : Shape) (S : SerS s) (b : BitsS s) (pl : Plains s),
      SerS.Within s S b → ((serPlains s S).put pl).length ≤ BitsS.plainBits s b
  | [], _, _, _, _ => Nat.le_refl _
  | _ :: s, ((_, c), S), ((_, y), b), (p, pl), hS => by
      show ((Ser.prod c (serPlains s S)).put (p, pl)).length ≤ _
      rw [Ser.length_put_prod]
      exact Nat.add_le_add (hS.2.1 p) (length_put_serPlains_le s S b pl hS.2.2)

/-- the numbers of the external openings: how many at most; the bits of (position, symbol); the
depth of the trees -/
structure ExtNums where
  n : ℕ
  x : ℕ
  d : ℕ

/-! ### Options -/

section Scheme

variable (p : Params)





theorem length_put_option_le
    {α : Type} (A : Ser α) {n : ℕ} (x : Option α) (h : ∀ a, x = some a → (A.put a).length ≤ n) :
    ((Ser.option A).put x).length ≤ n + 1 := by
  cases x with
  | none => rw [Ser.length_put_none]; omega
  | some a => rw [Ser.length_put_some]; exact Nat.add_le_add_right (h a rfl) 1




end Scheme

end Compile
