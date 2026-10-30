-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpRe2.lean: the data of an assembled lookup `LkAsm2` (Cb/Ld/LdLkpAsm2.lean), set among more
entries, with other states, keys and table.
An assembled lookup: the lookup sub-protocol put together from its parts, as one chain.
This file is book-keeping on places: it re-indexes the data of a lookup argument that is one block
among several of a larger protocol.

Definitions, statements and proofs. Auxiliary definitions and lemmas for instances; no protocol.

Why: the data `A : LkAsm2 E` hold numbers, the entries J, twelve families of places in J, four
fields on the order of rounds, and states, keys, table.
A protocol in which the lookup is one block among several has more entries (the
other blocks' data and masks), and may run the lookup with other states and keys (after a random
shift: states (state, shift), shifted keys).

Main names:
  `A.re St' J' e key' tab'`: the same numbers and orders of rounds; the places carried along
    e : A.J → J'; states St', keys key', table tab'. Nothing is asked of e, key', tab'.
  `re2_placesIn`: all named places of A in the range of ι ⇒ those of `A.re ..` in the range of
    e ∘ ι.
  `re2_nm`, `re2_plN`: the names of the own masks that are played (`LkAsm2.Nm`,
    Cb/Ld/LdLkpMaskPlaces2.lean) are the same; the place of a name is carried along e.
  `re2_placesOK`: the four plain conditions on places (`LkAsm2.PlacesOK`,
    Cb/Ld/LdLkpMaskPlaces2.lean) hold of `A.re ..` at Dt' (Dt, Dt': sets of entries, "the data", of
    A and of `A.re ..`), if:
      `he`: e injective;
      `hinj`, `hout`: A's own masks pairwise apart, outside Dt;
      `hbits`: bits in Dt;
      `h1`, `h2`: Dt' holds e of Dt and meets the range of e in nothing else;
      `hk`: key' reads Dt' only.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskPlaces2
import Cb.Ld.LdLkpAsm2Pull

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

variable {E : Type} [Field E] [Fintype E]

/-- The same lookup among more entries, with other states, keys and table. -/
def LkAsm2.re (A : LkAsm2 E) (St' J' : Type) [Fintype J'] (e : A.J → J')
    (key' : St' → (J' → E) → ℕ → E) (tab' : St' → ℕ → E) : LkAsm2 E where
  St := St'
  J := J'
  v' := A.v'
  d := A.d
  w := A.w
  n := A.n
  key := key'
  tab := tab'
  bAt := fun u j => e (A.bAt u j)
  wS := fun i => e (A.wS i)
  cS := fun b => e (A.cS b)
  wAt := fun l i => e (A.wAt l i)
  cAt := fun l b => e (A.cAt l b)
  wK := fun l i => e (A.wK l i)
  cK := fun l b => e (A.cK l b)
  wT := fun l i => e (A.wT l i)
  cT := fun l b => e (A.cT l b)
  wE := fun i => e (A.wE i)
  wB := fun i => e (A.wB i)
  cB := e A.cB
  oK := A.oK
  oT := A.oT
  oE := A.oE
  oB := A.oB

section
variable (A : LkAsm2 E) {St' J' : Type} [Fintype J'] (e : A.J → J')
  (key' : St' → (J' → E) → ℕ → E) (tab' : St' → ℕ → E)

theorem re2_placesIn {N : Type} (ι : N → A.J) (h : A.PlacesIn fun j => j ∈ Set.range ι) :
    (A.re St' J' e key' tab').PlacesIn fun j => j ∈ Set.range fun n => e (ι n) where
  bAt := fun u j => (h.bAt u j).elim fun n hn => ⟨n, congrArg e hn⟩
  wS := fun i => (h.wS i).elim fun n hn => ⟨n, congrArg e hn⟩
  cS := fun b => (h.cS b).elim fun n hn => ⟨n, congrArg e hn⟩
  wAt := fun l i => (h.wAt l i).elim fun n hn => ⟨n, congrArg e hn⟩
  cAt := fun l b => (h.cAt l b).elim fun n hn => ⟨n, congrArg e hn⟩
  wK := fun l i => (h.wK l i).elim fun n hn => ⟨n, congrArg e hn⟩
  cK := fun l b => (h.cK l b).elim fun n hn => ⟨n, congrArg e hn⟩
  wT := fun l i => (h.wT l i).elim fun n hn => ⟨n, congrArg e hn⟩
  cT := fun l b => (h.cT l b).elim fun n hn => ⟨n, congrArg e hn⟩
  wE := fun i => (h.wE i).elim fun n hn => ⟨n, congrArg e hn⟩
  wB := fun i => (h.wB i).elim fun n hn => ⟨n, congrArg e hn⟩
  cB := h.cB.elim fun n hn => ⟨n, congrArg e hn⟩

/-- the map of names: each own mask's name to the same name of A -/
def re2_nm : (A.re St' J' e key' tab').Nm → A.Nm
  | .s i => .s i
  | .t l h i => .t l h i
  | .k l h i => .k l h i
  | .f l h i => .f l h i
  | .e i => .e i
  | .b i => .b i

theorem re2_nm_inj : Function.Injective (re2_nm A e key' tab') := by
  rintro (i | ⟨l, h, i⟩ | ⟨l, h, i⟩ | ⟨l, h, i⟩ | i | i)
      (i' | ⟨l', h', i'⟩ | ⟨l', h', i'⟩ | ⟨l', h', i'⟩ | i' | i') hh
    <;> simp only [re2_nm] at hh <;> first
    | (cases hh; rfl)
    | exact absurd hh (by simp)

theorem re2_plN (x : (A.re St' J' e key' tab').Nm) :
    (A.re St' J' e key' tab').plN x = e (A.plN (re2_nm A e key' tab' x)) := by
  rcases x with (i | b) | ⟨l, h, (i | b)⟩ | ⟨l, h, (i | b)⟩ | ⟨l, h, (i | b)⟩ | i | (i | b) <;> rfl

theorem re2_placesOK (he : Function.Injective e) {Dt : A.J → Prop} {Dt' : J' → Prop}
    (hinj : Function.Injective A.plN) (hout : ∀ i, ¬ Dt (A.plN i)) (hbits : ∀ u j, Dt (A.bAt u j))
    (h1 : ∀ j, Dt j → Dt' (e j)) (h2 : ∀ j, Dt' (e j) → Dt j)
    (hk : ∀ st m m', (∀ j, Dt' j → m j = m' j) → key' st m = key' st m') :
    (A.re St' J' e key' tab').PlacesOK Dt' where
  inj := fun x y h => by
    rw [re2_plN, re2_plN] at h
    exact re2_nm_inj A e key' tab' (hinj (he h))
  out := fun i h => by
    rw [re2_plN] at h
    exact hout _ (h2 _ h)
  bits := fun u j => h1 _ (hbits u j)
  keys := hk

end
end Cb.LdLkp
