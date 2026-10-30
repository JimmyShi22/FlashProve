-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TiedPlaces.lean: THE CHAIN OF PROMISES IS PAID PLACE BY PLACE. A rule over
letters. NO RESULT ON THE PROTOCOL.

What is said. `EachTied` (Johnson/Desc/Sound/ChainOfPromises.lean) is a conjunction along a list of
pieces; the end theorems ask it at the list with the table's extractor laid in (`reExt`,
Johnson/Desc/Sound/ReExt.lean).
  **`eachTied_of_places`**: if at every number i the piece that stands there, with the extractor of
    border k₀ + i laid in, is tied at k₀ + i, then the whole list is: SO A KIND's FILES PAY ITS OWN
    PLACES, and whoever holds all places' ties has the field.
  `tiedAt_of_each`: the converse, at one number.
  `eachTied_at_id`: the same from ties at the kinds' reader of the record (the
    identity) to the end theorems' reader at getS := id.
  `KindTied … K`, `eachTied_of_kinds` (from K3's files: kind-free):
    one kind's share of the field; the field from all kinds' shares, where the list of pieces is no
    longer than the list of places.

Limits. Nothing is said of any block. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ChainOfPromises
import Johnson.Desc.Sound.ReExt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S)
  (E : ℕ → A × Fr.E.Str → A × Fr.E.Str → W → W)

/-- **Place by place.** -/
theorem eachTied_of_places : ∀ (l : List (Piece C Fr A Cl W)) (k₀ : ℕ),
    (∀ i q, l[i]? = some q → TiedAt N Mg links ps get (k₀ + i) (q.withMap (E (k₀ + i)))) →
    EachTied N Mg links ps get k₀ (reExt E k₀ l)
  | [], _, _ => trivial
  | p :: l, k₀, h =>
    ⟨h 0 p rfl, eachTied_of_places l (k₀ + 1) fun i q hq => by
      have := h (i + 1) q (by simpa using hq)
      rwa [show k₀ + (i + 1) = k₀ + 1 + i by omega] at this⟩

/-- The converse, at one number. -/
theorem tiedAt_of_each : ∀ (l : List (Piece C Fr A Cl W)) (k₀ : ℕ),
    EachTied N Mg links ps get k₀ (reExt E k₀ l) → ∀ i q, l[i]? = some q →
    TiedAt N Mg links ps get (k₀ + i) (q.withMap (E (k₀ + i)))
  | [], _, _, _, _, hq => by simp at hq
  | p :: l, k₀, h, 0, q, hq => by
    have e : p = q := by simpa using hq
    subst e
    exact h.1
  | p :: l, k₀, h, i + 1, q, hq => by
    have := tiedAt_of_each l (k₀ + 1) h.2 i q (by simpa using hq)
    rwa [show k₀ + 1 + i = k₀ + (i + 1) by omega] at this

/-- **From the kinds' letters to the end theorems' field**, where the chain's record IS the
table's: the kinds tie at the identity as the reader of the record; the end theorems' field reads
`fun a => (a.1, getS a.2)`: at getS := id the two are one (pairs' eta); the count starts at 0. -/
theorem eachTied_at_id (E' : ℕ → (P × First.S) × Fr.E.Str → (P × First.S) × Fr.E.Str → W → W)
    (l : List (Piece C Fr (P × First.S) Cl W))
    (h : ∀ i q, l[i]? = some q → TiedAt N Mg links ps (fun a => a) i (q.withMap (E' i))) :
    EachTied N Mg links ps (fun a : P × First.S => ((a.1, id a.2) : P × First.S)) 0
      (reExt E' 0 l) :=
  eachTied_of_places N Mg links ps _ E' l 0 fun i q hq => by
    rw [Nat.zero_add]
    exact h i q hq

section
variable (E : ℕ → (P × First.S) × Fr.E.Str → (P × First.S) × Fr.E.Str → W → W)
  (l : List (Piece C Fr (P × First.S) Cl W))

/-- **One kind's share of the chain of promises.** -/
def KindTied (K : KindName) : Prop :=
  ∀ i q a, l[i]? = some q → ps[i]? = some a → a.kind = K →
    TiedAt N Mg links ps (fun a => a) i (q.withMap (E i))

/-- **The field, kind by kind.** -/
theorem eachTied_of_kinds (hlen : l.length ≤ ps.length)
    (H : ∀ K, KindTied N Mg links ps E l K) :
    EachTied N Mg links ps (fun a : P × First.S => ((a.1, id a.2) : P × First.S)) 0 (reExt E 0 l) :=
  eachTied_at_id N Mg links ps E l fun i q hq => by
    have hi : i < l.length := (List.getElem?_eq_some_iff.1 hq).1
    have hp : i < ps.length := Nat.lt_of_lt_of_le hi hlen
    exact H _ i q ps[i] hq (List.getElem?_eq_getElem hp) rfl


end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.eachTied_of_kinds
#print axioms VerifiableInference.Desc.Sound.eachTied_at_id
#print axioms VerifiableInference.Desc.Sound.eachTied_of_places
#print axioms VerifiableInference.Desc.Sound.tiedAt_of_each
