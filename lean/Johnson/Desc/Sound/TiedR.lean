-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
lean/Johnson/Desc/Sound/TiedR.lean: THE FRAME OF THE CHAIN OF PROMISES IN ITS SECOND FORM: WITH A
    CONDITION Rch BESIDE THE TABLE'S PROMISE AT EVERY BORDER
(meant: "this verifier's state is reached from the state at the start by the sub-protocols in front"
    ). Over
Johnson/Desc/Sound/ChainOfPromisesR.lean (`onR`, `TiedAtR`, `HandsOn`,
    `EachTiedR`). The first forms
(TiedBy.lean, TiedPlaces.lean) stand unturned beside; each gives its second form for nothing.
  `TiedByR`: `TiedBy` with Rch k a one premise more in each of the five ties. `TiedByR.tiedAtR`.
      `TiedBy.toR`.
  `handsOn_withMap`: laying another extractor into a piece does not touch
      "an accepting run hands Rch on" .
  `eachTiedR_of_places`, `eachTiedR_at_id`: place by place.
  **`KindTiedR`**: one kind's share, second form. `KindTied.toR`: the first form gives it.
  **`eachTiedR_of_kinds`**: all kinds' shares and "every piece hands Rch on" give the chain's
      premise `EachTiedR`, where the list of pieces is no longer than the list of places (hlen).
Limits. General in Rch: no Rch is named here. A rule over letters: no member.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ChainOfPromisesR
import Johnson.Desc.Sound.TiedPlaces
import Johnson.Desc.Sound.TiedBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop)

/-- **`TiedAtR` with the kind's own words named.** -/
def TiedByR (k : ℕ) (q : Piece C Fr A Cl W) (o o' : A × Fr.E.Str → Prop)
    (R R' : A × Fr.E.Str → W → Prop) : Prop :=
  q.GoodIn o o' R R' ∧
    (∀ a, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none → o a) ∧
    (∀ a τ b, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → onQ N Mg links ps get (k + 1) b) ∧
    (∀ a τ b w, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R' b w) ∧
    (∀ a τ b w, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w)) ∧
    (∀ a τ b w i, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
      relQ N Mg links ps get (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i a (q.ext a τ w)) ∧
    (∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none) ∧
    (∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2))

theorem TiedByR.tiedAtR {k : ℕ} {q : Piece C Fr A Cl W} {o o' : A × Fr.E.Str → Prop}
    {R R' : A × Fr.E.Str → W → Prop} (h : TiedByR N Mg links ps get Rch k q o o' R R') :
    TiedAtR N Mg links ps get Rch k q := ⟨o, o', R, R', h⟩

/-- The first form gives the second for nothing. -/
theorem TiedBy.toR {k : ℕ} {q : Piece C Fr A Cl W} {o o' : A × Fr.E.Str → Prop}
    {R R' : A × Fr.E.Str → W → Prop} (h : TiedBy N Mg links ps get k q o o' R R') :
    TiedByR N Mg links ps get Rch k q o o' R R' := by
  obtain ⟨hl, t1, t2, t3, t4, t5, hMark, hDec⟩ := h
  exact ⟨hl, fun a ha _ => t1 a ha, fun a τ b ha _ => t2 a τ b ha,
    fun a τ b w ha _ => t3 a τ b w ha, fun a τ b w ha _ => t4 a τ b w ha,
    fun a τ b w i ha _ => t5 a τ b w i ha, hMark, hDec⟩

/-- Another extractor in the piece: the hand-on stays. -/
theorem handsOn_withMap {k : ℕ} {q : Piece C Fr A Cl W}
    (e : A × Fr.E.Str → A × Fr.E.Str → W → W) (h : HandsOn Rch k q) :
    HandsOn Rch k (q.withMap e) := fun a τ b ha hb => h a τ b ha hb

variable (E : ℕ → A × Fr.E.Str → A × Fr.E.Str → W → W)

/-- **Place by place.** -/
theorem eachTiedR_of_places : ∀ (l : List (Piece C Fr A Cl W)) (k₀ : ℕ),
    (∀ i q, l[i]? = some q → TiedAtR N Mg links ps get Rch (k₀ + i) (q.withMap (E (k₀ + i))) ∧
      HandsOn Rch (k₀ + i) q) →
    EachTiedR N Mg links ps get Rch k₀ (reExt E k₀ l)
  | [], _, _ => trivial
  | p :: l, k₀, h =>
    ⟨(h 0 p rfl).1, handsOn_withMap Rch _ (h 0 p rfl).2,
      eachTiedR_of_places l (k₀ + 1) fun i q hq => by
        have := h (i + 1) q (by simpa using hq)
        rwa [show k₀ + (i + 1) = k₀ + 1 + i by omega] at this⟩

end

section
variable {Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place) (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop)
  (E : ℕ → (P × First.S) × Fr.E.Str → (P × First.S) × Fr.E.Str → W → W)
  (l : List (Piece C Fr (P × First.S) Cl W))

/-- From the kinds' letters to the end theorems' field, where the chain's state IS the table's. -/
theorem eachTiedR_at_id
    (h : ∀ i q, l[i]? = some q → TiedAtR N Mg links ps (fun a => a) Rch i (q.withMap (E i)) ∧
      HandsOn Rch i q) :
    EachTiedR N Mg links ps (fun a : P × First.S => ((a.1, id a.2) : P × First.S)) Rch 0
      (reExt E 0 l) :=
  eachTiedR_of_places N Mg links ps _ Rch E l 0 fun i q hq => by
    rw [Nat.zero_add]
    exact h i q hq

/-- **One kind's share of the chain of promises, second form.** -/
def KindTiedR (K : KindName) : Prop :=
  ∀ i q a, l[i]? = some q → ps[i]? = some a → a.kind = K →
    TiedAtR N Mg links ps (fun a => a) Rch i (q.withMap (E i))

/-- The first form gives the second for nothing. -/
theorem KindTied.toR {K : KindName} (h : KindTied N Mg links ps E l K) :
    KindTiedR N Mg links ps Rch E l K :=
  fun i q a hq ha hk => tiedAtR_of_tiedAt N Mg links ps _ Rch i _ (h i q a hq ha hk)

/-- **The field, kind by kind, second form.** -/
theorem eachTiedR_of_kinds (hlen : l.length ≤ ps.length)
    (H : ∀ K, KindTiedR N Mg links ps Rch E l K)
    (hH : ∀ i q, l[i]? = some q → HandsOn Rch i q) :
    EachTiedR N Mg links ps (fun a : P × First.S => ((a.1, id a.2) : P × First.S)) Rch 0
      (reExt E 0 l) :=
  eachTiedR_at_id N Mg links ps Rch E l fun i q hq => by
    have hi : i < l.length := (List.getElem?_eq_some_iff.1 hq).1
    have hp : i < ps.length := Nat.lt_of_lt_of_le hi hlen
    exact ⟨H _ i q ps[i] hq (List.getElem?_eq_getElem hp) rfl, hH i q hq⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.TiedBy.toR
#print axioms VerifiableInference.Desc.Sound.handsOn_withMap
#print axioms VerifiableInference.Desc.Sound.eachTiedR_of_places
#print axioms VerifiableInference.Desc.Sound.KindTied.toR
#print axioms VerifiableInference.Desc.Sound.eachTiedR_of_kinds
