-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/PlusDoorA.lean: THE BRIDGE OF Johnson/Desc/Sound/PlusDoor.lean IN THE FORM IN
WHICH A KIND's FILES CALL IT: the wider filling parts from the narrower at a class of public items
alone. Definitions, and statements with their proofs; free of any kind of sub-protocol.
  cA : Pub → Bool: the class of the names that have left the door.
  `doorsFitB M₀ M cA links ps k`: A TEST WITH CODE ON THE TWO DOORS at border k: every public item
  that is open at the narrower door M₀ is open at the wider M and is not of the class; every one
    that is open at M is of the class or open at M₀; no public item that is tied to an open item
    is of the class.
  `FactsAt Mg pub' io' M cA links ps get k a`: WHAT THE CONDITION Rch IS TO GIVE at border k, at a
  state
    without a mark: the wider "in order" wherever Mg's holds; each item of the class that is open at
    M passes the wider test, and says what it says beside its test.
  `onQ_down_A`, `onQ_up_A`: the promise goes down; it goes up under `FactsAt`.
  `tiedAtR_of_classA`: **THE BRIDGE, AS A CALL**: a tie at `widen Mg M pub' io'` is a tie in the
  second form at Mg, WHERE: outside the class the wider tests are Mg's (hhand); the wider "in
    order" gives Mg's (hio); `doorsFitB` accepts at borders k and k + 1; Rch gives `FactsAt` at
    both; Rch is handed on over the piece.
What is not claimed. `FactsAt` anywhere. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PlusDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Pub More Meaning Numbers pubSets pubOfItems openSets
  start)

/-- **The test on the two doors** at border k. -/
def doorsFitB (M₀ M : More) (cA : Pub → Bool) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  (((pubSets M₀ links ps)[k]?.getD []).all fun q =>
      ((pubSets M links ps)[k]?.getD []).contains q && !cA q) &&
    (((pubSets M links ps)[k]?.getD []).all fun q =>
      cA q || ((pubSets M₀ links ps)[k]?.getD []).contains q) &&
    ((pubOfItems ((openSets links ps (start links))[k]?.getD [])).all fun q => !cA q)

theorem doorsFitB_parts {M₀ M : More} {cA : Pub → Bool} {links : List ModelPart} {ps : List Place}
    {k : ℕ} (h : doorsFitB M₀ M cA links ps k = true) :
    (∀ q ∈ (pubSets M₀ links ps)[k]?.getD [],
        q ∈ (pubSets M links ps)[k]?.getD [] ∧ cA q = false) ∧
      (∀ q ∈ (pubSets M links ps)[k]?.getD [],
        cA q = true ∨ q ∈ (pubSets M₀ links ps)[k]?.getD []) ∧
      ∀ q ∈ pubOfItems ((openSets links ps (start links))[k]?.getD []), cA q = false := by
  unfold doorsFitB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · have := List.all_eq_true.1 h1 q hq
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact ⟨List.contains_iff_mem.1 this.1, this.2⟩
  · have := List.all_eq_true.1 h2 q hq
    simp only [Bool.or_eq_true] at this
    exact this.imp id List.contains_iff_mem.1
  · have := List.all_eq_true.1 h3 q hq
    simpa using this

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (M : More)
  (pub' : Pub → P × First.S → Bool) (io' : P × First.S → Bool) (cA : Pub → Bool)
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S)

/-- **What the condition beside the promise is to give** at border k. -/
def FactsAt (k : ℕ) (a : A × Fr.E.Str) : Prop :=
  (get a.1).2.failed = none →
    (Mg.inOrder (get a.1) = true → io' (get a.1) = true) ∧
      ∀ q ∈ (pubSets M links ps)[k]?.getD [], cA q = true →
        pub' q (get a.1) = true ∧ Mg.pubP q (get a.1)

theorem onQ_down_A (k : ℕ) (a : A × Fr.E.Str)
    (hhand : ∀ q, cA q = false → ∀ x, pub' q x = Mg.pub q x)
    (hio : ∀ x, io' x = true → Mg.inOrder x = true)
    (hD : doorsFitB Mg.more M cA links ps k = true)
    (h : onQ N (widen Mg M pub' io') links ps get k a) : onQ N Mg links ps get k a := by
  obtain ⟨d1, _, d3⟩ := doorsFitB_parts hD
  refine onQ_down N Mg M pub' io' links ps get k a (fun q hq => (d1 q hq).1) (hio _)
    (fun q hq h0 => ?_) h
  rcases List.mem_append.1 hq with hq | hq
  · rw [← hhand q (d1 q hq).2]
    exact h0
  · rw [← hhand q (d3 q hq)]
    exact h0

theorem onQ_up_A (k : ℕ) (a : A × Fr.E.Str)
    (hhand : ∀ q, cA q = false → ∀ x, pub' q x = Mg.pub q x)
    (hD : doorsFitB Mg.more M cA links ps k = true)
    (hF : FactsAt Mg M pub' io' cA links ps get k a) (h : onQ N Mg links ps get k a) :
    onQ N (widen Mg M pub' io') links ps get k a := by
  obtain ⟨_, d2, d3⟩ := doorsFitB_parts hD
  refine onQ_up N Mg M pub' io' links ps get k a (fun hm => (hF hm).1) (fun hm hall q hq => ?_)
    (fun hm hP q hq => ?_) h
  · rcases List.mem_append.1 hq with hq | hq
    · cases hc : cA q with
      | true => exact ((hF hm).2 q hq hc).1
      | false =>
        rw [hhand q hc]
        refine hall q (List.mem_append_left _ ((d2 q hq).resolve_left ?_))
        rw [hc]
        exact Bool.false_ne_true
    · rw [hhand q (d3 q hq)]
      exact hall q (List.mem_append_right _ hq)
  · cases hc : cA q with
    | true => exact ((hF hm).2 q hq hc).2
    | false =>
      refine hP q ((d2 q hq).resolve_left ?_)
      rw [hc]
      exact Bool.false_ne_true

/-- **THE BRIDGE, AS A CALL.** -/
theorem tiedAtR_of_classA (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ) (q : Piece C Fr A Cl W)
    (hhand : ∀ i, cA i = false → ∀ x, pub' i x = Mg.pub i x)
    (hio : ∀ x, io' x = true → Mg.inOrder x = true)
    (hD : doorsFitB Mg.more M cA links ps k = true)
    (hD' : doorsFitB Mg.more M cA links ps (k + 1) = true)
    (hF : ∀ j a, Rch j a → FactsAt Mg M pub' io' cA links ps get j a) (hs : HandsOn Rch k q)
    (h : TiedAt N (widen Mg M pub' io') links ps get k q) : TiedAtR N Mg links ps get Rch k q :=
  tiedAtR_of_widen N Mg M pub' io' links ps get Rch k q
    (fun b => onQ_down_A N Mg M pub' io' cA links ps get (k + 1) b hhand hio hD')
    (fun a hr => onQ_up_A N Mg M pub' io' cA links ps get k a hhand hD (hF k a hr))
    (fun b hr => onQ_up_A N Mg M pub' io' cA links ps get (k + 1) b hhand hD' (hF (k + 1) b hr))
    hs h

end

end VerifiableInference.Desc.Sound
