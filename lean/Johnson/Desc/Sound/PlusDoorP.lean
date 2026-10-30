-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/PlusDoorP.lean: THE BRIDGE OF Johnson/Desc/Sound/PlusDoor.lean AND
PlusDoorA.lean AT A WIDER FILLING THAT TURNS `pubP` TOO: what a public item says beside its test.
ADDITIVE: `widen` and whatever stands on it do not turn. A definition, and statements with their
proofs; free of any kind of sub-protocol. Why. `widen Mg M pub' io'` leaves `pubP`: so the facts
that the bridge asks under the condition beside the promise hold "`Mg.pubP q`" at every item of
the class that is open at the wider door; at a filling whose `pubP` is False at a name that it
does not know nobody could pay that. `widenP Mg M pub' pubP' io'`: the filling with another door,
  other tests, other sentences beside them and another "in order". `FactsAtP`: what the condition
  is to give at border k, at a state without a mark: Mg's "in order" gives the wider; each item of
  the class that is open at M passes the wider test AND THE WIDER SENTENCE. `onQ_down_P`,
  `onQ_up_P`: the promise from the wider filling to the narrower and back, from the test on the
  two doors (`doorsFitB`) and: outside the class the wider tests and the wider sentences are Mg's.
  `tiedAtR_of_classAP`: **THE BRIDGE, AS A CALL**: by `tiedAtR_of_wider`, which is general in the
  wider filling. The facts are asked at the sub-protocol's two borders alone.
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PlusDoorA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Pub More Meaning Numbers pubSets pubOfItems openSets
  start)

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (M : More)
  (pub' : Pub → P × First.S → Bool) (pubP' : Pub → P × First.S → Prop)
  (io' : P × First.S → Bool) (cA : Pub → Bool) (links : List ModelPart) (ps : List Place)
  (get : A → P × First.S)

/-- The filling with another door, other tests, other sentences beside them, another "in order". -/
def widenP : Meaning P W :=
  { Mg with more := M, pub := pub', pubP := pubP', inOrder := io' }

/-- **What the condition beside the promise is to give** at border k. -/
def FactsAtP (k : ℕ) (a : A × Fr.E.Str) : Prop :=
  (get a.1).2.failed = none →
    (Mg.inOrder (get a.1) = true → io' (get a.1) = true) ∧
      ∀ q ∈ (pubSets M links ps)[k]?.getD [], cA q = true →
        pub' q (get a.1) = true ∧ pubP' q (get a.1)

theorem onQ_down_P (k : ℕ) (a : A × Fr.E.Str)
    (hhand : ∀ q, cA q = false → ∀ x, pub' q x = Mg.pub q x)
    (hhandP : ∀ q, cA q = false → ∀ x, pubP' q x ↔ Mg.pubP q x)
    (hio : ∀ x, io' x = true → Mg.inOrder x = true)
    (hD : doorsFitB Mg.more M cA links ps k = true)
    (h : onQ N (widenP Mg M pub' pubP' io') links ps get k a) : onQ N Mg links ps get k a := by
  obtain ⟨d1, _, d3⟩ := doorsFitB_parts hD
  obtain ⟨hd, hr⟩ := h
  refine ⟨hd, ?_⟩
  rcases hr with hm | ⟨hB, hS, hC, hP⟩
  · exact Or.inl hm
  · refine Or.inr ⟨?_, hS, hC, fun q hq => (hhandP q (d1 q hq).2 _).1 (hP q (d1 q hq).1)⟩
    simp only [Bool.and_eq_true] at hB ⊢
    obtain ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩ := hB
    refine ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, hio _ b4⟩, ?_⟩, b6⟩
    have hall := List.all_eq_true.1 b5
    refine List.all_eq_true.2 fun q hq => ?_
    rcases List.mem_append.1 hq with hq | hq
    · rw [← hhand q (d1 q hq).2]
      exact hall q (List.mem_append_left _ (d1 q hq).1)
    · rw [← hhand q (d3 q hq)]
      exact hall q (List.mem_append_right _ hq)

theorem onQ_up_P (k : ℕ) (a : A × Fr.E.Str)
    (hhand : ∀ q, cA q = false → ∀ x, pub' q x = Mg.pub q x)
    (hhandP : ∀ q, cA q = false → ∀ x, pubP' q x ↔ Mg.pubP q x)
    (hD : doorsFitB Mg.more M cA links ps k = true)
    (hF : FactsAtP Mg M pub' pubP' io' cA links ps get k a) (h : onQ N Mg links ps get k a) :
    onQ N (widenP Mg M pub' pubP' io') links ps get k a := by
  obtain ⟨_, d2, d3⟩ := doorsFitB_parts hD
  obtain ⟨hd, hr⟩ := h
  refine ⟨hd, ?_⟩
  by_cases hm : (get a.1).2.failed = none
  swap
  · exact Or.inl hm
  obtain ⟨hB, hS, hC, hP⟩ := hr.resolve_left fun h => h hm
  refine Or.inr ⟨?_, hS, hC, fun q hq => ?_⟩
  · simp only [Bool.and_eq_true] at hB ⊢
    obtain ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩ := hB
    have hall := List.all_eq_true.1 b5
    refine ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, (hF hm).1 b4⟩, List.all_eq_true.2 fun q hq => ?_⟩, b6⟩
    rcases List.mem_append.1 hq with hq | hq
    · cases hc : cA q with
      | true => exact ((hF hm).2 q hq hc).1
      | false =>
        show pub' q (get a.1) = true
        rw [hhand q hc]
        refine hall q (List.mem_append_left _ ((d2 q hq).resolve_left ?_))
        rw [hc]
        exact Bool.false_ne_true
    · show pub' q (get a.1) = true
      rw [hhand q (d3 q hq)]
      exact hall q (List.mem_append_right _ hq)
  · cases hc : cA q with
    | true => exact ((hF hm).2 q hq hc).2
    | false =>
      refine (hhandP q hc _).2 (hP q ((d2 q hq).resolve_left ?_))
      rw [hc]
      exact Bool.false_ne_true

/-- **THE BRIDGE, AS A CALL.** -/
theorem tiedAtR_of_classAP (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ) (q : Piece C Fr A Cl W)
    (hhand : ∀ i, cA i = false → ∀ x, pub' i x = Mg.pub i x)
    (hhandP : ∀ i, cA i = false → ∀ x, pubP' i x ↔ Mg.pubP i x)
    (hio : ∀ x, io' x = true → Mg.inOrder x = true)
    (hD : doorsFitB Mg.more M cA links ps k = true)
    (hD' : doorsFitB Mg.more M cA links ps (k + 1) = true)
    (hF : ∀ a, Rch k a → FactsAtP Mg M pub' pubP' io' cA links ps get k a)
    (hF' : ∀ b, Rch (k + 1) b → FactsAtP Mg M pub' pubP' io' cA links ps get (k + 1) b)
    (hs : HandsOn Rch k q) (h : TiedAt N (widenP Mg M pub' pubP' io') links ps get k q) :
    TiedAtR N Mg links ps get Rch k q :=
  tiedAtR_of_wider N Mg links ps get Rch (widenP Mg M pub' pubP' io') k q rfl rfl
    (fun b => onQ_down_P N Mg M pub' pubP' io' cA links ps get (k + 1) b hhand hhandP hio hD')
    (fun a hr => onQ_up_P N Mg M pub' pubP' io' cA links ps get k a hhand hhandP hD (hF a hr))
    (fun b hr =>
      onQ_up_P N Mg M pub' pubP' io' cA links ps get (k + 1) b hhand hhandP hD' (hF' b hr))
    hs h

end

end VerifiableInference.Desc.Sound
