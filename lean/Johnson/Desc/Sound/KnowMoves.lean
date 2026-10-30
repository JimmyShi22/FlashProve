-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/KnowMoves.lean: five ways in which round-by-round knowledge soundness
(`Reduction.Know`, Ior/Know.lean) is carried from one reduction to another with the same rounds, or
with one silent round more. Statements and proofs, at parameters: no protocol occurs here.

Main names.
  `know_cast`: along an equation of the lists of rounds, with the extractor and the errors.
  `know_sim`: to a reduction over the same rounds that, at each of its statements, either always
    refuses or puts out only where the first reduction does at some statement of its own, with the
    witnesses tied.
  `know_fam`: the same from a family of clauses with one extractor and one list of errors.
  `know_front`: behind one round more in front, whose challenge nothing reads and on whose message
    there is a test: that round's error is 0.
  `know_all`: a condition on the statements in front taken into the relation (`orOff`).

Limits: rules at parameters: no reduction of a protocol is shown to meet a premise.
Terms: lean/GLOSSARY.md.

-/
import Ior.KnowColl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open _root_.Iop (Reduction Err Shape Round Doomed)
open _root_.Iop.Reduction (orOff)
open _root_.Prob (cnt cnt_false)

variable {A B A' B' WA WB WA' WB' : Type}

/-- Along an equation of the lists of rounds. -/
theorem know_cast {s t : Shape} (h : s = t) (out : A → Iop.Tr t → Option B) (on : A → Prop)
    (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Iop.Tr s → WB → WA) (ε : Err s)
    (k : (⟨s, fun a τ => out a (cast (congrArg Iop.Tr h) τ)⟩ : Reduction A B).Know on RA RB ext ε) :
    (⟨t, out⟩ : Reduction A B).Know on RA RB
      (fun a τ w => ext a (cast (congrArg Iop.Tr h.symm) τ) w) (cast (congrArg Err h) ε) := by
  subst h
  exact k

/-- To a reduction over the same rounds that follows the first. -/
theorem know_sim (K : Reduction A B) (out' : A' → Iop.Tr K.shape → Option B') (on : A → Prop)
    (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Iop.Tr K.shape → WB → WA)
    (ε : Err K.shape) (on' : A' → Prop) (RA' : A' → WA' → Prop) (RB' : B' → WB' → Prop)
    (ext' : A' → Iop.Tr K.shape → WB' → WA')
    (h : ∀ a', on' a' → (∀ τ, out' a' τ = none) ∨ ∃ a, on a ∧ ∀ τ b' w', out' a' τ = some b' →
      RB' b' w' → ∃ b w, K.out a τ = some b ∧ RB b w ∧
        (RA a (ext a τ w) → RA' a' (ext' a' τ w')))
    (k : K.Know on RA RB ext ε) :
    (⟨K.shape, out'⟩ : Reduction A' B').Know on' RA' RB' ext' ε := by
  intro a' ha'
  rcases h a' ha' with hn | ⟨a, ha, hs⟩
  · refine Doomed.of_forall _ _ fun τ b w hb _ => ?_
    have hb' : out' a' τ = some b := hb
    rw [hn τ] at hb'
    cases hb'
  · refine Doomed.mono _ _ ?_ (k a ha)
    intro τ hτ b' w' hb' hw'
    obtain ⟨b, w, h1, h2, h3⟩ := hs τ b' w' hb' hw'
    exact h3 (hτ b w h1 h2)

/-- The same from a family of clauses of the first reduction, all with one extractor and one list of
errors: each statement of the second reduction picks the clause that it follows. -/
theorem know_fam {ι : Type} (K : Reduction A B) (out' : A' → Iop.Tr K.shape → Option B')
    (on : ι → A → Prop) (RA : ι → A → WA → Prop) (RB : ι → B → WB → Prop)
    (ext : A → Iop.Tr K.shape → WB → WA) (ε : Err K.shape) (on' : A' → Prop)
    (RA' : A' → WA' → Prop) (RB' : B' → WB' → Prop) (ext' : A' → Iop.Tr K.shape → WB' → WA')
    (h : ∀ a', on' a' → (∀ τ, out' a' τ = none) ∨ ∃ i a, on i a ∧ ∀ τ b' w',
      out' a' τ = some b' → RB' b' w' → ∃ b w, K.out a τ = some b ∧ RB i b w ∧
        (RA i a (ext a τ w) → RA' a' (ext' a' τ w')))
    (k : ∀ i, K.Know (on i) (RA i) (RB i) ext ε) :
    (⟨K.shape, out'⟩ : Reduction A' B').Know on' RA' RB' ext' ε := by
  intro a' ha'
  rcases h a' ha' with hn | ⟨i, a, ha, hs⟩
  · refine Doomed.of_forall _ _ fun τ b w hb _ => ?_
    have hb' : out' a' τ = some b := hb
    rw [hn τ] at hb'
    cases hb'
  · refine Doomed.mono _ _ ?_ (k i a ha)
    intro τ hτ b' w' hb' hw'
    obtain ⟨b, w, h1, h2, h3⟩ := hs τ b' w' hb' hw'
    exact h3 (hτ b w h1 h2)

/-- Behind one round more in front. -/
theorem know_front (r : Round) (K : Reduction A B) (ok : A → r.Msg → Bool) (on : A → Prop)
    (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Iop.Tr K.shape → WB → WA)
    (ε : Err K.shape) (k : K.Know on RA RB ext ε) :
    (⟨r :: K.shape, fun a τ => if ok a τ.1 then K.out a τ.2.2 else none⟩ : Reduction A B).Know on RA
      RB (fun a τ w => ext a τ.2.2 w) (0, ε) := by
  intro a ha m
  rw [cnt_false]
  intro c hc
  refine hc (Doomed.mono _ _ ?_ (k a ha))
  intro τ hτ b w hb hw
  have hb' : (if ok a m then K.out a τ else none) = some b := hb
  cases ho : ok a m with
  | false =>
    rw [ho] at hb'
    cases hb'
  | true =>
    rw [ho] at hb'
    exact hτ b w hb' hw

/-- A condition on the statements in front, taken into the relation. -/
theorem know_all (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
    (ext : A → Iop.Tr K.shape → WB → WA) (ε : Err K.shape) (k : K.Know on RA RB ext ε) :
    K.Know (fun _ => True) (orOff on RA) RB ext ε :=
  (Iop.know_iff_orOff A B WA WB K on RA RB ext ε).1 k

end VerifiableInference.Desc.Sound
