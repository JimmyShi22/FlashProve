-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/KnowInProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/KnowIn.lean.

Limits: those of Johnson/Desc/Sound/KnowIn.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KnowIn
import Johnson.Desc.Sound.FoldIsRowProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

theorem knowInOfBadFam : KnowInOfBadFam := by
  intro A B WA WB K on on' RA RB ext ε bad hW h2 h3 a ha
  exact Iop.doomed_of_clean _ _ (bad a) _ (hW a ha)
    fun τ hτ b hb => ⟨h2 a τ b ha hτ hb, fun w hw => h3 a τ b w ha hτ hb hw⟩

theorem knowInOfCarry : KnowInOfCarry := by
  intro A B WA WB K on on' RA RB ext ε hc hk a ha
  refine Doomed.mono _ _ ?_ (hk a ha)
  intro τ hτ b hb
  exact ⟨hc a τ b ha hb, fun w hw => hτ b w hb hw⟩

theorem knowIntoOfKnowIn : KnowIntoOfKnowIn := by
  intro A B WA WB K on on' RA RB ext ε h a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b w hb hw
  obtain ⟨ho, hk⟩ := hτ b hb
  exact hk w (hw.elim id fun n => absurd ho n)

theorem knowInSeq : KnowInSeq := by
  intro A B C WA WB WC K₁ K₂ on₁ on₂ on₃ RA RB RC e₁ e₂ ε₁ ε₂ d h₁ h₂ a ha
  refine Doomed.append K₁.shape K₂.shape ε₁ ε₂ _ (Doomed.mono _ _ ?_ (h₁ a ha))
  intro τ₁ hτ₁
  cases hout : K₁.out a τ₁ with
  | none =>
    refine Doomed.of_forall _ _ fun τ₂ c hc => ?_
    rw [Reduction.seq_out_app, hout] at hc
    exact absurd hc (by simp)
  | some b =>
    obtain ⟨hb, hk⟩ := hτ₁ b hout
    refine Doomed.mono _ _ ?_ (h₂ b hb)
    intro τ₂ h c hc
    rw [Reduction.seq_out_app, hout] at hc
    obtain ⟨h3, hk₂⟩ := h c hc
    refine ⟨h3, fun w hw => ?_⟩
    have := hk _ (hk₂ w hw)
    simpa [Reduction.extSeq, Tr.fst_app, Tr.snd_app, hout] using this

theorem pieceGoodIn : PieceGoodIn := by
  intro S Cl W C F p Xp Yp Wp Wq Kp G δ rd on on' onp onp' RA RB RAp RBp ep hF hon hyes hk a ha
  refine CarryS.doomed (G a) δ p.err (hF a) _
    (fun τ' => ∀ y, Kp.out (rd a) τ' = some y →
      onp' y ∧ ∀ w', RBp y w' → RAp (rd a) (ep (rd a) τ' w')) ?_ ?_ (hk (rd a) (hon a ha))
  · intro τ hτ a' ha'
    obtain ⟨τ', _, h1, _⟩ := hyes a τ a' ha ha'
    rw [hτ] at h1
    cases h1
  · intro τ τ' hτ hbad a' ha'
    obtain ⟨τ'', y, h1, h2, h3, h4⟩ := hyes a τ a' ha ha'
    rw [hτ] at h1
    cases h1
    obtain ⟨hy, hb⟩ := hbad y h2
    refine ⟨h3 hy, fun w hw => ?_⟩
    obtain ⟨w', hw', hr⟩ := h4 w hw
    exact hr (hb w' hw')

theorem rowKnowIn : RowKnowIn := by
  intro S Cl W C F on R d i p l
  induction l generalizing p i with
  | nil => exact fun hg => hg.1
  | cons q l ih =>
    intro hg
    have k := knowInSeq _ _ _ _ _ _ p.ior.red (rowIOR q l).red (on i) (on (i + 1))
      (on (i + 1 + 1 + l.length)) (R i) (R (i + 1)) (R (i + 1 + 1 + l.length)) p.ext
      (rowExt d q l) p.err (rowErr q l) d hg.1 (ih (i + 1) q hg.2)
    have e : i + 1 + 1 + l.length = i + 1 + (q :: l).length := by
      rw [List.length_cons]
      omega
    rw [e] at k
    intro a ha
    refine Doomed.mono _ _ ?_ (k a ha)
    intro τ hτ b hb
    exact hτ b ((IOR.red_seq_out p.ior (rowIOR q l) a τ).symm.trans hb)

theorem chainKnowIn_of (hf : FoldIsRow) : ChainKnowIn := by
  intro S Cl W C F name on R d p l h ht hg
  have k := rowKnowIn S Cl W C F on R d 0 p l hg
  rw [Nat.zero_add] at k
  intro a ha
  refine Doomed.mono _ _ ?_ (k a ha)
  intro τ hτ b hb
  exact hτ b ((hf S Cl W C F name p l h ht a τ).symm.trans hb)

theorem chainKnowIn : ChainKnowIn := chainKnowIn_of foldIsRow

end VerifiableInference.Desc.Sound
