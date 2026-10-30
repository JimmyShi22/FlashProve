-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/InterfaceProofs.lean: knowledge soundness of the interface (`BatchProtocol.SoundK`) gives the soundness
that the compiler's interface asks for (`BatchProtocol.Sound`), for the languages of the relations.

The proof of `Spec.sound_of_soundK` (stated in Hiop/Interface.lean), after two rules on batches
that leave the protocol as it is: (Snd-B) in its late form for a larger language (`SndBL.larger`);
(Snd-B) with a witness for a larger relation (`SndBK.larger`).
The offline and the link clause of `SoundK` are those of `Sound`, letter for letter. The clause on
the session follows from `Spec.sndB_of_sndBK` (Ior/Batch.lean) and the first rule: "some w is a
witness of: y does not decode, or y decodes to i and (i, x, w) is in Rno" implies "y does not
decode, or y decodes to i and x has a witness". (The converse would need a value of W where y does
not decode; it is not needed.)

Limits: this file says nothing on any protocol; nothing on the honest side.

Terms: lean/GLOSSARY.md.
-/
import Hiop.Interface
import Ior.BatchKProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace BatchInteractiveOracleProof
variable {X W : Type} {E : ExtSpec}

/-- (Snd-B), late form: the language may grow. -/
theorem SndBL.larger {Q : BatchInteractiveOracleProof X E} {N : ℕ} {early : X → X}
    {late : Option ℕ} {L L' : X → E.Str → Prop} {ε : Err Q.loc.shape}
    (h : Q.SndBL N early late L ε) (hL : ∀ x y, L x y → L' x y) : Q.SndBL N early late L' ε := by
  obtain ⟨h0, St, h1, h2, h3, h4, h5⟩ := h
  exact ⟨h0, St, fun y x hx => h1 y x fun hl => hx (hL x y hl), h2,
    fun y x τ hx => h3 y x τ fun hl => hx (hL x y hl),
    fun y x τ hx => h4 y x τ fun hl => hx (hL x y hl), h5⟩

/-- (Snd-B) with a witness: the relation may grow; the extractor and the errors stay. -/
theorem SndBK.larger {Q : BatchInteractiveOracleProof X E} {N : ℕ} {early : X → X} {late : Option ℕ}
    {R R' : X → E.Str → W → Prop} {wit : X → Orcs Q.loc.shape → W} {ε : Err Q.loc.shape}
    (h : Q.SndBK N early late R wit ε) (hR : ∀ x y w, R x y w → R' x y w) :
    Q.SndBK N early late R' wit ε := by
  classical
  obtain ⟨h0, St, h1, h2, h3, h4, h5⟩ := h
  refine ⟨h0, St, h1, h2, h3, fun y x τ hx hs => ?_, h5⟩
  have h := h4 y x τ hx hs
  have h : (Q.loc.accept x y τ && !decide (R x y (wit x τ.read))) = false := h
  show (Q.loc.accept x y τ && !decide (R' x y (wit x τ.read))) = false
  rcases (Bool.and_eq_false_iff.1 h) with ha | hr
  · rw [ha]; rfl
  · have hr' : R x y (wit x τ.read) := by simpa using hr
    simp [hR _ _ _ hr']

end BatchInteractiveOracleProof

/-- `Spec.sound_of_soundK` from the rule on batches (`h`). -/
theorem sound_of_soundK_of (h : Spec.sndB_of_sndBK) : Spec.sound_of_soundK := by
  intro I X W L Rno wit εs hK
  refine ⟨hK.sndT, hK.sndL, ?_⟩
  obtain ⟨ε, hε, hB⟩ := hK.sndB
  refine ⟨ε, hε, (h X W _ L.onlineBatch L.maxBatchSize L.early L.late _ wit ε hB).larger ?_⟩
  rintro x y ⟨w, hw | ⟨i, hi, hw⟩⟩
  · exact Or.inl hw
  · exact Or.inr ⟨i, hi, w, hw⟩

theorem sound_of_soundK : Spec.sound_of_soundK := sound_of_soundK_of sndB_of_sndBK

end Iop
