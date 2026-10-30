-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDProofs.lean: the proof of Cb/Ld/LdLayD.lean's statement (`ldReqRefLay_data`), by way of
`ldReqRefLay_ok`: the three clauses (`lay`, `layT`, `layB`) from the record (`LdReqRefLayD`,
Cb/Ld/LdLayD.lean) and: a sound Q, E of characteristic pp, the segments' bundles (`L.OK pp`), of the
witness each closing's link reads the group's members only, and hands the rest on (`L.Reads`), the
last body's bundle (`T.A.OK pp`): an assembly of Cb/Ld/LdLayDListProofs.lean (the induction along
the list), Cb/Ld/LdLayDBodyProofs.lean (a body behind its entry step), Cb/Ld/LdLayDTailProofs.lean
(the last segment). Then the three premises `L.OK pp`, `L.Reads`, `T.A.OK pp` from the model's side
and the protocol's side with standard senders and the groups' own links. What is said and what is
not: the head of Cb/Ld/LdLayD.lean.
-/
import Cb.Ld.LdLayD
import Cb.Ld.LdLayDListProofs
import Cb.Ld.LdLayDTailProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- under `hQ`: a block that the first sending lays has its fact among those fresh behind it in this
sense: it is in `MaskFact.JCl (ldReqRef1 R first b L T).base₀` -/
theorem ldLayD_base {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (R : LdORE F E Kc) {a : LdStage E Kc} (first : LdSendD a) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b) (Q : LdLayQ E) (hQ : Q.Sound)
    (β : LdPend first.tgt) (h : first.LaysD Q β) :
    MaskFact.JCl (ldReqRef1 R first b L T).base₀ β.fact := by
  refine .base _ ?_
  show ldReqBase first (.nil _) β.fact
  unfold ldReqBase
  rw [LdProg.After]
  exact ldLayD_lays a first β Q hQ h

/-- The three clauses, from the record and the bundles (`hQ`, `hL`, `hR`, `hT`, `h`; E of
characteristic pp). -/
theorem ldReqRefLay_ok (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (pp : ℕ) [CharP E pp] (R : LdORE F E Kc) (a : LdStage E Kc)
    (first : LdSendD a) (b : LdStage E Kc) (L : LdRefL E Kc R.ix first.tgt b)
    (T : LdRefT R b) (Q : LdLayQ E) (hQ : Q.Sound) (hL : L.OK pp) (hR : L.Reads)
    (hT : T.A.OK pp) (h : LdReqRefLayD Q pp R first b L T) :
    L.LayJ pp (ldReqRef1 R first b L T).base₀ ∧
    T.A.ZkAt pp (fun f =>
      ∃ g,
        L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
        ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f) ∧
    ∃ (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
      (∀ n, R.Rd n → Rd n) ∧
      ∃ g,
        L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
        ∀ Y : MaskFact b.J.W → Prop, Y g →
          T.tail.After Y
            (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M =>
              R.X.atVal R.X.wAt M) := by
  haveI : Nonempty R.ix.C.E0.Str := h.last.1
  have h0 := ldLayD_base R first b L T Q hQ
  have hl :=
    ldLayD_laid E Kc pp R.ix _ _ L Q (first.LaysD Q) (ldReqRef1 R first b L T).base₀ hQ hL hR h0
  refine ⟨ldLayD_segs E Kc pp R.ix _ _ L Q (first.LaysD Q) _ hQ hL hR h0 h.segs, ?_, ?_⟩
  · exact ldLayD_enter E Kc R.ix T.A Q pp b T.f T.g T.m T.back
      (L.LaidJ (ldReqRef1 R first b L T).base₀) (L.PendD Q pp (first.LaysD Q))
      (L.laidJ_closed _) hl h.last
  · obtain ⟨Rd, Rr, hRd, β, hβ, ht⟩ := h.fin
    obtain ⟨g, hg, hY⟩ := ldLayD_tail F E Kc pp R b T Q (L.LaidJ (ldReqRef1 R first b L T).base₀)
      β _ (L.laidJ_closed _) hT (hl β hβ) ht
    exact ⟨Rd, Rr, hRd, g, hg, hY⟩

/-- of the witness each closing's link reads the group's members only: from the groups' own links
(`L.ProtoSA pp`) -/
theorem ldLayD_reads {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a b : LdStage E Kc}
    (L : LdRefL E Kc I a b) (pp : ℕ) : L.ProtoSA pp → L.Reads := by
  induction L with
  | nil => intro _; rw [LdRefL.Reads]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.ProtoSA] at h
      rw [LdRefL.Reads]
      exact ⟨ih h.1, ldReqRefLayStd_link E Kc _ _ h.2.fold⟩

theorem ldReqRefLay_data :
    Spec.ldReqRefLay_data := fun F E Kc _ _ _ _ _ pp _ R a first b L T Q hQ hM hL hT h =>
  ldReqRefLay_ok F E Kc pp R a first b L T Q hQ
    ((ldReqModel_list E Kc _ _ _ L pp).2 ⟨hM.segs, ldReqStdAny_list E Kc _ _ _ L pp hL⟩)
    (ldLayD_reads L pp hL) ((ldReqModel_body E Kc _ T.A pp).2 ⟨hM.tail.body, hT.toProto⟩) h

end Cb
