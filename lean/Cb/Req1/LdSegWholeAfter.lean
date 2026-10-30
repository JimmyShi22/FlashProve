-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegWholeAfter.lean: which masks are fresh after a segment with one group
(Cb/Req1/LdSegWhole.lean: `segOne`).

Statements (Cb.Spec.ldSegAfter_*) and proofs, from the rules move by move of
Cb/Req1/LdSegCarry.lean.
Names and paths: facts: `IOR.MaskFact` (Cb/Req1/LdSegFresh.lean); "does not look", of the link `l`:
`Honest.Blind` (Ior/KnowCollRulesMask.lean).
`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. (`Honest.Fresh`, `Honest.seen`,
Ior/KnowCollRulesMask.lean.) In `Spec.ldSegAfter_new` it is a premise (on `Q.snd.link.H`).
A request's zero knowledge (Cb/Req1/LdReq.lean) follows the fresh masks from segment to segment
(`s.After base`). Two kinds of facts leave a segment.

Main names:
  `Spec.ldSegAfter_new`: masks that the one sending lays down (those of the next segment's sumchecks
    and splits): fresh after the segment, in this sense: the fact f is in
    `(segOne D body hT l Q).After base`, if the sending is Fresh for them (Cb/Ld/LdSendFresh*.lean)
    and the cut of the locations does not look at them.
  `Spec.ldSegAfter_old`: masks that cross the closing (those of the message with the masks for the
    rows on the encoded index): a fact fa that is fresh after the body (`body.After base fa`) is
    handed on as fz (`(segOne D body hT l Q).After base ⟨Kc₂, kc₂, fa.Mk, put₂⟩`), if: the link `l`
    (bridge-to-fold) does not look at it (into some fact fc at the stage with the open test); the
    sender's messages do not depend on it, and what the sender hands on is read as overwritten; the
    cut of the locations does not look at it. The batching and the step before the fold never look.

Limits: this file says nothing on two groups. It does not say that these conditions hold for a given
layout.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegWholeZk

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

namespace Spec

/-- Masks that the one sending lays down. -/
def ldSegAfter_new : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (D : LdCl1 E Kc)
      (body : LdProg a D.bat.src) (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
      (l : Link Kc D.fold.src.J D.fold.mid) (Q : LdCloseD D.fold)
      (base : MaskFact a.J.W → Prop) (f : MaskFact Q.snd.tgt.J.W),
    Q.snd.link.H.Fresh D.fold.tgt.J.rels.rel Q.snd.link.P.bud f.kc f.Mk f.put →
    (∀ (w w' : Q.loc.src.J.W) M,
      f.kc w' = f.put M (f.kc w) → Q.loc.cut (Q.loc.S.msgs w'.1) = Q.loc.cut (Q.loc.S.msgs w.1)) →
    (segOne D body hT l Q).After base f

/-- Masks that cross the closing. -/
def ldSegAfter_old : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (D : LdCl1 E Kc)
      (body : LdProg a D.bat.src) (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
      (l : Link Kc D.fold.src.J D.fold.mid) (Q : LdCloseD D.fold)
      (base : MaskFact a.J.W → Prop) (fa : MaskFact D.bat.src.J.W) (Kc₁ : Type)
      (kc₁ : D.fold.tgt.J.W → Kc₁) (put₁ : fa.Mk → Kc₁ → Kc₁) (Kc₂ : Type)
      (kc₂ : Q.snd.tgt.J.W → Kc₂) (put₂ : fa.Mk → Kc₂ → Kc₂),
    body.After base fa → l.H.Blind fa.kc (fun w => kc₁ (D.fold.pW w)) fa.Mk fa.put put₁ →
    (∀ (w w' : D.fold.tgt.W) M, kc₁ w' = put₁ M (kc₁ w) → ∀ k, Q.Sn.put w' k = Q.Sn.put w k) →
    (∀ (w w' : D.fold.tgt.W) M (nw : Q.N.Wit), kc₁ w' = put₁ M (kc₁ w) →
      kc₂ (D.fold.tgt.S.join Q.N (T := OMsg.Wit) (Q.Sn.rest w').1 nw, (Q.Sn.rest w').2) =
        put₂ M (kc₂ (D.fold.tgt.S.join Q.N (T := OMsg.Wit) (Q.Sn.rest w).1 nw, (Q.Sn.rest w).2))) →
    (∀ (w w' : Q.loc.src.J.W) M,
      kc₂ w' = put₂ M (kc₂ w) → Q.loc.cut (Q.loc.S.msgs w'.1) = Q.loc.cut (Q.loc.S.msgs w.1)) →
    (segOne D body hT l Q).After base ⟨Kc₂, kc₂, fa.Mk, put₂⟩

end Spec

theorem ldSegAfter_new : Spec.ldSegAfter_new := by
  intro E Kc _ _ a D body hT l Q base f hF hc
  show LdProg.After Q.locP _ f
  rw [LdCloseD.locP, LdProg.after_snoc, LdProg.after_nil]
  exact segCarry_loc Q.loc _ f ((freshGiven_one _ _ _).2 (Or.inl hF)) hc

theorem ldSegAfter_old : Spec.ldSegAfter_old := by
  intro E Kc _ _ a D body hT l Q base fa Kc₁ kc₁ put₁ Kc₂ kc₂ put₂ hb hl hs1 hs2 hc
  -- bat ; step
  have h1 : (LdMv.bat D.bat).After (body.After base) fa := segCarry_bat D.bat _ fa hb
  have h2 : D.step.After ((LdMv.bat D.bat).After (body.After base)) fa := by
    unfold LdCl1.step ldStepF
    exact segCarry_step D.bat.tgt D.fold.src _ _ _ _ _ fa _ fa.kc fa.put
      h1 (fun _ _ _ _ h => ⟨rfl, h⟩)
  have h2' : D.batP.After (body.After base) fa := by
    rw [LdCl1.batP, LdProg.after_snoc, LdProg.after_snoc, LdProg.after_nil]
    exact h2
  -- fold
  have h3 : (Q.foldP l).After (D.batP.After (body.After base)) ⟨Kc₁, kc₁, fa.Mk, put₁⟩ := by
    rw [LdCloseD.foldP, LdProg.after_snoc, LdProg.after_nil]
    exact segCarry_fold D.fold l _ fa Kc₁ kc₁ put₁ h2' hl
  -- the one sending
  have h4 : (LdMv.send D.fold.tgt Q.snd).After
      ((Q.foldP l).After (D.batP.After (body.After base))) ⟨Kc₂, kc₂, fa.Mk, put₂⟩ :=
    segCarry_send_old D.fold.tgt Q.snd _ ⟨Kc₁, kc₁, fa.Mk, put₁⟩ Kc₂ kc₂ put₂ h3 hs1 hs2
  -- the locations
  show LdProg.After Q.locP _ _
  rw [LdCloseD.locP, LdProg.after_snoc, LdProg.after_nil]
  exact segCarry_loc Q.loc _ ⟨Kc₂, kc₂, fa.Mk, put₂⟩ h4 hc

end Cb
