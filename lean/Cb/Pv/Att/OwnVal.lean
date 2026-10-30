-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/OwnVal.lean: the verifier of an attention sub-proof's own rounds (Cb/Pv/Att/Own.lean)
rejects nothing, and what it puts out.

Main names:
  Ch.fixOK_comap: a chain read through a map of statements keeps its picks.
  SumL.stage_fixOK, Tail.ch_fixOK, unitsCh_fixOK: the pick of every sumcheck of the chain is the
    choice of Cb/Pv/Att/Fix.lean for a plain sumcheck, which is lawful (plain_fix).
  attOwn_fixOK: so A.ch.FixOK holds for all letters A, without a condition (each sumcheck's
    conditions PlainSc.OK are fields of the letters).
  attOwn_tot: the reduction of A.ch.R Ex rejects nothing and its output is A.ch.val Ex
    (Cb/Pv/Att/ChainVal.lean), for all statements and transcripts.

Limits: those of Cb/Pv/Att/ChainVal.lean: A.ch.val Ex has no code. Nothing on soundness, knowledge
soundness or hiding.
-/
import Cb.Pv.Att.ChainVal
import Cb.Pv.Att.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole TWhole.G9 Johnson.L5.Layers

variable {E : Type} [Field E] [Fintype E] {M : Type}

theorem Ch.fixOK_comap : ∀ {X : Type} (c : Ch E M X) {X' : Type} (f : X' → X),
    c.FixOK → (c.comap f).FixOK
  | _, .done _, _, _, _ => trivial
  | _, .ride _ _ _ _ _ _ _ next, _, _, h => ⟨h.1, fixOK_comap next _ h.2⟩
  | _, .draw _ _ _ next, _, _, h => fixOK_comap next _ h
  | _, .send _ _ _ _ _ next, _, _, h => fixOK_comap next _ h

theorem SumL.stage_fixOK {X : Type} (S : SumL E M X) (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx)
    (h : next.FixOK) : (S.stage Ow next).FixOK := ⟨plain_fix S.T S.ok, h⟩

theorem Tail.ch_fixOK {X : Type} (T : Tail E M X) : T.ch.FixOK :=
  T.sE.stage_fixOK _ _ (T.sVM.stage_fixOK _ _ (T.sVD.stage_fixOK _ _ (T.sF.stage_fixOK _ _
    (T.sD.stage_fixOK _ _ (T.sH.stage_fixOK _ _ trivial)))))

theorem unitsCh_fixOK {X : Type} (tail : Ch E M (Seen E X)) (h : tail.FixOK) :
    ∀ (us : List (SumL E M (Seen E X))) {X' : Type} (pr : X' → Seen E X),
      (unitsCh us pr tail).FixOK
  | [], _, pr => Ch.fixOK_comap tail pr h
  | u :: us, _, _ => ⟨plain_fix u.T u.ok, unitsCh_fixOK tail h us _⟩

theorem attOwn_fixOK {X : Type} (A : AttOwn E M X) : A.ch.FixOK :=
  unitsCh_fixOK A.tail.ch A.tail.ch_fixOK A.units _

/-- The verifier of the own rounds rejects nothing, and what it puts out. -/
theorem attOwn_tot {X : Type} (A : AttOwn E M X) (Ex : ExtSpec) :
    Tot (A.ch.R Ex).red (A.ch.val Ex) := Ch.tot Ex A.ch (attOwn_fixOK A)

end Cb.Pv.Att

#print axioms Cb.Pv.Att.attOwn_fixOK
#print axioms Cb.Pv.Att.attOwn_tot
