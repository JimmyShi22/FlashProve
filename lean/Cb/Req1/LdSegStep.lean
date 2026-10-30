-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegStep.lean: three lemmas for whoever composes interactive oracle reductions into
sequences (lists of moves: Cb/Req1/LdSeg.lean, Cb/Req1/LdReq.lean).

Statements and proofs. No protocol occurs here.

Main names:
  `Cb.Spec.ldSeg_step`: the move "step" can be given at the joints S.over A, S'.over B: a step
    without rounds between two joints is one between the joints whose condition may fail
    (`ldPeel_cf`, Cb/Ld/LdBatPeel.lean).
  `Iop.Spec.okGiven_of_allT`: a chain with the whole bundle in every link is of the two kinds,
    whatever is fresh at its start: zero knowledge asks nothing of such a "sub", beside its
    hypotheses.
  `Cb.Spec.ldSeg_one`: one link between two stages as a move "sub": its hypothesis and what zero
    knowledge asks, from `GoodT` between S.over A and S'.over B.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqProofs
import Cb.Ld.LdBatPeelProofs

set_option autoImplicit false

namespace Iop
open Prob

namespace Spec
open IOR

def okGiven_of_allT : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (base : MaskFact A.W → Prop),
    c.AllT → c.OkGiven base

end Spec

open IOR IOR.Chain

theorem okGiven_of_allT : Spec.okGiven_of_allT := by
  intro K A B c base
  induction c with
  | one l => intro h; exact (okGiven_one l base).2 (Or.inl ((allT_one l).1 h))
  | snoc c l ih => intro h; exact (okGiven_snoc c l base).2 ⟨ih ((allT_snoc c l).1 h).1, Or.inl ((allT_snoc c l).1 h).2⟩

end Iop

namespace Cb
open Iop Prob Hiop IOR IOR.Chain

namespace Spec

/-- The move "step", given at the joints whose condition has not been moved. -/
def ldSeg_step : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc) (f : a.X → Option b.X)
      (g : ExtMap a.Ex b.Ex) (m : a.X × a.W → b.X × b.W) (back : a.X × a.Ex.Str → b.W → a.W),
    StepT f g m back (a.S.over a.A) (b.S.over b.A) → (LdMv.step a b f g m back).Hyp

/-- One link with the whole bundle as a move "sub". -/
def ldSeg_one : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc) (l : Link Kc a.J b.J),
    IOR.GoodT l.R l.H (a.S.over a.A) (b.S.over b.A) l.ext l.P →
    (LdMv.sub a b (.one l)).Hyp ∧ ∀ base, (LdMv.sub a b (.one l)).Zk base

end Spec

theorem ldSeg_step : Spec.ldSeg_step := fun _ _ _ _ _ _ _ _ _ _ h =>
  ldPeel_cf _ _ _ _ _ _ _ _ _ _ _ _ _ h

theorem ldSeg_one : Spec.ldSeg_one := fun E Kc _ _ a b l h =>
  have g := ldSeg_sub_goodT E Kc a b l h
  ⟨(allB_one l).2 (goodB_of_goodT' g), fun base => okGiven_of_allT Kc _ _ _ base ((allT_one l).2 g)⟩

end Cb
