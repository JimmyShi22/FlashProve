-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandPA.lean: the plan of this protocol's technical report (lean/CREDITS.md): the
same theorems for the term on which a batch is built.

A definition, and statements (each statement a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdLinCloseDemandPAProofs.lean. One instance's chain. Bookkeeping: no protocol beyond
Cb/Ld/LdLinCloseDemandP.lean.

Why: Cb/Ld/LdLinCloseDemandP.lean has the whole closing as
`C.cZf (p.x₁ ..) T.Q (C.fqP T.fa) T.front`: the step ; the front's moves ; T.Q. The closings for a
batch (Cb/Ld/LdAltB.lean) are built on closings as one term with a front inside (`LdTc.front`,
Cb/Ld/LdLinCloseAlt.lean), and what they forget to is `C.cZ T.QF (C.fqP T.fa)`: the step ; a link
that does nothing ; the front's moves ; T.Q. The two chains differ by that one link: no round, no
message, no error. They are different terms, so a theorem on one is not a theorem on the other.

Main names:
  `Spec.ldLinPpT_behindA`: under the hypotheses of its statement (ι nonempty among them), `T.QF` is
    in order after the core and the step.
  `Spec.ldLinPpT_tailA`: the test with `C.cZ T.QF (C.fqP T.fa)` is a tail; hypotheses: word for word
    those of `Spec.ldLinPpT_tail` (ι nonempty among them; κ fresh after the core and the step: the
    link that does nothing carries every fact).
  `Spec.ldLinPpT_topA`: the same, hypotheses word for word those of `Spec.ldLinPpT_top` (ι nonempty
    among them).
κ is the entry that the plan's field `k₀` names (not the type κ of the binders).
That the closing for a batch is built on this very term ((T.QA ..).Q = T.QF):
Cb/Obj/LdObjectPaperBatch.lean (`ldOnP_same`); that its annotated chain forgets to that closing's
chain: Cb/Ld/LdLinClosePlanPB.lean (`ldLinPpB_same`).
In `Spec.ldLinPpT_tailA` and `Spec.ldLinPpT_topA`, `TailTr` is the conclusion. `TailTr`, a tail of a
chain, asks of a reduction from a joint to a joint whose statements have no oracles the bundle
`IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which Cb/Ld/LdTowerKit.lean
states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Limits: this file says nothing on the batch's two sides (Cb/Ld/LdLinClosePlanPB.lean,
Cb/Ld/LdLinClosePlanPV.lean). It does not say that the two chains are equal in any sense beyond:
both are tails between the same joints under the same hypotheses. No theorem of this library states
that the hypotheses of `ldLinPpT_tailA` or `ldLinPpT_topA` can be met together.
-/
import Cb.Ld.LdLinCloseDemandP
import Cb.Ld.LdLinCloseDemandT
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The whole closing as one term: the front, the three tests, the closing of what the preamble
left. -/
def LdLinPpT.QF {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ]
    [Fintype J] {C : LdLinC E ι κ J Y} {p : LdLinPp C} (T : LdLinPpT p) : LdTc C.S C.E₀ C.Wpa :=
  LdTc.front (p.x₁ T.Q'.base) T.Q T.front

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

def ldLinPpT_behindA : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)) → p.SaysA T.Q'.base T.fa →
    p.Plain → p.Kept → T.D₁.OK → T.D₂.OK → T.D₃.OK → T.Q'.OK → (∀ n, p.Rs₀ n → Rd n) →
    ((C.P.chain on0 Sn εf).append (C.chain (C.fqP T.fa) (p.x₁ T.Q'.base).A)).FreshFor
      ((p.x₁ T.Q'.base).stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).kc E
      ((p.x₁ T.Q'.base).stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).put →
    T.QF.OkBehind ((C.P.chain on0 Sn εf).append (C.chain (C.fqP T.fa) T.QF.base))

/-- States, for ι nonempty and under the hypotheses below: the test with the term on which a batch
is built is a tail. -/
def ldLinPpT_tailA : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (q₀ : Finset C.E₀.Pos → Prop) (ba : C.Sa.O → ℕ)
      (b' : p.S₃.O → ℕ) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)) → p.SaysA T.Q'.base T.fa →
    p.Plain → p.Kept → T.D₁.OK → T.D₂.OK → T.D₃.OK → T.Q'.OK → (∀ n, p.Rs₀ n → Rd n) →
    ((C.P.chain on0 Sn εf).append (C.chain (C.fqP T.fa) (p.x₁ T.Q'.base).A)).FreshFor
      ((p.x₁ T.Q'.base).stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).kc E
      ((p.x₁ T.Q'.base).stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).put →
    (∀ V, T.Q'.q V → p.S₃.qFam q₀ b' V) → (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inr a) ≤ Sn.tO a) →
    TailTr (C.P.linC on0 Sn εf (C.cZ T.QF (C.fqP T.fa)) d).R
      (C.P.linC on0 Sn εf (C.cZ T.QF (C.fqP T.fa)) d).H (C.P.j0 on0) trivRels
      (C.P.linC on0 Sn εf (C.cZ T.QF (C.fqP T.fa)) d).ext
      (C.P.linC on0 Sn εf (C.cZ T.QF (C.fqP T.fa)) d).P (C.P.q0 qa)

open Classical in
def ldLinPpT_topA : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (q₀ : Finset C.E₀.Pos → Prop) (ba : C.Sa.O → ℕ)
      (b' : p.S₃.O → ℕ) (Rd : C.S.Ent → Prop) (n₀ : C.NO.Ent) (U₀ : Sn.dO.Own E),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → p.Plain → p.Kept → T.D₁.OK → T.D₂.OK → T.D₃.OK → T.Q'.OK →
    (∀ n, p.Rs₀ n → Rd n) → (⟨p.k₀.o, p.k₀.j⟩ : C.S.Ent) = C.eO n₀ → Rd (C.eO n₀) →
    U₀.Laws C.SdO (fun m w' => (C.NO.cut (fun n => Rd (C.eO n)) m, w'))
      (fun u k => (C.NO.ow (fun n => n = n₀) (fun _ => u) k.1, k.2)) →
    (∀ V, T.Q'.q V → p.S₃.qFam q₀ b' V) → (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inr a) ≤ Sn.tO a) →
    TailTr (C.P.linC on0 Sn εf (C.cZ T.QF (C.fqP T.fa)) d).R
      (C.P.linC on0 Sn εf (C.cZ T.QF (C.fqP T.fa)) d).H (C.P.j0 on0) trivRels
      (C.P.linC on0 Sn εf (C.cZ T.QF (C.fqP T.fa)) d).ext
      (C.P.linC on0 Sn εf (C.cZ T.QF (C.fqP T.fa)) d).P (C.P.q0 qa)

end
end Spec
end Cb
