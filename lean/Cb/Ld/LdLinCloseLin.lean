-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseLin.lean: the last part (the closing) of a test for linear constraints on an encoded
matrix (the index): proximity tests on groups of its oracles, after a step that re-brackets the
statement; as a chain, for any plan of groups without a splitting.

The core of the test for linear constraints (Cb/Ld/LdLin.lean) is an interactive oracle reduction
from one linear claim on the encoded index to linear claims ("rows") on the messages (`Sig.Msg`,
Cb/Ld/LdSig.lean) of oracle messages that it sends (W, G_u, Ω among them) and on a function
(`C.rest`) of those that the preamble left.
W, G_u and Ω are oracle messages, each sent in a family of its own (Cb/Ld/LdLin.lean); in its exact
relations: W holds w = gᵀ·(index matrix); G_u holds the whole folded full message u; Ω holds
ω = (index matrix)·eq(ψ*, ·). j6 is that file's joint after the last verifier message ζ: the rows
that are left.

Definitions and statements; the proofs are in Cb/Ld/LdLinCloseLinProofs.lean.
It uses Cb/Ld/LdLinClosePre.lean (the step without rounds from the test's last joint j6 to a joint
over one signature `C.S`: what the preamble left, and the three families sent with W, G_u, Ω),
Cb/Ld/LdLinCloseChain.lean (whole tests on groups in a row, as a chain) and Cb/Ld/LdLinChain.lean
(the test's core as a chain).

A plan is a closing `Q : LdTc C.S C.E₀ C.Wpa` (Cb/Ld/LdLinCloseChain.lean), with fq: how the
explicit part of the plan (targets and states of each test's rows) is read off the explicit part of
j6.
In the plan in view (Cb/Ld/LdLinClosePlan.lean) the shared tests come first: one group with G_u and
Ω (the record's rows, the columns at the drawn locations, the fold's row); Ω is kept. That one group
holds both G_u and Ω is our reading for the case without a splitting: a write-up of ours
(lean/CREDITS.md) names the groups of the case with a splitting only, and asks that every row touch
one group; the fold's
row reads G_u and Ω. Then the instance's: a group with Ω, W and what the evaluation reads of the
oracles left (evaluation, inner product). Then the tests on the groups that the preamble left. Which
groups is not fixed here.

Main names:
  `C.Says Q.base fq` (Cb/Ld/LdLinClosePre.lean): the plan's claim says the rows that are left and
    what the preamble left.
  `C.cZ Q fq`: the closing: the step without rounds, then the plan's chain.
  `Spec.ldLinCl_chain`: `C.Says Q.base fq`, `Q.OK`, and "what the plan needs of the oracles is
    within q" ⇒ the closing stands behind every chain (`OkFrom`, Ior/KnowCollPiece.lean) and has the
    budgets' halves from q (`SidesCT`, Cb/Ld/LdTowerKitChain.lean).
  `Spec.ldLinCl_tail`: so the test with this closing, (core.append cZ).link d, is a tail from the
    claim on the encoded index (on the statements with the condition) to the trivial statement
    (`ldLinC_tail`, Cb/Ld/LdLinChain.lean), from the core's hypotheses (ι nonempty,
    `C.P.FoldErr on0 εf`, `C.P.D.py` injective, `S.OK`), `C.Says`, `Q.OK` and the demand on
    positions at q5 (`C.P.q5 S qa`, Cb/Ld/LdLin.lean: what the three sendings bear).

Limits: no splitting: every row of the plan lies on one group. A plan with splittings has masked
links in front of the tests; Cb/Ld/LdLinkCloseProofs.lean's `ldChain_front` takes any chain in front
of `Q.c` that stands behind the core (with `Q.OK` and `c₁.SidesC qa Q.q`).
This file gives no plan, no test, no bound on a list. Nothing on batches. Cb/Ld/LdBatchBlocks.lean
has the tests' links for a batch.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLinClosePre
import Cb.Ld.LdLinChain
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The closing of the test, as a chain: the step without rounds, then the plan. -/
def LdLinC.cZ {E ι κ J Y : Type} [Field E] [Fintype Y] [Fintype ι] [Fintype κ]
    [Fintype J] (C : LdLinC E ι κ J Y) (Q : LdTc C.S C.E₀ C.Wpa) (fq : C.St6 → Q.St) :
    Chain Unit C.j6J ldTrivJ :=
  (C.chain fq Q.base).append Q.c

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

open Classical in
/-- States, under the hypotheses below: the closing stands behind every chain, and its budgets fit.
-/
def ldLinCl_chain : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (Q : LdTc C.S C.E₀ C.Wpa) (fq : C.St6 → Q.St)
      (q : Finset C.P.E5.Pos → Prop) (A : Joint Unit) (c₀ : Chain Unit A C.j6J),
    C.Says Q.base fq → Q.OK → (∀ V, Q.q V → q (V.biUnion C.toE.src)) →
    (C.cZ Q fq).OkFrom c₀ ∧ (C.cZ Q fq).SidesCT q

open Classical in
/-- States, for ι nonempty and under the hypotheses below: the test with this closing is a tail. -/
def ldLinCl_tail : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (S : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (Q : LdTc C.S C.E₀ C.Wpa) (fq : C.St6 → Q.St),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → S.OK → C.Says Q.base fq → Q.OK →
    (∀ V, Q.q V → C.P.q5 S qa (V.biUnion C.toE.src)) →
    TailTr (C.P.linC on0 S εf (C.cZ Q fq) d).R (C.P.linC on0 S εf (C.cZ Q fq) d).H (C.P.j0 on0)
      trivRels (C.P.linC on0 S εf (C.cZ Q fq) d).ext (C.P.linC on0 S εf (C.cZ Q fq) d).P (C.P.q0 qa)

end
end Spec
end Cb
