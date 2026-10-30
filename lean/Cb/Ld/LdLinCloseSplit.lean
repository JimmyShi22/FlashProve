-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseSplit.lean: the last part (the closing) of a test for linear constraints on an
encoded matrix (the index), where a linear claim touches two groups of oracles: the claim is first
split into one claim for each group (a splitting), then come the proximity tests.

In standard terms: a splitting (Cb/Ld/LdSplit.lean) replaces one linear claim on the messages m₁, m₂
of two groups, sl₁(m₁) + sl₂(m₂) = t (`splitIn`), by one claim on each group (`splitOut`), with the
entry κ added to the first form and subtracted from the second. (κ here names that entry,
`k : SplitAt G₁ G₂`, not the type κ of the statements.)

Definitions and statements; the proofs are in Cb/Ld/LdLinCloseSplitProofs.lean.
It uses Cb/Ld/LdLinClosePre.lean (the step without rounds from the test's last joint to a joint over
one signature `C.S`), Cb/Ld/LdLinChain.lean and Cb/Ld/LdLinChainFresh.lean (the test's core as a
chain; masks that ride with one of its three sendings are fresh after it, under the hypotheses of
its statements (`Spec.ldLinC_freshO`, `Spec.ldLinC_freshU`, `Spec.ldLinC_freshW`)).

Why: Cb/Ld/LdLinCloseLin.lean has the closing for plans in which every row lies on one group. If the
codes of the three families differ, a row on two groups is first split, by a mask entry κ of a
mask-only oracle message that the test itself has sent, with W, with G_u or with Ω. A splitting is a
masked block; so the closing has to stand behind the core.
Fresh: `Chain.FreshFor` (Ior/KnowCollRulesChain.lean).
W, G_u and Ω are oracle messages, each sent in a family of its own (Cb/Ld/LdLin.lean); in its exact
relations: W holds w = gᵀ·(index matrix); G_u holds the whole folded full message u; Ω holds
ω = (index matrix)·eq(ψ*, ·).
`TailTr`, a tail of a chain, asks of a reduction from a joint to a joint whose statements have no
oracles the bundle `IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which
Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Main names (in all statements but `Spec.own_laws_cut`, ι is nonempty; in `Spec.ldLinSp_freshO`,
`Spec.ldLinSp_freshU`, `Spec.ldLinSp_freshW` so is the type Mb of the masks):
  `C.cZf x Q fq p`, the closing: the step without rounds to the joint x (rows still unsplit); the
    front p (steps, batchings, splittings: Cb/Ld/LdFront.lean) down to the plan's first joint; the
    plan Q.
  `Spec.ldLinSp_freshO`, `Spec.ldLinSp_freshU`, `Spec.ldLinSp_freshW`: masks that ride in the family
    sent with Ω (G_u, W) are fresh at the start of the front, in the form of the wide fact
    (Cb/Req1/LdSegCarry.lean), in which the entries in Rd of all messages, the encoding randomness
    at Rr and the whole further witness are read.
      Asked: (1) of the family's sender the conditions of Cb/Ld/LdSendFresh.lean for the reading
      (its messages cut to Rd, the witness handed on); (2) its encoding hides; (3) Rr names no
      member of that family; (4) the own entries lie in Rd; (5) for G_u and W also what
      Cb/Ld/LdLinChainFresh.lean asks: `S.Apart` (later families' messages do not read earlier
      families' witnesses), `S.dO.Laws C.P.backO`, and for W also `S.dU.Laws C.P.backU`.
  `Spec.ldLinSp_entO`, `Spec.ldLinSp_entU`, `Spec.ldLinSp_entW`: each under the hypotheses of its
    statement, the same for one entry, its value the mask itself: literally the last clause that
    Cb/Ld/LdFront.lean's `p.ZkOK` asks for a splitting whose κ is that entry.
  `Spec.own_laws_cut`: these conditions on a sender, from plain ones: the own entries lie in Rd; the
    entry at an own place is the mask's value; an entry in Rd that is not own reads neither the own
    masks nor the pads; the one condition on the pads.
  `Spec.ldLinSp_chain`: the closing stands behind the core (`OkFrom`) and its budgets fit
    (`SidesCT`): from the core's hypotheses (`C.P.FoldErr on0 εf`: on the statements with on0 at
    most εf points γ are bad for the fold at the radius e', Cb/Ld/LdLin.lean; `C.P.D.py` injective;
    `S.OK`), "x says the rows that are left" (`C.Says x.A fq`), `Q.OK` (Cb/Ld/LdLinCloseChain.lean),
    the demand on positions at q5, the moves' own hypotheses (`p.prog.Hyp`), the steps' halves
    (`p.Sd Q.q`, Cb/Ld/LdFront.lean), and `p.ZkOK` at "fresh after the core and the step".
  `Spec.ldLinSp_tail`: so, from the hypotheses of `Spec.ldLinSp_chain`, for every value d of
    `C.P.W0`, the test with this closing is a tail (`TailTr`, Cb/Ld/LdTowerKit.lean), from the claim
    on the encoded index (on the statements with the condition `(C.P.j0 on0).on`, Cb/Ld/LdLin.lean)
    to the trivial statement: with honest-verifier exact zero knowledge (`GoodT.exact`:
    `Honest.Exact`, Ior/Honest.lean) of the whole.

`N.Hides bud` (`Enc.Hides`) asks that, for every set S of positions with `bud S` and all messages m
and m', the distribution of `N.shows S m r` over uniform r in `N.Rnd` equal that of
`N.shows S m' r`; `N.shows S m r` gives the symbols of `N.enc m r` at the positions of S. In this
file's statements it stands as a premise (`S.dO.Nn.Hides (C.NO.budT S.tO)`, and the like for G_u's
and W's families; `Hiop.Enc.Hides`: Cb/Gen/Code.lean).

The case in view, and what is wider or narrower here. In the protocol that we follow the oracle
message that holds a splitting's entry is mask-only, has a sample and a pad of its own, and is a
member of both groups of its splitting (so both tests take in its sample's row, and its encoding
bears both lists); there is one such message for a closing step with two or more groups; split are
the fold's row, if the codes of G_u and Ω differ (entry in the shared mask-only message, sent with
G_u or Ω), and an instance's inner-product row, if the codes of W and Ω differ (entry in the
instance's, sent with W). Wider here: any member of the three families, any number of splittings.

Limits: narrower here, declared: "Rr names no member of that family": the reading forgets the
encoding randomness of every oracle message sent with the holder of the masks, where only the
holder's own has to be forgotten. Cb/Ld/LdSendFreshVis.lean has that form. It does not bite: all
splittings come before the tests, so nothing between the sending and the use reads a neighbour's
randomness.
This file does not say which rows are split and which groups there are (a plan). It does not say
that senders with these properties exist (for the standard senders `T.snd`, under hypotheses of
their own: `Spec.ldLinStdSp_entO`, `Spec.ldLinStdSp_entU`, `Spec.ldLinStdSp_entW`,
Cb/Ld/LdSendStdOwnCut.lean). Nothing on batches.

Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldLinSp_tail` can be met
   together. -/
import Cb.Ld.LdFront
import Cb.Ld.LdLinCloseLin
import Cb.Ld.LdLinChainFresh
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdLinC
variable {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y)

/-- an entry of one of the three families, as an entry of C.S -/
def eO (n : C.NO.Ent) : C.S.Ent := ⟨.inr n.1, n.2⟩
def eU (n : C.NU.Ent) : C.S.Ent := ⟨.inl (.inr n.1), n.2⟩
def eW (n : C.NW.Ent) : C.S.Ent := ⟨.inl (.inl (.inr n.1)), n.2⟩

/-- a function of the entries of one family, over C.S: d at all other entries -/
def liO {β : Type} (d : β) (p : C.NO.Ent → β) : C.S.Ent → β
  | ⟨.inr a, j⟩ => p ⟨a, j⟩
  | ⟨.inl _, _⟩ => d
def liU {β : Type} (d : β) (p : C.NU.Ent → β) : C.S.Ent → β
  | ⟨.inl (.inr a), j⟩ => p ⟨a, j⟩
  | ⟨.inl (.inl _), _⟩ => d
  | ⟨.inr _, _⟩ => d
def liW {β : Type} (d : β) (p : C.NW.Ent → β) : C.S.Ent → β
  | ⟨.inl (.inl (.inr a)), j⟩ => p ⟨a, j⟩
  | ⟨.inl (.inl (.inl _)), _⟩ => d
  | ⟨.inl (.inr _), _⟩ => d
  | ⟨.inr _, _⟩ => d

variable [Fintype E] [Fintype Y] [Fintype ι] [Fintype κ] [Fintype J]

/-- The closing with a front: the step without rounds, the front, the plan. -/
def cZf (x : FSt C.S C.E₀ C.Wpa Unit) (Q : LdTc C.S C.E₀ C.Wpa)
    (fq : C.St6 → x.St) (p : Front x ⟨Q.St, Q.base⟩) : Chain Unit C.j6J ldTrivJ :=
  (p.prog.onto (C.chain fq x.A)).append Q.c

end LdLinC

namespace Spec

open Classical in
/-- The conditions on a sender, for the reading "its messages cut to Rd, and the witness handed on".
-/
def own_laws_cut : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (W W' : Type) (D : N.Sender W W') (Mb : Type) (U : D.Own Mb)
      (Sd : N.Seeds) (Rd own : N.Ent → Prop) (val : Mb → N.Ent → E),
    (∀ n, own n → Rd n) →
    (∀ w M k₀ η (n : N.Ent), own n → D.upM (D.put w (U.mk' M k₀ η)) n.1 n.2 = val M n) →
    (∀ w M M' k₀ η η' (n : N.Ent), Rd n → ¬ own n →
      D.upM (D.put w (U.mk' M k₀ η)) n.1 n.2 = D.upM (D.put w (U.mk' M' k₀ η')) n.1 n.2) →
    (∀ s w w' M M' k₀ k₀', (unif U.Pd).map (fun η => D.ans Sd s w (U.mk' M k₀ η)) =
      (unif U.Pd).map fun η => D.ans Sd s w' (U.mk' M' k₀' η)) →
    U.Laws Sd (fun m w' => (N.cut Rd m, w')) fun M k => (N.ow own (val M) k.1, k.2)

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

open Classical in
/-- States, for ι nonempty and under the hypotheses below: masks in the family of Ω are fresh at the
start of the front. -/
def ldLinSp_freshO : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ)
      (S : C.P.Snd) (x : FSt C.S C.E₀ C.Wpa Unit) (fq : C.St6 → x.St) (Mb : Type) [Fintype Mb]
      [Nonempty Mb] (U : S.dO.Own Mb) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop)
      (own : C.NO.Ent → Prop) (val : Mb → C.NO.Ent → E),
    U.Laws C.SdO (fun m w' => (C.NO.cut (fun n => Rd (C.eO n)) m, w'))
      (fun M k => (C.NO.ow own (val M) k.1, k.2)) →
    S.dO.Nn.Hides (C.NO.budT S.tO) → (∀ a, ¬ Rr (.inr a)) → (∀ n, own n → Rd (C.eO n)) →
    ((C.P.chain on0 S εf).append (C.chain fq x.A)).FreshFor
      (x.stage.wideFact Rd Rr (C.liO False own) Mb fun M => C.liO 0 (val M)).kc Mb
      (x.stage.wideFact Rd Rr (C.liO False own) Mb fun M => C.liO 0 (val M)).put

open Classical in
/-- Masks in the family of G_u. -/
def ldLinSp_freshU : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ)
      (S : C.P.Snd) (x : FSt C.S C.E₀ C.Wpa Unit) (fq : C.St6 → x.St) (Mb : Type) [Fintype Mb]
      [Nonempty Mb] (U : S.dU.Own Mb) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop)
      (own : C.NU.Ent → Prop) (val : Mb → C.NU.Ent → E),
    U.Laws C.SdU (fun m w' => (C.NU.cut (fun n => Rd (C.eU n)) m, w'))
      (fun M k => (C.NU.ow own (val M) k.1, k.2)) →
    S.dU.Nn.Hides (C.NU.budT S.tU) → S.dO.Laws C.P.backO → S.Apart →
    (∀ a, ¬ Rr (.inl (.inr a))) → (∀ n, own n → Rd (C.eU n)) →
    ((C.P.chain on0 S εf).append (C.chain fq x.A)).FreshFor
      (x.stage.wideFact Rd Rr (C.liU False own) Mb fun M => C.liU 0 (val M)).kc Mb
      (x.stage.wideFact Rd Rr (C.liU False own) Mb fun M => C.liU 0 (val M)).put

open Classical in
/-- Masks in the family of W. -/
def ldLinSp_freshW : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ)
      (S : C.P.Snd) (x : FSt C.S C.E₀ C.Wpa Unit) (fq : C.St6 → x.St) (Mb : Type) [Fintype Mb]
      [Nonempty Mb] (U : S.dW.Own Mb) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop)
      (own : C.NW.Ent → Prop) (val : Mb → C.NW.Ent → E),
    U.Laws C.SdW (fun m w' => (C.NW.cut (fun n => Rd (C.eW n)) m, w'))
      (fun M k => (C.NW.ow own (val M) k.1, k.2)) →
    S.dW.Nn.Hides (C.NW.budT S.tW) → S.dU.Laws C.P.backU → S.dO.Laws C.P.backO → S.Apart →
    (∀ a, ¬ Rr (.inl (.inl (.inr a)))) → (∀ n, own n → Rd (C.eW n)) →
    ((C.P.chain on0 S εf).append (C.chain fq x.A)).FreshFor
      (x.stage.wideFact Rd Rr (C.liW False own) Mb fun M => C.liW 0 (val M)).kc Mb
      (x.stage.wideFact Rd Rr (C.liW False own) Mb fun M => C.liW 0 (val M)).put

open Classical in
/-- One entry of a member of the family of Ω, as a splitting needs it. -/
def ldLinSp_entO : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (S : C.P.Snd)
      (x : FSt C.S C.E₀ C.Wpa Unit) (fq : C.St6 → x.St) (U : S.dO.Own E) (Rd : C.S.Ent → Prop)
      (Rr : C.S.O → Prop) (n₀ : C.NO.Ent),
    U.Laws C.SdO (fun m w' => (C.NO.cut (fun n => Rd (C.eO n)) m, w'))
      (fun u k => (C.NO.ow (fun n => n = n₀) (fun _ => u) k.1, k.2)) →
    S.dO.Nn.Hides (C.NO.budT S.tO) → (∀ a, ¬ Rr (.inr a)) → Rd (C.eO n₀) →
    ((C.P.chain on0 S εf).append (C.chain fq x.A)).FreshFor
      (x.stage.wideFact Rd Rr (fun n => n = C.eO n₀) E fun u _ => u).kc E
      (x.stage.wideFact Rd Rr (fun n => n = C.eO n₀) E fun u _ => u).put

open Classical in
def ldLinSp_entU : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (S : C.P.Snd)
      (x : FSt C.S C.E₀ C.Wpa Unit) (fq : C.St6 → x.St) (U : S.dU.Own E) (Rd : C.S.Ent → Prop)
      (Rr : C.S.O → Prop) (n₀ : C.NU.Ent),
    U.Laws C.SdU (fun m w' => (C.NU.cut (fun n => Rd (C.eU n)) m, w'))
      (fun u k => (C.NU.ow (fun n => n = n₀) (fun _ => u) k.1, k.2)) →
    S.dU.Nn.Hides (C.NU.budT S.tU) → S.dO.Laws C.P.backO → S.Apart →
    (∀ a, ¬ Rr (.inl (.inr a))) → Rd (C.eU n₀) →
    ((C.P.chain on0 S εf).append (C.chain fq x.A)).FreshFor
      (x.stage.wideFact Rd Rr (fun n => n = C.eU n₀) E fun u _ => u).kc E
      (x.stage.wideFact Rd Rr (fun n => n = C.eU n₀) E fun u _ => u).put

open Classical in
def ldLinSp_entW : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (S : C.P.Snd)
      (x : FSt C.S C.E₀ C.Wpa Unit) (fq : C.St6 → x.St) (U : S.dW.Own E) (Rd : C.S.Ent → Prop)
      (Rr : C.S.O → Prop) (n₀ : C.NW.Ent),
    U.Laws C.SdW (fun m w' => (C.NW.cut (fun n => Rd (C.eW n)) m, w'))
      (fun u k => (C.NW.ow (fun n => n = n₀) (fun _ => u) k.1, k.2)) →
    S.dW.Nn.Hides (C.NW.budT S.tW) → S.dU.Laws C.P.backU → S.dO.Laws C.P.backO → S.Apart →
    (∀ a, ¬ Rr (.inl (.inl (.inr a)))) → Rd (C.eW n₀) →
    ((C.P.chain on0 S εf).append (C.chain fq x.A)).FreshFor
      (x.stage.wideFact Rd Rr (fun n => n = C.eW n₀) E fun u _ => u).kc E
      (x.stage.wideFact Rd Rr (fun n => n = C.eW n₀) E fun u _ => u).put

open Classical in
/-- States, for ι nonempty and under the hypotheses below: the closing with splittings stands behind
the core, and its budgets fit. -/
def ldLinSp_chain : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (S : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (x : FSt C.S C.E₀ C.Wpa Unit) (Q : LdTc C.S C.E₀ C.Wpa)
      (fq : C.St6 → x.St) (p : Front x ⟨Q.St, Q.base⟩) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → S.OK → C.Says x.A fq → Q.OK →
    (∀ V, Q.q V → C.P.q5 S qa (V.biUnion C.toE.src)) → p.prog.Hyp → p.Sd Q.q →
    p.ZkOK Rd Rr
      (fun g => ((C.P.chain on0 S εf).append (C.chain fq x.A)).FreshFor g.kc g.Mk g.put) →
    (C.cZf x Q fq p).OkFrom (C.P.chain on0 S εf) ∧ (C.cZf x Q fq p).SidesCT (C.P.q5 S qa)

open Classical in
/-- States, for ι nonempty and under the hypotheses below: the test with this closing is a tail. -/
def ldLinSp_tail : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (S : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (x : FSt C.S C.E₀ C.Wpa Unit)
      (Q : LdTc C.S C.E₀ C.Wpa) (fq : C.St6 → x.St) (p : Front x ⟨Q.St, Q.base⟩)
      (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → S.OK → C.Says x.A fq → Q.OK →
    (∀ V, Q.q V → C.P.q5 S qa (V.biUnion C.toE.src)) → p.prog.Hyp → p.Sd Q.q →
    p.ZkOK Rd Rr
      (fun g => ((C.P.chain on0 S εf).append (C.chain fq x.A)).FreshFor g.kc g.Mk g.put) →
    TailTr (C.P.linC on0 S εf (C.cZf x Q fq p) d).R (C.P.linC on0 S εf (C.cZf x Q fq p) d).H
      (C.P.j0 on0) trivRels (C.P.linC on0 S εf (C.cZf x Q fq p) d).ext
      (C.P.linC on0 S εf (C.cZf x Q fq p) d).P (C.P.q0 qa)

end
end Spec
end Cb
