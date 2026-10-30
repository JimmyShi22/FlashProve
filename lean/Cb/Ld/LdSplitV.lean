-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSplitV.lean: batch proofs: how a sub-protocol for one instance is run for N instances, once
in each or once for all, on the side of knowledge soundness and on the honest side.

Definitions and statements (each a `Prop` in `Iop.Spec` or `Cb.Spec`); the proofs are in
Cb/Ld/LdSplitVProofs.lean.

Why: a splitting turns a row (a linear claim) on two groups into a row on each (Cb/Ld/LdSplit.lean).
The closing of a test for N instances may hold splittings: one on a row of the shared oracle
messages, sent once by the shared part; one in each slot, on a row of that slot's own. Both sides of
a batch take links; here a masked link for one instance (`GoodM`, Ior/Masked.lean) is made into one,
in the two ways.

Main names, generic:
  `l.lo` (Cb/Ld/LdBatchBlocksPlan.lean), `l.sh`: the link in every slot, in local rounds; the link
    once, only the shared part speaks, all verifier messages shared. Errors: those for one instance.
  `Spec.link_sh_kb`: if l is knowledge sound for one instance and the condition of its input joint
    (`A.rels.on`) holds of all statements, `l.sh` is knowledge sound for the vectors with one key,
    if N times its errors are its errors (so it is when all are 0), and the new key is a function of
    the old key and the transcript. Nothing is asked on "what acts is a function of the key": the
    union bound over the slots costs N · 0.
  `D.tagPub xp₀`, `Spec.mm_tagPub`: the letters (`MaskData`) of the item "masked messages"
    (`Honest.MM`, Ior/Masked.lean) with the public part written into what is read: reading (D's, a
    public part), claim "D's claim, and the public part read is the one given". The item is kept.
    Why: the rule for a masked block run by the shared part (`mmV_shared`,
    Ior/LinkVMaskedRules.lean) asks that the claim determine the public part from what is read (the
    shared part does not see a slot's explicit part). A claim on rows does not determine the rows'
    states; the shared witness holds them.
  `l.loV` (Cb/Ld/LdLinCloseVPlan.lean), `Spec.link_loV_pm`: the link in every slot as a link with
    the honest side of a batch: a masked link (`PM`, Cb/Ld/LdLinChainVMask.lean) with the letters
    `D.localV`: masks in the
    slots' witnesses. Asked: `GoodM` for one instance; no verifier message is withheld in public;
    its budget asks nothing; honest runs carry the tie to the shared witness; what follows needs of
    the old oracles is within the demand; the demand at the end is kept by subsets.
  `l.shV`, `Spec.link_shV_pm`: the link run by the shared part (strategy s0) as such a link: `PM`
    with the letters `(D.tagPub xp₀).sharedV k`: masks in the shared witness, read through k (what D
    reads, and the public part). Asked beside: on the joint's relation the one-instance prover's
    transcript is s0's; s0's plain parts are D's closed form on what k reads; the tie gives: k reads
    the slot's public part, and D's claim holds of what k reads.
Main names, the splitting (`D : LdSplD`, Cb/Req1/LdSegKit.lean):
  `Spec.ldSplV_lo_kb`, `Spec.ldSplV_sh_kb`: under `D.Hyp`, if the new key is a function of the old
    key (for `sh`: and of the transcript), `D.link.lo`, `D.link.sh` are knowledge sound for the
    vectors with one key (the splitting's error is 0), between the relaxed relations of `D.src.J`
    and `D.tgt.J`, which hold of every witness where the condition moved into them (`Rels.cf`,
    Ior/KnowCollGood.lean) fails.
  `ldSplS0 D rd`: the shared part's strategy: it says the scalar, computed from the messages and the
    first row's state that rd reads off the shared witness; the shared witness is handed on.
  `Spec.ldSplV_lo_pm`, `Spec.ldSplV_sh_pm`: the two masked links.
  `Spec.ldSplV_need`: a splitting needs of the oracles what follows needs, family by family: every
    demand is carried.

Limits: this file does not say that a splitting's entry is fresh after a batch's chain
(`FreshForV`). It says nothing on any chain or plan. All of KnowB's content hangs on which vectors
are admissible (Ior/BatchSeq.lean's header).

Terms: lean/GLOSSARY.md: link (the sense of Ior/), slot (a place of a batch), local round, shared
round, block, joint, closing, honest side, row, entry, mask, batch, demand, group.
-/
import Cb.Ld.LdLinCloseVPlan
import Cb.Ld.LdLinChainVMask
import Ior.LinkVMaskedRules
import Ior.LinkVBearsMore
import Cb.Req1.LdSeg
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR

/-- Any link, once: only the shared part speaks, all verifier messages are shared. -/
def Link.sh {K : Type} {A B : Joint K} (l : Link K A B) : LinkA K A B :=
  ⟨l, RoundSplits.const (RAnn.ofShared .sh) _, l.P.err⟩

/-- The public part written into what is read. -/
def MaskData.tagPub {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} {Wi : Type}
    (D : MaskData R Wi) (xp₀ : D.Xp) : MaskData R Wi where
  Kc  := D.Kc × D.Xp
  kc  := fun w => (D.kc w, xp₀)
  Xp  := D.Xp
  pub := D.pub
  Mk  := D.Mk
  put := fun M k => (D.put M k.1, k.2)
  Cl  := fun xp k => D.Cl xp k.1 ∧ k.2 = xp
  msg := fun k xp ρ => D.msg k.1 xp ρ
  sim := D.sim

variable {K : Type} {A B : Joint K}

/-- The link run by the shared part alone, with the honest side of a batch. s0: the shared part's
strategy. The budget: the link's, at the union of the slots' further positions. -/
def Link.shV (l : Link K A B) (N : ℕ) (VA : JV N A) {W0' : Type}
    (s0 : VA.W0 → l.H.Coin → Strat l.R.shape W0')
    (tieB : W0' → B.X → B.E.Str → B.W → Prop) (qB : QFam B.E N) :
    LinkV K N VA (⟨W0', tieB, qB⟩ : JV N B) :=
  ⟨l.sh, l.H.sharedV s0, budUnion l.R N l.P.bud⟩

end IOR

namespace Spec
open IOR

/-- A link whose errors are their own N-fold (so it is when all are 0), once, by the shared part. -/
def link_sh_kb : Prop :=
  ∀ (K : Type) (A B : Joint K) (l : Link K A B) (N : ℕ) (kA : JKey A)
      (kB : JKey B) (F : kA.κ → Tr l.R.shape → kB.κ),
    l.R.red.Know A.rels.on A.rels.relR B.rels.relR l.ext l.P.err → (∀ a, A.rels.on a) →
    Err.times N l.P.err = l.P.err →
    (∀ a τ b, l.R.red.out a τ = some b → kB.key b = F (kA.key a) τ) → l.sh.KB N kA kB

/-- The item is kept. -/
def mm_tagPub : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (D : MaskData R Wi) (xp₀ : D.Xp),
    H.MM D → H.MM (D.tagPub xp₀)

/-- A masked link in every slot. -/
def link_loV_pm : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (l : Link K A B) (D : MaskData l.R A.W) (VA : JV N A)
      (tieB : VA.W0 → B.X → B.E.Str → B.W → Prop) (qB : QFam B.E N),
    l.GoodM D → l.H.Bad = ∅ → (∀ ρ T, l.P.bud ρ T) →
    (∀ x y w c ρ, VA.rel x y w →
      tieB w.1 ((l.H.strat w.2 x c).run ρ).2.1
        (l.R.imp y ((l.H.strat w.2 x c).run ρ).1) ((l.H.strat w.2 x c).run ρ).2.2) →
    l.R.NeedsV (RoundSplits.allLocal _) VA.q qB → qB.Her → (l.loV N VA tieB qB).PM (D.localV VA.W0 N)

/-- A masked link run by the shared part. -/
def link_shV_pm : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (l : Link K A B) (D : MaskData l.R A.W) (xp₀ : D.Xp)
      (VA : JV N A) (W0' : Type) (s0 : VA.W0 → l.H.Coin → Strat l.R.shape W0')
      (k : VA.W0 → D.Kc × D.Xp) (tieB : W0' → B.X → B.E.Str → B.W → Prop) (qB : QFam B.E N),
    l.GoodM D → l.H.Bad = ∅ → (∀ ρ T, l.P.bud ρ T) →
    (∀ x y w c ρ, VA.rel x y w → ((l.H.strat w.2 x c).run ρ).1 = ((s0 w.1 c).run ρ).1) →
    (∀ x y w c ρ, VA.rel x y w →
      tieB ((s0 w.1 c).run ρ).2 ((l.H.strat w.2 x c).run ρ).2.1
        (l.R.imp y ((l.H.strat w.2 x c).run ρ).1) ((l.H.strat w.2 x c).run ρ).2.2) →
    (∀ w0 c ρ, ((s0 w0 c).run ρ).1.plains = D.msg (k w0).1 (k w0).2 ρ) →
    (∀ x y w, VA.rel x y w → D.Cl (D.pub x) (k w.1).1 ∧ (k w.1).2 = D.pub x) →
    l.R.NeedsV (RoundSplits.const (RAnn.ofShared .sh) _) VA.q qB → qB.Her →
    (l.shV N VA s0 tieB qB).PM ((D.tagPub xp₀).sharedV k N)

end Spec
end Iop

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

/-- The shared part's strategy for a splitting: rd reads the messages and the first row's state off
the shared witness. -/
def ldSplS0 {E Kc : Type} [Field E] [Fintype E] (D : LdSplD E Kc)
    {W0 : Type} (rd : W0 → D.S.Msg × D.St₁) :
    W0 → D.link.H.Coin → Strat D.link.R.shape W0 :=
  fun w0 _ =>
    ((((), splitVal D.k D.sl₁ (rd w0).1 (rd w0).2), fun _ => w0) : Strat [sayRound E 0] W0)

namespace Spec
section
variable (E Kc : Type) [Field E] [Fintype E]

/-- The splitting in every slot: sound. -/
def ldSplV_lo_kb : Prop :=
  ∀ (D : LdSplD E Kc) (N : ℕ) (kA : JKey D.src.J) (kB : JKey D.tgt.J) (F : kA.κ → kB.κ), D.Hyp →
    (∀ a τ b, D.link.R.red.out a τ = some b → kB.key b = F (kA.key a)) → D.link.lo.KB N kA kB

/-- The splitting once, by the shared part: sound. -/
def ldSplV_sh_kb : Prop :=
  ∀ (D : LdSplD E Kc) (N : ℕ) (kA : JKey D.src.J)
      (kB : JKey D.tgt.J) (F : kA.κ → Tr D.link.R.shape → kB.κ),
    D.Hyp → (∀ a τ b, D.link.R.red.out a τ = some b → kB.key b = F (kA.key a) τ) →
    D.link.sh.KB N kA kB

/-- Every demand is carried. -/
def ldSplV_need : Prop :=
  ∀ (D : LdSplD E Kc) (N : ℕ) (An : RoundSplits D.link.R.shape) (q : QFam D.src.J.E N),
    D.link.R.NeedsV An q q

/-- The splitting in every slot: a masked link. -/
def ldSplV_lo_pm : Prop :=
  ∀ (D : LdSplD E Kc) (N : ℕ) (VA : JV N D.src.J)
      (tieB : VA.W0 → D.tgt.J.X → D.tgt.J.E.Str → D.tgt.J.W → Prop),
    D.Hyp → (∀ x y w, VA.rel x y w →
      tieB w.1 (splitNx D.S D.St₁ D.St₂ D.St₀ x (splitVal D.k D.sl₁ (D.S.msgs w.2.1) x.1.1.2.1))
        y w.2) →
    VA.q.Her → (D.link.loV N VA tieB VA.q).PM (D.mask.localV VA.W0 N)

/-- The splitting by the shared part: a masked link. rd reads off the shared witness the messages,
cut to what the splitting reads, and its public part (target and the two states). (not all
hypotheses are named here: see the statement below) -/
def ldSplV_sh_pm : Prop :=
  ∀ (D : LdSplD E Kc) (N : ℕ) (VA : JV N D.src.J) (rd : VA.W0 → D.S.Msg × (E × (D.St₁ × D.St₂)))
      (xp₀ : E × (D.St₁ × D.St₂)) (tieB : VA.W0 → D.tgt.J.X → D.tgt.J.E.Str → D.tgt.J.W → Prop),
    D.Hyp →
    (∀ x y w, VA.rel x y w → (rd w.1).1 = D.S.cut D.Rd (D.S.msgs w.2.1) ∧ (rd w.1).2 = x.1.1) →
    (∀ x y w, VA.rel x y w →
      tieB w.1 (splitNx D.S D.St₁ D.St₂ D.St₀ x (splitVal D.k D.sl₁ (D.S.msgs w.2.1) x.1.1.2.1))
        y w.2) →
    VA.q.Her →
    (D.link.shV N VA (ldSplS0 D fun w0 => ((rd w0).1, (rd w0).2.2.1)) tieB VA.q).PM
      ((D.mask.tagPub xp₀).sharedV rd N)

end
end Spec
end Cb
