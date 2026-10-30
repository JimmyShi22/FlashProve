-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqEndSay.lean: for toys: the end of a request whose pending tensor rows are made on
the spot: the prover says the masked values; the batching; the last step.

A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves. Its last moves, the final batching, make the claims on the
encoded index that are still pending into one. In this file, for small examples, no segment leaves
the pending claims: one round before the batching makes them.
Definitions, statements and proofs (an assembly).
It uses Cb/Obj/LdObjectReqEnd.lean (`R : LdORE F E Kc`: the end of a request and the test that
follows; `R.X.link`, the batching of the pending tensor rows; `R.endStep`; `R.z`, the last stage)
and Cb/Ld/LdTenSay.lean (the stand-in, in a toy, for the ends of sumchecks at maps of the index:
no block of a write-up of ours (lean/CREDITS.md)).

Main names:
  `R.sayP`: three moves: from `R.X.p1` (the rows that stay open hold; the index is decoded by the
    statement; nothing else is claimed of the index) to `R.z`: the values are said (1 round); the
    batching (k + 2 rounds); the record is written beside the claim (no round). The two last moves
    are the two last of `R.lastP`; its first (a re-bracketing) is not needed: the say-block
    (`R.X.sayLink`, Cb/Ld/LdTenSay.lean) ends at the stage at which the batching's block starts.
  `Spec.ldORES_hyp`: `R.sayP.Hyp` from: 2 ≤ degree (`R.n`); the evader's law (`R.Z.OK`); `R.Tie`;
    `X.SayOK κ`.
  `Spec.ldORES_zk`: `R.sayP.Zk base` from these, `X.Own`, and two facts on freshness: the
    say-block's own entries are fresh before it; the batching's own entries are fresh after it.
  `Spec.ldORES_kinds`: the moves are of the kinds that the last part of a request holds.







Notation: `k`: the natural number `R.k` (`LdORE`, Cb/Obj/LdObjectReqEnd.lean): the number of column
variables of the matrix of the index; `κ`: a map from `R.X.Q` (`LdORE.Q`,
Cb/Obj/LdObjectReqEnd.lean: the pending tensor rows) to `R.X.Nm`; `base`: a predicate on
`MaskFact R.X.p1.J.W` (Cb/Req1/LdSegFresh.lean).

Limits: what this file exercises: nothing of the index is claimed before the values are said.
It exercises the plumbing: decoding by the statement,
the ghost, the conditions on own entries, freshness through two blocks, the datum `R.O`;
not a model's claim. This file does not say that the two facts
on freshness hold. It says nothing on the moves in front of `R.X.p1`.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdTenSay
import Cb.Obj.LdObjectReqEndToy
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The values are said; the batching; the last step. -/
def LdORE.sayP
    {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc) :
    LdProg R.X.p1 R.z :=
  (((LdProg.nil R.X.p1).snoc (.sub R.X.p1 R.X.m0 (.one R.X.sayLink))).snoc
    (.sub R.X.m0 R.X.m1 (.one R.X.link))).snoc R.endStep

namespace Spec
section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldORES_hyp : Prop :=
  ∀ (R : LdORE F E Kc) (κ : R.X.Q → R.X.Nm), 2 ≤ R.n → R.Z.OK → R.Tie → R.X.SayOK κ → R.sayP.Hyp

def ldORES_zk : Prop :=
  ∀ (R : LdORE F E Kc) (κ : R.X.Q → R.X.Nm) (base : MaskFact R.X.p1.J.W → Prop), 2 ≤ R.n → R.Z.OK →
    R.X.Own → R.X.SayOK κ → base (R.X.sayMask κ).fact →
    (LdMv.sub R.X.p1 R.X.m0 (.one R.X.sayLink)).After base R.X.mask.fact → R.sayP.Zk base

def ldORES_kinds : Prop := ∀ (R : LdORE F E Kc), R.sayP.All fun t => t = .sub ∨ t = .step

end

end Spec

section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldORES_hyp : Spec.ldORES_hyp F E Kc := by
  intro R κ hn hZ hT hS
  have h := ldORE_hyp F E Kc R hn hZ hT
  unfold LdORE.lastP at h
  rw [LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc] at h
  unfold LdORE.sayP
  rw [LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc]
  exact ⟨⟨⟨LdProg.hyp_nilK _, (Chain.allB_one R.X.sayLink).2 (ldTenSay_goodM E Kc R.X κ hS).base⟩,
      h.1.2⟩,
    h.2⟩

theorem ldORES_zk : Spec.ldORES_zk F E Kc := by
  intro R κ base hn hZ hO hS hb hf
  unfold LdORE.sayP
  rw [LdProg.zk_snoc, LdProg.zk_snoc, LdProg.zk_snoc, LdProg.after_snoc, LdProg.after_nil]
  refine ⟨⟨⟨(LdProg.zk_nil _ _).2 trivial, ?_⟩, ?_⟩, ldStepF_zk _ _ _ _ _⟩
  · rw [LdMv.Zk]
    exact (Chain.okGiven_one R.X.sayLink _).2
      (Or.inr ⟨R.X.sayMask κ, ldTenSay_goodM E Kc R.X κ hS, hb⟩)
  · rw [LdMv.Zk]
    exact (Chain.okGiven_one R.X.link _).2
      (Or.inr ⟨R.X.mask, ldSegRef_tn_goodM E Kc R.X hn hZ hO, hf⟩)

theorem ldORES_kinds : Spec.ldORES_kinds F E Kc := by
  intro R
  unfold LdORE.sayP
  rw [LdProg.all_snoc, LdProg.all_snoc, LdProg.all_snoc]
  exact ⟨⟨⟨LdProg.all_nilK _ _, Or.inl rfl⟩, Or.inl rfl⟩, Or.inr rfl⟩

end

end Cb
