-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqLast.lean: the last segment of a request has no closing of its own: it is in the last
part.

Definitions, statements (Cb.Spec.ldReqLast_*) and proofs.
A move (`LdMv`, Cb/Req1/LdSeg.lean) leads from one stage to another and is of one of seven kinds;
`LdMv.chain` is the move as a chain (`IOR.Chain`, Ior/KnowCollRulesChain.lean).

Why: a segment (`LdSeg`, Cb/Req1/LdSeg.lean) ends with folds, one sending and locations. The last
segment of a request has none of these: its groups stay open and are left to whoever follows. What
it has is a body (with the sendings of its reads and digits), then the batching of the pending
tensor rows. A request's last part (`LdReq.last`, Cb/Req1/LdReq.lean) has moves of the kinds "sub"
and "step". A sending, as any move, is a sub-protocol: its chain.

Main names:
  `m.asSub`, `p.asSub`: the move m, the list of moves p, with every move entered as the move "sub"
    of its own chain.
  `LdReq.withLast`: a request with any list of moves as last part.
  `Spec.ldReqLast_onto`: the links (`onto`) are the same.
  `Spec.ldReqLast_hyp`: `p.Hyp → p.asSub.Hyp`.
  `Spec.ldReqLast_after`: what is fresh after it is the same.
  `Spec.ldReqLast_zk`: `p.Hyp → p.Zk base → p.asSub.Zk base`.
  `Spec.ldReqLast_kinds`: all moves of `p.asSub` are of the kind "sub".
  `Spec.ldReqLast_nums`: the same numbers `nAll`, `nVer`, `pBad`, `pHid`.

Limits: this file does not say which groups are open at the end.
-/
import Cb.Req1.LdReqProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- a move as the move "sub" of its own chain -/
def LdMv.asSub {a b : LdStage E Kc} (m : LdMv a b) : LdMv a b := .sub a b m.chain

def LdProg.asSub : {a b : LdStage E Kc} → LdProg a b → LdProg a b
  | _, _, .nil a => .nil a
  | _, _, .snoc p m => .snoc p.asSub m.asSub

theorem LdProg.asSub_nil (a : LdStage E Kc) : (LdProg.nil a).asSub = .nil a := by rw [LdProg.asSub]
theorem LdProg.asSub_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).asSub = p.asSub.snoc m.asSub := by
  rw [LdProg.asSub]
theorem LdMv.asSub_chain {a b : LdStage E Kc} (m : LdMv a b) : m.asSub.chain = m.chain := rfl

theorem LdProg.asSub_kinds {a b : LdStage E Kc} (p : LdProg a b) :
    p.asSub.All fun t => t = .sub ∨ t = .step := by
  induction p with
  | nil => rw [LdProg.asSub_nil, LdProg.All]; trivial
  | snoc p m ih => rw [LdProg.asSub_snoc]; exact (LdProg.all_snoc _ _ _).2 ⟨ih, Or.inl rfl⟩

/-- A request whose last part is any list of moves, each entered as the move "sub" of its own
chain. -/
def LdReq.withLast {a z : LdStage E Kc} (first : LdSendD a) (a₁ : LdStage E Kc)
    (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
    (segs : LdSegs a₁ b) (last : LdProg b z) : LdReq a z :=
  ⟨first, a₁, more, b, segs, last.asSub, hm, last.asSub_kinds⟩

end

namespace Spec

def ldReqLast_onto : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (A : Joint Kc) (a b : LdStage E Kc)
      (c₀ : Chain Kc A a.J) (p : LdProg a b),
    p.asSub.onto c₀ = p.onto c₀

def ldReqLast_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc) (p : LdProg a b), p.Hyp → p.asSub.Hyp

def ldReqLast_after : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc)
      (p : LdProg a b) (base : MaskFact a.J.W → Prop),
    p.asSub.After base = p.After base

def ldReqLast_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc)
      (p : LdProg a b) (base : MaskFact a.J.W → Prop),
    p.Hyp → p.Zk base → p.asSub.Zk base

def ldReqLast_kinds : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc) (p : LdProg a b),
    p.asSub.All fun t => t = .sub

def ldReqLast_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc) (p : LdProg a b),
    p.asSub.nAll = p.nAll ∧ p.asSub.nVer = p.nVer ∧ p.asSub.pBad = p.pBad ∧ p.asSub.pHid = p.pHid

end Spec

theorem ldReqLast_onto : Spec.ldReqLast_onto := by
  intro E Kc _ _ A a b c₀ p
  induction p with
  | nil => rw [LdProg.asSub_nil]
  | snoc p m ih => rw [LdProg.asSub_snoc, LdProg.onto_snoc, LdProg.onto_snoc, ih, LdMv.asSub_chain]

theorem ldReqLast_hyp : Spec.ldReqLast_hyp := by
  intro E Kc _ _ a b p
  induction p with
  | nil => intro h; rw [LdProg.asSub_nil]; exact h
  | snoc p m ih =>
      intro h
      rw [LdProg.asSub_snoc]
      exact (LdProg.hyp_snoc _ _).2
        ⟨ih ((LdProg.hyp_snoc p m).1 h).1, ldSeg_mv E Kc _ _ m ((LdProg.hyp_snoc p m).1 h).2⟩

theorem ldReqLast_after : Spec.ldReqLast_after := by
  intro E Kc _ _ a b p
  induction p with
  | nil => intro base; rw [LdProg.asSub_nil]
  | snoc p m ih => intro base; rw [LdProg.asSub_snoc, LdProg.after_snoc, LdProg.after_snoc, ih]; rfl

theorem ldReqLast_zk : Spec.ldReqLast_zk := by
  intro E Kc _ _ a b p
  induction p with
  | nil => intro base _ h; rw [LdProg.asSub_nil]; exact h
  | snoc p m ih =>
      intro base h hz
      obtain ⟨h1, h2⟩ := (LdProg.hyp_snoc p m).1 h
      obtain ⟨z1, z2⟩ := (LdProg.zk_snoc p m base).1 hz
      rw [LdProg.asSub_snoc]
      refine (LdProg.zk_snoc _ _ _).2 ⟨ih base h1 z1, ?_⟩
      rw [ldReqLast_after]
      exact ldReq_mv_ok E Kc _ _ m _ h2 z2

theorem ldReqLast_kinds : Spec.ldReqLast_kinds := by
  intro E Kc _ _ a b p
  induction p with
  | nil => rw [LdProg.asSub_nil, LdProg.All]; trivial
  | snoc p m ih => rw [LdProg.asSub_snoc]; exact (LdProg.all_snoc _ _ _).2 ⟨ih, rfl⟩

theorem ldReqLast_nums : Spec.ldReqLast_nums := by
  intro E Kc _ _ a b p
  induction p with
  | nil => rw [LdProg.asSub_nil]; exact ⟨rfl, rfl, rfl, rfl⟩
  | snoc p m ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [LdProg.asSub_snoc, LdProg.nAll_snoc, LdProg.nVer_snoc, LdProg.pBad_snoc,
        LdProg.pHid_snoc, LdProg.nAll_snoc, LdProg.nVer_snoc, LdProg.pBad_snoc, LdProg.pHid_snoc,
        h1, h2, h3, h4, LdMv.asSub_chain]
      exact ⟨rfl, rfl, rfl, rfl⟩

end Cb
