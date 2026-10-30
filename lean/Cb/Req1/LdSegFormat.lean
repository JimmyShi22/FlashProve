-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFormat.lean: the format of the preamble of a request, read off its lists of moves.

Definitions, statements (in `Cb.Spec`) and proofs. By composition only: that a given move has a
format is in Cb/Req1/LdSegFormatMoves.lean.

Book-keeping: one input oracle, the encoded index, is followed through the steps of a request's
preamble.
Why: Cb/Req1/LdReqFormat.lean says what the format of a chain is (where the encoded index is at each
joint; the record is handed on; the honest prover hands its prover encoded index on; every link
bears what follows) and that it goes through chains. A request is not given as a chain but as lists
of moves in lists of segments (Cb/Req1/LdSeg.lean, Cb/Req1/LdReq.lean). Here the format is said of
these lists, and shown to be the format of the request's chain.

Main names:
  `a.fmt i rc px q`: the format of a stage, from data beside the stage: i (where the encoded index
    is among the stage's further oracles; the oracle messages with samples never hold it), rc (the
    record, read off the explicit part without the samples), px (the prover encoded index, read off
    the further witness), q (which sets of positions may still be asked for).
  `m.Fmt φ ψ`: a move: its chain has the format.
  `p.Fmt φ ψ`: a list of moves: the empty list changes nothing; else there is some format between
    the list and its last move.
  `s.Fmt φ ψ`: a segment: there are some formats before the batching, before the folds, with all
    tests open, and after the one sending.
  `S.Fmt`, `r.Fmt`: a list of segments; a request (first sending, further ones, segments, last
    part).
  `Spec.ldFmt_prog`, `Spec.ldFmt_seg`, `Spec.ldFmt_segs`: after any chain with a format: if the list
    of moves (the segment, the list of segments) has the format from there on, so has the chain of
    all links (`p.onto c₀`).
  `Spec.ldFmt_req`: r.Fmt φ ψ → r.chain.Fmt φ ψ. The conclusion is a hypothesis on formats of the
    theorems that take a request to the object's list (Cb/Obj/LdObjectReqSeg.lean).

Limits: this file does not say that any move has a format. The formats between are existential:
nothing says that they are of the form `a.fmt`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqFormat
import Cb.Req1.LdReqProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

section
variable {E Kc : Type} [Field E] [Fintype E] {E0 : ExtSpec} {Rc Pw : Type}

/-- The format of a stage. -/
def LdStage.fmt (a : LdStage E Kc) (i : IxAt E0 a.E₀) (rc : a.St → Rc)
    (px : a.Wp → Pw) (q : Finset a.Ex.Pos → Prop) : JFmt Kc E0 Rc Pw a.J :=
  ⟨i.inl a.S.ext, fun x => rc x.1, fun w => px w.2, q⟩

/-- a move has the format -/
def LdMv.Fmt {a b : LdStage E Kc} (m : LdMv a b)
    (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw b.J) : Prop := m.chain.Fmt φ ψ

/-- a list of moves has the format -/
def LdProg.Fmt :
    {a b : LdStage E Kc} → LdProg a b → JFmt Kc E0 Rc Pw a.J → JFmt Kc E0 Rc Pw b.J → Prop
  | _, _, .nil _, φ, ψ => φ = ψ
  | _, _, .snoc (b := b) p m, φ, ψ => ∃ χ : JFmt Kc E0 Rc Pw b.J, p.Fmt φ χ ∧ m.Fmt χ ψ

theorem LdProg.fmt_nil (a : LdStage E Kc) (φ ψ : JFmt Kc E0 Rc Pw a.J) :
    (LdProg.nil a).Fmt φ ψ ↔ φ = ψ := by rw [LdProg.Fmt]
theorem LdProg.fmt_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c)
    (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw c.J) :
    (p.snoc m).Fmt φ ψ ↔ ∃ χ : JFmt Kc E0 Rc Pw b.J, p.Fmt φ χ ∧ m.Fmt χ ψ := by rw [LdProg.Fmt]

/-- A segment has the format. -/
def LdSeg.Fmt {a d : LdStage E Kc} (s : LdSeg a d)
    (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw d.J) : Prop :=
  ∃ (φb : JFmt Kc E0 Rc Pw s.b.J) (φb₁ : JFmt Kc E0 Rc Pw s.b₁.J)
      (φc : JFmt Kc E0 Rc Pw s.c.J) (φs : JFmt Kc E0 Rc Pw s.snd.tgt.J),
    s.body.Fmt φ φb ∧ s.bat.Fmt φb φb₁ ∧ s.fold.Fmt φb₁ φc ∧ s.snd.link.Fmt φc φs ∧ s.loc.Fmt φs ψ

/-- a list of segments has the format -/
def LdSegs.Fmt :
    {a b : LdStage E Kc} → LdSegs a b → JFmt Kc E0 Rc Pw a.J → JFmt Kc E0 Rc Pw b.J → Prop
  | _, _, .nil _, φ, ψ => φ = ψ
  | _, _, .snoc (b := b) S s, φ, ψ => ∃ χ : JFmt Kc E0 Rc Pw b.J, S.Fmt φ χ ∧ s.Fmt χ ψ

theorem LdSegs.fmt_nil (a : LdStage E Kc) (φ ψ : JFmt Kc E0 Rc Pw a.J) :
    (LdSegs.nil a).Fmt φ ψ ↔ φ = ψ := by rw [LdSegs.Fmt]
theorem LdSegs.fmt_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c)
    (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw c.J) :
    (S.snoc s).Fmt φ ψ ↔ ∃ χ : JFmt Kc E0 Rc Pw b.J, S.Fmt φ χ ∧ s.Fmt χ ψ := by rw [LdSegs.Fmt]

/-- A request has the format. -/
def LdReq.Fmt {a z : LdStage E Kc} (r : LdReq a z)
    (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw z.J) : Prop :=
  ∃ (φ₀ : JFmt Kc E0 Rc Pw r.first.tgt.J)
      (φ₁ : JFmt Kc E0 Rc Pw r.a₁.J) (φb : JFmt Kc E0 Rc Pw r.b.J),
    r.first.link.Fmt φ φ₀ ∧ r.more.Fmt φ₀ φ₁ ∧ r.segs.Fmt φ₁ φb ∧ r.last.Fmt φb ψ

end

namespace Spec

/-- A list of moves after a chain. -/
def ldFmt_prog : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (A : Joint Kc)
      (a b : LdStage E Kc) (c₀ : Chain Kc A a.J) (p : LdProg a b) (φ₀ : JFmt Kc E0 Rc Pw A)
      (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw b.J),
    c₀.Fmt φ₀ φ → p.Fmt φ ψ → (p.onto c₀).Fmt φ₀ ψ

/-- A segment after a chain. -/
def ldFmt_seg : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (A : Joint Kc)
      (a d : LdStage E Kc) (c₀ : Chain Kc A a.J) (s : LdSeg a d) (φ₀ : JFmt Kc E0 Rc Pw A)
      (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw d.J),
    c₀.Fmt φ₀ φ → s.Fmt φ ψ → (s.onto c₀).Fmt φ₀ ψ

/-- A list of segments after a chain. -/
def ldFmt_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (A : Joint Kc)
      (a b : LdStage E Kc) (c₀ : Chain Kc A a.J) (S : LdSegs a b) (φ₀ : JFmt Kc E0 Rc Pw A)
      (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw b.J),
    c₀.Fmt φ₀ φ → S.Fmt φ ψ → (S.onto c₀).Fmt φ₀ ψ

/-- States: if `r.Fmt φ ψ`, the request's chain has the format. -/
def ldFmt_req : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (a z : LdStage E Kc)
      (r : LdReq a z) (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw z.J),
    r.Fmt φ ψ → r.chain.Fmt φ ψ

end Spec

theorem ldFmt_prog : Spec.ldFmt_prog := by
  intro E Kc _ _ E0 Rc Pw A a b c₀ p φ₀ φ
  induction p with
  | nil =>
      intro ψ h0 h
      rw [LdProg.onto_nil, ← (LdProg.fmt_nil _ φ ψ).1 h]
      exact h0
  | snoc p m ih =>
      intro ψ h0 h
      obtain ⟨χ, h1, h2⟩ := (LdProg.fmt_snoc p m φ ψ).1 h
      rw [LdProg.onto_snoc]
      exact fmt_append Kc E0 Rc Pw _ _ _ _ _ φ₀ χ ψ (ih χ h0 h1) h2

theorem ldFmt_seg : Spec.ldFmt_seg := by
  intro E Kc _ _ E0 Rc Pw A a d c₀ s φ₀ φ ψ h0 ⟨φb, φb₁, φc, φs, h1, h2, h3, h4, h5⟩
  refine ldFmt_prog E Kc E0 Rc Pw A _ _ _ s.loc φ₀ φs ψ ?_ h5
  exact (Chain.fmt_snoc _ _ φ₀ φs).2
    ⟨φc, ldFmt_prog E Kc E0 Rc Pw A _ _ _ s.fold φ₀ φb₁ φc
        (ldFmt_prog E Kc E0 Rc Pw A _ _ _ s.bat φ₀ φb φb₁
          (ldFmt_prog E Kc E0 Rc Pw A _ _ c₀ s.body φ₀ φ φb h0 h1) h2) h3,
      h4⟩

theorem ldFmt_segs : Spec.ldFmt_segs := by
  intro E Kc _ _ E0 Rc Pw A a b c₀ S φ₀ φ
  induction S with
  | nil =>
      intro ψ h0 h
      rw [LdSegs.onto_nil, ← (LdSegs.fmt_nil _ φ ψ).1 h]
      exact h0
  | snoc S s ih =>
      intro ψ h0 h
      obtain ⟨χ, h1, h2⟩ := (LdSegs.fmt_snoc S s φ ψ).1 h
      rw [LdSegs.onto_snoc]
      exact ldFmt_seg E Kc E0 Rc Pw A _ _ _ s φ₀ χ ψ (ih χ h0 h1) h2

theorem ldFmt_req : Spec.ldFmt_req := by
  intro E Kc _ _ E0 Rc Pw a z r φ ψ ⟨φ₀, φ₁, φb, h1, h2, h3, h4⟩
  exact ldFmt_prog E Kc E0 Rc Pw _ _ _ _ r.last φ φb ψ
    (ldFmt_segs E Kc E0 Rc Pw _ _ _ _ r.segs φ φ₁ φb
      (ldFmt_prog E Kc E0 Rc Pw _ _ _ _ r.more φ φ₀ φ₁ ((Chain.fmt_one _ φ φ₀).2 h1) h2) h3) h4

end Cb
