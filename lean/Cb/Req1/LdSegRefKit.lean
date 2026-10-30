-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefKit.lean: two lists of moves in a row.

Book-keeping for sequential composition: two sequences of reductions (lists of moves) are appended,
and their side conditions and numbers combine part by part.
A definition, statements and proofs. Rules of the framework only; nothing of a text is rendered
here.
A list of moves (`LdProg`, Cb/Req1/LdSeg.lean) grows by one move at the end. `LdProg.After` and
`LdProg.Zk` are defined in Cb/Req1/LdReq.lean.

Why: the parts of a segment's body are built apart, each as a list of its own.

Main names:
  `p.app q`: the moves of p, then those of q.
  `Spec.ldProg_app_hyp`: what is asked of p.app q (`LdProg.Hyp`) is what is asked of p and of q.
  `Spec.ldProg_app_all`: likewise the kinds of moves (`LdProg.All`).
  `Spec.ldProg_app_after`: what is fresh after p.app q, given "base": what is fresh after q, given
    what is fresh after p.
  `Spec.ldProg_app_zk`: what zero knowledge asks, beside their hypotheses (`LdProg.Hyp`): of p,
    given "base"; of q, given what is fresh after p.
  `Spec.ldProg_app_nums`: rounds (`nAll`, `nVer`) and the two numbers `pBad`, `pHid` add (what pBad
    and pHid bound: `GoodB`, Ior/Masked.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR
open scoped ENNReal

/-- Two lists of moves in a row. -/
def LdProg.app {E Kc : Type} [Field E] [Fintype E] {a b : LdStage E Kc} (p : LdProg a b) :
    {c : LdStage E Kc} → LdProg b c → LdProg a c
  | _, .nil _ => p
  | _, .snoc q m => .snoc (p.app q) m

namespace Spec

def ldProg_app_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b c : LdStage E Kc) (p : LdProg a b) (q : LdProg b c),
    (p.app q).Hyp ↔ p.Hyp ∧ q.Hyp

def ldProg_app_all : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b c : LdStage E Kc) (p : LdProg a b)
      (q : LdProg b c) (k : LdTag → Prop),
    (p.app q).All k ↔ p.All k ∧ q.All k

def ldProg_app_after : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b c : LdStage E Kc) (p : LdProg a b)
      (q : LdProg b c) (base : MaskFact a.J.W → Prop),
    (p.app q).After base = q.After (p.After base)

def ldProg_app_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b c : LdStage E Kc) (p : LdProg a b)
      (q : LdProg b c) (base : MaskFact a.J.W → Prop),
    (p.app q).Zk base ↔ p.Zk base ∧ q.Zk (p.After base)

def ldProg_app_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b c : LdStage E Kc) (p : LdProg a b) (q : LdProg b c),
    (p.app q).nAll = p.nAll + q.nAll ∧
    (p.app q).nVer = p.nVer + q.nVer ∧
    (p.app q).pBad = p.pBad + q.pBad ∧
    (p.app q).pHid = p.pHid + q.pHid

end Spec

namespace LdProg
variable {E Kc : Type} [Field E] [Fintype E] {a b c d : LdStage E Kc}

theorem app_nil (p : LdProg a b) : p.app (.nil b) = p := by rw [app]
theorem app_snoc (p : LdProg a b) (q : LdProg b c) (m : LdMv c d) :
    p.app (q.snoc m) = (p.app q).snoc m := by rw [app]
theorem hyp_nilK (a : LdStage E Kc) : (LdProg.nil a).Hyp := by rw [Hyp]; trivial
theorem all_nilK (k : LdTag → Prop) (a : LdStage E Kc) : (LdProg.nil a).All k := by
  rw [All]; trivial

end LdProg

theorem ldProg_app_hyp : Spec.ldProg_app_hyp := by
  intro E Kc _ _ a b c p q
  induction q with
  | nil => rw [LdProg.app_nil]; exact ⟨fun h => ⟨h, LdProg.hyp_nilK _⟩, fun h => h.1⟩
  | snoc q m ih => rw [LdProg.app_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc, ih, and_assoc]

theorem ldProg_app_all : Spec.ldProg_app_all := by
  intro E Kc _ _ a b c p q k
  induction q with
  | nil => rw [LdProg.app_nil]; exact ⟨fun h => ⟨h, LdProg.all_nilK _ _⟩, fun h => h.1⟩
  | snoc q m ih => rw [LdProg.app_snoc, LdProg.all_snoc, LdProg.all_snoc, ih, and_assoc]

theorem ldProg_app_after : Spec.ldProg_app_after := by
  intro E Kc _ _ a b c p q base
  induction q with
  | nil => rw [LdProg.app_nil, LdProg.after_nil]
  | snoc q m ih => rw [LdProg.app_snoc, LdProg.after_snoc, LdProg.after_snoc, ih]

theorem ldProg_app_zk : Spec.ldProg_app_zk := by
  intro E Kc _ _ a b c p q base
  induction q with
  | nil => rw [LdProg.app_nil, LdProg.zk_nil]; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | snoc q m ih =>
    rw [LdProg.app_snoc, LdProg.zk_snoc, LdProg.zk_snoc, ih, ldProg_app_after, and_assoc]

theorem ldProg_app_nums : Spec.ldProg_app_nums := by
  intro E Kc _ _ a b c p q
  induction q with
  | nil =>
    rw [LdProg.app_nil, LdProg.nAll_nil, LdProg.nVer_nil, LdProg.pBad_nil, LdProg.pHid_nil]; simp
  | snoc q m ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [LdProg.app_snoc, LdProg.nAll_snoc, LdProg.nVer_snoc, LdProg.pBad_snoc, LdProg.pHid_snoc,
        LdProg.nAll_snoc, LdProg.nVer_snoc, LdProg.pBad_snoc, LdProg.pHid_snoc, h1, h2, h3, h4]
      exact ⟨by ring, by ring, by ring, by ring⟩

end Cb
