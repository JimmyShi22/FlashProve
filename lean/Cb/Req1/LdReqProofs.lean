-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqProofs.lean: the proofs of the statements of Cb/Req1/LdReq.lean. By the rules for
chains (Ior/KnowCollRulesChain.lean), their relative forms (Cb/Req1/LdSegFresh.lean), the statements
on moves and segments (Cb/Req1/LdSegProofs.lean, Cb/Req1/LdSegProofsFold.lean,
Cb/Req1/LdSegProofsLoc.lean) and `goodT_pure` (stated in Ior/KnowCollRulesFrame.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReq
import Cb.Req1.LdSegProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain
open scoped ENNReal

theorem ldReq_mv_ok : Spec.ldReq_mv_ok := by
  intro E Kc _ _ a b m base h hz
  cases m with
  | send a d => exact (okGiven_one _ _).2 (Or.inl (d.goodT h))
  | sub a b c => exact hz
  | bat D => exact (okGiven_one _ _).2 (Or.inl (D.goodT h))
  | split D => exact (okGiven_one _ _).2 (Or.inr ⟨D.mask, ldSeg_split E Kc D h, hz⟩)
  | fold D l => exact (okGiven_one _ _).2 (Or.inl (ldSeg_fold_goodT D l h))
  | loc D => exact (okGiven_one _ _).2 (Or.inl (ldSeg_loc_goodT D h))
  | step a b f g m back => exact (okGiven_one _ _).2 (Or.inl (goodT_pure _ _ _ _ _ _ _ _ _ f g m back h))

section
variable {E Kc : Type} [Field E] [Fintype E]

namespace LdProg
theorem after_nil (a : LdStage E Kc) (base : MaskFact a.J.W → Prop) :
    (LdProg.nil a).After base = base := by rw [After]
theorem after_snoc {a b c : LdStage E Kc} (p : LdProg a b)
    (m : LdMv b c) (base : MaskFact a.J.W → Prop) :
    (p.snoc m).After base = m.After (p.After base) := by rw [After]
theorem zk_snoc {a b c : LdStage E Kc} (p : LdProg a b)
    (m : LdMv b c) (base : MaskFact a.J.W → Prop) :
    (p.snoc m).Zk base ↔ p.Zk base ∧ m.Zk (p.After base) := by rw [Zk]
theorem zk_nil (a : LdStage E Kc) (base : MaskFact a.J.W → Prop) :
    (LdProg.nil a).Zk base ↔ True := by rw [Zk]
theorem all_snoc {a b c : LdStage E Kc} (q : LdTag → Prop) (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).All q ↔ p.All q ∧ q m.tag := by rw [All]
theorem all_mono {a b : LdStage E Kc} (q q' : LdTag → Prop)
    (hq : ∀ t, q t → q' t) (p : LdProg a b) : p.All q → p.All q' := by
  induction p with
  | nil => intro _; rw [All]; trivial
  | snoc p m ih =>
    intro h; exact (all_snoc q' p m).2 ⟨ih ((all_snoc q p m).1 h).1, hq _ ((all_snoc q p m).1 h).2⟩
end LdProg

namespace LdSegs
variable {A : Joint Kc}
theorem onto_nil (a : LdStage E Kc) (c : Chain Kc A a.J) : (LdSegs.nil a).onto c = c := by rw [onto]
theorem onto_snoc {a b c : LdStage E Kc} (c₀ : Chain Kc A a.J) (S : LdSegs a b) (s : LdSeg b c) :
    (S.snoc s).onto c₀ = s.onto (S.onto c₀) := by rw [onto]
theorem hyp_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) :
    (S.snoc s).Hyp ↔ S.Hyp ∧ s.Hyp := by rw [Hyp]
theorem after_nil (a : LdStage E Kc) (base : MaskFact a.J.W → Prop) :
    (LdSegs.nil a).After base = base := by rw [After]
theorem after_snoc {a b c : LdStage E Kc} (S : LdSegs a b)
    (s : LdSeg b c) (base : MaskFact a.J.W → Prop) :
    (S.snoc s).After base = s.After (S.After base) := by rw [After]
theorem zk_snoc {a b c : LdStage E Kc} (S : LdSegs a b)
    (s : LdSeg b c) (base : MaskFact a.J.W → Prop) :
    (S.snoc s).Zk base ↔ S.Zk base ∧ s.Zk (S.After base) := by rw [Zk]
theorem len_nil (a : LdStage E Kc) : (LdSegs.nil a).len = 0 := by rw [len]
theorem len_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) :
    (S.snoc s).len = S.len + 1 := by rw [len]
theorem nAll_nil (a : LdStage E Kc) : (LdSegs.nil a).nAll = 0 := by rw [nAll]
theorem nVer_nil (a : LdStage E Kc) : (LdSegs.nil a).nVer = 0 := by rw [nVer]
theorem pBad_nil (a : LdStage E Kc) : (LdSegs.nil a).pBad = 0 := by rw [pBad]
theorem pHid_nil (a : LdStage E Kc) : (LdSegs.nil a).pHid = 0 := by rw [pHid]
theorem nAll_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) :
    (S.snoc s).nAll = S.nAll + s.nAll := by rw [nAll]
theorem nVer_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) :
    (S.snoc s).nVer = S.nVer + s.nVer := by rw [nVer]
theorem pBad_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) :
    (S.snoc s).pBad = S.pBad + s.pBad := by rw [pBad]
theorem pHid_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) :
    (S.snoc s).pHid = S.pHid + s.pHid := by rw [pHid]
theorem badLE_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) (α : ℝ≥0∞) :
    (S.snoc s).BadLE α ↔ S.BadLE α ∧ s.pBad ≤ α := by rw [BadLE]
theorem hidLE_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) (α : ℝ≥0∞) :
    (S.snoc s).HidLE α ↔ S.HidLE α ∧ s.pHid ≤ α := by rw [HidLE]
end LdSegs
end

theorem ldReq_prog_fresh : Spec.ldReq_prog_fresh := by
  intro E Kc _ _ A a b c₀ p
  induction p with
  | nil =>
      intro base hb f hf
      rw [LdProg.after_nil] at hf
      rw [LdProg.onto_nil]
      exact hb f hf
  | snoc p m ih =>
      intro base hb f hf
      rw [LdProg.after_snoc] at hf
      rw [LdProg.onto_snoc]
      exact freshFor_of_given Kc _ _ _ (p.onto c₀) m.chain (p.After base) f (ih base hb) hf

theorem ldReq_prog_ok : Spec.ldReq_prog_ok := by
  intro E Kc _ _ A a b c₀ p
  induction p with
  | nil =>
      intro base h0 _ _ _
      rw [LdProg.onto_nil]
      exact h0
  | snoc p m ih =>
      intro base h0 hb h hz
      rw [LdProg.onto_snoc]
      obtain ⟨h1, h2⟩ := (LdProg.hyp_snoc p m).1 h
      obtain ⟨z1, z2⟩ := (LdProg.zk_snoc p m base).1 hz
      exact ok_of_given Kc _ _ _ (p.onto c₀) m.chain (p.After base) (ih base h0 hb h1 z1)
        (ldReq_prog_fresh E Kc A _ _ c₀ p base hb) (ldReq_mv_ok E Kc _ _ m _ h2 z2)

section
variable {E Kc : Type} [Field E] [Fintype E] {A : Joint Kc} {a d : LdStage E Kc}

/-- what is fresh before, and after, the one sending of a segment -/
theorem LdSeg.mid_fresh (c₀ : Chain Kc A a.J) (s : LdSeg a d) (base : MaskFact a.J.W → Prop)
    (hb : ∀ g, base g → c₀.FreshFor g.kc g.Mk g.put) :
    ∀ f, s.mid base f → (s.fold.onto (s.bat.onto (s.body.onto c₀))).FreshFor f.kc f.Mk f.put :=
  ldReq_prog_fresh E Kc A _ _ _ s.fold _
    (ldReq_prog_fresh E Kc A _ _ _ s.bat _ (ldReq_prog_fresh E Kc A _ _ c₀ s.body base hb))

theorem LdSeg.snd_fresh (c₀ : Chain Kc A a.J) (s : LdSeg a d) (base : MaskFact a.J.W → Prop)
    (hb : ∀ g, base g → c₀.FreshFor g.kc g.Mk g.put) :
    ∀ f, (Chain.one s.snd.link).FreshGiven (s.mid base) f →
      (Chain.snoc (s.fold.onto (s.bat.onto (s.body.onto c₀))) s.snd.link).FreshFor
        f.kc f.Mk f.put := by
  intro f hf
  have := freshFor_of_given Kc _ _ _ (s.fold.onto (s.bat.onto (s.body.onto c₀))) (.one s.snd.link)
    (s.mid base) f (s.mid_fresh c₀ base hb) hf
  rwa [append_one] at this

end

theorem ldReq_seg_fresh : Spec.ldReq_seg_fresh := fun E Kc _ _ A _ _ c₀ s base hb =>
  ldReq_prog_fresh E Kc A _ _ _ s.loc _ (s.snd_fresh c₀ base hb)

theorem ldReq_seg_ok : Spec.ldReq_seg_ok := by
  intro E Kc _ _ A a d c₀ s base h0 hb h hz
  have f1 := ldReq_prog_fresh E Kc A _ _ c₀ s.body base hb
  have f2 := ldReq_prog_fresh E Kc A _ _ _ s.bat _ f1
  have o1 := ldReq_prog_ok E Kc A _ _ c₀ s.body base h0 hb h.body hz.body
  have o2 := ldReq_prog_ok E Kc A _ _ _ s.bat _ o1 f1 h.bat hz.bat
  have o3 := ldReq_prog_ok E Kc A _ _ _ s.fold _ o2 f2 h.fold hz.fold
  have o4 : (Chain.snoc (s.fold.onto (s.bat.onto (s.body.onto c₀))) s.snd.link).Ok :=
    (ok_snoc _ _).2 ⟨o3, Or.inl (s.snd.goodT h.snd)⟩
  exact ldReq_prog_ok E Kc A _ _ _ s.loc _ o4 (s.snd_fresh c₀ base hb) h.loc hz.loc

section
variable {E Kc : Type} [Field E] [Fintype E] {A : Joint Kc}

theorem LdSegs.onto_fresh {a b : LdStage E Kc} (S : LdSegs a b) :
    ∀ (c₀ : Chain Kc A a.J) (base : MaskFact a.J.W → Prop),
      (∀ g, base g → c₀.FreshFor g.kc g.Mk g.put) →
      ∀ f, S.After base f → (S.onto c₀).FreshFor f.kc f.Mk f.put := by
  induction S with
  | nil =>
      intro c₀ base hb f hf
      rw [LdSegs.after_nil] at hf
      rw [LdSegs.onto_nil]
      exact hb f hf
  | snoc S s ih =>
      intro c₀ base hb f hf
      rw [LdSegs.after_snoc] at hf
      rw [LdSegs.onto_snoc]
      exact ldReq_seg_fresh E Kc A _ _ (S.onto c₀) s (S.After base) (ih c₀ base hb) f hf

theorem LdSegs.onto_ok {a b : LdStage E Kc} (S : LdSegs a b) :
    ∀ (c₀ : Chain Kc A a.J) (base : MaskFact a.J.W → Prop),
      c₀.Ok → (∀ g, base g → c₀.FreshFor g.kc g.Mk g.put) → S.Hyp → S.Zk base → (S.onto c₀).Ok := by
  induction S with
  | nil =>
      intro c₀ base h0 _ _ _
      rw [LdSegs.onto_nil]
      exact h0
  | snoc S s ih =>
      intro c₀ base h0 hb h hz
      rw [LdSegs.onto_snoc]
      obtain ⟨h1, h2⟩ := (LdSegs.hyp_snoc S s).1 h
      obtain ⟨z1, z2⟩ := (LdSegs.zk_snoc S s base).1 hz
      exact ldReq_seg_ok E Kc A _ _ (S.onto c₀) s (S.After base) (ih c₀ base h0 hb h1 z1)
        (S.onto_fresh c₀ base hb) h2 z2

theorem LdSegs.onto_allB {a b : LdStage E Kc} (S : LdSegs a b) :
    ∀ c₀ : Chain Kc A a.J, c₀.AllB → S.Hyp → (S.onto c₀).AllB := by
  induction S with
  | nil =>
      intro c₀ h0 _
      rw [LdSegs.onto_nil]
      exact h0
  | snoc S s ih =>
      intro c₀ h0 h
      rw [LdSegs.onto_snoc]
      exact ldSeg_onto E Kc A _ _ _ s (ih c₀ h0 ((LdSegs.hyp_snoc S s).1 h).1)
        ((LdSegs.hyp_snoc S s).1 h).2

theorem LdSegs.onto_nums {a b : LdStage E Kc} (S : LdSegs a b) :
    ∀ c₀ : Chain Kc A a.J,
      (S.onto c₀).nAll = c₀.nAll + S.nAll ∧
      (S.onto c₀).nVer = c₀.nVer + S.nVer ∧
      (S.onto c₀).pBad = c₀.pBad + S.pBad ∧
      (S.onto c₀).pHid = c₀.pHid + S.pHid := by
  induction S with
  | nil =>
      intro c₀
      rw [LdSegs.onto_nil, LdSegs.nAll_nil, LdSegs.nVer_nil, LdSegs.pBad_nil, LdSegs.pHid_nil]
      exact ⟨rfl, rfl, (add_zero _).symm, (add_zero _).symm⟩
  | snoc S s ih =>
      intro c₀
      obtain ⟨h1, h2, h3, h4⟩ := ih c₀
      obtain ⟨k1, k2, k3, k4⟩ := (ldSeg_nums E Kc A _ _ (S.onto c₀) s).1
      rw [LdSegs.onto_snoc, LdSegs.nAll_snoc, LdSegs.nVer_snoc, LdSegs.pBad_snoc, LdSegs.pHid_snoc,
        k1, k2, k3, k4, h1, h2, h3, h4]
      exact ⟨Nat.add_assoc _ _ _, Nat.add_assoc _ _ _, add_assoc _ _ _, add_assoc _ _ _⟩

end

theorem ldReq_zk_free : Spec.ldReq_zk_free := by
  intro E Kc _ _ a b p
  induction p with
  | nil =>
      intro base _
      exact (LdProg.zk_nil _ _).2 trivial
  | snoc p m ih =>
      intro base h
      obtain ⟨h1, h2, h3⟩ := (LdProg.all_snoc _ p m).1 h
      refine (LdProg.zk_snoc p m base).2 ⟨ih base h1, ?_⟩
      cases m with
      | send a d => trivial
      | sub a b c => exact absurd rfl h2
      | bat D => trivial
      | split D => exact absurd rfl h3
      | fold D l => trivial
      | loc D => trivial
      | step a b f g m back => trivial

theorem ldReq_goodB : Spec.ldReq_goodB := fun _ Kc _ _ _ _ r w₀ h =>
  chain_goodB Kc _ _ r.chain w₀
    (r.last.onto_allB _
      (r.segs.onto_allB _
        (r.more.onto_allB _ ((allB_one _).2 (goodB_of_goodT' (r.first.goodT h.first))) h.more)
        h.segs) h.last)

theorem ldReq_goodT : Spec.ldReq_goodT := by
  intro E Kc _ _ a z r w₀ h hz
  have h0 : (Chain.one r.first.link).Ok := (ok_one _).2 (r.first.goodT h.first)
  have hb0 : ∀ g : MaskFact r.first.tgt.J.W,
      r.first.link.H.Fresh a.J.rels.rel r.first.link.P.bud g.kc g.Mk g.put →
      (Chain.one r.first.link).FreshFor g.kc g.Mk g.put :=
    fun g hg => (freshFor_one _ _ _ _).2 hg
  have hm : r.more.Zk _ :=
    ldReq_zk_free E Kc _ _ r.more
      (fun f => r.first.link.H.Fresh a.J.rels.rel r.first.link.P.bud f.kc f.Mk f.put)
      (LdProg.all_mono _ _
        (by
          rintro t (rfl | rfl)
            <;> exact ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩)
        r.more r.moreT)
  have h1 := ldReq_prog_ok E Kc _ _ _ _ r.more _ h0 hb0 h.more hm
  have hb : ∀ g, r.base₀ g → (r.more.onto (.one r.first.link)).FreshFor g.kc g.Mk g.put :=
    ldReq_prog_fresh E Kc _ _ _ _ r.more _ hb0
  exact chain_ok Kc _ _ r.chain w₀
    (ldReq_prog_ok E Kc _ _ _ _ r.last _ (r.segs.onto_ok _ _ h1 hb h.segs hz.segs)
      (r.segs.onto_fresh _ _ hb) h.last hz.last)

theorem ldReq_nums : Spec.ldReq_nums := by
  intro E Kc _ _ a z r w₀
  obtain ⟨n1, n2, n3, n4⟩ := chain_nums Kc _ _ r.chain w₀
  obtain ⟨m1, m2, m3, m4⟩ := r.more.onto_nums (.one r.first.link)
  obtain ⟨a1, a2, a3, a4⟩ := r.segs.onto_nums (r.more.onto (.one r.first.link))
  obtain ⟨b1, b2, b3, b4⟩ := r.last.onto_nums (r.segs.onto (r.more.onto (.one r.first.link)))
  obtain ⟨s1, -, s3, s4⟩ := (ldSeg_rounds E Kc).1 a r.first
  rw [n1, n2, n3, n4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (r.last.onto _).nAll = _
    rw [b1, a1, m1, nAll_one, s1]
  · show (r.last.onto _).nVer = _
    rw [b2, a2, m2, nVer_one]
  · show (r.last.onto _).pBad = _
    rw [b3, a3, m3, pBad_one, s3, zero_add]
  · show (r.last.onto _).pHid = _
    rw [b4, a4, m4, pHid_one, s4, zero_add]

theorem ldReq_alpha : Spec.ldReq_alpha := by
  intro E Kc _ _ a b S α
  induction S with
  | nil =>
      refine ⟨fun _ => ?_, fun _ => ?_⟩
      · rw [LdSegs.pBad_nil]; exact zero_le _
      · rw [LdSegs.pHid_nil]; exact zero_le _
  | snoc S s ih =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨h1, h2⟩ := (LdSegs.badLE_snoc S s α).1 h
        rw [LdSegs.pBad_snoc, LdSegs.len_snoc, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        exact add_le_add (ih.1 h1) h2
      · obtain ⟨h1, h2⟩ := (LdSegs.hidLE_snoc S s α).1 h
        rw [LdSegs.pHid_snoc, LdSegs.len_snoc, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        exact add_le_add (ih.2 h1) h2

end Cb
