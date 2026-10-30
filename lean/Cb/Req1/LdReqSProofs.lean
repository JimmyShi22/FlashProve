-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqSProofs.lean: the proofs of the statements of Cb/Req1/LdReqS.lean.
-/
import Cb.Req1.LdReqS
import Cb.Req1.LdReqProofs
import Cb.Req1.LdSegFreshSProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

section
variable {E Kc : Type} [Field E] [Fintype E]

namespace LdSegs
theorem afterJ_nil (a : LdStage E Kc) (base : MaskFact a.J.W → Prop) :
    (LdSegs.nil a).AfterJ base = MaskFact.JCl base := by rw [AfterJ]
theorem afterJ_snoc {a b c : LdStage E Kc} (S : LdSegs a b)
    (s : LdSeg b c) (base : MaskFact a.J.W → Prop) :
    (S.snoc s).AfterJ base = MaskFact.JCl (s.After (S.AfterJ base)) := by rw [AfterJ]
theorem zkJ_snoc {a b c : LdStage E Kc} (S : LdSegs a b)
    (s : LdSeg b c) (base : MaskFact a.J.W → Prop) :
    (S.snoc s).ZkJ base ↔ S.ZkJ base ∧ s.Zk (S.AfterJ base) := by rw [ZkJ]
theorem zkJ_nil (a : LdStage E Kc) (base : MaskFact a.J.W → Prop) : (LdSegs.nil a).ZkJ base := by
  rw [ZkJ]; trivial
end LdSegs

end

section
variable (E Kc : Type) [Field E] [Fintype E]

theorem ldReqS_prog_fresh : Spec.ldReqS_prog_fresh E Kc := by
  intro A a b c₀ p
  induction p with
  | nil =>
      intro base _ _ hb f hf
      rw [LdProg.after_nil] at hf
      rw [LdProg.onto_nil]
      exact hb f hf
  | snoc p m ih =>
      intro base h0 h hb f hf
      rw [LdProg.after_snoc] at hf
      rw [LdProg.onto_snoc]
      obtain ⟨h1, h2⟩ := (LdProg.hyp_snoc p m).1 h
      exact freshS_of_given Kc _ _ _ (p.onto c₀) m.chain (p.After base) f (p.onto_allB c₀ h0 h1)
        (ldSeg_mv E Kc _ _ m h2) (ih base h0 h1 hb) hf

theorem ldReqS_prog_ok : Spec.ldReqS_prog_ok E Kc := by
  intro A a b c₀ p
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
      exact okS_of_given Kc _ _ _ (p.onto c₀) m.chain (p.After base) (ih base h0 hb h1 z1)
        (ldReqS_prog_fresh E Kc A _ _ c₀ p base (allB_of_okS Kc _ _ c₀ h0) h1 hb)
        (ldReq_mv_ok E Kc _ _ m _ h2 z2)

/-- what is fresh after the one sending of a segment -/
theorem LdSeg.snd_freshS {A : Joint Kc} {a d : LdStage E Kc} (c₀ : Chain Kc A a.J) (s : LdSeg a d)
    (base : MaskFact a.J.W → Prop) (h0 : c₀.AllB) (h : s.Hyp)
    (hb : ∀ g, base g → c₀.FreshS g.kc g.Mk g.put) :
    ∀ f, (Chain.one s.snd.link).FreshGiven (s.mid base) f →
      (Chain.snoc (s.fold.onto (s.bat.onto (s.body.onto c₀))) s.snd.link).FreshS
        f.kc f.Mk f.put := by
  intro f hf
  have a1 := s.body.onto_allB c₀ h0 h.body
  have a2 := s.bat.onto_allB _ a1 h.bat
  have a3 := s.fold.onto_allB _ a2 h.fold
  have f1 := ldReqS_prog_fresh E Kc A _ _ c₀ s.body base h0 h.body hb
  have f2 := ldReqS_prog_fresh E Kc A _ _ _ s.bat _ a1 h.bat f1
  have f3 := ldReqS_prog_fresh E Kc A _ _ _ s.fold _ a2 h.fold f2
  have := freshS_of_given Kc _ _ _ (s.fold.onto (s.bat.onto (s.body.onto c₀))) (.one s.snd.link)
    (s.mid base) f a3 ((allB_one _).2 (goodB_of_goodT' (s.snd.goodT h.snd))) f3 hf
  rwa [append_one] at this

theorem ldReqS_seg_fresh : Spec.ldReqS_seg_fresh E Kc := by
  intro A a d c₀ s base h0 h hb
  have a3 := s.fold.onto_allB _ (s.bat.onto_allB _ (s.body.onto_allB c₀ h0 h.body) h.bat) h.fold
  exact ldReqS_prog_fresh E Kc A _ _ _ s.loc _
    ((allB_snoc _ _).2 ⟨a3, goodB_of_goodT' (s.snd.goodT h.snd)⟩) h.loc
    (LdSeg.snd_freshS E Kc c₀ s base h0 h hb)

theorem ldReqS_seg_ok : Spec.ldReqS_seg_ok E Kc := by
  intro A a d c₀ s base h0 hb h hz
  have b0 := allB_of_okS Kc _ _ c₀ h0
  have f1 := ldReqS_prog_fresh E Kc A _ _ c₀ s.body base b0 h.body hb
  have o1 := ldReqS_prog_ok E Kc A _ _ c₀ s.body base h0 hb h.body hz.body
  have f2 := ldReqS_prog_fresh E Kc A _ _ _ s.bat _ (allB_of_okS Kc _ _ _ o1) h.bat f1
  have o2 := ldReqS_prog_ok E Kc A _ _ _ s.bat _ o1 f1 h.bat hz.bat
  have o3 := ldReqS_prog_ok E Kc A _ _ _ s.fold _ o2 f2 h.fold hz.fold
  have o4 : (Chain.snoc (s.fold.onto (s.bat.onto (s.body.onto c₀))) s.snd.link).OkS :=
    (okS_snoc _ _).2 ⟨o3, Or.inl (s.snd.goodT h.snd)⟩
  exact ldReqS_prog_ok E Kc A _ _ _ s.loc _ o4
    (LdSeg.snd_freshS E Kc c₀ s base b0 h hb) h.loc hz.loc

theorem LdMv.mono {a b : LdStage E Kc} (m : LdMv a b)
    (X X' : MaskFact a.J.W → Prop) (hX : ∀ g, X g → X' g) :
    (∀ f, m.After X f → m.After X' f) ∧ (m.Zk X → m.Zk X') := by
  refine ⟨fun f hf => freshGiven_mono Kc _ _ m.chain X X' f hX hf, ?_⟩
  cases m with
  | sub _ _ c => exact fun h => okGiven_mono Kc _ _ c X X' hX h
  | split D => exact fun h => hX _ h
  | send _ _ => exact fun _ => trivial
  | bat _ => exact fun _ => trivial
  | fold _ _ => exact fun _ => trivial
  | loc _ => exact fun _ => trivial
  | step _ _ _ _ _ _ => exact fun _ => trivial

theorem LdProg.mono {a b : LdStage E Kc} (p : LdProg a b) :
    ∀ (X X' : MaskFact a.J.W → Prop),
      (∀ g, X g → X' g) → (∀ f, p.After X f → p.After X' f) ∧ (p.Zk X → p.Zk X') := by
  induction p with
  | nil =>
      intro X X' hX
      refine ⟨fun f hf => ?_, fun _ => (LdProg.zk_nil _ _).2 trivial⟩
      rw [LdProg.after_nil] at hf ⊢
      exact hX f hf
  | snoc p m ih =>
      intro X X' hX
      obtain ⟨i1, i2⟩ := ih X X' hX
      obtain ⟨m1, m2⟩ := LdMv.mono E Kc m (p.After X) (p.After X') i1
      refine ⟨fun f hf => ?_, fun h => ?_⟩
      · rw [LdProg.after_snoc] at hf ⊢
        exact m1 f hf
      · obtain ⟨z1, z2⟩ := (LdProg.zk_snoc p m X).1 h
        exact (LdProg.zk_snoc p m X').2 ⟨i2 z1, m2 z2⟩

theorem LdSeg.mono {a d : LdStage E Kc} (s : LdSeg a d)
    (X X' : MaskFact a.J.W → Prop) (hX : ∀ g, X g → X' g) :
    (∀ f, s.After X f → s.After X' f) ∧ (s.Zk X → s.Zk X') := by
  obtain ⟨b1, b2⟩ := LdProg.mono E Kc s.body X X' hX
  obtain ⟨c1, c2⟩ := LdProg.mono E Kc s.bat _ _ b1
  obtain ⟨d1, d2⟩ := LdProg.mono E Kc s.fold _ _ c1
  have e1 : ∀ f, (Chain.one s.snd.link).FreshGiven (s.mid X) f →
      (Chain.one s.snd.link).FreshGiven (s.mid X') f :=
    fun f hf => freshGiven_mono Kc _ _ _ _ _ f d1 hf
  obtain ⟨g1, g2⟩ := LdProg.mono E Kc s.loc _ _ e1
  exact ⟨g1, fun h => ⟨b2 h.body, c2 h.bat, d2 h.fold, g2 h.loc⟩⟩

theorem ldReqS_mono : Spec.ldReqS_mono E Kc :=
  ⟨fun _ _ p X X' hX => LdProg.mono E Kc p X X' hX, fun _ _ s X X' hX => LdSeg.mono E Kc s X X' hX⟩

/-- the sets `S.After base` lie in the closed ones; `S.Zk base` gives `S.ZkJ base` -/
theorem LdSegs.toJ {a b : LdStage E Kc} (S : LdSegs a b) (base : MaskFact a.J.W → Prop) :
    (∀ f, S.After base f → S.AfterJ base f) ∧ (S.Zk base → S.ZkJ base) := by
  induction S with
  | nil =>
      refine ⟨fun f hf => ?_, fun _ => LdSegs.zkJ_nil _ _⟩
      rw [LdSegs.after_nil] at hf
      rw [LdSegs.afterJ_nil]
      exact .base f hf
  | snoc S s ih =>
      obtain ⟨i1, i2⟩ := ih
      obtain ⟨m1, m2⟩ := LdSeg.mono E Kc s _ _ i1
      refine ⟨fun f hf => ?_, fun h => ?_⟩
      · rw [LdSegs.after_snoc] at hf
        rw [LdSegs.afterJ_snoc]
        exact .base f (m1 f hf)
      · obtain ⟨z1, z2⟩ := (LdSegs.zk_snoc S s base).1 h
        exact (LdSegs.zkJ_snoc S s base).2 ⟨i2 z1, m2 z2⟩

theorem ldReqS_of_zk : Spec.ldReqS_of_zk E Kc := fun _ _ r h =>
  ⟨(LdSegs.toJ E Kc r.segs r.base₀).2 h.segs,
    (LdProg.mono E Kc r.last _ _ (LdSegs.toJ E Kc r.segs r.base₀).1).2 h.last⟩

/-- the segments after a chain -/
theorem LdSegs.ontoS {A : Joint Kc} {a b : LdStage E Kc} (S : LdSegs a b) :
    ∀ (c₀ : Chain Kc A a.J) (base : MaskFact a.J.W → Prop), c₀.OkS →
      (∀ g, base g → c₀.FreshS g.kc g.Mk g.put) → S.Hyp → S.ZkJ base →
      (S.onto c₀).OkS ∧ ∀ f, S.AfterJ base f → (S.onto c₀).FreshS f.kc f.Mk f.put := by
  induction S with
  | nil =>
      intro c₀ base h0 hb _ _
      rw [LdSegs.onto_nil, LdSegs.afterJ_nil]
      exact ⟨h0, freshS_jcl Kc _ _ c₀ base hb⟩
  | snoc S s ih =>
      intro c₀ base h0 hb h hz
      obtain ⟨h1, h2⟩ := (LdSegs.hyp_snoc S s).1 h
      obtain ⟨z1, z2⟩ := (LdSegs.zkJ_snoc S s base).1 hz
      obtain ⟨o, f⟩ := ih c₀ base h0 hb h1 z1
      rw [LdSegs.onto_snoc, LdSegs.afterJ_snoc]
      exact ⟨ldReqS_seg_ok E Kc A _ _ (S.onto c₀) s _ o f h2 z2,
        freshS_jcl Kc _ _ _ _
          (ldReqS_seg_fresh E Kc A _ _ (S.onto c₀) s _ (allB_of_okS Kc _ _ _ o) h2 f)⟩

theorem ldReqS_goodT : Spec.ldReqS_goodT E Kc := by
  intro a z r w₀ h hz
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
  have hb : ∀ g, r.base₀ g → (r.more.onto (.one r.first.link)).FreshS g.kc g.Mk g.put := fun g hg =>
    freshS_of_for Kc _ _ _ _ g.kc g.Mk g.put ((ok_of_allT Kc _ _ _).2 h1)
      (ldReq_prog_fresh E Kc _ _ _ _ r.more _ hb0 g hg)
  obtain ⟨o, f⟩ := LdSegs.ontoS E Kc r.segs _ _ (okS_of_ok Kc _ _ _ h1) hb h.segs hz.segs
  exact chainS_ok Kc _ _ r.chain w₀ (ldReqS_prog_ok E Kc _ _ _ _ r.last _ o f h.last hz.last)

end
end Cb
