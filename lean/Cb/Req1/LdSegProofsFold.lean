-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegProofsFold.lean: proofs for Cb/Req1/LdSeg.lean: the lemma on kept messages
(`ldSeg_kept`), and: under `D.Hyp l`, the move "fold" has the whole bundle (`ldSeg_fold_goodT`). No
new definition.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSeg
import Cb.Ld.LdSigProofs
import Cb.Ld.LdBatSigProofs
import Ior.KnowCollRulesFrameProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

section
variable {E : Type} [Field E]

/-- the decoder and "collision" for a word as sent are those of the native word -/
theorem OMsg.dec_eq_decW (o : OMsg E) (f : o.Str) (σ : o.Smp) : o.dec f σ = o.decW (o.upW f) σ :=
  rfl
theorem OMsg.clash_iff_clashW (o : OMsg E) (f : o.Str) (ρ : o.Z.D) :
    o.Clash f ρ ↔ o.ClashW (o.upW f) ρ := Iff.rfl

/-- at a seed without collision the decoder returns the only candidate: for native words -/
theorem OMsg.decW_good (o : OMsg E) (f : o.C.Word) (σ : o.Smp) (h : ¬ o.ClashW f σ.1) (m : o.Msg) :
    o.decW f σ = some m ↔ o.C.Msgs o.e f m ∧ o.Z.val σ.1 m = σ.2 :=
  sig_dec_good E (OMsg.plain o.C o.Z o.e o.rank) f σ.1 h σ.2 m

end

theorem ldSeg_kept : Spec.ldSeg_kept := by
  intro E P _ _ _ C e h hL f w k σ hc hn hv
  refine ((h.o k).decW_good (h.sW k f) σ hc _).2 ⟨⟨h.rnd w.2 k, ?_⟩, hv⟩
  rw [← hL.slot k w.1 w.2]
  exact hL.fits k _ _ hn

section
variable {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc)

theorem LdFoldD.pE_isLocal : D.pE.IsLocal := by
  obtain ⟨-, hfs, -, hcomp, hpair⟩ := extMap_isLocal
  exact hpair _ _ _ _ _ (hpair _ _ _ _ _ (hfs _ _).1 (hcomp _ _ _ _ _ (hfs _ _).1 (hfs _ _).2))
    (hcomp _ _ _ _ _ (Sig.subExt_isLocal _) (hcomp _ _ _ _ _ (hfs _ _).2 (hfs _ _).2))

/-- the messages after the bridge, put together again (not all hypotheses are named here: see the
statement below) -/
theorem LdFoldD.rd_pW (w : D.mid.W)
    (hs : ∀ k : {a // D.cl a}, (D.held.msg w.1.1 k, D.held.rnd w.1.2 k) = w.2.1 k.1) :
    D.rd (D.S₂.msgs (D.pW w).1) (D.held.msg w.1.1) = D.S₁.msgs w.2.1 := by
  funext a
  by_cases h : D.cl a
  · have := congrArg Prod.fst (hs ⟨a, h⟩)
    simp only [LdFoldD.rd, dif_pos h]
    exact this
  · simp only [LdFoldD.rd, dif_neg h]
    rfl

theorem LdFoldD.rd_pB (w : D.tgt.W) :
    D.S₁.msgs (D.pB w).2.1 = D.rd (D.S₂.msgs w.1) (D.held.msg w.2.1.1) := by
  funext a
  by_cases h : D.cl a
  · simp only [LdFoldD.rd, LdFoldD.pB, Sig.msgs, dif_pos h]
  · simp only [LdFoldD.rd, LdFoldD.pB, Sig.msgs, dif_neg h]

/-- The bundle without its clause on zero knowledge, the condition not yet moved. (not all
hypotheses are named here: see the statement below) -/
theorem LdFoldD.link_goodB₀ (l : IOR.Link Kc D.src.J D.mid) (h : D.Hyp l) :
    IOR.GoodB (D.link l).R (D.link l).H (D.S.over D.src.A) (D.S₂.over D.tgt.A)
      (D.link l).ext (D.link l).P := by
  have g := ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 h.good).1
  refine ⟨g.point, g.isLocal.post _ _ D.pE_isLocal, ?_, ?_, ?_, g.prBad, g.cover, g.prCov, ?_⟩
  · intro x y w c ρ hR hρ
    obtain ⟨ho, hb⟩ := g.acc x y w c ρ hR hρ
    have hs := h.wit w x c ρ
    show (l.R.out x y ((Strat.map (fun p => (D.pX p.1, D.pW p.2)) (l.H.strat w x c)).run ρ).1).bind
          (fun x => some (D.pX x)) =
        some ((Strat.map (fun p => (D.pX p.1, D.pW p.2)) (l.H.strat w x c)).run ρ).2.1 ∧
      (D.S₂.over D.tgt.A).rel
        ((Strat.map (fun p => (D.pX p.1, D.pW p.2)) (l.H.strat w x c)).run ρ).2.1
        (D.pE.map
          (l.R.imp y ((Strat.map (fun p => (D.pX p.1, D.pW p.2)) (l.H.strat w x c)).run ρ).1))
        ((Strat.map (fun p => (D.pX p.1, D.pW p.2)) (l.H.strat w x c)).run ρ).2.2
    rw [Strat.run_map]
    refine ⟨by rw [ho]; rfl, ?_⟩
    generalize ((l.H.strat w x c).run ρ).2.1 = xo at hb
    generalize ((l.H.strat w x c).run ρ).2.2 = wo at hb hs
    generalize l.R.imp y ((l.H.strat w x c).run ρ).1 = yo at hb
    obtain ⟨hf, hE, hA, hA₀⟩ := hb
    refine ⟨fun a => hE a.1, fun a => hA a.1, hf, fun k => ?_, ?_⟩
    · have h1 := hA k.1
      have h2 : D.held.msg wo.1.1 k = (wo.2.1 k.1).1 := congrArg Prod.fst (hs k)
      show (D.S.om k.1.1).Z.val (xo.2.2 k.1).1 (D.held.msg wo.1.1 k) = (xo.2.2 k.1).2
      rw [h2]
      exact h1
    · show D.A₀.rel xo.2.1 yo.2.1 (D.rd (D.S₂.msgs (D.pW wo).1) (D.held.msg wo.1.1), wo.2.2)
      rw [D.rd_pW wo hs]
      exact hA₀
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
    have hb0 : l.R.red.out a τ = some (xo, l.R.imp a.2 τ) := red_out_eq_some.2 ⟨hxo, rfl⟩
    have hon := g.onOut a τ _ ha hb0
    have hT := h.word a τ _ hb0
    rw [show b = (b.1, D.pE.map (l.R.imp a.2 τ)) from Prod.ext rfl h2, ← Option.some.inj hf]
    refine ⟨fun i => hon.2.1 i.1, fun k => ?_, hon.2.2⟩
    have h3 : ¬ (D.S.om k.1.1).ClashW
        ((D.S.om k.1.1).upW ((l.R.imp a.2 τ).2.2 k.1)) (xo.2.2 k.1).1 := hon.2.1 k.1
    have hT' : D.sW k (l.R.imp a.2 τ).1 = (D.S.om k.1.1).upW ((l.R.imp a.2 τ).2.2 k.1) := hT k
    rw [← hT'] at h3
    exact h3
  · intro w x c ρ
    show D.tgt.A.core _ = _
    have hs := h.wit w x c ρ
    have hk := g.keeps w x c ρ
    show (D.S₂.over D.tgt.A).core
        ((Strat.map (fun p => (D.pX p.1, D.pW p.2)) (l.H.strat w x c)).run ρ).2.2 = _
    rw [Strat.run_map, ← hk]
    show D.A₀.core
        (D.rd (D.S₂.msgs (D.pW ((l.H.strat w x c).run ρ).2.2).1)
            (D.held.msg ((l.H.strat w x c).run ρ).2.2.1.1),
          ((l.H.strat w x c).run ρ).2.2.2.2) = _
    rw [D.rd_pW _ hs]
    rfl
  · intro a ha
    refine Doomed.mono _ _ ?_ (g.know a ha)
    intro τ hτ b w hb hw
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
    have hb0 : l.R.red.out a τ = some (xo, l.R.imp a.2 τ) := red_out_eq_some.2 ⟨hxo, rfl⟩
    have hT := h.word a τ _ hb0
    rw [show b = (b.1, D.pE.map (l.R.imp a.2 τ)) from Prod.ext rfl h2, ← Option.some.inj hf] at hw
    refine hτ _ (D.pB w) hb0 ?_
    obtain ⟨hd, hc, hk, hA₀⟩ := hw
    refine ⟨hc, fun i => ?_, ?_⟩
    · by_cases hi : D.cl i
      · have : (D.S.om i.1).decW (D.sW ⟨i, hi⟩ (l.R.imp a.2 τ).1) (xo.2.2 i) =
            some (D.held.msg w.2.1.1 ⟨i, hi⟩) := hk ⟨i, hi⟩
        have hT' : D.sW ⟨i, hi⟩ (l.R.imp a.2 τ).1 = (D.S.om i.1).upW ((l.R.imp a.2 τ).2.2 i) :=
          hT ⟨i, hi⟩
        rw [hT'] at this
        show (D.S.om i.1).dec _ _ = some ((D.pB w).2.1 i).1
        simp only [LdFoldD.pB, dif_pos hi]
        exact this
      · have := hd ⟨i, hi⟩
        show (D.S.om i.1).dec _ _ = some ((D.pB w).2.1 i).1
        simp only [LdFoldD.pB, dif_neg hi]
        exact this
    · show D.A₀.relR _ (D.S₁.msgs (D.pB w).2.1, w.2.2)
      rw [D.rd_pB]
      exact hA₀

/-- Under `h`: the move "fold" has the whole bundle. -/
theorem ldSeg_fold_goodT (l : IOR.Link Kc D.src.J D.mid) (h : D.Hyp l) : (D.link l).GoodT :=
  goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _
    ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).2
      ⟨D.link_goodB₀ l h, exact_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.good.exact⟩)

end
end Cb
