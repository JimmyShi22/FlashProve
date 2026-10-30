-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefLkpPreProofs.lean: proofs for Cb/Req1/LdSegRefLkpPre.lean: each move from its
block's own theorem; the steps by the rule for a step that only maps the explicit part.

Main names (statements and hypotheses: Cb/Req1/LdSegRefLkpPre.lean):
  `ldSegRef_pre_hyp`: for E of characteristic p and `F : LdPreD E Kc S E₀ Wp`, `F.OK p` gives
    `F.prog.Hyp`, the hypotheses of all four moves of the list `F.prog` (the random shift, a step,
    the lookup, a step).
  `ldStepF_fmt` (stated in this file): see its docstring.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefLkpPre
import Cb.Ld.LdLkpAsm2Fmt
import Cb.Ld.LdLkpShiftProofs
import Cb.Req1.LdSegFrontTabZk

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section Step
variable {E Kc : Type} [Field E] [Fintype E]

theorem pre_mem_biUnion {α β : Type} (inst : DecidableEq β) {s : Finset α}
    {t : α → Finset β} {b : β} :
    b ∈ @Finset.biUnion α β inst s t ↔ ∃ a ∈ s, b ∈ t a :=
  Finset.mem_biUnion

omit [Field E] [Fintype E] in
/-- a position of the new oracles comes from that position alone -/
theorem sideG_id_mem (S : Sig E) (E₀ : ExtSpec) (u x : (E₀.prod S.ext).Pos) :
    x ∈ (sideG S (ExtMap.id E₀)).src u ↔ x = u := by
  rcases u with p | r
  · constructor
    · intro h
      obtain ⟨p', hp', hx⟩ := (pre_mem_biUnion _).1 h
      obtain rfl := Finset.mem_singleton.1 hp'
      exact Finset.mem_singleton.1 hx
    · rintro rfl
      exact (pre_mem_biUnion _).2 ⟨p, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
  · exact Finset.mem_singleton

/-- A step that only maps the explicit part has the format, if rc' (f x) = rc x for all x. -/
theorem ldStepF_fmt (S : Sig E) {St St' Wp : Type} {E₀ E0 : ExtSpec} {Rc Pw : Type}
    (A : Rels Kc St E₀ (S.Msg × Wp)) (A' : Rels Kc St' E₀ (S.Msg × Wp)) (f : St → St')
    (i : IxAt E0 E₀) (rc : St → Rc) (rc' : St' → Rc) (px : Wp → Pw)
    (q : Finset (E₀.prod S.ext).Pos → Prop) (h : ∀ x, rc' (f x) = rc x) :
    (ldStepF S A A' f).Fmt ((⟨S, St, E₀, Wp, A⟩ : LdStage E Kc).fmt i rc px q)
      ((⟨S, St', E₀, Wp, A'⟩ : LdStage E Kc).fmt i rc' px q) := by
  refine ldFmt_step E Kc E0 Rc Pw _ _ _ _ _ _ _ _
    (ExtMap.Moves.pair_left (ExtMap.Moves.comp (ExtMap.Moves.id i) (ExtMap.Moves.fst i S.ext))
      (ExtMap.Avoids.snd i S.ext))
    ?_ (fun _ => rfl) ?_
  · intro x x' e
    obtain rfl := Option.some.inj e
    exact h x.1
  · intro U V hV hU
    have e : V = U :=
      Finset.ext fun x =>
        (hV x).trans ⟨fun ⟨u, hu, hx⟩ => ((sideG_id_mem S E₀ u x).1 hx) ▸ hu,
          fun hx => ⟨x, hx, (sideG_id_mem S E₀ x x).2 rfl⟩⟩
    rw [e]
    exact hU

end Step

section
variable (E : Type) [Field E] [Fintype E]

theorem pre_shGood {Kc : Type} {S : Sig E} {E₀ : ExtSpec} {Wp : Type}
    (F : LdPreD E Kc S E₀ Wp) (h : TagInj F.P.g F.P.tag) :
    F.shBk.Good (F.PS.jIn F.Rr) (F.PS.jOut F.Rr) :=
  ldLkpShift_goodAt E F.St S.Msg Wp Kc E₀ F.PS F.Rr h

theorem pre_shCarry {Kc : Type} {S : Sig E} {E₀ : ExtSpec} {Wp : Type} (F : LdPreD E Kc S E₀ Wp)
    (base : MaskFact F.s0.J.W → Prop) (f : MaskFact F.s0.J.W) (hb : base f) : F.m1.After base f :=
  mvA_carry F.s0 (F.PS.jOut F.Rr) F.shBk (plain_draw _ _ _) (msg := F.msg) (Rd := fun _ => False)
    (fun _ _ _ _ _ _ => ⟨rfl, rfl⟩) base f (fun _ _ _ _ _ h => h.elim) hb

theorem ldSegRef_pre_hyp : Spec.ldSegRef_pre_hyp E := by
  intro p _ Kc S E₀ Wp F h
  unfold LdPreD.prog
  simp only [LdProg.hyp_snoc]
  refine ⟨⟨⟨⟨LdProg.hyp_nilK _, mvA_hyp F.s0 _ F.shBk (pre_shGood E F h.tags)⟩, ?_⟩, ?_⟩,
    ldStepF_hyp S _ _ F.e h.lastFw h.lastOn h.lastCo h.lastBw⟩
  · refine ldStepF_hyp S _ _ id ?_ (fun _ _ h => h) (fun _ => rfl) ?_
    · intro x y w hx
      refine ⟨hx.1, ⟨?_, trivial⟩, h.muFrom x y w hx.1 hx.2⟩
      show InTable (F.A0.v' + 1) F.A0.d _ _
      rw [← h.numV, ← h.numD]
      exact hx.2
    · intro x y w _ hx
      refine ⟨hx.1, ?_⟩
      have h1 : InTable (F.A0.v' + 1) F.A0.d (shKey F.P.v (F.P.key x.1 (F.msg w.1)) F.P.tag x.2)
          (shTab F.P.d (F.P.tab x.1) F.P.tag x.2) := hx.2.1
      rw [← h.numV, ← h.numD] at h1
      exact h1
  · exact mvA_hyp F.s2 F.jT F.lkBk
      (ldLkpAsm2F_base E p F.A F.N F.ι F.Mu E₀ Kc S.Msg Wp F.R1 F.msg h.inj h.places h.adm h.muOK)

theorem ldSegRef_pre_kinds : Spec.ldSegRef_pre_kinds E := by
  intro Kc S E₀ Wp F
  unfold LdPreD.prog
  simp only [LdProg.all_snoc]
  exact ⟨⟨⟨⟨LdProg.all_nilK _ _, Or.inr (Or.inl rfl)⟩, Or.inr (Or.inr rfl)⟩, Or.inr (Or.inl rfl)⟩,
    Or.inr (Or.inr rfl)⟩

theorem ldSegRef_pre_rounds : Spec.ldSegRef_pre_rounds E := by
  intro Kc S E₀ Wp F
  unfold LdPreD.prog
  rw [LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_nil]
  have e2 : F.m2.chain.nAll = 0 := (ldStepF_nums S _ _ _).1
  have e4 : F.m4.chain.nAll = 0 := (ldStepF_nums S _ _ _).1
  have e1 : F.m1.chain.nAll = 1 := by
    unfold LdPreD.m1 LdStage.mvA
    simp only [LdMv.chain, Chain.nAll]
    rfl
  have e3 : F.m3.chain.nAll = F.lkBk.R.shape.nAll := by
    unfold LdPreD.m3 LdStage.mvA
    simp only [LdMv.chain, Chain.nAll]
    rfl
  rw [e1, e2, e3, e4]
  omega

theorem ldSegRef_pre_zk : Spec.ldSegRef_pre_zk E := by
  intro p _ Kc S E₀ Wp F base D h hG hb
  unfold LdPreD.prog
  simp only [LdProg.zk_snoc, LdProg.zk_nil, LdProg.after_snoc, LdProg.after_nil]
  refine ⟨⟨⟨⟨trivial, ?_⟩, ldStepF_zk S _ _ _ _⟩, ?_⟩, ldStepF_zk S _ _ _ _⟩
  · exact mvA_okT F.s0 _ F.shBk base (pre_shGood E F h.tags)
      (draw_exact_any E₀ (S.Msg × Wp) E Prod.mk _)
  · exact mvA_okM F.s2 F.jT F.lkBk _ D hG
      (ldStepF_carry S _ _ id _ D.fact (pre_shCarry E F base D.fact hb))

theorem ldSegRef_pre_carry : Spec.ldSegRef_pre_carry E := by
  intro Kc S E₀ Wp F Rd hs base f hk hb
  unfold LdPreD.prog
  simp only [LdProg.after_snoc, LdProg.after_nil]
  exact ldStepF_carry S _ _ F.e _ f
    (mvA_carry F.s2 F.jT F.lkBk (ldLkpAsm2F_plain E F.A F.N F.ι E₀ S.Msg Wp Kc F.msg) hs _ f hk
      (ldStepF_carry S _ _ id _ f (pre_shCarry E F base f hb)))

theorem ldSegRef_pre_fmt : Spec.ldSegRef_pre_fmt E := by
  intro Kc S E₀ Wp F E0 Rc Pw i rc rc' px q he
  unfold LdPreD.prog
  simp only [LdProg.fmt_snoc, LdProg.fmt_nil]
  refine ⟨F.s3.fmt i (fun x => rc x.1.1) px q,
    ⟨F.s2.fmt i (fun x => rc x.1) px q, ⟨F.s1.fmt i (fun x => rc x.1) px q, ⟨_, rfl, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩
  · exact mvA_fmt F.s0 _ F.shBk (plain_draw _ _ _) i
      (Passes.draw E Prod.mk E₀ rc (fun x => rc x.1) fun _ _ => rfl) px q
  · exact ldStepF_fmt S _ _ id i _ _ px q fun _ => rfl
  · exact mvA_fmt F.s2 F.jT F.lkBk (ldLkpAsm2F_plain E F.A F.N F.ι E₀ S.Msg Wp Kc F.msg) i
      (passes_map (ldLkpAsm2F_pass E F.A F.N F.ι E₀ S.Msg Wp Kc F.msg) fun x => rc x.1) px q
  · exact ldStepF_fmt S _ _ F.e i _ _ px q he

end
end Cb
