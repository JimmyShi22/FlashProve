-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Skip.lean: under the hypotheses of the three statements, the hypothesis of the lemma
on deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean: `Step.Alw`,
with `DSt.Ok2`, `MarkFit`) passes from a program to the program that leaves out work that is never
shown (Rom/Skip.lean: `Skip`; Rom/SkipRel.lean: `StRel`).

Three statements (`Rom.DeferTail2.Spec.ok2_skip`, `Rom.DeferTail2.Spec.markFit_skip`,
`Rom.DeferTail2.Spec.alw_skip`) and their proofs. Generic in the family of oracles, the classes, the
programs. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs. Programs, states and the two modes: Rom/Defer.lean. `StRel w d₁ d₂`: the two states have the
same table and the same plain counts; w is a partial one-to-one matching of the two states' tokens
(`TokRel`); every record of the second is a record of the first renamed along w; and if the first
has no violation, neither has the second.
`stRel_marked`, `stRel_markedL`, `stRel_reveal`: the pieces of the proof of `Skip.run`
(Rom/SkipRun.lean), stated for the states `postMarked`, `postReveal`.

Why it holds: every record of the second experiment is a record of the first with the same oracle,
point, answer and flag, on matched tokens; the matching is one-to-one, keeps the strings, and keeps
"shown" (a sealed token is unshown on both sides). So lengths, "the right child is unshown", "it
stands in no earlier point" pass over. The adversary's queries read the table: `StRel` has the
clause "the two tables are equal".

Limits: this file is no statement on whole runs against two challengers, and none on any program of
the scheme. That PpU is Pp without such work is `skipFPpU`'s (Compile/Batch/MainKEGr.lean). Counts
are not carried here. They only fall: `EvsRel.count_le`, by oracle. `alw_skip` asks that G passes
along `StRel`: for G := Ok2 that is `ok2_skip`. A G with counts is not carried here (upper bounds by
oracle do pass along `StRel`: `StRel.within`, Rom/SkipWithin.lean): so the property at a halt comes
by CompileK/Defer2Supp.lean (from a theorem on the support), not through here.
-/
import CompileK.SpecDefer2
import Rom.SkipWithin
import Rom.SkipRun

set_option autoImplicit false

namespace Rom
namespace DeferTail2
open DeferTail

variable {S : OSpec} {K : Type}

namespace Spec

/-- States: what `Spec.defer2` asks of a state (`DSt.Ok2`) passes along `StRel` to the experiment
that leaves work out. -/
def ok2_skip : Prop :=
  ∀ (S : OSpec) (K : Type) (cl : PtCls S K) (J : K → Bool) (ℓ : K → ℕ) (ks : Finset K)
      (w : Wd) (d₁ d₂ : DSt S),
    StRel w d₁ d₂ → d₁.Ok2 cl J ℓ ks → d₂.Ok2 cl J ℓ ks

/-- States, at a marked evaluation: StRel w d₁ d₂, the further tokens matched by w, MarkFit d₁ us₁
pt ⇒ MarkFit d₂ us₂ pt. -/
def markFit_skip : Prop :=
  ∀ (S : OSpec) (K : Type) (cl : PtCls S K) (J : K → Bool) (w : Wd) (d₁ d₂ : DSt S) (o : S.ι)
      (us₁ us₂ : List Tok) (pt : Bits → List Bits → S.Dom o),
    StRel w d₁ d₂ → List.Forall₂ w.rel us₁ us₂ → MarkFit cl J d₁ us₁ pt → MarkFit cl J d₂ us₂ pt

end Spec

/-- Under `StRel w d₁ d₂`: an unshown token's partner is unshown -/
theorem not_shown_rel {w : Wd} {d₁ d₂ : DSt S} (h : StRel w d₁ d₂) {a b : Tok}
    (hab : w.rel a b) (ha : a ∉ d₁.shown) : b ∉ d₂.shown := by
  rcases hab with hab | hab
  · exact fun hb => ha ((h.tok.shown a b hab).2 hb)
  · exact (h.tok.slshown a b hab).2

theorem ok2_skip : Spec.ok2_skip := by
  intro S K cl J ℓ ks w d₁ d₂ h h₁
  refine ⟨h.viol h₁.1, fun v hv => ?_⟩
  obtain ⟨e₁, he₁, hch, hus, -, heq⟩ := h.evs.exists_left v hv
  obtain ⟨a1, a2, a3⟩ := h₁.2 e₁ he₁
  have hval : d₂.val v.charged = d₁.val e₁.charged := (h.tok.val _ _ hch).symm
  have hk : (⟨v.o, v.pt⟩ : Pt S) = ⟨e₁.o, e₁.pt⟩ := by rw [heq]; rfl
  have hrel : v.released = e₁.released := by rw [heq]; rfl
  rw [hk]
  refine ⟨a1, fun hJ => ?_, fun hJ => ?_⟩
  · rw [hval]
    exact a2 hJ
  · obtain ⟨b, hb, hl, hs⟩ := a3 hJ
    rw [hb] at hus
    obtain ⟨b₂, hb₂, hbb⟩ : ∃ b₂, v.others = [b₂] ∧ w.rel b b₂ := by
      obtain ⟨b₂, l, hbb, hnil, e⟩ := List.forall₂_cons_left_iff.1 hus
      rw [List.forall₂_nil_left_iff.1 hnil] at e
      exact ⟨b₂, e, hbb⟩
    refine ⟨b₂, hb₂, ?_, fun hr => not_shown_rel h hbb (hs (hrel ▸ hr))⟩
    rw [hval, show d₂.val b₂ = d₁.val b from (h.tok.val _ _ hbb).symm]
    exact hl

theorem markFit_skip : Spec.markFit_skip := by
  intro S K cl J w d₁ d₂ o us₁ us₂ pt h hus hm hJ
  obtain ⟨b, hb, hs, hn⟩ := hm hJ
  rw [hb] at hus
  cases hus with
  | cons hbb hnil =>
    cases hnil
    rename_i b₂
    refine ⟨b₂, rfl, not_shown_rel h hbb hs, fun v hv ho => ?_⟩
    obtain ⟨e₁, he₁, hch, hot, -, heq⟩ := h.evs.exists_left v hv
    have ho₁ : e₁.o = o := by rw [heq] at ho; exact ho
    obtain ⟨n1, n2⟩ := hn e₁ he₁ ho₁
    refine ⟨fun e => n1 (h.tok.injR _ _ _ hbb (e ▸ hch)), fun hm2 => ?_⟩
    obtain ⟨a, ha, hab⟩ := TokRel.mem_right hot hm2
    exact n2 (h.tok.injR _ _ _ hbb hab ▸ ha)

/-! ## The programs -/

variable {sp : Split S} {cl : PtCls S K} {J : K → Bool} {G : DSt S → Prop}

namespace Spec

/-- States, under the hypotheses below: the hypothesis on the way passes from a program to the
program that leaves out work that is never shown. The end: some pair (result, state) with Post₁,
related. -/
def alw_skip : Prop :=
  ∀ (S : OSpec) (sp : Split S) (K : Type) (cl : PtCls S K) (J : K → Bool) (G : DSt S → Prop),
    (∀ w d₁ d₂, StRel w d₁ d₂ → G d₁ → G d₂) →
    ∀ (α₁ α₂ : Type) (Q : Wd → α₁ → α₂ → Prop) (w : Wd) (c₁ : Step S sp α₁) (c₂ : Step S sp α₂),
      Skip Q w c₁ c₂ →
      ∀ (Post₁ : α₁ × DSt S → Prop) (d₁ d₂ : DSt S), StRel w d₁ d₂ → c₁.Alw cl J G d₁ Post₁ →
        c₂.Alw cl J G d₂ fun y₂ => ∃ y₁ w', Q w' y₁.1 y₂.1 ∧ StRel w' y₁.2 y₂.2 ∧ Post₁ y₁

end Spec

theorem stRel_marked {w w' : Wd} {d₁ d₂ : DSt S} (hs : StRel w d₁ d₂) (o : S.ι) {t₁ t₂ : Tok}
    {us₁ us₂ : List Tok} (pt : Bits → List Bits → S.Dom o) (ht : w.rel t₁ t₂)
    (hus : List.Forall₂ w.rel us₁ us₂) (a : S.Rng o) (hw : w ≤ w')
    (htok : TokRel w' (d₁.vals ++ [List.ofFn (sp.split o a).2])
      (d₂.vals ++ [List.ofFn (sp.split o a).2]) d₁.shown d₂.shown)
    (hrel : w'.rel d₁.vals.length d₂.vals.length) :
    StRel w' (postMarked sp d₁ o t₁ us₁ (pt (d₁.val t₁) (us₁.map d₁.val)) a d₁.table)
      (postMarked sp d₂ o t₂ us₂ (pt (d₂.val t₂) (us₂.map d₂.val)) a d₂.table) := by
  have hP : pt (d₁.val t₁) (us₁.map d₁.val) = pt (d₂.val t₂) (us₂.map d₂.val) := by
    have e1 : d₁.val t₁ = d₂.val t₂ := hs.tok.val _ _ ht
    have e2 : us₁.map d₁.val = us₂.map d₂.val := hs.tok.map_val hus
    rw [e1, e2]
  refine ⟨htok, hs.table, ?_, hs.nPlain, ?_⟩
  · have h1 := (hs.evs.mono hw).snoc_both
      (e₁ := ⟨o, pt (d₁.val t₁) (us₁.map d₁.val), a, t₁, us₁, d₁.vals.length, false⟩)
      (c := t₂) (us := us₂) (t := d₂.vals.length) (hw.rel _ _ ht)
        (Skip.forall₂_rel_mono hw hus) hrel
    simp only [Ev.ren, hP] at h1
    simp only [postMarked, hP]
    exact h1
  · intro hv
    simp only [postMarked] at hv ⊢
    rw [Bool.or_eq_false_iff] at hv ⊢
    exact ⟨hs.viol hv.1, markBad_rel hs o ht hus hv.2⟩

theorem stRel_markedL {w w' : Wd} {d₁ d₂ d₂' : DSt S} (hs : StRel w d₁ d₂) (o : S.ι) {t₁ : Tok}
    (us₁ : List Tok) (P : S.Dom o) (ht : w.hid t₁) (a : S.Rng o) (hw : w ≤ w')
    (htok : TokRel w' (d₁.vals ++ [List.ofFn (sp.split o a).2]) d₂'.vals d₁.shown d₂'.shown)
    (h1 : d₂'.table = d₂.table) (h2 : d₂'.evs = d₂.evs) (h3 : d₂'.nPlain = d₂.nPlain)
    (h4 : d₂'.viol = d₂.viol) :
    StRel w' (postMarked sp d₁ o t₁ us₁ P a d₁.table) d₂' := by
  refine ⟨htok, hs.table.trans h1.symm, ?_, hs.nPlain.trans h3.symm, fun hv => ?_⟩
  · rw [h2]
    exact (hs.evs.mono hw).snoc_left (hw.hid _ ht)
  · simp only [postMarked] at hv
    rw [Bool.or_eq_false_iff] at hv
    rw [h4]
    exact hs.viol hv.1

theorem stRel_reveal {w : Wd} {d₁ d₂ : DSt S} (hs : StRel w d₁ d₂)
    {ts₁ ts₂ : List Tok} (hts : List.Forall₂ w.ρ ts₁ ts₂) :
    StRel w (postReveal true d₁ ts₁) (postReveal true d₂ ts₂) := by
  have ht' := hs.tok.reveal hts
  have hr := releaseAll_rel ht' hs.evs d₁.table
  refine ⟨ht', ?_, ?_, hs.nPlain, ?_⟩
  · simp only [postReveal]
    rw [← hs.table]; exact hr.1
  · simp only [postReveal]
    rw [← hs.table]; exact hr.2
  · intro hv
    simp only [postReveal] at hv ⊢
    rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hv ⊢
    refine ⟨⟨hs.viol hv.1.1, ?_⟩, ?_⟩
    · have h1 : closedUnder (d₁.shown ++ ts₁)
            (releaseAll true (d₁.shown ++ ts₁) d₁.evs d₁.table).1 = true := by
        simpa using hv.1.2
      have h2 := closedUnder_rel ht' hr.2 h1
      rw [← hs.table, h2]
      rfl
    · rw [List.any_eq_false]
      intro u hu
      obtain ⟨a, _, hab⟩ := TokRel.mem_right hts hu
      have := (hs.tok.lt _ _ (Or.inl hab)).2
      simp only [decide_eq_true_eq]
      omega

theorem alw_skip : Spec.alw_skip := by
  intro S sp K cl J G hG α₁ α₂ Q w c₁ c₂ h Post₁
  induction h with
  | pure h => exact fun d₁ d₂ hs hA => ⟨(_, d₁), _, h, hs, hA⟩
  | sample n _ ih => exact fun d₁ d₂ hs hA r => ih r d₁ d₂ hs (hA r)
  | plain o q _ ih =>
    intro d₁ d₂ hs hA y hy
    rw [← hs.table] at hy
    refine ih y.1 (postPlain d₁ o y.2) (postPlain d₂ o y.2)
      ⟨hs.tok, rfl, hs.evs, ?_, hs.viol⟩ (hA y hy)
    simp only [postPlain]
    rw [hs.nPlain]
  | fresh ℓ _ ih =>
    intro d₁ d₂ hs hA u
    exact ih _ _ hs.tok.n₁ hs.tok.n₂ (postFresh d₁ (List.ofFn u)) (postFresh d₂ (List.ofFn u))
      ⟨hs.tok.pair _, hs.table, hs.evs.mono (Wd.le_pair _ hs.tok.n₁ hs.tok.n₂), hs.nPlain, hs.viol⟩
      (hA u)
  | @marked w o t₁ t₂ us₁ us₂ pt inj k₁ k₂ ht hus _ ih =>
    intro d₁ d₂ hs hA
    refine ⟨hA.1, markFit_skip S K cl J w d₁ d₂ o us₁ us₂ pt hs hus hA.2.1, fun r => ?_⟩
    have hs' := stRel_marked (sp := sp) hs o pt ht hus r (Wd.le_pair w hs.tok.n₁ hs.tok.n₂)
      (hs.tok.pair _) (Or.inl (Wd.pair_ρ _ _ _))
    exact ⟨hG _ _ _ hs' (hA.2.2 r).1, ih _ _ _ hs.tok.n₁ hs.tok.n₂ _ _ hs' (hA.2.2 r).2⟩
  | @markedS w o t₁ t₂ us₁ us₂ pt inj k₁ k₂ ht hus _ ih =>
    intro d₁ d₂ hs hA
    refine ⟨hA.1, markFit_skip S K cl J w d₁ d₂ o us₁ us₂ pt hs hus hA.2.1, fun r => ?_⟩
    have hs' := stRel_marked (sp := sp) hs o pt ht hus r (Wd.le_shut w hs.tok.n₁ hs.tok.n₂)
      (hs.tok.shut _) (Or.inr (Wd.shut_sl _ _ _))
    exact ⟨hG _ _ _ hs' (hA.2.2 r).1, ih _ _ _ hs.tok.n₁ hs.tok.n₂ _ _ hs' (hA.2.2 r).2⟩
  | @reveal w ts₁ ts₂ k₁ k₂ hts _ ih =>
    intro d₁ d₂ hs hA
    have hs' := stRel_reveal hs hts
    have e2 : ts₁.map d₁.val = ts₂.map d₂.val := hs.tok.map_val (Skip.forall₂_rel hts)
    refine ⟨hG _ _ _ hs' hA.1, ih _ _ _ hs' ?_⟩
    rw [← e2]
    exact hA.2
  | sampleL n _ ih => exact fun d₁ d₂ hs hA => ih 0 d₁ d₂ hs (hA 0)
  | freshL ℓ _ ih =>
    intro d₁ d₂ hs hA
    exact ih _ hs.tok.n₁ (postFresh d₁ (List.ofFn fun _ => false)) d₂
      ⟨hs.tok.dead _, hs.table, hs.evs.mono (Wd.le_dead _ hs.tok.n₁), hs.nPlain, hs.viol⟩
      (hA fun _ => false)
  | @markedL w o t₁ us₁ pt inj k₁ c₂ ht _ ih =>
    intro d₁ d₂ hs hA
    have r : S.Rng o := Classical.arbitrary _
    exact ih _ _ hs.tok.n₁ _ _
      (stRel_markedL (sp := sp) hs o us₁ _ ht r (Wd.le_dead w hs.tok.n₁)
        (hs.tok.dead _) rfl rfl rfl rfl) (hA.2.2 r).2
  | @markedF w o t₁ us₁ pt inj k₁ k₂ ht _ ih =>
    intro d₁ d₂ hs hA u
    let r : S.Rng o := (sp.split o).symm ((sp.split o (Classical.arbitrary _)).1, u)
    have hr : (sp.split o r).2 = u := by simp [r]
    refine ih _ _ _ hs.tok.n₁ hs.tok.n₂ _ _
      (stRel_markedL (sp := sp) (d₂' := postFresh d₂ (List.ofFn u)) hs o us₁ _ ht r
        (Wd.le_pair w hs.tok.n₁ hs.tok.n₂) ?_ rfl rfl rfl rfl) (hA.2.2 r).2
    rw [hr]
    exact hs.tok.pair _

end DeferTail2
end Rom
