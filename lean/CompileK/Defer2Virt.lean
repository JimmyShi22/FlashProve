-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Virt.lean: the hypothesis of the lemma on deferred programming of the random oracle
(`Rom.Spec.defer2`, CompileK/SpecDefer2.lean), through the translation of token numbers
(Compile/Step1_life2_Virt.lean: `virt`; Compile/Step1_life2_VirtMany.lean: `view`, `WF`, `Frame`):
under the hypotheses of its statement, if a program c obeys the discipline with joint charges
(`SafeO2`) at what it sees of a state, then virt N₀ δ c has `Step.Alw`, with `DSt.Ok2` after every
marked evaluation and every reveal, at the whole state.

One statement (`Compile.Batch.Disc.Spec.virt_of_safeO2`), its proof, and the lemmas under it.
Generic in the family of oracles. Nothing assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs. Programs, states and the two modes: Rom/Defer.lean. `virt N₀
δ c` is the program c with its token numbers translated: c's number v is the experiment's v if v <
N₀, else v + δ (`up`).

Why: the challengers of the scheme run the prover behind virt (a batch sees the setup's tokens and
its own, not those of earlier batches). The discipline speaks of what the program sees. The library
carries final states back (`run_virt`, `frame_virt`: lemmas on runs;
Compile/Batch/DisciplineVirt.lean: `tidy_of_view` ..); `Rom.Spec.defer2` asks its hypothesis of
every state on the way.

Main names, by the file's six parts, each under the hypotheses of its statement (in parts 1 to 3:
`WF N₀ δ D`):
  1. `view_postFresh`, `markedBad_view`, `view_postMarked`, `view_postReveal`: one move of the
    translated program, seen through the view, is the program's move (the pieces of the proof of
    `run_virt`, stated for `postFresh`, `postMarked`, `postReveal`).
  3. `markFit_virt`: `MarkFit` at the view ⇒ `MarkFit` at the whole state: an evaluation that is not
    seen holds only tokens that are not seen.
  4. `virt_alw`: Alw → Alw, for any classes and any pair of properties on the way with "Gv at the
    view, within the frame ⇒ G at the whole state".
  5. `tidy2_of_view`: the state's upward side (`Tidy2`) from the view and the frame: the companion
    of `tidy_of_view`.

Limits: this file says nothing on the scheme's challengers: what a batch sees at its start (the
upward twins of `tidy_view_start`, `closed_view_start`) and the key's handles at its end
(`closed_of_view`) are not here.
-/
import CompileK.Defer2Safe
import Compile.Batch.DisciplineVirt

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom Rom.DeferTail Rom.DeferTail2
open Compile.Life2
  (virt up down vis vis_iff vis_up down_up up_down viewVals viewShown viewVals_append
    contains_viewShown viewShown_append_up deadEvs deadEvs_releaseAll)
open Compile.Life2.Many
open Compile.Life2.WorldsX (mem_viewShown mem_deadEvs not_vis_iff getD_of_take_eq)
open Compile.Disc (Rules)
open VirtO

variable {S : OSpec} {sp : Split S} {α : Type} {N₀ δ : ℕ}

/-! ## 1. One move, seen through the view -/

theorem view_postFresh {D : DSt S} (h : WF N₀ δ D) (v : Bits) :
    view N₀ δ (postFresh D v) = postFresh (view N₀ δ D) v := by
  simp only [view, postFresh, viewVals_append h.len]

theorem markedBad_view {D : DSt S} (h : WF N₀ δ D) (o : S.ι) (t : Tok) (us : List Tok) :
    markedBad D o (up N₀ δ t) (us.map (up N₀ δ)) = markedBad (view N₀ δ D) o t us := by
  unfold markedBad
  rw [decide_le_up h, any_le_up h, contains_map_up,
    show (view N₀ δ D).shown = viewShown N₀ δ D.shown from rfl, contains_viewShown,
    show (view N₀ δ D).evs = viewEvs N₀ δ D.evs from rfl, any_view h.evs]

theorem view_postMarked {D : DSt S} (h : WF N₀ δ D) (o : S.ι) (t : Tok) (us : List Tok)
    (P : S.Dom o) (r : S.Rng o) (T : Table S) :
    view N₀ δ (postMarked sp D o (up N₀ δ t) (us.map (up N₀ δ)) P r T) =
      postMarked sp (view N₀ δ D) o t us P r T := by
  have e1 : viewEvs N₀ δ (D.evs ++ [⟨o, P, r, up N₀ δ t, us.map (up N₀ δ), D.vals.length, false⟩])
      = viewEvs N₀ δ D.evs ++ [⟨o, P, r, t, us, (view N₀ δ D).vals.length, false⟩] := by
    rw [viewEvs_append, viewEvs_cons_vis N₀ δ (vis_up N₀ δ t), length_view h]
    simp only [ren, down_up, down_length h, map_down_map_up]
    rfl
  show (⟨T, viewVals N₀ δ (D.vals ++ [List.ofFn (sp.split o r).2]),
      viewShown N₀ δ D.shown,
      viewEvs N₀ δ (D.evs ++ [⟨o, P, r, up N₀ δ t, us.map (up N₀ δ), D.vals.length, false⟩]),
      D.nPlain,
      D.viol || markedBad D o (up N₀ δ t) (us.map (up N₀ δ))⟩ : DSt S) = _
  rw [viewVals_append h.len, e1, markedBad_view h]
  rfl

theorem view_postReveal {D : DSt S} (h : WF N₀ δ D) (m : Bool) (ts : List Tok) :
    view N₀ δ (postReveal m D (ts.map (up N₀ δ))) = postReveal m (view N₀ δ D) ts := by
  have hs := h.evs.show_up ts
  have hr := hs.release m D.table
  have h3 := releaseAll_view m (D.shown ++ ts.map (up N₀ δ)) D.evs hs.inert D.table
  rw [viewShown_append_up] at h3
  simp only [view, postReveal]
  rw [h3, any_le_up h, ← closedUnder_view hr, viewShown_append_up]
  rfl

/-! ## 2. One move keeps the frame -/

theorem frame_postPlain {D : DSt S} (h : WF N₀ δ D) (o : S.ι) (T : Table S) :
    Frame N₀ δ D (postPlain D o T) :=
  ⟨⟨h.len, h.evs⟩, rfl, rfl, fun _ _ => rfl, fun _ h => h⟩

theorem frame_postFresh {D : DSt S} (h : WF N₀ δ D) (v : Bits) : Frame N₀ δ D (postFresh D v) :=
  ⟨⟨by have := h.len; simp only [postFresh, List.length_append]; omega, h.evs⟩,
    List.take_append_of_le_length h.len,
    rfl, fun _ _ => rfl, fun _ h => h⟩

theorem frame_postMarked {D : DSt S} (h : WF N₀ δ D) (o : S.ι) (t : Tok) (us : List Tok)
    (P : S.Dom o) (r : S.Rng o) (T : Table S) :
    Frame N₀ δ D (postMarked sp D o (up N₀ δ t) (us.map (up N₀ δ)) P r T) := by
  refine ⟨h.mark o P r t us T (List.ofFn (sp.split o r).2) _, List.take_append_of_le_length h.len,
    ?_, fun _ _ => rfl, fun _ h => h⟩
  simp [postMarked, deadEvs, vis_up]

theorem frame_postReveal {D : DSt S} (h : WF N₀ δ D) (m : Bool) (ts : List Tok) :
    Frame N₀ δ D (postReveal m D (ts.map (up N₀ δ))) := by
  have hs := h.evs.show_up ts
  have hr := hs.release m D.table
  refine ⟨⟨h.len, hr⟩, rfl, deadEvs_releaseAll m _ _ hs.inert _,
    fun t ht => ?_, fun t ht => List.mem_append_left _ ht⟩
  show (D.shown ++ ts.map (up N₀ δ)).contains t = D.shown.contains t
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_append]
  refine ⟨fun h1 => h1.resolve_right fun h2 => ?_, Or.inl⟩
  obtain ⟨v, -, hv⟩ := List.mem_map.1 h2
  rw [← hv, vis_up] at ht
  exact Bool.noConfusion ht

/-! ## 3. What is asked at a marked evaluation -/

theorem markFit_virt {K : Type} (cl : PtCls S K) (J : K → Bool) {D : DSt S} (h : WF N₀ δ D)
    {o : S.ι} (us : List Tok) (pt : Bits → List Bits → S.Dom o)
    (hm : MarkFit cl J (view N₀ δ D) us pt) :
    MarkFit cl J D (us.map (up N₀ δ)) pt := by
  intro hJ
  obtain ⟨b, hb, hs, hn⟩ := hm hJ
  refine ⟨up N₀ δ b, by rw [hb]; rfl, fun hsb => hs ?_, fun v hv ho => ?_⟩
  · have := contains_viewShown N₀ δ D.shown b
    rw [List.contains_iff_mem.2 hsb] at this
    exact List.contains_iff_mem.1 this
  · by_cases hvis : vis N₀ δ v.charged = true
    · obtain ⟨n1, n2⟩ := hn (ren N₀ δ v) (mem_viewEvs.2 ⟨v, hv, hvis, rfl⟩) ho
      refine ⟨fun e => n1 (by show b = down N₀ δ v.charged; rw [← e, down_up]), fun hmem => n2 ?_⟩
      show b ∈ v.others.map (down N₀ δ)
      exact List.mem_map.2 ⟨_, hmem, down_up N₀ δ b⟩
    · have hvis' : vis N₀ δ v.charged = false := by simpa using hvis
      refine ⟨fun e => ?_, fun hmem => ?_⟩
      · rw [← e, vis_up] at hvis'
        exact Bool.noConfusion hvis'
      · have := h.evs.unseen v hv hvis' _ hmem
        rw [vis_up] at this
        exact Bool.noConfusion this

/-! ## 4. The hypothesis on the way, behind the translation -/

theorem virt_alw {K : Type} {cl : PtCls S K} {J : K → Bool} {Gv G : DSt S → Prop} {D₁ : DSt S}
    (hG : ∀ D', Frame N₀ δ D₁ D' → Gv (view N₀ δ D') → G D') (c : Step S sp α) :
    ∀ (D : DSt S) (PostV : α × DSt S → Prop), Frame N₀ δ D₁ D → c.Alw cl J Gv (view N₀ δ D) PostV →
      (virt N₀ δ c).Alw cl J G D fun y => Frame N₀ δ D₁ y.2 ∧ PostV (y.1, view N₀ δ y.2) := by
  induction c with
  | pure a => exact fun D PostV hf h => ⟨hf, h⟩
  | sample n k ih => exact fun D PostV hf h r => ih r D PostV hf (h r)
  | plain o q k ih =>
    exact fun D PostV hf h y hy =>
      ih y.1 (postPlain D o y.2) PostV (hf.trans (frame_postPlain hf.wf o y.2)) (h y hy)
  | fresh L k ih =>
    intro D PostV hf h u
    have h1 := h u
    rw [length_view hf.wf, ← view_postFresh hf.wf] at h1
    exact ih _ _ PostV (hf.trans (frame_postFresh hf.wf _)) h1
  | marked o t us pt inj k ih =>
    intro D PostV hf h
    refine ⟨h.1, markFit_virt cl J hf.wf us pt h.2.1, fun r => ?_⟩
    have h1 := h.2.2 r
    rw [length_view hf.wf, ← view_postMarked hf.wf, val_view hf.wf, ← map_val_view hf.wf] at h1
    have hf' := hf.trans
      (frame_postMarked (sp := sp) hf.wf o t us
        (pt (D.val (up N₀ δ t)) ((us.map (up N₀ δ)).map D.val)) r D.table)
    exact ⟨hG _ hf' h1.1, ih _ _ _ PostV hf' h1.2⟩
  | reveal ts k ih =>
    intro D PostV hf h
    have h1 : Gv (postReveal true (view N₀ δ D) ts) ∧
        (k (ts.map (view N₀ δ D).val)).Alw cl J Gv (postReveal true (view N₀ δ D) ts) PostV := h
    rw [← view_postReveal hf.wf, ← map_val_view hf.wf] at h1
    have hf' := hf.trans (frame_postReveal hf.wf true ts)
    exact ⟨hG _ hf' h1.1, ih _ _ PostV hf' h1.2⟩

/-! ## 5. The state's upward side, from the view -/

/-- Under the hypotheses below: if what the program sees is orderly upwards, and it has left alone
what it does not see, the whole state is orderly upwards. The companion of `tidy_of_view`
(Compile/Batch/DisciplineVirt.lean). -/
theorem tidy2_of_view {Rl : Rules S} {Jo : S.ι → Bool} {ℓ2 : S.ι → ℕ} {D₁ D' : DSt S}
    (h1 : TidyO Rl D₁) (h2 : Tidy2 Jo ℓ2 D₁) (hl : N₀ + δ = D₁.vals.length)
    (hf : Frame N₀ δ D₁ D') (hv : Tidy2 Jo ℓ2 (view N₀ δ D')) : Tidy2 Jo ℓ2 D' := by
  intro e he hJ
  by_cases hvis : vis N₀ δ e.charged = true
  · obtain ⟨bv, hb, hlen, hsn⟩ := hv (ren N₀ δ e) (mem_viewEvs.2 ⟨e, he, hvis, rfl⟩) hJ
    have hb' : e.others.map (down N₀ δ) = [bv] := hb
    obtain ⟨b, hbe, hbd⟩ : ∃ b, e.others = [b] ∧ down N₀ δ b = bv := List.map_eq_singleton_iff.1 hb'
    have hbvis : vis N₀ δ b = true :=
      hf.wf.evs.seen e he hvis b (by rw [hbe]; exact List.mem_singleton.2 rfl)
    refine ⟨b, hbe, ?_, fun hs => ?_⟩
    · have e1 : (view N₀ δ D').val (down N₀ δ e.charged) = D'.val e.charged := by
        rw [val_view hf.wf, up_down N₀ δ hvis]
      have e2 : (view N₀ δ D').val bv = D'.val b := by
        rw [← hbd, val_view hf.wf, up_down N₀ δ hbvis]
      have hlen' : ℓ2 e.o ≤
          ((view N₀ δ D').val (down N₀ δ e.charged)).length + ((view N₀ δ D').val bv).length := hlen
      rw [e1, e2] at hlen'
      exact hlen'
    · have h3 : bv ∈ (view N₀ δ D').shown := by
        have := contains_viewShown N₀ δ D'.shown bv
        rw [← hbd, up_down N₀ δ hbvis, List.contains_iff_mem.2 hs] at this
        rw [← hbd]
        exact List.contains_iff_mem.1 this
      have h4 : down N₀ δ e.charged ∈ viewShown N₀ δ D'.shown := hsn h3
      have := contains_viewShown N₀ δ D'.shown (down N₀ δ e.charged)
      rw [up_down N₀ δ hvis, List.contains_iff_mem.2 h4] at this
      exact List.contains_iff_mem.1 this.symm
  · have hvis' : vis N₀ δ e.charged = false := by simpa using hvis
    have he₁ : e ∈ D₁.evs := (mem_deadEvs.1 (hf.dead ▸ mem_deadEvs.2 ⟨he, hvis'⟩)).1
    obtain ⟨b, hbe, hlen, hsn⟩ := h2 e he₁ hJ
    have hbm : b ∈ e.others := by rw [hbe]; exact List.mem_singleton.2 rfl
    have hbvis : vis N₀ δ b = false := hf.wf.evs.unseen e he hvis' b hbm
    have hval : ∀ x, x < D₁.vals.length → D'.val x = D₁.val x := fun x hx =>
      getD_of_take_eq hf.vals (hl ▸ hx)
    refine ⟨b, hbe, ?_, fun hs => ?_⟩
    · rw [hval _ (h1.charged_lt e he₁), hval _ (h1.others_lt e he₁ b hbm)]
      exact hlen
    · have h3 : b ∈ D₁.shown := by
        have := hf.shown b hbvis
        rw [List.contains_iff_mem.2 hs] at this
        exact List.contains_iff_mem.1 this.symm
      exact hf.sub _ (hsn h3)

/-! ## 6. From the discipline at the view to the hypothesis at the whole state -/

/-- The bridge of CompileK/Defer2Safe.lean (`alw_of_safeO2`), with "orderly both ways" kept as the
property on the way. -/
theorem alw_of_safeO2T (Rl : Rules S) (Jo : S.ι → Bool) (ℓ2 : S.ι → ℕ) (c : Step S sp α) :
    ∀ (d : DSt S) (Q : α → DSt S → Prop), TidyO Rl d → Tidy2 Jo ℓ2 d → SafeO2 Rl Jo ℓ2 c d Q →
      c.Alw (clO S) Jo (fun d' => TidyO Rl d' ∧ Tidy2 Jo ℓ2 d') d fun y =>
        Q y.1 y.2 ∧ TidyO Rl y.2 ∧ Tidy2 Jo ℓ2 y.2 := by
  induction c with
  | pure a => exact fun d Q hd h2 h => ⟨h, hd, h2⟩
  | sample n k ih => exact fun d Q hd h2 h r => ih r d Q hd h2 (h r)
  | plain o q k ih => exact fun d Q hd h2 h y _ => ih y.1 _ Q (hd.plain o y.2) (h2.plain o y.2) (h.2 y.1 y.2)
  | fresh L k ih => exact fun d Q hd h2 h u => ih _ _ Q (hd.fresh _) (Tidy2.fresh hd h2 _) (h u)
  | marked o t us pt inj k ih =>
    intro d Q hd h2 h
    obtain ⟨hus, htu, hfree, hbit, hmk, hJ, hk⟩ := h
    refine ⟨⟨fun _ _ _ _ => rfl, fun hJo => (hJ hJo).inj2⟩, fun hJo => ?_, fun r => ?_⟩
    · obtain ⟨b, hb, hbs, hbe, _⟩ := (hJ hJo).snd
      exact ⟨b, hb, hbs, hbe⟩
    · have hd' := hd.mark (sp := sp) hus htu hfree _ hbit hmk r d.table
      have h2' := Tidy2.mark (sp := sp) hd h2 hus hfree hJ (pt (d.val t) (us.map d.val)) r d.table
      exact ⟨⟨hd', h2'⟩, ih _ _ _ Q hd' h2' (hk r d.table)⟩
  | reveal ts k ih =>
    intro d Q hd h2 h
    obtain ⟨hc, hu, hk⟩ := h
    have hd' := hd.reveal hc (releaseAll true (d.shown ++ ts) d.evs d.table).2
    have h2' := Tidy2.reveal h2 hu (releaseAll true (d.shown ++ ts) d.evs d.table).2
    show (TidyO Rl (postReveal true d ts) ∧ Tidy2 Jo ℓ2 (postReveal true d ts)) ∧
      Step.Alw _ _ _ (k (ts.map d.val)) (postReveal true d ts) _
    rw [postReveal_eq]
    exact ⟨⟨hd', h2'⟩, ih _ _ Q hd' h2' (hk _)⟩

namespace Spec

/-- Through the translation of token numbers. Marked points lie at oracles of ks. D₁: a state that
is orderly both ways, with N₀ + δ tokens, from which the translation works, and whose view is
orderly both ways too (two premises of their own: `TidyO`, `Tidy2` at view N₀ δ D₁; at the start of
a batch they are proved by `tidy_view_start` (Compile/Batch/DisciplineVirt.lean) and
`tidy2_view_start` (CompileK/Defer2Door.lean), under their hypotheses). If c obeys the discipline
with joint charges at what it sees of D₁, then virt N₀ δ c has the hypothesis on the way at the
whole state; at its end: the frame, c's end at the view, and the whole state is orderly both ways.
-/
def virt_of_safeO2 : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α : Type) (N₀ δ : ℕ) (Rl : Rules S) (Jo : S.ι → Bool)
      (ℓ2 : S.ι → ℕ) (ks : Finset S.ι),
    (∀ o q, Rl.Mk o q → o ∈ ks) →
    ∀ (c : Step S sp α) (D₁ : DSt S) (Q : α → DSt S → Prop), TidyO Rl D₁ → Tidy2 Jo ℓ2 D₁ →
      N₀ + δ = D₁.vals.length → WF N₀ δ D₁ → TidyO Rl (view N₀ δ D₁) → Tidy2 Jo ℓ2 (view N₀ δ D₁) →
      SafeO2 Rl Jo ℓ2 c (view N₀ δ D₁) Q →
      (virt N₀ δ c).Alw (clO S) Jo (DSt.Ok2 (clO S) Jo (bits2 Rl Jo ℓ2) ks) D₁ fun y =>
        Frame N₀ δ D₁ y.2 ∧ Q y.1 (view N₀ δ y.2) ∧ TidyO Rl (view N₀ δ y.2) ∧
        TidyO Rl y.2 ∧ Tidy2 Jo ℓ2 y.2

end Spec

theorem virt_of_safeO2 : Spec.virt_of_safeO2 := by
  intro S sp α N₀ δ Rl Jo ℓ2 ks hks c D₁ Q h1 h2 hl hwf hv1 hv2 hc
  have hA := alw_of_safeO2T Rl Jo ℓ2 c (view N₀ δ D₁) Q hv1 hv2 hc
  refine alw_mono (fun y hy => ?_) _ _
    (virt_alw (G := DSt.Ok2 (clO S) Jo (bits2 Rl Jo ℓ2) ks) (D₁ := D₁)
      (fun D' hf hg =>
        ok2_of_tidy2 hks (tidy_of_view h1 hl hf hg.1) (tidy2_of_view h1 h2 hl hf hg.2))
      c D₁ _ (Frame.refl hwf) hA)
  exact ⟨hy.1, hy.2.1, hy.2.2.1, tidy_of_view h1 hl hy.1 hy.2.2.1,
    tidy2_of_view h1 h2 hl hy.1 hy.2.2.2⟩

end Compile.Batch.Disc
