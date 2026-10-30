--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Keep/CEndWorth.lean: THE LOOKUP: THE KEY SIDE's END FORM, WRITTEN OUT: behind a
hearing whose key side has a level at all, the form g.cEnd is worth
  (1 - tau) * (vL - beta * mask sL) + tau * (vR - beta * mask (sL + 1))
at every later ledger and every mask row: sL, sL + 1: the two slots of the last level's end values;
vL, vR: what was shown under them; beta: the factor under which both were laid (that level's draw in
the further variable); tau: that level's line's draw. SO, WHERE beta IS NOT 0, TURNING ONE ENTRY OF
THE MASK ROW ALONE TURNS THE FORM's WORTH. Of the library's flat copy lkPad. Definitions, statements
and proofs.

Main names:
  EndIs rho F f sL tau beta vL vR: the sentence above, of a form f, from the ledger F on.
  level_end: behind every level the form that it hands down is such a form.
  fold_end: so behind every walk of at least one level.
  pad_end, lkPad_end: of g.cEnd behind a hearing, where the shape's number v of levels is not 0.
  EndIs.turns: where the reading of beta is not 0, in a field: there is a place j (sL or sL + 1)
    such that two mask rows which part at j alone give two worths.

Limits. That beta is not 0 is a premise of EndIs.turns: the flat routine tests a round's flag, not
the drawn value; the value's test stands in the maker of tapes. Nothing on which place of a view the
five letters are read from.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.PadNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie OnBytes.Psc

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The form's worth, written out, at every ledger later than F. -/
def EndIs (F : Fork) (f : Aff) (sL : ℕ) (tau beta vL vR : E) : Prop :=
  ∀ H, Later F H → ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
    f.value ρ (H.worldOf ρ mask entry) =
      (1 - ρ.val tau) * (ρ.val vL - ρ.val beta * mask sL) +
        ρ.val tau * (ρ.val vR - ρ.val beta * mask (sL + 1))

theorem EndIs.later {F G : Fork} {f : Aff} {sL : ℕ} {tau beta vL vR : E}
    (h : EndIs ρ F f sL tau beta vL vR) (hL : Later F G) : EndIs ρ G f sL tau beta vL vR :=
  fun H hH => h H (hL.trans hH)

/-- **Behind every level.** -/
theorem level_end (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Tape)
    (h : lkLevel s mu order F c = .ok ((s', G), c')) (hF : Sized F) :
    Later F G ∧ Sized G ∧ ∃ sL tau beta vL vR, EndIs ρ G s'.form sL tau beta vL vR := by
  obtain ⟨o, ho, _, _, e3⟩ := level_ok s mu order F G c c' s' h
  obtain ⟨p, m0, eps, rs, sentY, beta, vals, vL, vR, F3, p', _, _, _, _, _, _, _, hv2, _, _, _,
    hsR, hH3, _, _, hHG, _, _, _⟩ := levelIn_ran mu s.rho s.form order F G c c' o ho
  have hT := took_sized (1 + 2 * order.length + (2 + 2)) hF
  obtain ⟨_, s3, hnew, _⟩ := hideRun_ok _ F3 o.sL vals beta hT hH3
  obtain ⟨lG, sG, _⟩ := hide_new s3 hHG
  have L : Later F G := ((took_later F _).trans (hideRun_later hT hH3)).trans lG
  refine ⟨L, sG, o.sL, o.tau, beta, vals.getD 0 zeroE, vals.getD 1 zeroE, fun H hH mask entry => ?_⟩
  obtain ⟨_, _, a3, a4, a5⟩ := hnew 0 (by rw [hv2]; exact Nat.two_pos)
  obtain ⟨_, _, b3, b4, b5⟩ := hnew 1 (by rw [hv2]; exact Nat.one_lt_two)
  obtain ⟨_, a6, a7⟩ := (lG.trans hH).keep _ a3
  obtain ⟨_, b6, b7⟩ := (lG.trans hH).keep _ b3
  rw [Nat.add_zero] at a4 a5 a6 a7
  have wL : (H.worldOf ρ mask entry).slot o.sL =
      ρ.val (vals.getD 0 zeroE) - ρ.val beta * mask o.sL := by
    show ρ.val (H.vp.getD o.sL zeroE) - ρ.val (H.mf.getD o.sL zeroE) * mask o.sL = _
    rw [a6, a7, a4, a5]
  have wR : (H.worldOf ρ mask entry).slot (o.sL + 1) =
      ρ.val (vals.getD 1 zeroE) - ρ.val beta * mask (o.sL + 1) := by
    show ρ.val (H.vp.getD (o.sL + 1) zeroE) - ρ.val (H.mf.getD (o.sL + 1) zeroE) *
      mask (o.sL + 1) = _
    rw [b6, b7, b4, b5]
  rw [e3, hsR, Aff.value_add, Aff.value_scale, Aff.value_scale, Aff.value_slot, Aff.value_slot,
    wL, wR, ρ.sub, ρ.one]

/-- **Behind every walk of at least one level.** -/
theorem fold_end {α : Type} (f : Forest.Descent → α → Fl Forest.Descent)
    (hf : ∀ s a, ∃ mu order, f s a = lkLevel s mu order) :
    ∀ (l : List α) (s s' : Forest.Descent) (A B : Fork) (c c' : Tape), l ≠ [] →
      (l.foldlM f s) A c = .ok ((s', B), c') → Sized A →
      Sized B ∧ ∃ sL tau beta vL vR, EndIs ρ B s'.form sL tau beta vL vR
  | [], _, _, _, _, _, _, hne, _, _ => absurd rfl hne
  | a :: l, s, s', A, B, c, c', _, h, hA => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s a l A c ((s', B), c')).1 h
    obtain ⟨mu, order, e⟩ := hf s a
    rw [e] at h1
    obtain ⟨_, z1, x1⟩ := level_end ρ s s₁ mu order A F₁ c c₁ h1 hA
    cases l with
    | nil =>
      have e2 := (foldlM_nil_ok f s₁ F₁ c₁ ((s', B), c')).1 h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s₁ ∧ B = F₁) ∧ c' = c₁ := by simpa [Prod.ext_iff] using e2
      exact ⟨z1, x1⟩
    | cons b l' => exact fold_end f hf (b :: l') s₁ s' F₁ B c₁ c' (by simp) h2 z1

/-- From the chain of the runs of the routines that lkPad calls. -/
theorem pad_end {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (hF : Sized F)
    (hv : (M.h pub).v ≠ 0) (hL : Later M.F6 F') :
    ∃ sL tau beta vL vR, EndIs ρ F' g.cEnd sL tau beta vL vR := by
  have h4 : M.F4 = owed3 F := (head_cut P).1
  have z4 : Sized M.F4 := h4 ▸ owed3_sized hF
  obtain ⟨_, z5, _⟩ := tie_named M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie z4
  obtain ⟨_, sL, tau, beta, vL, vR, x⟩ := fold_end ρ _ (fun s mu => ⟨_, _, rfl⟩) _ _ _ _ _ _ _
    (by
      intro e
      exact hv (by simpa using congrArg List.length e)) P.keys z5
  refine ⟨sL, tau, beta, vL, vR, ?_⟩
  rw [P.heard]
  exact x.later ρ hL

end

/-- **Of the library's flat copy**, wherever it returns from a ledger that has its sizes, at a shape
whose key side has a level. -/
theorem lkPad_end (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) (hF : Sized F)
    (hv : g.shape.v ≠ 0) :
    ∃ sL tau beta vL vR, EndIs Reading.gl F' g.cEnd sL tau beta vL vR := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  have hg : g.shape = M.h pub := pad_shape P
  have H : FoNums.ok (M.h pub) = true := Cb.Fo.shape_ok P.shape (_root_.Fo.ask_ok P.ask)
  obtain ⟨l, scs, ptT, lvK, lvT, rowsK, rowsT, evK, evT, D, R⟩ :=
    pad_read Reading.gl P hF trivial 5 H
  exact pad_end Reading.gl P hF (hg ▸ hv) (P.fork ▸ R.table.later.trans R.r5.later)

/-- **Where beta is not 0, one entry of the mask row alone turns the worth.** -/
theorem EndIs.turns {K : Type} [Field K] {ρ : Reading K} {F : Fork} {f : Aff} {sL : ℕ}
    {tau beta vL vR : E} (h : EndIs ρ F f sL tau beta vL vR) (hb : ρ.val beta ≠ 0) :
    ∃ j, (j = sL ∨ j = sL + 1) ∧ ∀ H, Later F H → ∀ (m m' : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
      (∀ i, i ≠ j → m' i = m i) → m' j ≠ m j →
      f.value ρ (H.worldOf ρ m' entry) ≠ f.value ρ (H.worldOf ρ m entry) := by
  by_cases ht : ρ.val tau = 0
  · refine ⟨sL, Or.inl rfl, fun H hH m m' entry _ hj e => ?_⟩
    rw [h H hH m' entry, h H hH m entry, ht] at e
    have e' : ρ.val beta * (m' sL - m sL) = 0 := by linear_combination -e
    rcases mul_eq_zero.1 e' with x | x
    · exact hb x
    · exact hj (sub_eq_zero.1 x)
  · refine ⟨sL + 1, Or.inr rfl, fun H hH m m' entry hs hj e => ?_⟩
    rw [h H hH m' entry, h H hH m entry, hs sL (by omega)] at e
    have e' : ρ.val tau * (ρ.val beta * (m' (sL + 1) - m (sL + 1))) = 0 := by
      linear_combination -e
    rcases mul_eq_zero.1 e' with x | x
    · exact ht x
    · rcases mul_eq_zero.1 x with y | y
      · exact hb y
      · exact hj (sub_eq_zero.1 y)

end Fo.Tp

#print axioms Fo.Tp.level_end
#print axioms Fo.Tp.fold_end
#print axioms Fo.Tp.pad_end
#print axioms Fo.Tp.lkPad_end
#print axioms Fo.Tp.EndIs.turns
