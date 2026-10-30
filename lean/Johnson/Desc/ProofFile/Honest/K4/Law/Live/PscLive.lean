-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/PscLive.lean: CONDITIONAL. WHEN THE CLAIM THAT A MASKED
SUMCHECK LEAVES NAMES A SLOT WITH A COEFFICIENT THAT IS NOT 0; AND THE CLAUSE ON A TAPE OF ROUNDS
FROM WHICH THAT IS HAD.

What is here. A KIT ON THE VERIFIER's TEXT: no prover is in it. Definitions, statements and proofs.

  `TapeLive t`: **the clause on a tape** t of rounds (OnBytes/K/Kc/Flat.lean): of EVERY round of
      t that holds just one drawn element: the element reads, in the library's field, as not 0; and
      as not 1 where the round's name is the plan's name "BAT-sigma" (a round that batches rows) or
      "JOIN" (a round that draws a joining point). The names are compared as strings; three of the
      library's round names share "JOIN" (OnBytes/Model/Rounds.lean).
  `TapeLive.sub`, `TapeLive.at_`, `TapeLive.ne_one_bat`, `TapeLive.ne_one_join`: a tape whose
      rounds are rounds of t meets the clause; "not 0", and "not 1" under each of the two names, at
      a round that is written out. (`TapeLive.drop`, `TapeLive.of_putBack`: Law/Live/Stages.lean.)
  `PscLive p`: the sumcheck's state p is live: its joining element eps reads as not 0, and so
      do each variable's challenge and its psi at that challenge. `PscLive.walk1`, `PscLive.walk2`:
      then no word of its hiding walk reads as 0, nor does the product P of the psi.
  `live_win`, `live_start`: **the two ways in which a live sumcheck's own claim makes a slot
      live**: it has a coefficient that is not 0 on every slot of its window that its start form and
      its kept form do not name; and on every slot outside its window that its kept form does not
      name and on which its start form has a coefficient that is not 0.
  `IsEqOrPlain`, `pscLive_of`: `PscLive` from three premises: eps reads as not 0; each weight is
      an equality weight or the plain one; each challenge reads as not 0.
  `msOf_drawn`: the challenges that the library reads off rounds of one drawn element each
      (`msOf`, OnBytes/Desc/First/P1/FlTape.lean) are these rounds' drawn elements.
  `win_len`: how long the window is.

Kin. Of the verifier program's own state the library has cases of `live_win` and `live_start`:
`coef_rowForm_window`, `coef_rowForm_start`, with `walk_at` (Johnson/Desc/K11/Live/Run.lean: the
head's merge; nothing kept; a start form of one pair), and `word_leaves`, `live_leaves`
(Johnson/Desc/K8/Honest/EqSlots.lean). Of the description's `MaskedSum.Heard`: `delta_own`,
`delta_lead` (Honest/K6/GoodLaw/Coef.lean), `record_coef` (Honest/K3/Good/Coef.lean),
`row_own_live`, `row_start_live` (Johnson/Desc/K5/Honest/Law/Live.lean). `win_len` is `win_three`
(Johnson/Road/K4/Slots/HearSpares.lean: "at most") with one challenge for each variable asked, and
"just". `TapeLive` is a condition on drawn elements, as `ClauseBy` (Honest/K3/Good/Live/Clause.lean)
is for a lookup and `heardLive` (Johnson/Desc/K5/Honest/Law/Live.lean) for an attention segment: the
first is a test on a lookup's samples at its face, the second a test with code on what a sumcheck
heard, this one a sentence on a tape's rounds by their names.

Not shown here. THAT ANY TAPE MEETS `TapeLive`, OR ANY STATE `PscLive`. Which tape a sub-protocol
hands to the function that reads K4's rounds (`hear`, OnBytes/Desc/First/K4/Hear.lean). Nothing on
rounds that hold several drawn elements, or none. THE CLAUSE ASKS MORE THAN THE LAWS OVER IT SPEND
(Law/Live/Heard.lean, Stages.lean, Whole.lean). It speaks of every round of t, those that a routine
leaves on the tape among them. And of the rounds of K4's own table
(OnBytes/Desc/First/K4/Rounds.lean) that draw one element, these are asked and are spent by none of
these three files: "not 0" at the three rounds that draw a point on a line, at the element that
batches the sums, and at the joining elements of the squares' layer and of the first token sumcheck;
"not 1" at three of the four rounds that batch rows (it is spent at the batched sumcheck's alone);
"not 0" at a round that draws a point of one coordinate, and "not 1" too where its name is "JOIN",
but for the point between the two gated layers, where both are spent. Nothing on entries. Nothing on
what a form is worth.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.Coef
import Johnson.Road.K4.Slots.HearSpares
import OnBytes.Desc.First.P1.FlTape
import OnBytes.Desc.First.P1.LevelKit
import OnBytes.Tie.Pv.Psc.FlatTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Psc (Weight polyAt)
open OnBytes.Desc.First.K4.Slots (SlotsIn)
open OnBytes.Desc.First.P1 (msOf msOf_cons msOf_nil hidingWalk_length)
open OnBytes.Tie.Pv.Lay (entries_three)

/-- **The clause on a tape.** Of every round that holds just one drawn element e: e reads as not 0;
and as not 1 where the round's name is the plan's "BAT-sigma" or "JOIN". -/
def TapeLive (t : Tape) : Prop :=
  ∀ r ∈ t, ∀ e, r.drawn = [e] →
    Reading.gl.val e ≠ 0 ∧
      (r.name = some RoundName.batSigma.name ∨ r.name = some RoundName.join.name →
        Reading.gl.val e ≠ 1)

/-- A tape whose rounds are all rounds of t. -/
theorem TapeLive.sub {t u : Tape} (h : TapeLive t) (hs : ∀ r ∈ u, r ∈ t) : TapeLive u :=
  fun r hr => h r (hs r hr)

/-- "Not 0" at a round of the tape that is written out. -/
theorem TapeLive.at_ {t : Tape} (h : TapeLive t) {nm : Option String} {z w : ℕ} {s : List E}
    {e : E} (hm : (⟨nm, z, w, s, [e]⟩ : FlatRound) ∈ t) : Reading.gl.val e ≠ 0 :=
  (h _ hm e rfl).1

/-- "Not 1" at a written-out round that batches rows. -/
theorem TapeLive.ne_one_bat {t : Tape} (h : TapeLive t) {z w : ℕ} {s : List E} {e : E}
    (hm : (⟨some RoundName.batSigma.name, z, w, s, [e]⟩ : FlatRound) ∈ t) :
    Reading.gl.val e ≠ 1 :=
  (h _ hm e rfl).2 (Or.inl rfl)

/-- "Not 1" at a written-out round that draws a joining point of one coordinate. -/
theorem TapeLive.ne_one_join {t : Tape} (h : TapeLive t) {z w : ℕ} {s : List E} {e : E}
    (hm : (⟨some RoundName.join.name, z, w, s, [e]⟩ : FlatRound) ∈ t) : Reading.gl.val e ≠ 1 :=
  (h _ hm e rfl).2 (Or.inr rfl)

/-- **The sumcheck's state is live**: its joining element reads as not 0, and so do each variable's
challenge and its psi at that challenge. -/
structure PscLive (p : Psc) : Prop where
  eps : Reading.gl.val p.eps ≠ 0
  vars : ∀ y ∈ zipT p.vars.toList p.r.toList,
    Reading.gl.val y.2 ≠ 0 ∧ Reading.gl.val (polyAt y.1.psi y.2) ≠ 0

theorem PscLive.walk1 {p : Psc} (L : PscLive p) : ∀ x ∈ p.walk.1, Reading.gl.val x ≠ 0 :=
  (walk_ne Reading.gl _ L.vars).1

theorem PscLive.walk2 {p : Psc} (L : PscLive p) : Reading.gl.val p.walk.2 ≠ 0 :=
  (walk_ne Reading.gl _ L.vars).2

/-- **A slot of the window** that neither the start form nor the kept form names. -/
theorem live_win {p : Psc} (L : PscLive p) (S0 : E) {kept : Aff} {j : ℕ} (h1 : p.first ≤ j)
    (h2 : j < p.first + p.walk.1.length) (hs : SlotsIn (fun i => i ≠ j) p.start)
    (hk : SlotsIn (fun i => i ≠ j) kept) : cf Reading.gl (p.rowForm S0 kept) j ≠ 0 := by
  have hi : j - p.first < p.walk.1.length := by omega
  rw [cf_rowForm_in Reading.gl p S0 h1 hs hk, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]
  exact L.walk1 _ (List.getElem_mem hi)

/-- **A slot outside the window** on which the start form has a coefficient that is not 0, and which
the kept form does not name (hk). -/
theorem live_start {p : Psc} (L : PscLive p) (S0 : E) {kept : Aff} {j : ℕ}
    (h : j < p.first ∨ p.first + p.walk.1.length ≤ j) (hk : SlotsIn (fun i => i ≠ j) kept)
    (hc : cf Reading.gl p.start j ≠ 0) : cf Reading.gl (p.rowForm S0 kept) j ≠ 0 := by
  rw [cf_rowForm_out Reading.gl p S0 kept h, cf_of_slotsIn Reading.gl hk, mul_zero, zero_sub]
  exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero L.eps L.walk2) hc)

/-- The weight is an equality weight or the plain one. -/
def IsEqOrPlain (w : Weight) : Prop :=
  (∃ z d, w = Weight.equality z d) ∨ ∃ d, w = Weight.plain d

/-- **`PscLive` from three premises.** -/
theorem pscLive_of {p : Psc} (he : Reading.gl.val p.eps ≠ 0)
    (hw : ∀ w ∈ p.vars.toList, IsEqOrPlain w) (hg : ∀ g ∈ p.r.toList, Reading.gl.val g ≠ 0) :
    PscLive p := by
  refine ⟨he, fun y hy => ?_⟩
  rw [zipT_eq] at hy
  obtain ⟨h1, h2⟩ := List.of_mem_zip (a := y.1) (b := y.2) hy
  refine ⟨hg _ h2, ?_⟩
  rcases hw _ h1 with ⟨z, d, e⟩ | ⟨d, e⟩
  · rw [e, OnBytes.PscTie.psi_equality]
    exact one_ne_zero
  · rw [e, psi_plain]
    exact hg _ h2

/-- The challenges that the library reads off rounds of one drawn element each are these rounds'
drawn elements. -/
theorem msOf_drawn : ∀ (ws : List Weight) (rs : List FlatRound),
    (∀ x ∈ rs, x.drawn.length = 1) → ∀ m ∈ msOf ws rs, ∃ x ∈ rs, x.drawn = [m.2.2]
  | [], rs, _, m, hm => by
    rw [msOf_nil] at hm
    cases hm
  | _ :: _, [], _, m, hm => by cases hm
  | w :: ws, r :: rs, h, m, hm => by
    rw [msOf_cons] at hm
    rcases List.mem_cons.1 hm with rfl | hm
    · refine ⟨r, List.mem_cons_self, ?_⟩
      have h1 := h r List.mem_cons_self
      show r.drawn = [r.drawn.headD zeroE]
      cases hd : r.drawn with
      | nil =>
        rw [hd] at h1
        cases h1
      | cons a l =>
        rw [hd] at h1
        have hl : l = [] := List.length_eq_zero_iff.1 (by simpa using h1)
        subst hl
        rfl
    · obtain ⟨x, hx, e⟩ := msOf_drawn ws rs (fun x hx => h x (List.mem_cons_of_mem _ hx)) m hm
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

/-- How long the window is: the variables have three coefficients each, then comes one with
dy + 1; one challenge for each. -/
theorem win_len (p : Psc) (ws : List Weight) (dy : ℕ) (h3 : ∀ w ∈ ws, w.d = 3)
    (hv : p.vars.toList = ws ++ [Weight.atZero (dy + 1)])
    (hr : p.r.toList.length = ws.length + 1) : p.walk.1.length = 1 + 2 * ws.length + dy := by
  have hl : p.vars.toList.length = p.r.toList.length := by
    rw [hv, hr, List.length_append]
    rfl
  have hm : (p.vars.toList.zip p.r.toList).map (·.1) = p.vars.toList :=
    List.map_fst_zip (Nat.le_of_eq hl)
  unfold Psc.walk
  rw [zipT_eq, hidingWalk_length _ ?_ ?_, hm, hv,
    entries_three ws (Weight.atZero (dy + 1)) dy h3 rfl]
  · intro h0
    have h1 := congrArg List.length hm
    rw [h0, hv, List.length_append] at h1
    simp at h1
  · intro x hx
    have h1 : x.1 ∈ p.vars.toList := (List.of_mem_zip (a := x.1) (b := x.2) hx).1
    rw [hv] at h1
    rcases List.mem_append.1 h1 with h1 | h1
    · rw [h3 _ h1]
      omega
    · rw [List.mem_singleton.1 h1]
      show 1 ≤ dy + 1
      omega

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.TapeLive
#print axioms ProofFile.Honest.K4.Live.TapeLive.sub
#print axioms ProofFile.Honest.K4.Live.TapeLive.at_
#print axioms ProofFile.Honest.K4.Live.TapeLive.ne_one_bat
#print axioms ProofFile.Honest.K4.Live.TapeLive.ne_one_join
#print axioms ProofFile.Honest.K4.Live.PscLive
#print axioms ProofFile.Honest.K4.Live.PscLive.walk1
#print axioms ProofFile.Honest.K4.Live.PscLive.walk2
#print axioms ProofFile.Honest.K4.Live.live_win
#print axioms ProofFile.Honest.K4.Live.live_start
#print axioms ProofFile.Honest.K4.Live.IsEqOrPlain
#print axioms ProofFile.Honest.K4.Live.pscLive_of
#print axioms ProofFile.Honest.K4.Live.msOf_drawn
#print axioms ProofFile.Honest.K4.Live.win_len
