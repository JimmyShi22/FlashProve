-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumAtRun.lean: CONDITIONAL. Statements with their proofs; no
definition.

What is here. FROM THE PUBLIC TEST `k4Fits` (Honest/K4/Part.lean) TO THE MAKERS AT A RUN, at five
masked sumchecks of the feed-forward layers' rounds, at the run's own input and challenges. At the
squares and the row products: the maker returns a job of its call's public shape (`k4JobFits`). At
the two gated products: the tables' maker returns and the run's cube fits. At the merge: the list of
claims is made, as many as the plan counts and as there are powers, each of the verifier's sizes.
THE PUBLIC SHAPE OF THE THREE LATER JOBS IS NOT SAID HERE. The test asks each maker at the zero
input and at the zero challenges in front of its part; whether a maker returns a job of that shape
hangs on lengths, and in the first group of layers on whether a token is at or above the size of the
vocabulary (`InSkel`; `k4MakersAt_skel`, MakersAt.lean beside this file).

K4 is the sub-protocol of the feed-forward layers' rounds.

  `all2_of_get`, `idxOf_lt`, `starts_le`, `drawnSkel_of_ownFits`   the challenges' shape, in the
     letters of PtsFullOf.lean
  `ptsFull_refl`, `makersAt_one`   the test's clause on the makers with one part's sampled values
     taken from the run
  `at_squares`, `at_rows`, `at_gated`, `at_gated2`, `at_count`, `at_rhoW`, `at_shapes`   seven
     clauses of the test's clause on the makers
  `squares_run`, `rows_run`, `gated_run`, `gated2_run`, `merge_run`   **the five**

Limits. Premises beside «the test accepts», which is asked at the run's own tokens: K4's own
challenges heard so far have the shape of the verifier's table of rounds (`OwnFits`,
Johnson/Desc/K4/Honest/Law/PtsSizes.lean) and are JUST AS MANY AS STAND IN FRONT OF THE PART (the
number of the part's first round in the table: `starts`); what the lookup in front has sampled at
the run has the public numbers and the lengths of that at which the test was asked (`LookSkel`).
Nothing on any value. No example of the four premises together is shown here. Of the two on K4's own
challenges the zero challenges in front of the sumcheck are one, with no hypothesis (`zero_ownFits`,
`zero_len`, Law/ZeroSizes.lean).

Kin. That a maker's answer which passes a test is there is the library's `any_some`
(Johnson/Desc/First/K4/Returns/Pub/ClaimsB.lean), called here; the library states it once more,
under the same name (Johnson/Desc/Kinds/Law/K6SeatsTest.lean). `makersAt_one` is a case of
`k4Makers_everywhere` (MakersAt.lean), which it does not call. `k4Makers_run` (PtsFullOf.lean) ends
in the same clause with the sampled values in front of all seven sumchecks, and in front of the
rounds that batch rows, made of lists of challenges at once, and at every list of shown values; no
law here calls it.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsFullOf
import Johnson.Desc.ProofFile.Honest.K4.Law.CubeSum
import Johnson.Desc.K4.Honest.Law.PtsSizes
import Johnson.Desc.First.K4.Returns.Pub.ClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (WsClaim orderRange Forest.Heard)
open OnBytes.Model.Layer (downFrom nEndT)
open OnBytes.Desc.First.K4 (Rd rounds)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.PtsLaw
open OnBytes.Flat (All2)
open OnBytes.Desc.First.K4.RtPub (any_some)

/-! ## 1 The challenges' shape -/

/-- Two lists of one length whose members of one number are related. -/
theorem all2_of_get {α β : Type} {R : α → β → Prop} : ∀ (l : List α) (l' : List β),
    l.length = l'.length → (∀ (j : ℕ) a b, l[j]? = some a → l'[j]? = some b → R a b) →
    All2 R l l'
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', h, hr =>
    .cons (hr 0 a b rfl rfl) (all2_of_get l l' (by simpa using h) fun j x y hx hy =>
      hr (j + 1) x y (by simpa using hx) (by simpa using hy))

/-- A row's number is below the numbers that the table has. -/
theorem idxOf_lt (r : OnBytes.Model.RoundName) : ∀ (l : List Rd) (k i : ℕ), i ∈ idxOf l r k →
    i < k + l.length
  | [], _, _, h => by simp [idxOf] at h
  | x :: l, k, i, h => by
    rw [idxOf_cons] at h
    rw [List.length_cons]
    split at h
    · rcases List.mem_cons.mp h with rfl | h'
      · omega
      · have := idxOf_lt r l (k + 1) i h'
        omega
    · have := idxOf_lt r l (k + 1) i h
      omega

/-- The number of a sumcheck's first round is at most the number of the table's rows. -/
theorem starts_le (Q : K4Pub) (k : ℕ) : (starts Q).getD k 0 ≤ (rounds Q.P Q.hp Q.g).length := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (starts Q)[k]? with
  | none => exact Nat.zero_le _
  | some i =>
    have hm : i ∈ idxOf (rounds Q.P Q.hp Q.g) .pscEpsilon 0 := List.mem_of_getElem? h
    have := idxOf_lt _ _ _ _ hm
    show i ≤ _
    omega

/-- **K4's own challenges, where they have the table's shape, are n, and n is at most the number of
the table's rows, stand to the first n zero challenges as PtsFullOf.lean asks.** -/
theorem drawnSkel_of_ownFits (Q : K4Pub) (heard : List Fmt.Drawn) (n : ℕ) (hf : OwnFits Q heard)
    (hn : (heard.drop Q.r0).length = n) (hle : n ≤ (rounds Q.P Q.hp Q.g).length) :
    DrawnSkel (heard.drop Q.r0) ((k4ZeroOwn Q).take n) := by
  refine all2_of_get _ _ ?_ fun j d d0 hd hd0 => ?_
  · rw [hn, List.length_take, k4ZeroOwn, List.length_map]
    omega
  · rw [List.getElem?_take] at hd0
    split at hd0
    · unfold k4ZeroOwn at hd0
      rw [List.getElem?_map] at hd0
      obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.mp hd0
      rw [hf j d x hd hx, ← e]
      simp
    · cases hd0

/-! ## 2 One part's sampled values taken from the run -/

/-- Sampled values have their own lengths. -/
theorem ptsFull_refl (p : Pts) : PtsFull p p :=
  ⟨⟨lookSkel_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The test's clause on the makers, at the run's input, with the sampled values in front of
masked sumcheck number k taken from the run.** ONE SUMCHECK AT A TIME: of s nothing is said but at
k; the sampled values in front of the rounds that batch rows are those at the zero input and the
zero challenges (`k4AtBat`); the shown values are 0. -/
theorem makersAt_one {Q : K4Pub} {fo : Forest.Heard} (w : K4In)
    (hk : k4Fits Q fo w.tokv = true) (k : ℕ) (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (heard.drop Q.r0).length = (starts Q).getD k 0)
    (hL : LookSkel (w.look (heard.take Q.r0)) fo) :
    ∃ s : ℕ → Pts, s k = ptsOf Q w heard ∧
      k4MakersAt Q w (k4AtBat Q fo) s (Array.replicate (nEndT Q.P.y) zeroE) = true := by
  refine ⟨fun i => if i = k then ptsOf Q w heard else k4AtSum Q fo i, if_pos rfl, ?_⟩
  unfold k4Fits at hk
  simp only [Bool.and_eq_true] at hk
  rw [k4MakersAt_skel Q (inSkel_of_tokens fo hk.1.2) (lookSkel_refl _) (s₀ := k4AtSum Q fo)
    (fun i => ?_) _ (Array.replicate (nEndT Q.P.y) zeroE), ← k4MakersFit_at]
  · exact hk.2
  · by_cases hi : i = k
    · rw [if_pos hi, hi]
      exact ptsOf_zero Q w _ (drawnSkel_of_ownFits Q heard _ hf hn (starts_le Q k)) hL
    · rw [if_neg hi]
      exact ptsFull_refl _

/-! ## 3 Seven clauses -/

/-- The clause on the squares. Each clause is found by walking the conjunction from its end: not by
its place in it. -/
theorem at_squares {Q : K4Pub} {w : K4In} {b s : ℕ → Pts} {sh : Array E}
    (h : k4MakersAt Q w b s sh = true) :
    (jobSquares Q w (s 0)).any (k4JobFits ((k4Shapes Q).getD 0 ⟨0, [], none⟩)) = true := by
  unfold k4MakersAt at h
  simp only [Bool.and_eq_true] at h
  repeat (first | (with_reducible exact h.2) | replace h := h.1)

/-- The clause on the row products. -/
theorem at_rows {Q : K4Pub} {w : K4In} {b s : ℕ → Pts} {sh : Array E}
    (h : k4MakersAt Q w b s sh = true) :
    (jobRows Q w (s 1)).any (k4JobFits ((k4Shapes Q).getD 1 ⟨0, [], none⟩)) = true := by
  unfold k4MakersAt at h
  simp only [Bool.and_eq_true] at h
  repeat (first | (with_reducible exact h.2) | replace h := h.1)

/-- The clause on the first gated product. -/
theorem at_gated {Q : K4Pub} {w : K4In} {b s : ℕ → Pts} {sh : Array E}
    (h : k4MakersAt Q w b s sh = true) :
    (jobGated Q w (s 4)).any (k4JobFits ((k4Shapes Q).getD 4 ⟨0, [], none⟩)) = true := by
  unfold k4MakersAt at h
  simp only [Bool.and_eq_true] at h
  repeat (first | (with_reducible exact h.2) | replace h := h.1)

/-- The clause on the second gated product. -/
theorem at_gated2 {Q : K4Pub} {w : K4In} {b s : ℕ → Pts} {sh : Array E}
    (h : k4MakersAt Q w b s sh = true) :
    (jobGated2 Q w (s 5)).any (k4JobFits ((k4Shapes Q).getD 5 ⟨0, [], none⟩)) = true := by
  unfold k4MakersAt at h
  simp only [Bool.and_eq_true] at h
  repeat (first | (with_reducible exact h.2) | replace h := h.1)

/-- The clause on the number of the merge's claims. -/
theorem at_count {Q : K4Pub} {w : K4In} {b s : ℕ → Pts} {sh : Array E}
    (h : k4MakersAt Q w b s sh = true) :
    ((mergeClaimsAt Q w (s 6)).any fun l => l.length == Q.hp.NCL) = true := by
  unfold k4MakersAt at h
  simp only [Bool.and_eq_true] at h
  repeat (first | (with_reducible exact h.2) | replace h := h.1)

/-- The clause on the powers that batch them. -/
theorem at_rhoW {Q : K4Pub} {w : K4In} {b s : ℕ → Pts} {sh : Array E}
    (h : k4MakersAt Q w b s sh = true) :
    ((s 6).rhoW.size == Q.hp.NCL) = true := by
  unfold k4MakersAt at h
  simp only [Bool.and_eq_true] at h
  repeat (first | (with_reducible exact h.2) | replace h := h.1)

/-- The clause on the claims' sizes. -/
theorem at_shapes {Q : K4Pub} {w : K4In} {b s : ℕ → Pts} {sh : Array E}
    (h : k4MakersAt Q w b s sh = true) :
    ((mergeClaimsAt Q w (s 6)).any fun l =>
      l.all fun c => (OnBytes.Model.wsClaimShape Q.P.wsLay c).isOk) = true := by
  unfold k4MakersAt at h
  simp only [Bool.and_eq_true] at h
  repeat (first | (with_reducible exact h.2) | replace h := h.1)

/-! ## 4 The five -/

/-- **The squares' maker returns at the run, a job of its call's shape.** -/
theorem squares_run {Q : K4Pub} {fo : Forest.Heard} (w : K4In) (hk : k4Fits Q fo w.tokv = true)
    (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (heard.drop Q.r0).length = (starts Q).getD 0 0)
    (hL : LookSkel (w.look (heard.take Q.r0)) fo) :
    ∃ j, jobSquares Q w (ptsOf Q w heard) = some j ∧
      k4JobFits ((k4Shapes Q).getD 0 ⟨0, [], none⟩) j = true := by
  obtain ⟨s, hs, h⟩ := makersAt_one w hk 0 heard hf hn hL
  have h' := at_squares h
  rw [hs] at h'
  exact any_some h'

/-- **The row products' maker returns at the run, a job of its call's shape.** -/
theorem rows_run {Q : K4Pub} {fo : Forest.Heard} (w : K4In) (hk : k4Fits Q fo w.tokv = true)
    (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (heard.drop Q.r0).length = (starts Q).getD 1 0)
    (hL : LookSkel (w.look (heard.take Q.r0)) fo) :
    ∃ j, jobRows Q w (ptsOf Q w heard) = some j ∧
      k4JobFits ((k4Shapes Q).getD 1 ⟨0, [], none⟩) j = true := by
  obtain ⟨s, hs, h⟩ := makersAt_one w hk 1 heard hf hn hL
  have h' := at_rows h
  rw [hs] at h'
  exact any_some h'

/-- **The first gated product: the tables' maker returns at the run, and the run's cube fits.** -/
theorem gated_run {Q : K4Pub} {fo : Forest.Heard} (w : K4In) (hk : k4Fits Q fo w.tokv = true)
    (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (heard.drop Q.r0).length = (starts Q).getD 4 0)
    (hL : LookSkel (w.look (heard.take Q.r0)) fo) :
    ∃ tb, gatedTabs Q w = some tb ∧ (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (ptsOf Q w heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q (ptsOf Q w heard))
      tb).cube.fits = true := by
  obtain ⟨s, hs, h⟩ := makersAt_one w hk 4 heard hf hn hL
  have h' := at_gated h
  rw [hs] at h'
  obtain ⟨j, hj, hfit⟩ := any_some h'
  unfold jobGated at hj
  obtain ⟨tb, ht, e⟩ := Option.map_eq_some_iff.mp hj
  exact ⟨tb, ht, by rw [e]; exact (jobFits_parts hfit).1⟩

/-- **The second gated product: the tables' maker returns at the run, and the run's cube fits.** -/
theorem gated2_run {Q : K4Pub} {fo : Forest.Heard} (w : K4In) (hk : k4Fits Q fo w.tokv = true)
    (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (heard.drop Q.r0).length = (starts Q).getD 5 0)
    (hL : LookSkel (w.look (heard.take Q.r0)) fo) :
    ∃ tb, gatedTabs2 Q w = some tb ∧ (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((ptsOf Q w heard).rhoM ++ downFrom (ptsOf Q w heard).rs Q.P.y.lfe ++ (ptsOf Q w heard).rt)
      tb).cube.fits = true := by
  obtain ⟨s, hs, h⟩ := makersAt_one w hk 5 heard hf hn hL
  have h' := at_gated2 h
  rw [hs] at h'
  obtain ⟨j, hj, hfit⟩ := any_some h'
  unfold jobGated2 at hj
  obtain ⟨tb, ht, e⟩ := Option.map_eq_some_iff.mp hj
  exact ⟨tb, ht, by rw [e]; exact (jobFits_parts hfit).1⟩

/-- **The merge: the list of claims is made at the run; the claims are as many as the plan counts,
as many as there are powers to batch them, and each passes the verifier's test on a claim's
sizes.** -/
theorem merge_run {Q : K4Pub} {fo : Forest.Heard} (w : K4In) (hk : k4Fits Q fo w.tokv = true)
    (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (heard.drop Q.r0).length = (starts Q).getD 6 0)
    (hL : LookSkel (w.look (heard.take Q.r0)) fo) :
    ∃ cls, mergeClaimsAt Q w (ptsOf Q w heard) = some cls ∧ cls.length = Q.hp.NCL ∧
      (ptsOf Q w heard).rhoW.size = Q.hp.NCL ∧
      ∀ c ∈ cls, (OnBytes.Model.wsClaimShape Q.P.wsLay c).isOk = true := by
  obtain ⟨s, hs, h⟩ := makersAt_one w hk 6 heard hf hn hL
  have h1 := at_shapes h
  have h2 := at_rhoW h
  have h3 := at_count h
  rw [hs] at h1 h2 h3
  obtain ⟨cls, hc, a1⟩ := any_some h1
  obtain ⟨cls', hc', a3⟩ := any_some h3
  have e : cls' = cls := Option.some.inj (hc'.symm.trans hc)
  rw [e] at a3
  exact ⟨cls, hc, beq_iff_eq.mp a3, beq_iff_eq.mp h2, fun c hcm => List.all_eq_true.mp a1 c hcm⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.all2_of_get
#print axioms ProofFile.Honest.K4.idxOf_lt
#print axioms ProofFile.Honest.K4.starts_le
#print axioms ProofFile.Honest.K4.drawnSkel_of_ownFits
#print axioms ProofFile.Honest.K4.ptsFull_refl
#print axioms ProofFile.Honest.K4.makersAt_one
#print axioms ProofFile.Honest.K4.at_squares
#print axioms ProofFile.Honest.K4.at_rows
#print axioms ProofFile.Honest.K4.at_gated
#print axioms ProofFile.Honest.K4.at_gated2
#print axioms ProofFile.Honest.K4.at_count
#print axioms ProofFile.Honest.K4.at_rhoW
#print axioms ProofFile.Honest.K4.at_shapes
#print axioms ProofFile.Honest.K4.squares_run
#print axioms ProofFile.Honest.K4.rows_run
#print axioms ProofFile.Honest.K4.gated_run
#print axioms ProofFile.Honest.K4.gated2_run
#print axioms ProofFile.Honest.K4.merge_run
