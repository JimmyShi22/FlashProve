-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FitPowers.lean: NO HYPOTHESIS. Eight statements with their
proofs.

What is here. Four of the fifteen clauses of `k4MakersFit` (Honest/K4/Part.lean), the clause on the
makers of the public test on the parts of the feed-forward layers' own rounds (the sub-protocol K4):
AT EVERY PUBLIC DATA Q AND EVERY VALUE fo OF WHAT THE LOOKUP HAS SAMPLED, WITH NO HYPOTHESIS, the
four lists of powers of a sampled element (gp, omV, om, rhoW) have, at the zero challenges in front
of the masked sumcheck whose summand reads them, the numbers that the test asks. `powers_fit` has
the four as the test types them. How. Each list is made of the first element that one of the four
rounds which batch rows has sampled (`pts_gp_val` and its like, Law/PtsVals.lean; `bats_eq`,
Law/StartsAre.lean); each of these rounds stands in front of that sumcheck's first round; in the
verifier's table of rounds (OnBytes/Desc/First/K4/Rounds.lean) every round that batches rows samples
one element (`bat_drawn`), and the zero challenges hold as many elements as the table says.

  `bat_drawn`   in the table every round that batches rows samples one element
  `rowsNamed_get`   a number that `rowsNamed` lists is that of a row of the name
  `zero_powers`   at the zero challenges the powers of such a round's element are as many as asked
  `gp_zero`, `omV_zero`, `om_zero`, `rhoW_zero`   **the four sizes**
  `powers_fit`   **the four clauses, as the test types them**

Not shown here. THE FOUR TEST NOTHING: they are true at every public data, so these four clauses of
the test cannot fail: each list is compared with the number by which it is itself made. That no
summand reads a list beyond that number is said by no clause of the test, and not here. The eleven
other clauses of `k4MakersFit` are not here. Nothing on soundness, on completeness or on any other
property.

Kin. Sought: by statement, to the letter and up to the bound letters, among the theorems of the
library and of files that are no part of it yet, as they lay with the writer: no hit; no short name
of the eight stands elsewhere.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsVals
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsFullOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (RoundName powers ledNS ledNP Forest.Heard)
open OnBytes.Desc.First.K4 (Rd rounds masked layerRds pointRd batchRd k0)
open OnBytes.Desc.First.K4.Honest

/-- In the verifier's table every round that batches rows samples one element. -/
theorem bat_drawn (P : OnBytes.Model.Layer.Pub) (hp : OnBytes.Model.Layer.HPlan2) (g : Nat) (d : Rd)
    (hd : d ∈ rounds P hp g) (hn : (d.name == RoundName.batSigma) = true) : d.drawn = 1 := by
  have key : (rounds P hp g).all
      (fun d => !(d.name == RoundName.batSigma) || d.drawn == 1) = true := by
    unfold rounds layerRds masked pointRd batchRd
    by_cases hg : (g == 0) = true
    · simp [hg]
    · simp [hg]
  have h1 := List.all_eq_true.1 key d hd
  rw [hn] at h1
  simpa using h1

/-- A number that `rowsNamed` lists is that of a row of the name. -/
theorem rowsNamed_get {Q : K4Pub} {r : RoundName} {j : Nat} (h : j ∈ rowsNamed Q r) :
    ∃ d, (rounds Q.P Q.hp Q.g)[j]? = some d ∧ (d.name == r) = true := by
  unfold rowsNamed at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hx
  exact ⟨x.1, List.mem_zipIdx_iff_getElem?.1 h1, h2⟩

/-- At the zero challenges the powers of the element of a round that batches rows are as many as
asked. -/
theorem zero_powers (Q : K4Pub) (j n : Nat) (hj : j ∈ rowsNamed Q .batSigma) :
    (powersAt (k4ZeroOwn Q) j n).size = n := by
  obtain ⟨d, hd, hn⟩ := rowsNamed_get hj
  have h1 := bat_drawn _ _ _ d (List.mem_of_getElem? hd) hn
  have e : elemsAt (k4ZeroOwn Q) j = #[E.ofTriple zeroE.triple] := by
    unfold elemsAt k4ZeroOwn
    rw [List.getElem?_map, hd]
    show elemsOf ⟨List.replicate d.drawn zeroE.triple, [], [], none⟩ = _
    rw [h1]
    rfl
  unfold powersAt
  rw [e]
  exact OnBytes.Desc.First.P1.powers_size _ _

variable (Q : K4Pub) (fo : Forest.Heard)

/-- **The powers gp**, in front of the first masked sumcheck. -/
theorem gp_zero : (k4ZeroPts Q fo ((starts Q).getD 0 0)).gp.size = ledNS Q.P.y.h.xl := by
  have s : (starts Q).getD 0 0 = k4StartAt Q 0 := by rw [starts_eq]; rfl
  unfold k4ZeroPts k4ZeroHeard
  rw [pts_gp_val, drop_take_rep, s, powersAt_take _ _ _ _ (by simp only [k4StartAt]; omega)]
  exact zero_powers Q _ _ (by rw [bats_eq]; simp)

/-- **The powers omV**, in front of the second. -/
theorem omV_zero :
    (k4ZeroPts Q fo ((starts Q).getD 1 0)).omV.size = ledNP Q.P.y.h.xl * Q.P.y.NI := by
  have s : (starts Q).getD 1 0 = k4StartAt Q 1 := by rw [starts_eq]; rfl
  unfold k4ZeroPts k4ZeroHeard
  rw [pts_omV_val, drop_take_rep, s, powersAt_take _ _ _ _ (by simp only [k4StartAt]; omega)]
  exact zero_powers Q _ _ (by rw [bats_eq]; simp)

/-- **The powers om**, in front of the fourth. -/
theorem om_zero : (k4ZeroPts Q fo ((starts Q).getD 3 0)).om.size = 2 := by
  have s : (starts Q).getD 3 0 = k4StartAt Q 3 := by rw [starts_eq]; rfl
  unfold k4ZeroPts k4ZeroHeard
  rw [pts_om_val, drop_take_rep, s, powersAt_take _ _ _ _ (by simp only [k4StartAt]; omega)]
  exact zero_powers Q _ _ (by rw [bats_eq]; simp)

/-- **The powers rhoW**, in front of the seventh. -/
theorem rhoW_zero : (k4ZeroPts Q fo ((starts Q).getD 6 0)).rhoW.size = Q.hp.NCL := by
  have s : (starts Q).getD 6 0 = k4StartAt Q 6 := by rw [starts_eq]; rfl
  unfold k4ZeroPts k4ZeroHeard
  rw [pts_rhoW_val, drop_take_rep, s, powersAt_take _ _ _ _ (by simp only [k4StartAt]; omega)]
  exact zero_powers Q _ _ (by rw [bats_eq]; simp)

/-- **THE FOUR CLAUSES, AS `k4MakersFit` TYPES THEM.** -/
theorem powers_fit :
    ((k4ZeroPts Q fo ((starts Q).getD 0 0)).gp.size == ledNS Q.P.y.h.xl &&
      (k4ZeroPts Q fo ((starts Q).getD 1 0)).omV.size == ledNP Q.P.y.h.xl * Q.P.y.NI &&
      (k4ZeroPts Q fo ((starts Q).getD 3 0)).om.size == 2 &&
      (k4ZeroPts Q fo ((starts Q).getD 6 0)).rhoW.size == Q.hp.NCL) = true := by
  rw [gp_zero, omV_zero, om_zero, rhoW_zero]
  simp

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.bat_drawn
#print axioms ProofFile.Honest.K4.rowsNamed_get
#print axioms ProofFile.Honest.K4.zero_powers
#print axioms ProofFile.Honest.K4.gp_zero
#print axioms ProofFile.Honest.K4.omV_zero
#print axioms ProofFile.Honest.K4.om_zero
#print axioms ProofFile.Honest.K4.rhoW_zero
#print axioms ProofFile.Honest.K4.powers_fit
