-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/MakersSkel.lean: CONDITIONAL: on `LookSkel`.

What is here. A CONGRUENCE: THE PUBLIC TEST ON THE PARTS OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(`k4Fits`, Honest/K4/Part.lean) AT TWO LISTS OF WHAT THE LOOKUP IN FRONT HAS SAMPLED, of one
skeleton (`LookSkel`, Law/LookSkel.lean). BOTH SIDES OF `k4MakersFit_skel` STAND AT THE ZERO INPUT
AND, for each maker, AT THE ZERO CHALLENGES IN FRONT OF ITS PART: what carries the clause on the
makers to a run's own input and challenges is Law/MakersAt.lean's. Two definitions, and statements
with their proofs.

  `k4LookFits_skel`, `k4MakersFit_skel`   two of the test's four clauses at two such lists. The
      other two read nothing of the lookup.
  `k4AtSum`, `k4AtBat`, `k4MakersFit_def`   where the test asks the makers; the clause in these
      words.
  `wSums_congr`, `jobSquares_congr`, `jobGated2_congr`   the makers that read nothing of the lookup.
  `k4Fits_skel`   the test.
  **`k4Fits_everywhere`**   a yes at one list and one request is a yes at every list of the same
      public numbers and lengths, and every request that fits.

Debts and ends. THIS FILE DEFINES NO RELATION. ITS LAWS TAKE ONE DEBT: `LookSkel`: see
Law/LookSkel.lean for its payers: all stand at one and the same front. `k4Fits_everywhere` takes
besides: h, a yes of the test at one list and one request; ht, the test's own clause on the tokens
at the other request. THE LAWS ON THE TEST TAKE NO INPUT: the test stands at the zero input by its
text. The three small congruences (`wSums_congr`, `jobSquares_congr`, `jobGated2_congr`) take two
inputs WITH ONE FUNCTION OF CELLS (hc); they are spent here alone, at two zero inputs, where hc is
rfl.

Not shown here. THE TEST IS SHOWN TRUE NOWHERE IN THIS FILE: each statement compares two calls, or
carries a yes from one to the other. `LookSkel` asks MORE than the test's own clause on the lookup
(`k4LookFits`) gives: see there. The laws stand over the text of `Reads.has` as a test on names,
lengths and public numbers (`wtsFit`, Johnson/Desc/K4/Honest/Cells.lean). BETWEEN
`k4Fits_everywhere` AND THE CLAUSE fits OF `K4Seated` (Law/Seated.lean) STAND THREE PREMISES, AND NO
LEMMA HERE JOINS THEM. (i) `LookSkel (look Q front) fo₀` at every list of challenges that the rounds
in front can sample: owed by whoever makes `look`: A LAW ON PUBLIC SIZES; NO FILE THAT ITS WRITERS
KNOW OF HAS IT BETWEEN TWO LISTS. (ii) `k4TokensFit Q (tokens w.x)` at every valid input: owed by
whoever states which inputs are valid; at the member of the first chain: `hTk_of`
(Law/TokensSeat.lean), from a test on the request; `hTk_later` there: from nothing, in a later
group. (iii) `k4Fits Q fo₀ tok₀ = true` AS A TERM: an evaluation under #guard is the evaluator's
word and no proof; at the member's own public data, at the full size and the format's second hash
function alone, `fits_member` (Law/FitsMember.lean) has it from two of its four clauses, those on
the lookup's sizes and on the tokens. THE CLAUSE fits AT THAT MEMBER IS REACHED BY ANOTHER ROAD,
WHICH DOES NOT CALL `k4Fits_everywhere`: `k4Seated_member` (Law/SeatedMember.lean) asks the clause
on the lookup's sizes AT EACH FRONT (hLk; had at the text `k4LookAt` by `lookFits_lookAt`,
Law/LookAtFill.lean) and calls `fits_member` there. WHERE THE TEST IS ASKED ONCE, AT A LIST LAID
BEFORE ANY CHALLENGE (`k4Side`, Honest/K4/Part.lean), (i) STAYS OWED.

Kin. No twin is known to its writers. `k4MakersAt_skel` (Law/MakersAt.lean) is the wider law on the
clause on the makers: two inputs in `InSkel` and sampled values in `PtsFull`; `k4MakersFit_skel`
does not call it: three of its steps are equations where that law has lengths. `k4Fits_everywhere`
is called by no file of its writers.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelStack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Forest.Heard ledNS ledNP)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub

/-- The clause on the lookup's sizes. -/
theorem k4LookFits_skel (Q : K4Pub) {fo fo₀ : Forest.Heard} (S : LookSkel fo fo₀) :
    k4LookFits Q fo = k4LookFits Q fo₀ := by
  unfold k4LookFits OnBytes.Desc.First.K4.shapeFits
  simp only [S.shape, S.zx, S.e, S.zks, S.zk]

/-! ## Where the test asks the makers -/

/-- The sampled values at the zero input and zero challenges, in front of masked sumcheck number k.
-/
def k4AtSum (Q : K4Pub) (fo : Forest.Heard) (k : Nat) : Pts := k4ZeroPts Q fo ((starts Q).getD k 0)

/-- The same in front of the round number k that batches rows. -/
def k4AtBat (Q : K4Pub) (fo : Forest.Heard) (k : Nat) : Pts :=
  k4ZeroPts Q fo ((rowsNamed Q .batSigma).getD k 0)

/-- What the clause on the makers is, in these words. -/
theorem k4MakersFit_def (Q : K4Pub) (fo : Forest.Heard) :
    k4MakersFit Q fo =
      ((wSums Q (k4ZeroIn Q fo) (k4AtBat Q fo 0)).length == ledNS Q.P.y.h.xl * Q.P.y.NI &&
        (rowProducts Q (k4ZeroIn Q fo) (k4AtBat Q fo 1)).length == ledNP Q.P.y.h.xl * Q.P.y.NI &&
        (jobSquares Q (k4ZeroIn Q fo) (k4AtSum Q fo 0)).any
          (k4JobFits ((k4Shapes Q).getD 0 ⟨0, [], none⟩)) &&
        (jobRows Q (k4ZeroIn Q fo) (k4AtSum Q fo 1)).any
          (k4JobFits ((k4Shapes Q).getD 1 ⟨0, [], none⟩)) &&
        (jobTerms Q (k4ZeroIn Q fo) (k4AtSum Q fo 2)).any
          (k4JobFits ((k4Shapes Q).getD 2 ⟨0, [], none⟩)) &&
        (jobStack Q (k4ZeroIn Q fo) (k4AtSum Q fo 3) (Array.replicate (nEndT Q.P.y) zeroE)).any
          (k4JobFits ((k4Shapes Q).getD 3 ⟨0, [], none⟩)) &&
        (jobGated Q (k4ZeroIn Q fo) (k4AtSum Q fo 4)).any
          (k4JobFits ((k4Shapes Q).getD 4 ⟨0, [], none⟩)) &&
        (jobGated2 Q (k4ZeroIn Q fo) (k4AtSum Q fo 5)).any
          (k4JobFits ((k4Shapes Q).getD 5 ⟨0, [], none⟩)) &&
        (jobMerge Q (k4ZeroIn Q fo) (k4AtSum Q fo 6)).any
          (k4JobFits ((k4Shapes Q).getD 6 ⟨0, [], none⟩)) &&
        ((mergeClaimsAt Q (k4ZeroIn Q fo) (k4AtSum Q fo 6)).any fun l => l.length == Q.hp.NCL) &&
        (k4AtSum Q fo 0).gp.size == ledNS Q.P.y.h.xl &&
        (k4AtSum Q fo 1).omV.size == ledNP Q.P.y.h.xl * Q.P.y.NI && (k4AtSum Q fo 3).om.size == 2 &&
        (k4AtSum Q fo 6).rhoW.size == Q.hp.NCL &&
        ((mergeClaimsAt Q (k4ZeroIn Q fo) (k4AtSum Q fo 6)).any fun l =>
          l.all fun c => (OnBytes.Model.wsClaimShape Q.P.wsLay c).isOk)) := rfl

/-! ## The makers that read nothing of the lookup -/

/-- The sums of limb products read the cells and one point. -/
theorem wSums_congr (Q : K4Pub) {w w₀ : K4In} {p p₀ : Pts} (hc : w.cell = w₀.cell)
    (hP : p.PV = p₀.PV) : wSums Q w p = wSums Q w₀ p₀ := by
  unfold wSums limbSumsAt
  rw [hc, hP]

/-- The squares' job reads the cells and three lists of sampled values. -/
theorem jobSquares_congr (Q : K4Pub) {w w₀ : K4In} {p p₀ : Pts} (hc : w.cell = w₀.cell)
    (hg : p.gp = p₀.gp) (hr : p.rhoI = p₀.rhoI) (hP : p.PV = p₀.PV) :
    jobSquares Q w p = jobSquares Q w₀ p₀ := by
  unfold jobSquares squaresTab
  rw [hc, hg, hr, hP]

/-- The second gated layer's job reads the cells and three lists of sampled values. -/
theorem jobGated2_congr (Q : K4Pub) {w w₀ : K4In} {p p₀ : Pts} (hc : w.cell = w₀.cell)
    (hm : p.rhoM = p₀.rhoM) (hs : p.rs = p₀.rs) (ht : p.rt = p₀.rt) :
    jobGated2 Q w p = jobGated2 Q w₀ p₀ := by
  unfold jobGated2 gatedTabs2
  rw [hc, hm, hs, ht]

/-- **The clause on the makers gives one answer at two lists of one skeleton.** Both sides stand at
the zero input and, for each maker, at the zero challenges in front of its part. -/
theorem k4MakersFit_skel (Q : K4Pub) {fo fo₀ : Forest.Heard} (S : LookSkel fo fo₀) :
    k4MakersFit Q fo = k4MakersFit Q fo₀ := by
  have L : ∀ k, LookSkel (k4AtSum Q fo k).fo (k4AtSum Q fo₀ k).fo := fun _ => S
  have Lb : ∀ k, LookSkel (k4AtBat Q fo k).fo (k4AtBat Q fo₀ k).fo := fun _ => S
  have P : ∀ k, PtsSkel (k4AtSum Q fo k) (k4AtSum Q fo₀ k) := fun k =>
    ⟨L k, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hM := mergeClaimsAt_rel Q (k4ZeroIn Q fo) (k4ZeroIn Q fo₀) (L 6) rfl rfl rfl rfl
  rw [k4MakersFit_def, k4MakersFit_def,
    wSums_congr Q (w := k4ZeroIn Q fo) (w₀ := k4ZeroIn Q fo₀) (p := k4AtBat Q fo 0)
      (p₀ := k4AtBat Q fo₀ 0) rfl rfl,
    rowProducts_len Q (k4ZeroIn Q fo) (k4ZeroIn Q fo₀) (Lb 1),
    jobSquares_congr Q (w := k4ZeroIn Q fo) (w₀ := k4ZeroIn Q fo₀) (p := k4AtSum Q fo 0)
      (p₀ := k4AtSum Q fo₀ 0) rfl rfl rfl rfl,
    fitsAny_rel (jobRows_skel Q (k4ZeroIn Q fo) (k4ZeroIn Q fo₀) (L 1) rfl rfl),
    fitsAny_rel (jobTerms_skel Q (k4ZeroIn Q fo) (k4ZeroIn Q fo₀) (L 2)),
    fitsAny_rel (jobStack_skel Q (k4ZeroIn Q fo) (k4ZeroIn Q fo₀) (P 3) rfl _ _),
    fitsAny_rel (jobGated_skel Q (k4ZeroIn Q fo) (k4ZeroIn Q fo₀) (L 4) rfl),
    jobGated2_congr Q (w := k4ZeroIn Q fo) (w₀ := k4ZeroIn Q fo₀) (p := k4AtSum Q fo 5)
      (p₀ := k4AtSum Q fo₀ 5) rfl rfl rfl rfl,
    fitsAny_rel (jobMerge_skel Q (k4ZeroIn Q fo) (k4ZeroIn Q fo₀) (L 6) rfl rfl rfl rfl),
    any_rel hM (f := fun l => l.length == Q.hp.NCL) (f₀ := fun l => l.length == Q.hp.NCL)
      fun a b h => congrArg (· == Q.hp.NCL) h.length,
    any_rel hM
      (f := fun l => l.all fun c => (OnBytes.Model.wsClaimShape Q.P.wsLay c).isOk)
      (f₀ := fun l => l.all fun c => (OnBytes.Model.wsClaimShape Q.P.wsLay c).isOk)
      fun a b h => OnBytes.Flat.all_alike
        (fun c c₀ k => congrArg Except.isOk (OnBytes.Flat.shape_alike Q.P.wsLay k)) h]
  rfl

/-- The test, at one request. -/
theorem k4Fits_skel (Q : K4Pub) {fo fo₀ : Forest.Heard} (S : LookSkel fo fo₀) (tokv : Array Nat) :
    k4Fits Q fo tokv = k4Fits Q fo₀ tokv := by
  unfold k4Fits
  rw [k4LookFits_skel Q S, k4MakersFit_skel Q S]

/-- **A yes at one list and one request is a yes at every list of one skeleton with it and every
request that fits.** -/
theorem k4Fits_everywhere {Q : K4Pub} {fo₀ : Forest.Heard} {tok₀ : Array Nat}
    (h : k4Fits Q fo₀ tok₀ = true) (fo : Forest.Heard) (tokv : Array Nat) (S : LookSkel fo fo₀)
    (ht : k4TokensFit Q tokv = true) : k4Fits Q fo tokv = true := by
  unfold k4Fits at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, _⟩, h4⟩ := h
  exact ⟨⟨⟨h1, (k4LookFits_skel Q S).trans h2⟩, ht⟩, (k4MakersFit_skel Q S).trans h4⟩

end ProofFile.Honest.K4




#print axioms ProofFile.Honest.K4.k4LookFits_skel
#print axioms ProofFile.Honest.K4.k4AtSum
#print axioms ProofFile.Honest.K4.k4AtBat
#print axioms ProofFile.Honest.K4.k4MakersFit_def
#print axioms ProofFile.Honest.K4.wSums_congr
#print axioms ProofFile.Honest.K4.jobSquares_congr
#print axioms ProofFile.Honest.K4.jobGated2_congr
#print axioms ProofFile.Honest.K4.k4MakersFit_skel
#print axioms ProofFile.Honest.K4.k4Fits_skel
#print axioms ProofFile.Honest.K4.k4Fits_everywhere
