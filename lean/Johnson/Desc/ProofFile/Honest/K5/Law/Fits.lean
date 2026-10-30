-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Fits.lean: CONDITIONAL: THE ROW FITS ITS SHAPES. The parts of
the honest side of an attention segment's own rounds fill a list that is too short with zeros and
cut one that is too long, in silence (`padTo`, Honest/Sum.lean). Here: under two tests with code on
public data, at EVERY input, every list of values that is sent by itself has the length that its
part's shape counts, and every summand has the shape's numbers of variables and end values
(`Jobs.fits`, Honest/K5/RowOf.lean). So, AT CHALLENGES c AT WHICH THE FIRST TEST SAYS YES, nothing
is filled up or cut in this row among the values that ride in front of a sumcheck, the values of a
round by itself, and the end values. Statements with their proofs, definitions of propositions, and
one definition with code.

  `fitsAt`, `fits_eq`   the test of `Jobs.fits` at one part
  `fit_unit`, `fit_tail`, `fit_at`   the test at a softmax-table unit's part; at each of the eleven
      behind; at the part of a number
  `jobs_fit`   **the row's jobs fit**
  `padTo_same`, `jobs_whole`   **no list is filled up or cut**
  `KeySizes`, `blank_elems`, `fits_congr`, `fits_of_blank`   **the first test on the place's public
      data (`Seat5.fits`, Honest/K5/Row.lean), asked at challenges that are all 0, holds at every
      list of challenges that the rounds in front can draw**: under a named public premise on the
      reader of the key points: their lengths hang on the challenges' numbers of elements alone
  `KeyLong`, `aloneOk_longer`   from the first test at the front to `aloneOk` at every longer list:
      under a second named public premise on that reader: what is heard behind the place's front
      leaves the lengths

The two premises, both public, both with code. `aloneOk P c` (Johnson/Desc/K5/Honest/Alone.lean):
the verifier's function for the named points returns at the key points. `P.counted`
(Johnson/Desc/K5/Honest/Law/Lengths.lean): the planner's numbers of these rounds are the shape's.
Who is meant to show them: whoever makes the place's public data of the public files.
AT WHICH c. `jobs_fit` and `jobs_whole` stand at a letter c. In a run a part reads the challenges of
all that was heard, a list longer than the front from the place's second round on; `K5Seated`
(Honest/K5/Law/Seated.lean) gives `aloneOk` at the front alone. The bridge: `aloneOk_longer`.

Limits. NONE OF `P.counted`, `KeySizes`, `KeyLong` IS SHOWN HERE TO HOLD ANYWHERE. Counts alone.
Nothing is said of the round polynomials' numbers of coefficients: what a sender that keeps a
variable's number of coefficients drops is another statement's. Nothing is said of a value.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Row
import Johnson.Desc.ProofFile.Honest.SumLaw.Lists
import Johnson.Desc.K5.Honest.Law.Named
import Johnson.Desc.K5.Honest.Law.Lengths
import Johnson.Desc.K5.Honest.Law.FitsSizes
import Johnson.Desc.ProofFile.Honest.SumLaw.More

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open H2K5.Honest
open H2K5.Honest.Lengths

variable {W : Type}

/-! ## 1 The test at one part -/

/-- The test of `Jobs.fits` at the part number q of the shape s. -/
def fitsAt (J : Jobs W) (w : W) (c : Chal) (s : PartShape) (q : Nat) : Bool :=
  match s with
  | .sum k => (J.alone q w c).length == k.lead &&
      (J.sum q w c).fits k.vs.length ((k.ends.map (·.n)).getD 0)
  | .one n => (J.alone q w c).length == n

theorem fits_eq (J : Jobs W) (x : OnBytes.Params.AttentionRounds) (w : W) (c : Chal) :
    J.fits x w c = (shapes x).zipIdx.all fun s => fitsAt J w c s.1 s.2 := rfl

private theorem zipIdx_mem {α : Type} : ∀ (l : List α) (j : Nat) (s : α) (q : Nat),
    (s, q) ∈ l.zipIdx j → ∃ i, q = j + i ∧ l[i]? = some s
  | [], _, _, _, h => by cases h
  | a :: l, j, s, q, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
      exact ⟨0, rfl, rfl⟩
    · obtain ⟨i, h1, h2⟩ := zipIdx_mem l (j + 1) s q h
      exact ⟨i + 1, by omega, h2⟩

/-! ## 2 Part by part -/

variable {P : Pub5} {c : Chal}

/-- A softmax-table unit's part. Conditional: the two tests. -/
theorem fit_unit (ha : aloneOk P c = true) (hc : P.counted = true) (w : K5In) (i : Nat)
    (u : Nat × Nat) (hu : P.x.score[i]? = some u) :
    fitsAt (jobs P) w c (productsShape ((if i = 0 then P.x.planeMessages * 3 else 0) + 7) u.1 u.2)
      i = true := by
  have hi : i < P.x.score.length := (List.getElem?_eq_some_iff.1 hu).1
  have e1 : (jobs P).alone i w c =
      (if i == 0 then aloneKR P w c else []) ++ leadK P w c i (sK P w c i).total := if_pos hi
  have e2 : (jobs P).sum i w c = sK P w c i := if_pos hi
  show (((jobs P).alone i w c).length == _ &&
    ((jobs P).sum i w c).fits (List.replicate u.1 _).length (2 * u.2)) = true
  rw [e1, e2, List.length_append, leadK_length ha w hi, List.length_replicate]
  unfold Summand.fits
  rw [sK_vars, sK_ends, cut_unit P.x i u hu, (counted_spec hc).2.2.2.2.2.2.2 i u hu]
  by_cases h0 : i = 0
  · subst h0
    simp [aloneKR_length ha w]
  · simp [h0]

/-- Each of the eleven parts behind the units. Conditional: the two tests. -/
theorem fit_tail (ha : aloneOk P c = true) (hc : P.counted = true) (w : K5In) (j : Nat)
    (s : PartShape) (hs : (tailShapes P.x (leadBehind P.x))[j]? = some s) :
    fitsAt (jobs P) w c s (P.x.score.length + j) = true := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, -⟩ := counted_spec hc
  rw [leadBehind_zero P.x c1] at hs
  have vSE : (sSE P w c).vars = P.x.e := (sSE_vars P w c).trans (cut_iSE P.x)
  have vVM : (sVM P w c).vars = P.x.valueM := (sVM_vars P w c).trans (cut_iVM P.x)
  have vVD : (sVD P w c).vars = P.x.valueD := (sVD_vars P w c).trans (cut_iVD P.x)
  match j, hs with
  | 0, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, productsShape, jobs, iSE, Summand.fits, leadSE_length ha, vSE, sSE_ends, c2, c3]
  | 1, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, jobs, iSE, iVM, iM6]
  | 2, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, productsShape, jobs, iSE, iVM, Summand.fits, vVM, sVM_ends, c2]
  | 3, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, productsShape, jobs, iSE, iVM, iVD, iM6, Summand.fits, vVD, sVD_ends, c2]
  | 4, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, jobs, iSE, iVM, iM6]
  | 5, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, jobs, iSE, iVM, iM6, m6_length, c2]
  | 6, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, productsShape, jobs, iSE, iVM, iVD, iM6, iSF, Summand.fits, sSF_vars, sSF_ends,
      c2, c6]
  | 7, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, jobs, iSE, iVM, iM6]
  | 8, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, keyVars, jobs, iSE, iVM, iVD, iM6, iSF, iSD, Summand.fits, sSD_vars, sSD_ends,
      c2, c3, c4, c5]
    omega
  | 9, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, jobs, iSE, iVM, iM6]
  | 10, hs =>
    obtain rfl := Option.some.inj hs
    simp [fitsAt, productsShape, jobs, iSE, iVM, iVD, iM6, iSF, iSD, Summand.fits, sHB_vars,
      sHB_ends, c2, c7]
  | _ + 11, hs => cases hs

/-! ## 3 The row -/

/-- The test at the part number q. Conditional: the two tests. -/
theorem fit_at (ha : aloneOk P c = true) (hc : P.counted = true) (w : K5In) (q : Nat)
    (s : PartShape) (hq : (shapes P.x)[q]? = some s) : fitsAt (jobs P) w c s q = true := by
  by_cases hlt : q < P.x.score.length
  · have hu : P.x.score[q]? = some P.x.score[q] := List.getElem?_eq_getElem hlt
    obtain rfl := Option.some.inj ((shape_unit P.x q _ hu).symm.trans hq)
    exact fit_unit ha hc w q _ hu
  · obtain ⟨j, rfl⟩ : ∃ j, q = P.x.score.length + j := ⟨q - P.x.score.length, by omega⟩
    rw [shape_tail] at hq
    exact fit_tail ha hc w j s hq

/-- **THE ROW's JOBS FIT**, at every input. CONDITIONAL: the verifier's function for the named
points returns at the key points, with its lists' lengths (`aloneOk`); the planner's numbers are the
shape's (`Pub5.counted`). Both are tests with code on public data. -/
theorem jobs_fit (ha : aloneOk P c = true) (hc : P.counted = true) (w : K5In) :
    (jobs P).fits P.x w c = true := by
  rw [fits_eq, List.all_eq_true]
  rintro ⟨s, q⟩ hm
  obtain ⟨i, rfl, hi⟩ := zipIdx_mem _ 0 s q hm
  rw [Nat.zero_add]
  exact fit_at ha hc w i s hi

/-! ## 4 Nothing is filled up or cut -/

/-- A list of just n members is neither filled up nor cut. -/
theorem padTo_same : ∀ (n : Nat) (a : List E), a.length = n → padTo n a = a := by
  intro n a h
  unfold padTo
  rw [h, Nat.sub_self]
  show (a ++ []).take n = a
  rw [List.append_nil, ← h, List.take_length]

/-- **IN THIS ROW NO LIST OF VALUES IS FILLED UP OR CUT**: at the part number q: the values that
ride in front of a sumcheck, or that a round by itself sends; and a sumcheck's end values, at every
point. CONDITIONAL: as `jobs_fit`. -/
theorem jobs_whole (ha : aloneOk P c = true) (hc : P.counted = true) (w : K5In) (q : Nat)
    (s : PartShape) (hq : (shapes P.x)[q]? = some s) :
    match s with
    | .sum k => padTo k.lead ((jobs P).alone q w c) = (jobs P).alone q w c ∧
        ∀ rs, padTo ((k.ends.map (·.n)).getD 0) (((jobs P).sum q w c).endsAt rs) =
          ((jobs P).sum q w c).endsAt rs
    | .one n => padTo n ((jobs P).alone q w c) = (jobs P).alone q w c := by
  have h := fit_at ha hc w q s hq
  cases s with
  | sum k =>
    simp only [fitsAt, Summand.fits, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨padTo_same _ _ h.1, fun rs => padTo_same _ _ ?_⟩
    unfold Summand.endsAt
    rw [List.length_map, List.length_range, h.2.2]
  | one n =>
    simp only [fitsAt, beq_iff_eq] at h
    exact padTo_same _ _ h

/-! ## 5 From the test at challenges that are all 0 to every list of challenges -/

/-- **A NAMED PUBLIC PREMISE on the reader of the key points**: at two lists of challenges with the
same numbers of elements, round by round, each key point has the same length. It is a definition: a
premise's form. It speaks of lengths alone. -/
def KeySizes (Z : Seat5) : Prop :=
  ∀ f f' : List Fmt.Drawn, f.map (·.elems.length) = f'.map (·.elems.length) →
    SameSizes (Z.keyAt f) (Z.keyAt f')

/-- Challenges that are all 0 have the declared numbers of elements. -/
theorem blank_elems (ds : List Fmt.DeclaredRound) :
    (blankDraws ds).map (·.elems.length) = ds.map (·.entry.drawE) := by
  unfold blankDraws
  rw [List.map_map]
  exact List.map_congr_left fun r _ => List.length_replicate

/-- **The first test on the place's public data says the same at two lists of challenges with the
same numbers of elements.** CONDITIONAL: `KeySizes`. -/
theorem fits_congr (Z : Seat5) (hK : KeySizes Z) {f f' : List Fmt.Drawn}
    (h : f.map (·.elems.length) = f'.map (·.elems.length)) : Z.fits f = Z.fits f' := by
  have hl : f.length = f'.length := by
    have := congrArg List.length h
    rwa [List.length_map, List.length_map] at this
  unfold Seat5.fits
  rw [hl, aloneOk_congr (P := Z.P) (c := chalOf Z f) (c' := chalOf Z f') (hK f f' h)]

/-- **FROM THE TEST AT CHALLENGES THAT ARE ALL 0 TO EVERY LIST THAT THE ROUNDS IN FRONT CAN DRAW.**
This is the form of the last clause of `K5Seated` (Honest/K5/Law/Seated.lean), at ds the declared
rounds in front of the member; the test at challenges that are all 0 is the one that `seatAt`
(Honest/K5/Row.lean) asks. CONDITIONAL: `KeySizes`; the test says yes at the challenges that are
all 0. Who is meant to show the first: whoever lays the reader of the key points. -/
theorem fits_of_blank (Z : Seat5) (hK : KeySizes Z) (ds : List Fmt.DeclaredRound)
    (hb : Z.fits (blankDraws ds) = true) :
    ∀ front, drawsFit ds front = true → Z.fits front = true := by
  intro front hf
  rw [← hb]
  exact fits_congr Z hK ((SumLaw.elems_of_fit ds front hf).trans (blank_elems ds).symm)

/-- **A NAMED PUBLIC PREMISE on the reader of the key points, for the lists that a part reads in a
run**: what is heard BEHIND THE PLACE's FRONT, a list of just `base` challenges, leaves each key
point's length as it is. It is a definition: a premise's form. It speaks of lengths alone. The front
is bound: a reader that cuts the key points out of drawn elements has nothing to cut at a shorter
list. -/
def KeyLong (Z : Seat5) : Prop :=
  ∀ front more : List Fmt.Drawn, front.length = Z.base →
    SameSizes (Z.keyAt (front ++ more)) (Z.keyAt front)

/-- **From the first test at the front to the test on the named points at every longer list**: at
the challenges that a part of the row reads in a run. CONDITIONAL: `KeyLong`; the first test says
yes at the front. -/
theorem aloneOk_longer (Z : Seat5) (hL : KeyLong Z) (front more : List Fmt.Drawn)
    (h : Z.fits front = true) : aloneOk Z.P (chalOf Z (front ++ more)) = true := by
  unfold Seat5.fits at h
  rw [Bool.and_eq_true] at h
  rw [← h.2]
  exact aloneOk_congr (P := Z.P) (c := chalOf Z (front ++ more)) (c' := chalOf Z front)
    (hL front more (beq_iff_eq.1 h.1))

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.aloneOk_longer
#print axioms ProofFile.Honest.K5.blank_elems
#print axioms ProofFile.Honest.K5.fits_congr
#print axioms ProofFile.Honest.K5.fits_of_blank
#print axioms ProofFile.Honest.K5.fits_eq
#print axioms ProofFile.Honest.K5.fit_unit
#print axioms ProofFile.Honest.K5.fit_tail
#print axioms ProofFile.Honest.K5.fit_at
#print axioms ProofFile.Honest.K5.jobs_fit
#print axioms ProofFile.Honest.K5.padTo_same
#print axioms ProofFile.Honest.K5.jobs_whole
#print axioms ProofFile.Honest.K5.zipIdx_mem
