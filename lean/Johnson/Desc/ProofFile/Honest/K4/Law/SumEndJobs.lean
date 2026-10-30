-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumEndJobs.lean: CONDITIONAL.

What is here. At five masked sumchecks of the feed-forward layers' rounds (the squares, the row
products, the two gated products, the merge): the form that is left (`rowForm`), made with the
verifier's summand on the values AS THEY ARE SENT in the part's last message, is worth the first
challenge times what is kept. Statements and proofs.

  `prod_rowForm_sent`, `level_ends`, `level_rowForm_sent`   a product of two end values
  `rowsJob_rowForm_sent`, `heardOf_omV`   the row products' job, of its tables
  `squaresSum`, `rowsSum`, `gatedSum`, `gated2Sum`   four of the row's jobs (the fifth: `mergeSum`)
  `squares_rowForm_sent`, `gated_rowForm_sent`, `gated2_rowForm_sent`, `merge_rowForm_sent`,
  `rows_rowForm_sent`   **the five**

Limits. At the reading `Reading.gl` alone. THE VERIFIER's TEXT HERE IS THE PART's (`hear`,
Johnson/Desc/Part/MaskedSum4.lean; `rowForm`, Johnson/Desc/Part/MaskedSumMore.lean), not the flat
text that the layers' own rounds run. Premises, as in the law that is called: the challenges have
the call's shape, the part's moves answer, `hear` accepts. THE WORLD IS A PREMISE: it holds the
part's coins under the sumcheck's own slots, and the claimed form is worth the reading of the cube's
total in it. On the job: its maker returns at the run's input; for a gated product the run's cube
fits; for the row products: norms of five limbs (xl = 5), and the verifier's heard powers omV are
the maker's. The two laws at large (`level_rowForm_sent`, `rowsJob_rowForm_sent`) ask that the cube
fits, the second also that there are as many tables as the call states end values. The summand on
sent values is typed here as the verifier's texts have it by reading: a product of two; the first;
`rowsSummand`: that a verifier's step hands just that to its row is not said here. No example of the
premises together is known to us at the full size. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumEnd
import Johnson.Desc.ProofFile.Honest.K4.Law.SumLevels
import Johnson.Desc.ProofFile.Honest.K4.Law.SumRowsSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F mulE zeroE oneE)
open OnBytes.Model (Reading Aff Fork World WsClaim orderRange ledNO)
open OnBytes.Model.Layer (downFrom)
open OnBytes.Slice (GE)
open OnBytes.Desc.First.K4 (rowsSummand)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends Heard hear rowForm ownSlots scalars)
open ProofFile.Honest.SumLaw
open VerifiableInference.Desc.K9L (toList_getD)

variable {V W X : Type}

/-! ## 1 A product of two end values -/

/-- At a job whose summand on end values is the product of the first two: the form that is left,
made with that product of the sent values, is worth the first challenge times what is kept. -/
theorem prod_rowForm_sent (name endName : String) (sh : Call) (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob sh job)) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (kept : Aff)
    (Wd : World GE) (j : Job) (e : Ends)
    (hd : drawsOk ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (k4SumJob sh job)) c t seen ds = some rounds)
    (hh : hear C ((k4SumJob sh job).callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((k4SumJob sh job).callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (hσ : C.value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hj : job t.input (frontOf t seen) = some j) (hfit : SumShape sh j) (he : sh.ends = some e)
    (hdY : j.dY = 2)
    (hat : ∀ rs e, j.atEnds rs e = mulE (e.getD 0 zeroE) (e.getD 1 zeroE))
    (hn : (j.ends (h.r.take j.cube.n)).length = e.n)
    (hE : Reading.gl.val ((j.ends (h.r.take j.cube.n)).getD 0 zeroE) *
        Reading.gl.val ((j.ends (h.r.take j.cube.n)).getD 1 zeroE) =
      Reading.gl.val (j.cube.summandAt (h.r.take j.cube.n))) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = e.n ∧
      (rowForm h (mulE (s.getD 0 zeroE) (s.getD 1 zeroE)) kept).value Reading.gl Wd =
        Reading.gl.val h.eps * kept.value Reading.gl Wd := by
  have hfun : j.atEnds (h.r.take j.cube.n) = fun e => mulE (e.getD 0 zeroE) (e.getD 1 zeroE) :=
    funext (hat _)
  obtain ⟨r, s, h1, h2, h3, h4⟩ := k4_rowForm_sent (V := V) name endName sh job c t seen ds rounds
    C F G h kept Wd j e hd ha hh hs hσ hj hfit he (by rw [hdY]; norm_num) hn
    (by rw [hdY, hfun]; exact (PolyOn.entry _ _ 0).mul (PolyOn.entry _ _ 1))
    (by rw [hfun]; exact (ReadsAlike.entry 0).mul (ReadsAlike.entry 1))
    (by rw [hat, Reading.gl.mul]; exact hE)
  rw [hat] at h4
  exact ⟨r, s, h1, h2, h3, h4⟩

/-- At a product level the product of the two end values reads as the cube's summand. -/
theorem level_ends (mu : ℕ) (order : List ℕ) (rho : Array E) (tb : Tab × Tab) (rs : List E) :
    Reading.gl.val (((levelJob mu order rho tb).ends rs).getD 0 zeroE) *
        Reading.gl.val (((levelJob mu order rho tb).ends rs).getD 1 zeroE) =
      Reading.gl.val ((levelJob mu order rho tb).cube.summandAt rs) := by
  show Reading.gl.val (((levelJob mu order rho tb).cube.valuesAt rs).toList.getD 0 zeroE) *
    Reading.gl.val (((levelJob mu order rho tb).cube.valuesAt rs).toList.getD 1 zeroE) = _
  rw [summandAt_read, toList_getD, toList_getD]
  show _ = Reading.gl.val oneE * _ + 0
  rw [Reading.gl.one, one_mul, add_zero]

/-- A product level of two tables, where its cube fits. -/
theorem level_rowForm_sent (name endName : String) (mu : ℕ) (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob (k4LevelShape mu) job)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork)
    (h : Heard) (kept : Aff) (Wd : World GE) (order : List ℕ) (rho : Array E) (tb : Tab × Tab)
    (hd : drawsOk ((k4SumJob (k4LevelShape mu) job).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (k4SumJob (k4LevelShape mu) job)) c t seen ds =
      some rounds)
    (hh : hear C ((k4SumJob (k4LevelShape mu) job).callAt t.input (frontOf t seen)) F rounds =
      some (h, G))
    (hs : ∀ i,
      i < ownSlots ((k4SumJob (k4LevelShape mu) job).callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (hj : job t.input (frontOf t seen) = some (levelJob mu order rho tb))
    (hfit : (levelJob mu order rho tb).cube.fits = true)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (levelJob mu order rho tb).cube.total) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = 2 ∧
      (rowForm h (mulE (s.getD 0 zeroE) (s.getD 1 zeroE)) kept).value Reading.gl Wd =
        Reading.gl.val h.eps * kept.value Reading.gl Wd :=
  prod_rowForm_sent (V := V) name endName (k4LevelShape mu) job c t seen ds rounds C F G h kept Wd
    (levelJob mu order rho tb) ⟨2, 2⟩ hd ha hh hs hσ hj
    (jobFits_parts (levelJob_jobFits mu order rho tb hfit)) rfl rfl (fun _ _ => rfl)
    (by
      show ((levelJob mu order rho tb).cube.valuesAt _).toList.length = 2
      rw [Array.length_toList, valuesAt_size]
      rfl)
    (level_ends mu order rho tb _)

/-- The job of the sumcheck on the row products, of its tables, where its cube fits. k: the number
of end values that the call states. -/
theorem rowsJob_rowForm_sent (name endName : String) (Q : K4Pub) (k : ℕ)
    (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob (k4TokenShape Q.P.y.h.lt 2 k) job)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork)
    (h : Heard) (kept : Aff) (Wd : World GE) (p : Pts) (ms : Array Tab)
    (hd : drawsOk ((k4SumJob (k4TokenShape Q.P.y.h.lt 2 k) job).callAt t.input (frontOf t seen))
      ds = true)
    (ha : alone (sumPart (V := V) name endName (k4SumJob (k4TokenShape Q.P.y.h.lt 2 k) job)) c t
      seen ds = some rounds)
    (hh : hear C ((k4SumJob (k4TokenShape Q.P.y.h.lt 2 k) job).callAt t.input (frontOf t seen)) F
      rounds = some (h, G))
    (hs : ∀ i, i < ownSlots
        ((k4SumJob (k4TokenShape Q.P.y.h.lt 2 k) job).callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (hj : job t.input (frontOf t seen) = some (rowsJobOf Q p ms))
    (hf : (rowsJobOf Q p ms).cube.fits = true) (hk : ms.size = k)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (rowsJobOf Q p ms).cube.total) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = k ∧
      (rowForm h (rowsSummand Q.P.y (heardOf Q p) s.toArray) kept).value Reading.gl Wd =
        Reading.gl.val h.eps * kept.value Reading.gl Wd :=
  k4_rowForm_sent (V := V) name endName (k4TokenShape Q.P.y.h.lt 2 k) job c t seen ds rounds C F G h
    kept Wd (rowsJobOf Q p ms) ⟨2, k⟩ hd ha hh hs hσ hj (rowsJob_shape Q p ms k hf) rfl
    (by show 2 + 1 < 2 ^ 32; norm_num)
    (by
      show ((rowsJobOf Q p ms).cube.valuesAt _).toList.length = k
      rw [Array.length_toList, valuesAt_size]
      exact hk)
    (rowsJob_poly Q p ms _ _) (rowsJob_alike Q p ms _) (rowsJob_ends Q p ms _)

/-- The powers omV in the structure that the maker lays for the verifier's functions. -/
theorem heardOf_omV (Q : K4Pub) (p : Pts) : (heardOf Q p).omV = p.omV := rfl

/-! ## 2 The row's jobs -/

/-- The squares' job in the row. -/
abbrev squaresSum (Q : K4Pub) : SumJob K4In Unit :=
  k4SumJob (k4LevelShape Q.P.rd.muV) fun w fr => jobSquares Q w (ptsOf Q w fr.heard)

/-- The row products' job in the row. -/
abbrev rowsSum (Q : K4Pub) : SumJob K4In Unit :=
  k4SumJob (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)) fun w fr =>
    jobRows Q w (ptsOf Q w fr.heard)

/-- The first gated product's job in the row. -/
abbrev gatedSum (Q : K4Pub) : SumJob K4In Unit :=
  k4SumJob (k4LevelShape Q.P.rd.muH) fun w fr => jobGated Q w (ptsOf Q w fr.heard)

/-- The second gated product's job in the row. -/
abbrev gated2Sum (Q : K4Pub) : SumJob K4In Unit :=
  k4SumJob (k4LevelShape Q.P.rd.muH2) fun w fr => jobGated2 Q w (ptsOf Q w fr.heard)

/-! ## 3 The five -/

/-- **The first gated product.** -/
theorem gated_rowForm_sent (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (gatedSum Q)) (t : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (kept : Aff)
    (Wd : World GE)
    (hd : drawsOk ((gatedSum Q).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (gatedSum Q)) c t seen ds = some rounds)
    (hh : hear C ((gatedSum Q).callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((gatedSum Q).callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (tb : Tab × Tab) (ht : gatedTabs Q t.input = some tb)
    (hfit : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (ptsOf Q t.input t.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
        ztOf Q (ptsOf Q t.input t.heard)) tb).cube.fits = true)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (ptsOf Q t.input t.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
        ztOf Q (ptsOf Q t.input t.heard)) tb).cube.total) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = 2 ∧
      (rowForm h (mulE (s.getD 0 zeroE) (s.getD 1 zeroE)) kept).value Reading.gl Wd =
        Reading.gl.val h.eps * kept.value Reading.gl Wd :=
  level_rowForm_sent (V := V) name endName Q.P.rd.muH
    (fun w fr => jobGated Q w (ptsOf Q w fr.heard)) c t seen ds rounds C F G h kept Wd _ _ tb hd ha
    hh hs (by show (gatedTabs Q t.input).map _ = _; rw [ht]; rfl) hfit hσ

/-- **The second gated product.** -/
theorem gated2_rowForm_sent (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (gated2Sum Q)) (t : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (kept : Aff)
    (Wd : World GE)
    (hd : drawsOk ((gated2Sum Q).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (gated2Sum Q)) c t seen ds = some rounds)
    (hh : hear C ((gated2Sum Q).callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((gated2Sum Q).callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (tb : Tab × Tab) (ht : gatedTabs2 Q t.input = some tb)
    (hfit : (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((ptsOf Q t.input t.heard).rhoM ++ downFrom (ptsOf Q t.input t.heard).rs Q.P.y.lfe ++
        (ptsOf Q t.input t.heard).rt) tb).cube.fits = true)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((ptsOf Q t.input t.heard).rhoM ++ downFrom (ptsOf Q t.input t.heard).rs Q.P.y.lfe ++
        (ptsOf Q t.input t.heard).rt) tb).cube.total) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = 2 ∧
      (rowForm h (mulE (s.getD 0 zeroE) (s.getD 1 zeroE)) kept).value Reading.gl Wd =
        Reading.gl.val h.eps * kept.value Reading.gl Wd :=
  level_rowForm_sent (V := V) name endName Q.P.rd.muH2
    (fun w fr => jobGated2 Q w (ptsOf Q w fr.heard)) c t seen ds rounds C F G h kept Wd _ _ tb hd
    ha hh hs (by show (gatedTabs2 Q t.input).map _ = _; rw [ht]; rfl) hfit hσ

/-- **The squares.** -/
theorem squares_rowForm_sent (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (squaresSum Q)) (t : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (kept : Aff)
    (Wd : World GE)
    (hd : drawsOk ((squaresSum Q).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (squaresSum Q)) c t seen ds = some rounds)
    (hh : hear C ((squaresSum Q).callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((squaresSum Q).callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (j : Job) (hj : jobSquares Q t.input (ptsOf Q t.input t.heard) = some j)
    (hσ : C.value Reading.gl Wd = Reading.gl.val j.cube.total) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = 2 ∧
      (rowForm h (mulE (s.getD 0 zeroE) (s.getD 1 zeroE)) kept).value Reading.gl Wd =
        Reading.gl.val h.eps * kept.value Reading.gl Wd := by
  have hj' := hj
  rw [jobSquares_eq] at hj'
  split at hj'
  · rename_i hf
    obtain rfl := Option.some.inj hj'
    exact prod_rowForm_sent (V := V) name endName (k4LevelShape Q.P.rd.muV)
      (fun w fr => jobSquares Q w (ptsOf Q w fr.heard)) c t seen ds rounds C F G h kept Wd _ ⟨2, 2⟩
      hd ha hh hs hσ hj (jobFits_parts (sqJob_jobFits _ _ _ hf)) rfl rfl (fun _ _ => rfl) rfl (by
        rw [summandAt_read]
        show _ = Reading.gl.val oneE * _ + 0
        rw [Reading.gl.one, one_mul, add_zero]
        rfl)
  · cases hj'

/-- **The merge.** -/
theorem merge_rowForm_sent (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (mergeSum Q)) (t : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (kept : Aff)
    (Wd : World GE)
    (hd : drawsOk ((mergeSum Q).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (mergeSum Q)) c t seen ds = some rounds)
    (hh : hear C ((mergeSum Q).callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((mergeSum Q).callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (cls : List WsClaim) (hc : mergeClaimsAt Q t.input (ptsOf Q t.input t.heard) = some cls)
    (hσ : C.value Reading.gl Wd = Reading.gl.val
      (mergeJobOf Q.P.wsLay t.input.w cls (ptsOf Q t.input t.heard).rhoW).cube.total) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = 1 ∧
      (rowForm h (s.headD zeroE) kept).value Reading.gl Wd =
        Reading.gl.val h.eps * kept.value Reading.gl Wd :=
  k4_rowForm_sent (V := V) name endName (k4PlainShape Q.P.wsLay.lk 1 1)
    (fun w fr => jobMerge Q w (ptsOf Q w fr.heard)) c t seen ds rounds C F G h kept Wd
    (mergeJobOf Q.P.wsLay t.input.w cls (ptsOf Q t.input t.heard).rhoW) ⟨1, 1⟩ hd ha hh hs hσ
    (by show (mergeClaimsAt Q t.input (ptsOf Q t.input t.heard)).map _ = _; rw [hc]; rfl)
    (jobFits_parts (mergeJob_jobFits _ _ _ _)) rfl (by show 1 + 1 < 2 ^ 32; norm_num) rfl
    (mergeJob_poly _ _ _ _ _ _) (mergeJob_alike _ _ _ _ _) rfl

/-- **The row products.** H: what the verifier has heard: of it the summand reads the powers omV
alone. At norms of five limbs. -/
theorem rows_rowForm_sent (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (rowsSum Q)) (t : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (kept : Aff)
    (Wd : World GE)
    (hd : drawsOk ((rowsSum Q).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (rowsSum Q)) c t seen ds = some rounds)
    (hh : hear C ((rowsSum Q).callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((rowsSum Q).callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (j : Job) (hj : jobRows Q t.input (ptsOf Q t.input t.heard) = some j)
    (hxl : Q.P.y.h.xl = 5) (H : OnBytes.Model.Layer.Heard)
    (hom : H.omV = (ptsOf Q t.input t.heard).omV)
    (hσ : C.value Reading.gl Wd = Reading.gl.val j.cube.total) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = ledNO Q.P.y.h.xl * Q.P.y.NI ∧
      (rowForm h (rowsSummand Q.P.y H s.toArray) kept).value Reading.gl Wd =
        Reading.gl.val h.eps * kept.value Reading.gl Wd := by
  have hj' := hj
  rw [jobRows_eq] at hj'
  cases hms : rowMaps Q t.input (ptsOf Q t.input t.heard) with
  | none =>
    rw [hms] at hj'
    cases hj'
  | some ms =>
    rw [hms] at hj'
    have hj2 : (if (rowsJobOf Q (ptsOf Q t.input t.heard) ms).cube.fits then
        some (rowsJobOf Q (ptsOf Q t.input t.heard) ms) else none) = some j := hj'
    split at hj2
    · rename_i hf
      obtain rfl := Option.some.inj hj2
      obtain ⟨r, s, h1, h2, h3, h4⟩ := rowsJob_rowForm_sent (V := V) name endName Q
        (ledNO Q.P.y.h.xl * Q.P.y.NI) (fun w fr => jobRows Q w (ptsOf Q w fr.heard)) c t seen ds
        rounds C F G h kept Wd (ptsOf Q t.input t.heard) ms hd ha hh hs hj hf
        (by rw [rowMaps_size Q t.input _ ms hms, hxl]; rfl) hσ
      refine ⟨r, s, h1, h2, h3, ?_⟩
      rw [rowsSummand_congr Q.P.y H (heardOf Q (ptsOf Q t.input t.heard))
        (hom.trans (heardOf_omV Q _).symm)]
      exact h4
    · cases hj2

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.prod_rowForm_sent
#print axioms ProofFile.Honest.K4.level_ends
#print axioms ProofFile.Honest.K4.level_rowForm_sent
#print axioms ProofFile.Honest.K4.rowsJob_rowForm_sent
#print axioms ProofFile.Honest.K4.heardOf_omV
#print axioms ProofFile.Honest.K4.gated_rowForm_sent
#print axioms ProofFile.Honest.K4.gated2_rowForm_sent
#print axioms ProofFile.Honest.K4.squares_rowForm_sent
#print axioms ProofFile.Honest.K4.merge_rowForm_sent
#print axioms ProofFile.Honest.K4.rows_rowForm_sent
