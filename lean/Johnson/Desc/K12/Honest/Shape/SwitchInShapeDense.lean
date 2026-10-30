-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/SwitchInShapeDense.lean: the "dense" twins of `door_facts`,
`switchIn_shape` (SwitchInShape.lean in this folder).

What it is. The old statements take as a hypothesis that every row taken in is a `PlainRow`. The
twins take `DenseRow` in its place. `PlainRow` (OnBytes/Slice/BlkPlain.lean) says that no tensor of
a row has a written-out variable. `DenseRow` (OnBytes/Slice/BlkProxDense.lean) allows such variables
where every tensor is in order and its slice lies inside its vector; it follows from `PlainRow`
(`denseRow_of_plain`). The rows meant are those that the proximity test takes in at the group under
test (`runRows`, OnBytes/Slice/BlkBegin.lean). Apart from that and from the twins' names, each
statement is the old one, letter for letter.

Why. The only place where the old chain spends its hypothesis is the field `dense` of the library's
`TestFront`, which `testFront_of` fills from `PlainRow` by `denseRow_of_plain`. So the weaker
hypothesis is enough. That a row taken in at the first chain's proximity test has written-out
variables is read off the description's text; no theorem in these files says so.

Main names. `door_facts_dense`, `switchIn_shape_dense`.

By what. Each proof is the old proof with the twins' names in it.

Limits.
- These statements rest on this: in Johnson/Prover/Link/FormFirst.lean the structure
  `TestFront` has the field `dense`. With a field `plain` in its place,
  `testFront_of_dense` (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean), on which all the twins
  rest, could not be proved.
- They do not reach the first chain's proximity test yet. The library proves the new hypothesis
  there, of the verifier's state (`taken_dense_entered`, Johnson/AtFull/Shape/TakenRowsDense.lean).
  These files do not show that the other hypotheses hold there: the other fields of `ShapeAsksD`
  (Johnson/Desc/ProofFile/Honest/K12/PlanBDense.lean), `planB`, and the hypotheses on the prover's
  data.
- `ShapeAsksD` is made from the old `ShapeAsks` (`shapeAsksD_of`), and so from the old mark
  `stPlainB`; and from `FrontAsksD`, the hypotheses on the front with the same new field, by
  `shapeAsksD_of_front` (ShapeAllDense.lean) and `shapeAsksD_of_two`, `shapeAsksD_of_form`,
  `shapeAsksD_of_draws` (ShapeOfTwoDense.lean); `FrontAsksD` is made by `frontAsksD_of_five`
  (FrontAtShapeDense.lean). These files lie in Johnson/Desc/ProofFile/Honest/K12/. Without a twin:
  `sorts_of_coreB` (SortsMember.lean) and `frontAsks_of_shape` (OneToAll.lean, not in the library
  yet).
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- Only the case in which the fresh table has come earlier is served, as in the old statements.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.K12.Honest.Shape.SwitchInShape
import Johnson.Desc.K12.Honest.Shape.TestDoorDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.Sh
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.K12

/-- The twin of `door_facts` (SwitchInShape.lean), with `DenseRow` in the place of `PlainRow`. -/
theorem door_facts_dense {p : P12} {a next : Fmt.M1.Stage} {t₀ : T12} {i nn : ℕ × ℕ} {id : ℕ}
    {dB : Fmt.Drawn}
    (h : doorB p a next (((laidOf p).take 1).map (·.1)) i nn (testSh t₀) = true)
    (hm : t₀.mask = some id) (ht : stTidyB t₀.st = true)
    (hpl : ∀ G, t₀.st.groups[t₀.g]? = some G → ∀ r ∈ (runRows t₀.st G).toList, DenseRow r)
    (hv : claimsB t₀ = true) (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (fB : roundsFit (((laidOf p).take 1).map (·.1)) [⟨[], dB⟩] = true) :
    ∃ G row x, TestFront p a next t₀ G i nn id ∧
      Bat.combine (begun t₀.st t₀.g G) t₀.g ⟨Means.layoutOf t₀.st G, runRows t₀.st G⟩ x =
        some row ∧
      tBat p t₀ dB = batT t₀ G row ∧ p.nums.free = t₀.roots := by
  unfold doorB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h4' : (match t₀.mask with
    | some id => cameB a (testSh t₀).core t₀.g i id
    | none => (testSh t₀).core.st.oracles.length == (testSh t₀).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := ProofFile.Honest.Sh.testFront_of_dense h1 hm h4' ht hpl
  obtain ⟨row, hr, hb⟩ := bat5_yes H _ (batOwes_of h2 H.group) hB [⟨[], dB⟩] fB
  exact ⟨G, row, _, H, hr, getD_of_ok hb, (frontOwes_of h3 hv H.group).roots⟩

/-- The twin of `switchIn_shape` (SwitchInShape.lean), with `DenseRow` in the place of `PlainRow`.
-/
theorem switchIn_shape_dense (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage)
    (a next : Fmt.M1.Stage)
    (o : ℕ) (t₀ : T12) (P : PS) (D : ℕ → Fmt.Drawn) (dB : Fmt.Drawn) (Dp : Plain)
    (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (id : ℕ) (dS dC : Fmt.DeclaredRound)
    (h : doorB p a next (((laidOf p).take 1).map (·.1)) i (n.code, n.maskCode) (testSh t₀) = true)
    (hm : t₀.mask = some id) (ht : stTidyB t₀.st = true)
    (hpl : ∀ G, t₀.st.groups[t₀.g]? = some G → ∀ r ∈ (runRows t₀.st G).toList, DenseRow r)
    (hv : claimsB t₀ = true)
    (Pl : SwitchPub p t₀.st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (hF : foldCut a.k (((laidS p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf p).take 1).map (·.1)) [⟨[], dB⟩] = true)
    (A : TermAsks p K rest a next o (tBat p t₀ dB) P D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (rC : Fmt.RoundView) (hrC : rC.drawn.poss = (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss) :
    ∃ rows, SwitchIn p 0 a next n (tBat p t₀ dB).st.groups.size
        (t1At p K 0 a (laidS p) o (tBat p t₀ dB) P D) rows rC ∧
      (t1At p K 0 a (laidS p) o (tBat p t₀ dB) P D).st =
        Ground.withGroup (spent (tBat p t₀ dB).st id) n.code n.maskCode := by
  obtain ⟨G, row, x, H, hr, eB, hroots⟩ := door_facts_dense h hm ht hpl hv hB fB
  rw [eB] at A ⊢
  have F := foldFront_first H x row hr
  have hfold := fold5_yes F hF (rfAt K 0 a o (batT t₀ G row) P D) A.fitF
  have e1 : t1At p K 0 a (laidS p) o (batT t₀ G row) P D = _ := getD_of_ok hfold
  obtain ⟨rE, rR, hrs, hR⟩ := rounds_split (length_of_foldCut hF) A.fitF
  obtain ⟨places, Pb⟩ := readPub_sh (A.pub _ _ (by rw [e1]; rfl))
  rw [e1] at Pb ⊢
  rw [hrs] at Pb ⊢
  have hcodes : (batT t₀ G row).st.codes = t₀.st.codes := batT_codes t₀ G row
  have hrow : foldRowOk (spent (batT t₀ G row).st id)
      (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)) row = true :=
    (Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans F.rowFits)
  have hlen : (rR.map drawnOf).length = a.k := by rw [List.length_map]; exact hR
  have hplain : DenseForm row.c := combine_dense _ _ _ _ _ H.dense hr
  obtain ⟨cd, hcd, ecd⟩ := Pl.codes.base
  refine ⟨_, ⟨rfl, ?_,
    inOrder_foldT _ row _ _ _ id _ (H.order.begun t₀.g G H.group), hroots.symm, ?_,
    denseForm_foldOutput _ _ row id _ _ _ hplain, ?_, by rw [hrC]; exact A.range,
    oldIn_of_pub Pb⟩, rfl⟩
  · show ((batT t₀ G row).st.groups.push _)[(batT t₀ G row).st.groups.size]? = _
    rw [Array.getElem?_push_size]
  · have Pl' : SwitchPub p (batT t₀ G row).st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS
        dC := by
      rw [hcodes]
      exact Pl
    exact foldedFit_pure (batT t₀ G row).st.codes (sgOf a) (sgOf next) ⟨i.1, i.2, a.k, a.h⟩
      Pl'.codes n.code n.maskCode Pl'.zk Pl'.codeN Pl'.zkN Pl'.small (batT t₀ G row).st
      (spent (batT t₀ G row).st id) row (Means.layoutOf t₀.st G) id (drawnOf rE)
      (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) (rR.map drawnOf) rfl
      rfl
      (H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun k => H.noKept k) (fun k _ => H.noKept k)
      (hlen.trans Pl.codes.k) ((Own.foldShapeFits_agrees _ _).trans F.shape) hrow
  · have h1 := cfits_foldOutput (spent (batT t₀ G row).st id)
      (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)) row id (drawnOf rE)
      (rR.map drawnOf) (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) hlen
      hrow
    have e : ((spent (batT t₀ G row).st id).codes.base.getD
        (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)).code default).ell =
        (sgOf a).C.l := by
      show ((batT t₀ G row).st.codes.base.getD i.1 default).ell = _
      rw [hcodes, Array.getD_eq_getD_getElem?, hcd]
      exact congrArg (·.l) ecd
    rw [e] at h1
    exact h1

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.door_facts_dense
#print axioms ProofFile.Honest.Sh.switchIn_shape_dense
