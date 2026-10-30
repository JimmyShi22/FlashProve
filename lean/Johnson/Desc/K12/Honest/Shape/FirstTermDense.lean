-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/FirstTermDense.lean: the "dense" twin of `first_of_shape`
(FirstTerm.lean in this folder).

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

Main names. `first_of_shape_dense`.

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
import Johnson.Desc.K12.Honest.Shape.FirstTerm
import Johnson.Desc.K12.Honest.Shape.TestDoorDense
import Johnson.Desc.K12.Honest.Shape.TestSwitchDense

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

/-- The twin of `first_of_shape` (FirstTerm.lean), with `DenseRow` in the place of `PlainRow`. -/
theorem first_of_shape_dense (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage)
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
    (A : TermAsks p K rest a next o (tBat p t₀ dB) P D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC) :
    (guardedProximityTestParts.front p).decide t₀ [] [] = .ok t₀ ∧
      (guardedProximityTestParts.bat p (((laidOf p).take 1).map (·.1))).decide t₀ [noDigest ⟨[], dB⟩] [] =
        .ok (tBat p t₀ dB) ∧
      (guardedProximityTestParts.group (tBat p t₀ dB)).any (firstFits a) = true ∧
      (∃ row L, (tBat p t₀ dB).pass = .claim row L) ∧
      FirstYes p K rest 0 a next (laidS p) o (tBat p t₀ dB) P
        (groupTrees Dp.ts (logAt Dp.book) c) D := by
  obtain ⟨G, row, hG, hr, d1, d2, d3, d4⟩ := door_of_shape_dense h hm ht hpl hv hB hF [⟨[], dB⟩]
    (rfAt K 0 a o (tBat p t₀ dB) P D) fB A.fitF
  have eB : tBat p t₀ dB = batT t₀ G row := getD_of_ok d2
  obtain ⟨G', row', hG', hr', -, -, -, -, hS⟩ := first_stage_of_shape_dense (last := rest.isEmpty) h
      hm ht
    hpl hv Pl hB hF [⟨[], dB⟩] (rfAt K 0 a o (tBat p t₀ dB) P D) fB A.fitF
    (noDigest ⟨[], D (o + 1 + ((sgOf a).h + (sgOf a).g))⟩)
    (noDigest ⟨[.answer (ofE (aAns p 0 a next o D (t1At p K 0 a (laidS p) o (tBat p t₀ dB) P D)
      (qAt K rest 0 a next o P D)))], D (o + 2 + ((sgOf a).h + (sgOf a).g))⟩)
    A.fitS _ rfl (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D) (bump · Dp.ts)
    fun G₂ row₂ hG₂ hr₂ => by
      obtain rfl : G = G₂ := Option.some.inj (hG.symm.trans hG₂)
      obtain rfl : row = row₂ := Option.some.inj (hr.symm.trans hr₂)
      exact readsAny_term p K rest a next o (tBat p t₀ dB) P D Dp c _ dS dC A row _
        (by rw [eB]; rfl) _ (by rw [eB] at d4 ⊢; exact d4) _ _ rfl n rest.isEmpty _ rfl
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  obtain rfl : row = row' := Option.some.inj (hr.symm.trans hr')
  refine ⟨d1, by rw [eB]; exact d2, by rw [eB]; exact d3, ⟨row, _, by rw [eB]; rfl⟩, ?_⟩
  exact firstYes_of_done p K rest a next (laidS p) o (tBat p t₀ dB) P _ D _
    (by rw [eB] at d4 ⊢; exact d4) n dS dC A.cut _ _ _ _ _ _ rfl hS A.nF A.oF A.nS
    (by rw [A.oS]; simp [groupTrees])

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.first_of_shape_dense
