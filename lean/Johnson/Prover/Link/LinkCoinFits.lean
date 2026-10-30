-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkCoinFits.lean: THE PUBLIC TEST kFits (Johnson/Prover/Link/LinkCoin.lean):
WHO PAYS IT, AND WHAT IT GIVES. Statements on public numbers and their proofs.

  FitsAlong     along the stages, in LinkCoin.lean's own letters: at each stage but the last: h ≤ k;
                the fresh table's packing has room (packedN's own guard,
                Johnson/Prover/Link/BodyPack.lean); what the switch carries AND ONE ENTRY MORE, the
                pad's, have room in the new mask table: so SwK.free's size is not cut and is not 0;
                THE LIBRARY's CLAUSE AT A SWITCH, CsFit (OnBytes/Slice/CsData.lean), whole: where it
                fails ansAt (Johnson/Prover/Link/BodyAll.lean) lays 0 · the last stage has
                k = h = 0: one main row, one mask row
  stage_gives   what the library's test on a stage by itself holds, of what is spent here
  fitsAlong_of_stagesOk, fitsAlong_of_kFits   the library's walk gives it; so kFits does
  sizesOk_of_planOk   the test on the plan of the structure Block that proximityTestKind makes holds sizesOk
  kFits_of_planOk     that test pays kFits' clause on the stages; the other clauses are asked

Limits. Public numbers alone. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.LinkCoin
import Johnson.Desc.K12.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

/-- **What the sizes' test gives, along the stages.** -/
def FitsAlong : Fmt.M1.Stage → List Fmt.M1.Stage → Prop
  | cur, [] => cur.k = 0 ∧ cur.h = 0
  | cur, next :: rest =>
    cur.h ≤ cur.k ∧ (sgOf cur).h + 2 * (sgOf cur).g + 1 ≤ (sgOf cur).Z.l ∧
      maskUsed (sgOf cur) + 1 ≤ 2 ^ (sgOf next).h * (sgOf next).Z.l ∧
      CsFit (sgOf cur) (sgOf next) ∧ FitsAlong next rest

/-- What the library's test on a stage by itself holds, of what is spent here. -/
theorem stage_gives (last : Bool) (s : Fmt.M1.Stage) (h : K12.stageOk last s = true) :
    s.C.l = 2 ^ Fmt.M1.lg s.C.l ∧ s.Z.l = 2 ^ Fmt.M1.lg s.Z.l ∧ s.Z.a ≤ s.C.a ∧ s.h ≤ s.k ∧
      (last = true → s.k = 0) ∧ (last = false → 2 * s.k + 1 - s.h ≤ s.Z.l) := by
  simp only [K12.stageOk, K12.pow2, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hC⟩, hZ⟩, ha⟩, -⟩, hh⟩ := h.1
  refine ⟨hC.symm, hZ.symm, ha, hh, fun hl => ?_, fun hl => ?_⟩
  · have := h.2
    rw [hl] at this
    simpa using this
  · have := h.2
    rw [hl] at this
    simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2

theorem fitsAlong_of_stagesOk : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (b : Option Fmt.M1.Stage), stagesOk 1 b (cur :: rest) = true → FitsAlong cur rest
  | cur, [], b, h => by
    simp only [stagesOk, Bool.and_eq_true] at h
    obtain ⟨-, -, -, hh, hk, -⟩ := stage_gives _ cur h.1.1
    have hk0 : cur.k = 0 := hk rfl
    exact ⟨hk0, by omega⟩
  | cur, next :: rest, b, h => by
    have h1 : K12.stageOk false cur = true ∧ stagesOk 1 (some cur) (next :: rest) = true := by
      unfold stagesOk at h
      simp only [Bool.and_eq_true] at h
      exact ⟨h.1.1, h.2⟩
    have h2 : K12.stageOk rest.isEmpty next = true ∧ K12.stepOk 1 cur next = true := by
      have := h1.2
      unfold stagesOk at this
      simp only [Bool.and_eq_true] at this
      exact this.1
    obtain ⟨-, -, ha, hh, -, hroom⟩ := stage_gives _ cur h1.1
    obtain ⟨hC', hZ', -, hh', -, -⟩ := stage_gives _ next h2.1
    have h3 := h2.2
    simp only [K12.stepOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h3
    have hmask : 2 * cur.Z.l + cur.C.r + 2 * cur.Z.r + 1 ≤ 2 ^ next.h * next.Z.l := by
      rw [Nat.mul_comm (2 ^ next.h) next.Z.l]
      exact h3.1.2
    have hmain : 2 ^ (next.h + (next.k - next.h)) * next.C.l = cur.C.l := by
      rw [Nat.add_sub_cancel' hh', Nat.mul_comm (2 ^ next.k) next.C.l]
      exact h3.1.1
    refine ⟨hh, ?_, hmask, ⟨hmain, hmask, hC', hZ', ha⟩,
      fitsAlong_of_stagesOk next rest (some cur) h1.2⟩
    show cur.h + 2 * (cur.k - cur.h) + 1 ≤ cur.Z.l
    have := hroom rfl
    omega

/-- **kFits gives it.** -/
theorem fitsAlong_of_kFits (P : Desc.K15.P15) (S : Sz) (first : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (h : kFits P S (first :: rest) = true) : FitsAlong first rest := by
  simp only [kFits, sizesOk, Bool.and_eq_true] at h
  exact fitsAlong_of_stagesOk first rest none h.1.1.1.2.2

/-- The test on the plan holds sizesOk. -/
theorem sizesOk_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : sizesOk p.nums.stages p.answers = true := by
  unfold proximityTestKind at hp
  split at hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact hp.1.1.1.1
  · cases hp

/-- **Who pays kFits.** -/
theorem kFits_of_planOk {T Cl : Type} (X : Parts T) (P : Desc.K15.P15) (S : Sz)
    (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hp : (proximityTestKind X (Desc.K15.p12Of P) : Block T Cl).planOk = true)
    (ha : (Desc.K15.p12Of P).answers = 1) (hs : (Desc.K15.p12Of P).nums.stages = first :: rest)
    (hM : S.P.T.l + 1 ≤ S.P.R * S.P.C.l) (hT : S.P.t0 + S.P.T.r + 1 ≤ S.P.R * S.P.C.l)
    (hC : sameCode S.P.C first.C = true) (hZ : sameCode S.P.Z first.Z = true) (h0 : first.h = 0)
    (hk : first.k = S.P.aR + 1) : kFits P S (Desc.K15.p12Of P).nums.stages = true := by
  have h := sizesOk_of_planOk X (Desc.K15.p12Of P) hp
  rw [ha] at h
  unfold kFits
  rw [h, ha, hs]
  simp only [hC, hZ, h0, hk, hM, hT, decide_true, beq_self_eq_true, Bool.and_self]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.stage_gives
#print axioms Johnson.Prover.Link.fitsAlong_of_stagesOk
#print axioms Johnson.Prover.Link.fitsAlong_of_kFits
#print axioms Johnson.Prover.Link.sizesOk_of_planOk
#print axioms Johnson.Prover.Link.kFits_of_planOk
