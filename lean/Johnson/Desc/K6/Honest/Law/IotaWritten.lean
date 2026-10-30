-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/IotaWritten.lean: THE FIELD iota OF THE LOOKUP ON THE OUTPUT HEAD's SIX
CALLS IS 1, 1, 1, 0, 0, 0: UNDER `SizesH` (`iota_written`), AND IN THE GOALS' SCOPE
(`iota_in_scope`). By the library's reading of that field (Johnson/Road/FormsKeysForest.lean) a call
has 2 ^ iota trees: these two statements say the list alone.

WHAT IT IS NOT. A new argument: it is the library's own, cut off at a step. BOTH STATEMENTS HOLD AT
THE FULL SIZE's NUMBERS ALONE. Nothing on any property. Its two names stand in the namespace of the
output head's honest side (ProofFile.Honest.K6), not in the library's: the ten names of the library's
(…Head.Law.InScope) that the proofs call are opened by name. Should the library one day export that
equation, this file is to be removed.

Why it is typed. The library proves that equation as a step INSIDE its proof of `fs_written`
(Johnson/Desc/Kinds/Law/HeadFsWritten.lean), whose conclusion (`FsWritten`) does not hold it. A
search over the whole library for a statement that ends in it found none: the list stands in five
files, in four as a field of a written shape, in that proof as a step: a search, not a proof that
there is none. THE PROOF OF `iota_written` IS THAT PROOF's OWN LINES UP TO THAT STEP, less five
steps that the equation does not need, with two lists of binders blanked and two closing lines
added. That step spends the first clause of the library's general law on that list (`shape_numbers`,
Johnson/Road/FormsKeysForest.lean: a call's iota is its number of key bits less dT; `shape_iota_at`,
there, says the same call by call); what that search found exported nowhere is the six values in
scope.

Of lean/Johnson/Goal/ it calls `InScope.calls_six`, `InScope.place_lJ`
(Goal/Meaning/HeadColsScope.lean), as the library's own proof does, and `Hd.scan_of_scope`
(Goal/Meaning/ScopeScanTies.lean); it imports no module of that folder directly: they come beneath
Kinds/Law/HeadFsWritten.lean.
-/
import Johnson.Desc.Kinds.Law.HeadFsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales is no instance in this file: no statement here can take it
in silence. An instance is taken away, none is added. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6

open OnBytes.Model (Call CallD place Forest.Shape)
open OnBytes.Model.Head (HL)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (SizesH layout_fs numbers_JV calls_six
  lookups_is lookOne lookOne_n place_lJ foldl_six sizesH_scan)

/-- **The six numbers, at the full size's sizes.** CONDITIONAL ON `SizesH h` (the library's nine
equations on the head's public data at the full size: the equation here does not need all nine) and
on the layout's return. -/
theorem iota_written {h : OnBytes.Model.Head.Shape} {tauFC : Array UInt64} {L : HL} (Z : SizesH h)
    (hy : OnBytes.Model.Head.layout h tauFC = .ok L) : L.fs.iota = #[1, 1, 1, 0, 0, 0] := by
  obtain ⟨L0, calls, fs0, pub, h3, h4, _, h7, _, hcl, hfs⟩ := layout_fs hy
  obtain ⟨j1, j2⟩ := numbers_JV h3
  have hJV : L0.JV = 202048 := by
    rw [j1, Z.V, Z.S2]
    decide
  have hJVa : L0.JVa = 131072 := by
    rw [j2, Z.V, Z.S2]
    decide
  have hc := calls_six h4 Z.lines
  rw [Z.d, hJV, hJVa, Z.XL, Z.floor, Z.lt] at hc
  generalize OnBytes.Model.Head.tauFEOf h.famF h.digSh h.tabS = tauFE at h7 hcl
  rw [lookups_is, hc] at h7 hcl
  simp only [List.map_cons, List.map_nil] at h7 hcl
  -- the key bits and the table bits of the six
  have n0 : (lookOne h tauFC tauFE (place "R16a" "R16"
      [("NF", 5120, false), ("NFH", 5120, false), ("HD0", 202048, false)] (27 - 10))).n = 28 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have n1 : (lookOne h tauFC tauFE (place "R16b" "R16" [("HD1", 202048, false)] (27 - 10))).n =
      28 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have n2 : (lookOne h tauFC tauFE (place "R8" "R8"
      [("ROW", OnBytes.Model.ledNRH 5, false), ("HD2", 202048, false)] (27 - 10))).n = 28 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have n3 : (lookOne h tauFC tauFE (place "FEa" "FE" [("HE0", 131072, false)] (27 - 10))).n =
      27 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have n4 : (lookOne h tauFC tauFE (place "FEb" "FE" [("HE1", 202048 - 131072, false)]
      (27 - 10))).n = 27 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have n5 : (lookOne h tauFC tauFE (place "FC" "FC" [("CNF", 5120, false)] (27 - 10))).n = 27 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have d1 := OnBytes.Road.shape_dT h7
  obtain ⟨i1, _, _, _⟩ := OnBytes.Road.shape_numbers h7
  have edT : fs0.dT = 27 := by
    rw [d1, foldl_six, n0, n1, n2, n3, n4, n5, Z.LIDB]
    decide
  have eio : fs0.iota = #[1, 1, 1, 0, 0, 0] := by
    rw [i1, edT]
    simp only [List.map_toArray, List.map_cons, List.map_nil, n0, n1, n2, n3, n4, n5]
  rw [hfs]
  exact eio

/-- **At all public files in the goals' scope.** -/
theorem iota_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    X.HLy.fs.iota = #[1, 1, 1, 0, 0, 0] := by
  have St := VerifiableInference.PlanWritten.publicSteps_of h
  have hP := OnBytes.Road.Hd.scan_of_scope hZ hR h
  exact iota_written (by rw [St.hS, hP]; exact sizesH_scan _ _) St.head

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.iota_written
#print axioms ProofFile.Honest.K6.iota_in_scope
