-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/PublicInScope.lean: the premises of `publicOfO_returns_withPol`
(Johnson/LPFPol/PublicAtPolicy.lean) hold at the parameter files of the goals' scope. So where the
public part of a stage is made at `VerifierAndGoals.policyFile v`, it is made at the same file with other
numbers C, theta, cap, if the goals' reader accepts that second file with the same scale file.

Main names.
* `publicOfO_returns_read`: THE LAW. Premises: h, `publicOfO secondHashFunction` returns X at `policyFile v`,
  KL, layout; hR, the goals' reader (`settingsAtRef`, Johnson/Flat/SettingsRead.lean;
  `VerifierAndGoals.readFiles` is that function) returns at `policyFile { v with C, theta, cap }` and KL. Then
  `publicOfO secondHashFunction` returns `X.withPol C theta cap` at that second file, KL, layout.
* `publicOfO_returns_inScope`: the same with `VerifierAndGoals.InScope` of the second set of files for hR.
* `gap_of_full`: an instance, at the two named sets of files. It shows that the premise on the
  second set can be met: `VerifierAndGoals.inScope_gap` (Johnson/Goal/Files/ScopeExample.lean) is a theorem.
* `premises_of_read`: where the reader returns at `policyFile v`: the strict scan returns there,
  theta ≤ C, cap ≤ 1024 and C < 2^32. The three bounds are a clause of `Inst.Model.Lawful`, which
  the reader tests.
* `T_of_public`: where `publicOf` returns X at `policyFile v`, the number of positions `X.hS.T` is
  1024: the line lt is a fixed line of that file.
* `digits_free`: where the strict scan returns at `policyFile v`, each of the eleven free lines
  holds a number of at most ten digits. `size_policyFile`: so the file has fewer than 2^32 bytes.

Limits.
* Both h and hR are premises. Nothing here shows that `publicOfO` returns at any file: in
  `gap_of_full` too the return at the stored example's files is a premise. `publicOf_zFull_returns`
  (AtFullSide/Planner/PublicReturns.lean) proves it at layout `some VerifierAndGoals.storedPublicFiles.lay`: limits there.
* The first file need not be in scope: it need only be `policyFile v` for some v. The scale file and
  the layout argument are the same on both sides.
* The law speaks of the public part alone: not of the chains, of the links, of a plan, or of any
  test on a key file or a proof file.
* The bound in `size_policyFile` is coarse: each fixed part of the file is bounded by 2^20 bytes,
  and not measured.
* Nothing on soundness, on hiding or on a security level.

For proofs only; no program imports this file.


-/
import Johnson.LPFPol.PublicAtPolicy
import Johnson.Goal.Meaning.ScopeScanTies
import Johnson.Flat.SettingsRead
import Johnson.Goal.Files.ScopeExample
import Ladder

set_option autoImplicit false

namespace LPFPol

open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open VerifierAndGoals (FreeLines policyFile)
open VerifierAndGoals.Lines
open OnBytes.Flat (settingsAtRef settingsAtRef_lines settingsAtRef_lawful)
open VerifiableInference.PlanWritten (publicOfO publicOfO_older)

/-! ### the length of the parameter file -/

/-- Where the strict scan returns at `policyFile v`, each free line's number has at most ten
digits. -/
theorem digits_free {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P)
    {p : String × Nat} (hp : p ∈ freeValues v) : (bytesOf (toString p.2)).length ≤ 10 := by
  have e4 : P.h.prof = 4 := by
    have a : P.value "prof" = 20 := value_fixed h (p := ("prof", 20)) (by decide)
    have b := polScan_prof h
    omega
  have hn : p.1 ∈ valueNames P.h.prof := by
    rw [e4]
    simp only [freeValues, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only; decide)
  have a := polWord_of_prof h hn
  rw [polWord_free v hp] at a
  unfold hit at a
  split at a
  · cases a
  · omega

/-- Where the strict scan returns at `policyFile v`, the file has fewer than 2^32 bytes. -/
theorem size_policyFile {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P) :
    (policyFile v).size < 2 ^ 32 := by
  have e : (policyFile v).toList = concatenatedWithLineFeeds frameLines ++ bytesOf (behindText v) := by
    rw [← frame_bytes, policyFile_eq, K.Left.toList_data, K.Left.toList_data,
      ByteArray.data_append, Array.toList_append, ConfigReaders.bytesOf_data]
  have s : (policyFile v).size = (policyFile v).toList.length := by
    rw [K.Left.toList_data, Array.length_toList]
    rfl
  have D : ∀ p ∈ freeValues v, (bytesOf (Nat.repr p.2)).length ≤ 10 := fun _ hp => digits_free h hp
  have d1 : (bytesOf (Nat.repr (v.eps1 % 2 ^ 32))).length ≤ 10 :=
    D ("eps1_lo", v.eps1 % 2 ^ 32) (by simp [freeValues])
  have d2 : (bytesOf (Nat.repr (v.eps1 / 2 ^ 32))).length ≤ 10 :=
    D ("eps1_hi", v.eps1 / 2 ^ 32) (by simp [freeValues])
  have d3 : (bytesOf (Nat.repr (v.eps2 % 2 ^ 32))).length ≤ 10 :=
    D ("eps2_lo", v.eps2 % 2 ^ 32) (by simp [freeValues])
  have d4 : (bytesOf (Nat.repr (v.eps2 / 2 ^ 32))).length ≤ 10 :=
    D ("eps2_hi", v.eps2 / 2 ^ 32) (by simp [freeValues])
  have d5 : (bytesOf (Nat.repr v.MF)).length ≤ 10 := D ("MF", v.MF) (by simp [freeValues])
  have d6 : (bytesOf (Nat.repr v.KF)).length ≤ 10 := D ("KF", v.KF) (by simp [freeValues])
  have d7 : (bytesOf (Nat.repr (v.epsF % 2 ^ 32))).length ≤ 10 :=
    D ("epsF_lo", v.epsF % 2 ^ 32) (by simp [freeValues])
  have d8 : (bytesOf (Nat.repr (v.epsF / 2 ^ 32))).length ≤ 10 :=
    D ("epsF_hi", v.epsF / 2 ^ 32) (by simp [freeValues])
  have d9 : (bytesOf (Nat.repr v.C)).length ≤ 10 := D ("C", v.C) (by simp [freeValues])
  have d10 : (bytesOf (Nat.repr v.theta)).length ≤ 10 := D ("theta", v.theta) (by simp [freeValues])
  have d11 : (bytesOf (Nat.repr v.cap)).length ≤ 10 := D ("cap", v.cap) (by simp [freeValues])
  have f0 : (concatenatedWithLineFeeds frameLines).length ≤ 2 ^ 20 := by decide +kernel
  have f1 : (concatenatedWithLineFeeds linesA1).length ≤ 2 ^ 20 := by decide +kernel
  have f2 : (concatenatedWithLineFeeds linesA2).length ≤ 2 ^ 20 := by decide +kernel
  have f3 : (concatenatedWithLineFeeds linesA3).length ≤ 2 ^ 20 := by decide +kernel
  have f4 : (concatenatedWithLineFeeds linesB).length ≤ 2 ^ 20 := by decide +kernel
  have n0 : (bytesOf "\n").length ≤ 16 := by decide +kernel
  have n1 : (bytesOf "eps1_lo ").length ≤ 16 := by decide +kernel
  have n2 : (bytesOf "\neps1_hi ").length ≤ 16 := by decide +kernel
  have n3 : (bytesOf "eps2_lo ").length ≤ 16 := by decide +kernel
  have n4 : (bytesOf "\neps2_hi ").length ≤ 16 := by decide +kernel
  have n5 : (bytesOf "MF ").length ≤ 16 := by decide +kernel
  have n6 : (bytesOf "\nKF ").length ≤ 16 := by decide +kernel
  have n7 : (bytesOf "epsF_lo ").length ≤ 16 := by decide +kernel
  have n8 : (bytesOf "\nepsF_hi ").length ≤ 16 := by decide +kernel
  have n9 : (bytesOf "C ").length ≤ 16 := by decide +kernel
  have n10 : (bytesOf "\ntheta ").length ≤ 16 := by decide +kernel
  have n11 : (bytesOf "\ncap ").length ≤ 16 := by decide +kernel
  rw [s, e, List.length_append]
  unfold behindText
  simp only [toString, bytesOf_append, bytesA1, bytesA2, bytesA3, bytesB, List.length_append]
  omega

/-! ### the other premises -/

/-- Where `publicOf` returns X at `policyFile v`, there are 1024 positions. -/
theorem T_of_public {v : FreeLines} {KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf (policyFile v) KL layout = .ok X) : X.hS.T = 1024 := by
  have hP := publicOf_scan h
  have a : X.P.value "lt" = 10 := value_fixed hP (p := ("lt", 10)) (by decide)
  have b : X.P.h.lt = 10 := by
    rw [ConfigReaders.polScan_h hP]
    exact a
  unfold Head.Shape.T
  rw [publicOf_lt h, b]

/-- Where the goals' reader returns at `policyFile v`: the strict scan returns there, and the three
numbers are in the range that `Inst.Model.Lawful` asks. -/
theorem premises_of_read {v : FreeLines} {KL : ByteArray} {pp : Inst.Model.ScalesAndPolicy}
    (hR : settingsAtRef (policyFile v) KL = .ok pp) :
    ∃ S, polScan (policyFile v) = .ok S ∧ v.theta ≤ v.C ∧ v.cap ≤ 1024 ∧ v.C < 2 ^ 32 := by
  obtain ⟨S, hS, -, -, -, hp⟩ := settingsAtRef_lines hR
  obtain ⟨-, -, -, -, c1, c2, c3⟩ := hdr_free hS
  have L := (settingsAtRef_lawful hR).pol
  rw [hp, c1, c2, c3] at L
  exact ⟨S, hS, L.2.1, L.2.2, L.1⟩

/-! ### the law -/

/-- **THE LAW.** Premises: h, `publicOfO secondHashFunction` returns X at `policyFile v`, KL, layout; hR, the
goals' reader returns at the same file with the numbers C, theta, cap, and KL. Then
`publicOfO secondHashFunction` returns `X.withPol C theta cap` at that second file, KL, layout. -/
theorem publicOfO_returns_read {v : FreeLines} {C theta cap : Nat} {KL : ByteArray}
    {layout : Option ByteArray} {X : Public} {pp' : Inst.Model.ScalesAndPolicy}
    (h : publicOfO secondHashFunction (policyFile v) KL layout = .ok X)
    (hR : settingsAtRef (policyFile { v with C := C, theta := theta, cap := cap }) KL = .ok pp') :
    publicOfO secondHashFunction (policyFile { v with C := C, theta := theta, cap := cap }) KL layout =
      .ok (X.withPol C theta cap) := by
  obtain ⟨S, hS, p1, p2, p3⟩ := premises_of_read hR
  have p1' : theta ≤ C := p1
  have p2' : cap ≤ 1024 := p2
  have p3' : C < 2 ^ 32 := p3
  have h' : publicOf (policyFile v) KL layout = .ok X := by
    rw [← publicOfO_older]
    exact h
  have hs : polScan (policyFile { v with C := C, theta := theta, cap := cap }) =
      .ok (X.P.withPol C theta cap) := by
    rw [hS, scan_withPol (publicOf_scan h') hS]
  have hT := T_of_public h'
  exact publicOfO_returns_withPol h hs p1' (by rw [hT]; exact p2') (by omega) p3'
    (size_policyFile hS)

/-- The law with `VerifierAndGoals.InScope` of the second set of public files for hR. lay: that set's layout
file; `InScope` fixes it. layout: the layout argument of `publicOfO`, the same on both sides. -/
theorem publicOfO_returns_inScope {v : FreeLines} {C theta cap : Nat} {lay KL : ByteArray}
    {layout : Option ByteArray} {X : Public}
    (h : publicOfO secondHashFunction (policyFile v) KL layout = .ok X)
    (hZ : VerifierAndGoals.InScope ⟨policyFile { v with C := C, theta := theta, cap := cap }, lay, KL⟩ =
      true) :
    publicOfO secondHashFunction (policyFile { v with C := C, theta := theta, cap := cap }) KL layout =
      .ok (X.withPol C theta cap) := by
  cases hR : VerifierAndGoals.readFiles
      ⟨policyFile { v with C := C, theta := theta, cap := cap }, lay, KL⟩ with
  | error e =>
    unfold VerifierAndGoals.InScope at hZ
    rw [hR] at hZ
    simp at hZ
  | ok pp' => exact publicOfO_returns_read h hR

/-- An instance: from the stored full-size example's files to the same files with the policy
(25856, 512, 1). The return at the first set is a premise. -/
theorem gap_of_full {layout : Option ByteArray} {X : Public}
    (h : publicOfO secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL layout = .ok X) :
    publicOfO secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL layout = .ok (X.withPol 25856 512 1) :=
  publicOfO_returns_inScope h VerifierAndGoals.inScope_gap

end LPFPol

#print axioms LPFPol.size_policyFile
#print axioms LPFPol.publicOfO_returns_read
#print axioms LPFPol.publicOfO_returns_inScope
#print axioms LPFPol.gap_of_full
