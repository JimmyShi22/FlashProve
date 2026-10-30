-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/ScanReturns.lean: if the strict scan of the parameter file (`polScan`,
OnBytes/Model/Config.lean) returns at `VerifierAndGoals.policyFile v`, it returns at the same file with other
numbers C, theta, cap below 2^32.

Why. The laws on the scan of `policyFile v` (Johnson/Goal/Meaning/ScopeScan.lean and
ScopeScanTies.lean) take the scan's return as a premise. Johnson/Goal/Files/FilesReadChecks.lean
shows at two files, by the kernel's evaluation, a test whose first clause is a return of the scan's
twin on lists.

How. The two files have the same lines but for three. In front of the three the two runs are one.
At the three the step returns (Johnson/LPFPol/FreeLine.lean). Behind them the two states differ in
the values read so far alone, of which a step reads only how many they are (`step_sim`, `fold_sim`).
The three numbers that the scan reads by name before its steps stand in fixed lines.

Main names.
* `scan_returns_withPol`: THE LAW. Premises: h, the scan returns at `policyFile v`; hC, ht, hc: C,
  theta, cap are below 2^32. Then it returns at `policyFile { v with C, theta, cap }`.
* `Sim`: two states of the scan agree but for the values read, and have read equally many.
  `step_sim`, `fold_sim`: where a step, or a run of steps, returns from the one state, it returns
  from the other, and the two states that are returned are such states again.
* `polWord_rest`: the reader by name at the bytes behind the frame's lines of `policyFile v`
  searches the lines `linesAt v`. `polWord_rest_fixed`: at a fixed line's name it finds the stored
  number.
* `three_return`: the three steps at the lines C, theta, cap. `fold_returns`: the run of steps over
  all lines behind the frame's. `preLines`: the lines behind the frame's and in front of the line C.
  `restOf`: the bytes of `policyFile v` behind the frame's lines. `fl_form`: a free line in the form
  of Johnson/LPFPol/FreeLine.lean.

Limits. The return at the first file is a premise. What the scan returns at the second file is not
said here: `VerifierAndGoals.Lines.scan_withPol` (Johnson/Goal/Meaning/ScopeScanTies.lean) says it. The five
other free numbers are the same in both files. Nothing on soundness.

For proofs only; no program imports this file.


-/
import Johnson.LPFPol.FreeLine
import Johnson.Goal.Meaning.ScopeScan

set_option autoImplicit false

namespace LPFPol

open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.ConfigReaders
open OnBytes.Params (exc_bind)
open VerifierAndGoals (FreeLines policyFile)
open VerifierAndGoals.Lines

/-! ### a step reads of the values only how many they are -/

/-- Two states of the scan agree but for the values read, and have read equally many. -/
def Sim (s t : PolState) : Prop := er s = er t ∧ s.vals.size = t.vals.size

/-- A test that passes under one name passes under another. -/
theorem refuseIf_name {b : Bool} {n m : String} {u : Unit} (h : refuseIf b n = .ok u) :
    refuseIf b m = .ok () := refuseIf_no (refuseIf_ok h)

/-- **One step.** -/
theorem step_sim {frame : Params.Lines} {prof : Nat} {names : Array String} {s t s' : PolState}
    {line : List UInt8} (hs : Sim s t) (h : polStep frame prof names s line = .ok s') :
    ∃ t', polStep frame prof names t line = .ok t' ∧ Sim s' t' := by
  obtain ⟨he, hz⟩ := hs
  cases hd : names[s.vals.size]? with
  | some due =>
    have hd' : names[t.vals.size]? = some due := by
      rw [← hz]
      exact hd
    have key : ∃ t', polStep frame prof names t line = .ok t' := by
      unfold polStep at h ⊢
      obtain ⟨_, a1, h⟩ := exc_bind h
      obtain ⟨_, a2, h⟩ := exc_bind h
      dsimp only at h
      rw [hd] at h
      dsimp only at h
      obtain ⟨x, hx, h⟩ := exc_bind h
      cases x with
      | none => cases h
      | some y =>
        obtain ⟨name, val⟩ := y
        dsimp only at h
        obtain ⟨_, a3, h⟩ := exc_bind h
        obtain ⟨_, a4, h⟩ := exc_bind h
        obtain ⟨_, a5, h⟩ := exc_bind h
        refine ⟨{ t with tblPrev := false, vals := t.vals.push val }, ?_⟩
        refine (bind_ok a1).trans ?_
        refine (bind_ok a2).trans ?_
        dsimp only
        rw [hd']
        dsimp only
        refine (bind_ok hx).trans ?_
        dsimp only
        refine (bind_ok (refuseIf_name a3)).trans ?_
        refine (bind_ok a4).trans ?_
        refine (bind_ok a5).trans ?_
        dsimp only at h ⊢
        rw [Array.size_push] at h ⊢
        rw [← hz]
        split at h
        · rename_i hc
          rw [if_pos hc]
          obtain ⟨_, a6, h⟩ := exc_bind h
          refine (bind_ok a6).trans ?_
          rfl
        · rename_i hc
          rw [if_neg hc]
          rfl
    obtain ⟨t', ht⟩ := key
    obtain ⟨e1, e2⟩ := polStep_value_rest hd h
    obtain ⟨f1, f2⟩ := polStep_value_rest hd' ht
    exact ⟨t', ht, by rw [e1, f1, he], by rw [e2, f2, hz]⟩
  | none =>
    have hd' : names[t.vals.size]? = none := by
      rw [← hz]
      exact hd
    have hv := polStep_after hd h
    rw [polStep_none line hd] at h
    have a : afterStep prof (er t) line = .ok (er s') := by
      rw [← he, afterStep_er, h]
      rfl
    rw [afterStep_er] at a
    cases ht : afterStep prof t line with
    | error e =>
      rw [ht] at a
      cases a
    | ok t' =>
      rw [ht] at a
      have ht' : polStep frame prof names t line = .ok t' := by
        rw [polStep_none line hd']
        exact ht
      have hv' := polStep_after hd' ht'
      exact ⟨t', ht', (Except.ok.inj a).symm, by rw [hv, hv', hz]⟩

/-- **A run of steps.** -/
theorem fold_sim {frame : Params.Lines} {prof : Nat} {names : Array String} :
    ∀ (lines : List (List UInt8)) {s t s' : PolState}, Sim s t →
      lines.foldlM (polStep frame prof names) s = .ok s' →
      ∃ t', lines.foldlM (polStep frame prof names) t = .ok t' ∧ Sim s' t'
  | [], s, t, s', hs, h => by
    cases h
    exact ⟨t, rfl, hs⟩
  | line :: lines, s, t, s', hs, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨s1, h1, h⟩ := exc_bind h
    obtain ⟨t1, g1, hs1⟩ := step_sim hs h1
    obtain ⟨t', g, hs'⟩ := fold_sim lines hs1 h
    exact ⟨t', (bind_ok g1).trans g, hs'⟩

/-! ### the reader by name at the bytes behind the frame's lines -/

/-- The bytes of `policyFile v` behind the frame's lines, as the frame's reader hands them on. -/
abbrev restOf (v : FreeLines) : ByteArray := ⟨(bytesOf (behindText v)).toArray⟩

theorem restOf_toList (v : FreeLines) : (restOf v).toList = bytesOf (behindText v) := by
  rw [K.Left.toList_data]

/-- These bytes begin with the letter p. -/
theorem rest_begins_p (v : FreeLines) : ∃ tail, bytesOf (behindText v) = 0x70 :: tail := by
  have a : ∃ t0, concatenatedWithLineFeeds linesA1 = 0x70 :: t0 := ⟨(concatenatedWithLineFeeds linesA1).tail, by decide +kernel⟩
  obtain ⟨t0, h0⟩ := a
  unfold behindText
  simp only [bytesOf_append, bytesA1, List.append_assoc, h0, List.cons_append]
  exact ⟨_, rfl⟩

/-- The reader by name at these bytes searches the lines `linesAt v`. -/
theorem polWord_rest (v : FreeLines) (n : String) :
    polWord (restOf v) n = findWord n (linesAt v) := by
  obtain ⟨tail, ht⟩ := rest_begins_p v
  obtain ⟨e, he⟩ := lines_refuses tail
  have hre : Params.readLines (restOf v) = .error e := by
    unfold Params.readLines
    rw [restOf_toList, ht, he]
    rfl
  have hb : begins "version " (restOf v).toList = false := by
    unfold begins
    rw [restOf_toList, ht, bytesOf_data]
    rfl
  unfold polWord
  rw [hre]
  simp only [hb, Bool.false_eq_true, if_false]
  rw [restOf_toList, linesOf_behind]

/-- At a fixed line's name it finds the stored number. -/
theorem polWord_rest_fixed (v : FreeLines) {p : String × Nat} (hp : p ∈ fixedValues) :
    polWord (restOf v) p.1 = some p.2 := by
  rw [polWord_rest, ← polWord_policyFile]
  exact polWord_fixed v hp

/-! ### the lines -/

/-- The lines of `policyFile v` behind the frame's and in front of the line C. -/
def preLines (v : FreeLines) : List (List UInt8) :=
  fed linesA1 ++ (fls (free1 v) ++ (fed linesA2 ++ (fls (free2 v) ++ fed linesA3)))

theorem linesAt_cut (v : FreeLines) :
    linesAt v = preLines v ++ (fls (free3 v) ++ fed linesB) := by
  unfold linesAt preLines
  simp only [List.append_assoc]

theorem preLines_length (v : FreeLines) : (preLines v).length = 90 := by
  have a1 : (fed linesA1).length = 12 := by decide +kernel
  have a2 : (fed linesA2).length = 56 := by decide +kernel
  have a3 : (fed linesA3).length = 14 := by decide +kernel
  unfold preLines
  simp only [List.length_append, a1, a2, a3]
  rfl

/-- A free line as `fls` writes it, in the form of Johnson/LPFPol/FreeLine.lean. -/
theorem fl_form {q due : String} (hq : bytesOf q = bytesOf due ++ [0x20]) (x : Nat) :
    fl q x ++ [0x0A] = bytesOf due ++ 0x20 :: bytesOf (toString x) ++ [0x0A] := by
  unfold fl
  rw [hq]
  simp

/-- **The three steps at the lines C, theta, cap return**, from a state that has read 90 values. -/
theorem three_return {frame : Params.Lines} {s : PolState} (hs : s.vals.size = 90) (w : FreeLines)
    (hC : w.C < 2 ^ 32) (ht : w.theta < 2 ^ 32) (hc : w.cap < 2 ^ 32) :
    ∃ s', (fls (free3 w)).foldlM (polStep frame 4 (valueNames 4).toArray) s = .ok s' := by
  have hsz : (valueNames 4).toArray.size = 97 := by decide +kernel
  have n0 : (valueNames 4).toArray[90]? = some "C" := by decide +kernel
  have n1 : (valueNames 4).toArray[91]? = some "theta" := by decide +kernel
  have n2 : (valueNames 4).toArray[92]? = some "cap" := by decide +kernel
  obtain ⟨s1, g1, z1⟩ := polStep_number (frame := frame) (prof := 4)
    (names := (valueNames 4).toArray) (s := s) (due := "C") (x := w.C) (by rw [hs]; exact n0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hC (by rw [hs, hsz]; decide)
  obtain ⟨s2, g2, z2⟩ := polStep_number (frame := frame) (prof := 4)
    (names := (valueNames 4).toArray) (s := s1) (due := "theta") (x := w.theta)
    (by rw [z1, hs]; exact n1) (by decide +kernel) (by decide +kernel) (by decide +kernel) ht
    (by rw [z1, hs, hsz]; decide)
  obtain ⟨s3, g3, -⟩ := polStep_number (frame := frame) (prof := 4)
    (names := (valueNames 4).toArray) (s := s2) (due := "cap") (x := w.cap)
    (by rw [z2, z1, hs]; exact n2) (by decide +kernel) (by decide +kernel) (by decide +kernel) hc
    (by rw [z2, z1, hs, hsz]; decide)
  refine ⟨s3, ?_⟩
  show [fl "C " w.C ++ [0x0A], fl "theta " w.theta ++ [0x0A], fl "cap " w.cap ++ [0x0A]].foldlM
    (polStep frame 4 (valueNames 4).toArray) s = .ok s3
  rw [fl_form (due := "C") (by decide +kernel), fl_form (due := "theta") (by decide +kernel),
    fl_form (due := "cap") (by decide +kernel), List.foldlM_cons]
  refine (bind_ok g1).trans ?_
  rw [List.foldlM_cons]
  refine (bind_ok g2).trans ?_
  rw [List.foldlM_cons]
  refine (bind_ok g3).trans ?_
  rfl

/-- The run of steps over all lines behind the frame's returns at the second file, and leaves a
state like the first file's. -/
theorem fold_returns {frame : Params.Lines} {v : FreeLines} {s : PolState} {C theta cap : Nat}
    (h : (linesAt v).foldlM (polStep frame 4 (valueNames 4).toArray) {} = .ok s)
    (hC : C < 2 ^ 32) (ht : theta < 2 ^ 32) (hc : cap < 2 ^ 32) :
    ∃ s', (linesAt { v with C := C, theta := theta, cap := cap }).foldlM
      (polStep frame 4 (valueNames 4).toArray) {} = .ok s' ∧ Sim s s' := by
  have hsz : (valueNames 4).toArray.size = 97 := by decide +kernel
  rw [linesAt_cut, List.foldlM_append] at h
  obtain ⟨sp, hp, h⟩ := exc_bind h
  rw [List.foldlM_append] at h
  obtain ⟨sm, hm, h⟩ := exc_bind h
  obtain ⟨p1, p2⟩ := fold_values (preLines v) {} sp rfl
    (by rw [preLines_length, hsz]; decide) hp
  have hp90 : sp.vals.size = 90 := by
    rw [p2, preLines_length]
    rfl
  obtain ⟨sm', hm'⟩ := three_return (frame := frame) hp90
    { v with C := C, theta := theta, cap := cap } hC ht hc
  have l3 : ∀ w : FreeLines, (fls (free3 w)).length = 3 := fun _ => rfl
  obtain ⟨m1, m2⟩ := fold_values (fls (free3 v)) sp sm p1
    (by rw [hp90, l3, hsz]; decide) hm
  obtain ⟨m1', m2'⟩ := fold_values (fls (free3 { v with C := C, theta := theta, cap := cap })) sp
    sm' p1 (by rw [hp90, l3, hsz]; decide) hm'
  obtain ⟨s', hs', sim⟩ := fold_sim (fed linesB) (s := sm) (t := sm')
    ⟨by rw [m1, m1'], by rw [m2, m2', l3, l3]⟩ h
  refine ⟨s', ?_, sim⟩
  rw [linesAt_cut, List.foldlM_append]
  refine (bind_ok (a := sp) hp).trans ?_
  rw [List.foldlM_append]
  exact (bind_ok hm').trans hs'

/-! ### the scan -/

/-- **THE LAW.** Premises: h, the strict scan returns at `policyFile v`; hC, ht, hc: C, theta, cap
are below 2^32. Then it returns at the same file with these three numbers. -/
theorem scan_returns_withPol {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P)
    {C theta cap : Nat} (hC : C < 2 ^ 32) (ht : theta < 2 ^ 32) (hc : cap < 2 ^ 32) :
    ∃ P', polScan (policyFile { v with C := C, theta := theta, cap := cap }) = .ok P' := by
  obtain ⟨fr, hfr, hr⟩ := readLines_policyFile v
  obtain ⟨fr', hfr', hr'⟩ := readLines_policyFile { v with C := C, theta := theta, cap := cap }
  obtain rfl : fr' = fr := congrArg Prod.fst (Except.ok.inj (hfr'.symm.trans hfr))
  have w1 : ∀ w : FreeLines, polWord (restOf w) "prof" = some 20 := fun w =>
    polWord_rest_fixed w (p := ("prof", 20)) (by decide)
  have w2 : ∀ w : FreeLines, polWord (restOf w) "toksrc" = some 1 := fun w =>
    polWord_rest_fixed w (p := ("toksrc", 1)) (by decide)
  have w3 : ∀ w : FreeLines, polWord (restOf w) "lt" = some 10 := fun w =>
    polWord_rest_fixed w (p := ("lt", 10)) (by decide)
  -- the first file's run, step by step
  unfold polScan at h
  rw [hr] at h
  dsimp only at h
  obtain ⟨w, hw, h⟩ := exc_bind h
  cases hw
  dsimp only at h
  rw [w1 v, w2 v, w3 v] at h
  dsimp only at h
  obtain ⟨_, t1, h⟩ := exc_bind h
  obtain ⟨y, hy, h⟩ := exc_bind h
  try dsimp only at h
  obtain ⟨_, t2, h⟩ := exc_bind h
  obtain ⟨s, hs, h⟩ := exc_bind h
  obtain ⟨_, t3, h⟩ := exc_bind h
  obtain ⟨_, t4, h⟩ := exc_bind h
  have hs4 : (linesAt v).foldlM (polStep fr' 4 (valueNames 4).toArray) {} = .ok s := by
    rw [← linesOf_behind, ← restOf_toList]
    exact hs
  obtain ⟨s', hs', sim⟩ := fold_returns hs4 hC ht hc
  -- the second file's
  apply Exists.intro
  unfold polScan
  rw [hr']
  dsimp only
  refine (bind_ok (a := (fr', restOf { v with C := C, theta := theta, cap := cap })) rfl).trans ?_
  dsimp only
  rw [w1 { v with C := C, theta := theta, cap := cap },
    w2 { v with C := C, theta := theta, cap := cap },
    w3 { v with C := C, theta := theta, cap := cap }]
  dsimp only
  refine (bind_ok t1).trans ?_
  refine (bind_ok hy).trans ?_
  try dsimp only
  refine (bind_ok t2).trans ?_
  refine (bind_ok (a := s') ?_).trans ?_
  · rw [restOf_toList, linesOf_behind]
    exact hs'
  refine (bind_ok (a := ()) ?_).trans ?_
  · rw [← sim.2]
    exact t3
  refine (bind_ok (a := ()) ?_).trans ?_
  · have e : s'.tbl = s.tbl := (congrArg PolState.tbl sim.1).symm
    rw [e]
    exact t4
  rfl

end LPFPol

#print axioms LPFPol.fold_returns
#print axioms LPFPol.scan_returns_withPol
