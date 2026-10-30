-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/SettingsRead.lean: the integer model's settings, with the acceptance policy, read off a
parameter file and a scale file: the functions `settingsAny` and `settingsAtRef`, what they call,
and their laws, over two imports.

Purpose. A statement about a parameter file and a scale file needs the integer model's settings at
these files: a value of `Inst.Model.ScalesAndPolicy` (Inst/Model/ProgTests.lean): the scales of the 48 layers,
the final normalisation, and the policy. This file holds that reading. It imports
OnBytes/Model/Config.lean, for the strict scan of the parameter file (`polScan`) and the words of a
file (`fileWords`), and Inst/Model/Scales.lean, for the settings' type and `Lawful`; nothing else.
So whoever wants to see what `settingsAtRef` is opens this file and what lies beneath these two.

Definitions.
  `refRecord`, `klFileOf h KL`: the implementation's public numbers, off a scanned header and the
    scale file's bytes; nothing unless the parameter file has at most 48 layers and the scale file
    has exactly 13 L + 3 (L / 2) words. The library's type has 48 layers: BEHIND THE FILE's LAST
    LAYER STAND THE REFERENCE's SHIFTS, EXPONENTS AND FLAGS, with the file's own eps1 and eps2 as in
    every layer; a program of L layers does not read them. How the scale file is laid out: the head
    of Johnson/Flat/ScalesOf.lean.
  `otherLinesOf S`, with its helpers `refTableWords`, `modelRowsOf`, `tableLineNames`;
    `firstOtherLine S`; `otherLinesHeld S`: the test that a scanned parameter file's further model
    lines are the reference's. These are the lines that describe the model beside its sizes and
    scales. Which lines they are, and where each reference value comes from: the head of
    Johnson/Flat/ModelLines.lean.
  `settingsAny policy KL`: the scan; `klFileOf`; `ofKL`; the test `Lawful`. No acceptance policy is
    refused for not being exact match.
  `settingsAtRef policy KL`: `settingsAny`, refused where one of the further model lines is not the
    reference's. The acceptance policy's lines sh = 8, sT = 4 and F = 24 are among them.
Theorems.
  `settingsAny_iff`, `settingsAny_parts`: what a returned value was made from.
  `settingsAny_lawful`, `settingsAtRef_lawful`: a returned value is lawful (`Inst.Model.Lawful`).
  `settingsAny_pol`: its policy is the scanned file's lines C, theta, cap.
  `settingsAtRef_eq`, `settingsAtRef_held`, `settingsAtRef_of`: what is returned is what
    `settingsAny` returns; the scan returned and the test on the further lines held; the way back.
  `otherLinesHeld_all`, `otherLinesHeld_policy`, `settingsAtRef_lines`: where the test on the
    further lines holds, every row's two numbers agree; so profile 4, sh = 8, sT = 4, F = 24.
How the two functions stand to the reading at exact match (`settingsOfFiles`, `scalesAtRef`):
Johnson/Flat/SettingsAtRef.lean.

Limits. Nothing on a protocol, on soundness or on what a proof under a policy means.
Neither function asks that the model's ten sizes are the reference's: beyond the scan they read of
the ten the number of layers alone (`klFileOf`: at most 48, and fitting the scale file's length);
`settingsAtRef` also refuses a file without experts (NE 0), where the scan lays the digit form 0 for
five classes (see the head of Johnson/Flat/ModelLines.lean). At a file with fewer than 48 layers
`klFileOf` fills the layers behind the file's last with the reference's records. `Lawful` asks of
the policy only C < 2 ^ 32, theta ≤ C and cap ≤ 1024: a policy that passes can be one under which no
output is ruled out (some such cases are named at `policyEmpty`, OnBytes/Model/Config.lean).
THE LIMITS ON THE EIGHT DEFINITIONS OF PARTS 1 AND 2 STAND IN TWO OTHER HEADS, AND HOLD HERE:
WHOEVER OPENS THIS FILE ALONE SHOULD OPEN THESE TOO. On `refRecord` and `klFileOf`: the head of
Johnson/Flat/ScalesOf.lean, under `klFileOf` and under Limits: what stands behind the file's last
layer; what a dense layer gets; that the small example's settings are read and are not lawful; that
the numbers are a parameter file's model's only if that file's other model lines are the library's;
that the verifier program reads the scale file this way is not proved. On `otherLinesOf`,
`refTableWords` and the rest: the head of Johnson/Flat/ModelLines.lean, under Limits: that the
library's fixed tables are the tables with these four digests is not shown; that the list of further
model lines is complete is a reading, not a theorem; which lines are left out on purpose; what name
the refusal bears at a file without experts.
Hash functions. No definition of this file calls a hash function: none is named here, and none is
reached from `settingsAtRef` through types, definitions' values and constructors (by a walk of
Lean's environment, which is no part of this library and no theorem). BLAKE2b's text lies beneath
this file all the same, by imports: OnBytes/Model/Config.lean, where `polScan` stands, imports it.
`klFileOf` takes the scale file's words as `(fileWords KL).map (·.toUInt32)`. That is
`Model.Verify.words32 KL` (OnBytes/Model/VerifyStages.lean) by definition: the two texts are one; no
theorem here states it.
Nothing is evaluated at a file here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.Config
import Inst.Model.Scales

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales here: each table is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Flat

/-! ## 1. The scale file's reader -/

section
open Inst.Model

/-- The reference's record of a layer: its eleven scales, the shift sh, and the rotary flag of the
reference pattern. The numbers are those of the stored example's scale file
prover/examples/target_full_f2/KL.bin: the record of each of its 48 layers is this list (compared
outside Lean: no theorem). -/
def refRecord (L : ℕ) : List ℕ :=
  [29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, if L % 4 = 3 then 0 else 1]

/-- The implementation's public numbers, off the scan of the parameter file and the scale file's
bytes. -/
def klFileOf (h : Model.Hdr) (KL : ByteArray) : Option KLFile :=
  let w := (Model.fileWords KL).map (·.toUInt32)
  if h.L ≤ 48 ∧ KL.size % 4 = 0 ∧ w.size = 13 * h.L + 3 * (h.L / 2) then
    some
      { lay := fun L j =>
          if L.val < h.L then (w.getD (13 * L.val + j.val) 0).toNat
          else (refRecord L.val).getD j.val 0
        moe := fun e j =>
          if 2 * e.val + 1 < h.L then (w.getD (13 * h.L + 3 * e.val + j.val) 0).toNat
          else [17, 16, 20].getD j.val 0
        eps1 := h.eps.getD 0 0
        eps2 := h.eps.getD 1 0
        MF := h.MF
        KF := h.KF
        epsF := h.epsF
        C := h.clipC
        theta := h.theta
        cap := h.cap }
  else none

end

/-! ## 2. The test on the further model lines -/

section
open OnBytes.Model

/-- The 32 words of the four public tables' digests in the reference parameter file: the lines
tsilu0 to tsilu7, tsig0 to tsig7, trope0 to trope7, texp0 to texp7. -/
def refTableWords : List Nat :=
  [2048398297, 192427613, 2862900154, 2853881485, 2797826050, 1420723544, 3686369553, 2593882461,
   1965976300, 2359599336, 2246761285, 2426172242, 3869868832, 310049175, 339407438, 2601410768,
   786409086, 1563166184, 1100635208, 2272768750, 1260813977, 3744463197, 3300849996, 4050797957,
   3648852807, 2402568834, 4186852988, 523559909, 1873895626, 3042864545, 1726265496, 165292856]

/-- A list of numbers that the scan has laid out of several lines, entry by entry: the name of the
entry's line, the file's value (0 beyond its end), the reference's. The first row compares the two
lengths; it bears the list's name and is no line of the file. -/
def modelRowsOf (list : String) (file : Array Nat) (ref : List (String × Nat)) :
    List (String × Nat × Nat) :=
  (list ++ " (how many)", file.size, ref.length) ::
    ref.zipIdx.map fun r => (r.1.1, file.getD r.2 0, r.1.2)

/-- The names of the 32 lines of the four public tables' digests, in the file's order. -/
def tableLineNames : List String :=
  ["tsilu", "tsig", "trope", "texp"].flatMap fun t => (List.range 8).map fun i => t ++ toString i

/-- The further model lines of a scanned parameter file: name, the file's value, the reference's. -/
def otherLinesOf (S : PolScan) : List (String × Nat × Nat) :=
  [("prof", S.h.prof, 4), ("ll", S.h.ll, 2), ("cs", S.h.cs, 12), ("theta0", S.h.theta0, 500000)] ++
  modelRowsOf "digit forms" S.h.hf
    [("hq", 2), ("hq", 2), ("hv", 1), ("ho", 1), ("hgD", 1), ("huD", 1), ("hdD", 1), ("hr", 1),
     ("hgD", 1), ("huD", 1), ("hgD", 1), ("huD", 1), ("hdD", 1)] ++
  [("ut", S.h.ut, 1)] ++
  modelRowsOf "widths" S.h.wb
    (["qk", "v", "o", "g", "u", "gs", "us", "gr", "ur", "dn", "dnr", "r"].map
      fun k => ("wb_" ++ k, 13)) ++
  modelRowsOf "widths of the embedding and the last matrix" S.h.wbH
    [("wb_emb", 21), ("wb_head", 13)] ++
  [("S", S.h.Sx, 12), ("rx", S.h.rx, 8), ("kFD", S.h.kFD, 16), ("toksrc", S.h.toksrc, 1),
   ("sh", S.h.digSh, 8), ("sT", S.h.tabS, 4), ("F", S.h.famF, 24),
   ("eg", S.eg.isSome.toNat, 0), ("smax", S.smax.isSome.toNat, 0), ("rcl", S.rcl.toNat, 1),
   ("gcl", S.gcl.toNat, 1), ("xl", S.xl.toNat, 1)] ++
  modelRowsOf "table digests" S.tblPol (tableLineNames.zip refTableWords)

/-- The name of the first further line that is not the reference's. -/
def firstOtherLine (S : PolScan) : Option String :=
  ((otherLinesOf S).find? fun r => r.2.1 != r.2.2).map (·.1)

/-- True if every further line is the reference's. -/
def otherLinesHeld (S : PolScan) : Bool := (firstOtherLine S).isNone

end

open OnBytes.Model Inst.Model

/-! ## 3. The settings, whatever the policy -/

/-- The settings of the integer model, with the acceptance policy, off the parameter file's and the
scale file's bytes. Refused where the program's scan refuses the parameter file; where `klFileOf` or
`ofKL` gives nothing ("scales-not-read": more than 48 layers, a scale file of the wrong length, or
rotary flags that are not the reference pattern); and where the settings are not lawful. No
acceptance policy is refused for not being exact match. -/
def settingsAny (policy KL : ByteArray) : Except String ScalesAndPolicy := do
  let P ← Model.polScan policy
  match (klFileOf P.h KL).bind ofKL with
  | none => throw "scales-not-read"
  | some pp => if Lawful pp then pure pp else throw "scales-not-lawful"

/-- `settingsAny` returns pp exactly if the scan returns, the two readers `klFileOf` and `ofKL` give
pp at the scan's header, and pp is lawful. -/
theorem settingsAny_iff {policy KL : ByteArray} {pp : ScalesAndPolicy} :
    settingsAny policy KL = .ok pp ↔
      ∃ P, polScan policy = .ok P ∧ (klFileOf P.h KL).bind ofKL = some pp ∧ Lawful pp := by
  unfold settingsAny
  cases hP : polScan policy with
  | error e =>
    constructor
    · intro h
      cases h
    · rintro ⟨P, h, -⟩
      cases h
  | ok P =>
    show (match (klFileOf P.h KL).bind ofKL with
      | none => (throw "scales-not-read" : Except String ScalesAndPolicy)
      | some pp => if Lawful pp then pure pp else throw "scales-not-lawful") = .ok pp ↔ _
    cases h3 : (klFileOf P.h KL).bind ofKL with
    | none =>
      constructor
      · intro h
        cases h
      · rintro ⟨P', h, h', -⟩
        cases h
        rw [h3] at h'
        cases h'
    | some q =>
      show (if Lawful q then (pure q : Except String ScalesAndPolicy) else throw "scales-not-lawful") =
        .ok pp ↔ _
      by_cases hl : Lawful q
      · rw [if_pos hl]
        constructor
        · intro h
          cases h
          exact ⟨P, rfl, h3, hl⟩
        · rintro ⟨P', h, h', -⟩
          cases h
          rw [h3] at h'
          cases h'
          rfl
      · rw [if_neg hl]
        constructor
        · intro h
          cases h
        · rintro ⟨P', h, h', hl'⟩
          cases h
          rw [h3] at h'
          cases h'
          exact absurd hl' hl

/-- What a returned value was made from: the scan P of the parameter file, the public numbers f that
`klFileOf` reads at P's header, and `ofKL f`. -/
theorem settingsAny_parts {policy KL : ByteArray} {pp : ScalesAndPolicy} (h : settingsAny policy KL = .ok pp) :
    ∃ P f, Model.polScan policy = .ok P ∧ klFileOf P.h KL = some f ∧ ofKL f = some pp := by
  obtain ⟨P, hP, hb, -⟩ := settingsAny_iff.1 h
  cases hf : klFileOf P.h KL with
  | none =>
    rw [hf] at hb
    cases hb
  | some f =>
    rw [hf] at hb
    exact ⟨P, f, hP, hf, hb⟩

/-- The settings that are returned are lawful. -/
theorem settingsAny_lawful {policy KL : ByteArray} {pp : ScalesAndPolicy}
    (h : settingsAny policy KL = .ok pp) : Lawful pp := by
  obtain ⟨_, -, -, hl⟩ := settingsAny_iff.1 h
  exact hl

/-- The policy of the settings that are returned is the scanned parameter file's lines C, theta,
cap. -/
theorem settingsAny_pol {policy KL : ByteArray} {P : PolScan} {pp : ScalesAndPolicy}
    (hP : polScan policy = .ok P) (h : settingsAny policy KL = .ok pp) :
    pp.pol = ⟨P.h.clipC, P.h.theta, P.h.cap⟩ := by
  obtain ⟨P', f, hP', hf, ho⟩ := settingsAny_parts h
  have e0 : P' = P := Except.ok.inj (hP'.symm.trans hP)
  subst e0
  have e1 : pp.pol = ⟨f.C, f.theta, f.cap⟩ := by
    unfold ofKL at ho
    split at ho
    · cases ho
      rfl
    · cases ho
  have e2 : f.C = P'.h.clipC ∧ f.theta = P'.h.theta ∧ f.cap = P'.h.cap := by
    unfold klFileOf at hf
    dsimp only at hf
    split at hf
    · cases hf
      exact ⟨rfl, rfl, rfl⟩
    · cases hf
  rw [e1, e2.1, e2.2.1, e2.2.2]

/-! ## 4. The settings at a file whose further model lines are the reference's -/

/-- The settings off the two files' bytes, refused where a further model line of the parameter file
(`otherLinesOf`) is not the reference's. The lines C, theta, cap are not among those lines. -/
def settingsAtRef (policy KL : ByteArray) : Except String ScalesAndPolicy := do
  let S ← polScan policy
  match firstOtherLine S with
  | some name => throw ("model-line-not-the-reference's: " ++ name)
  | none => settingsAny policy KL

/-- What is returned is what `settingsAny` returns. -/
theorem settingsAtRef_eq {policy KL : ByteArray} {pp : ScalesAndPolicy}
    (h : settingsAtRef policy KL = .ok pp) : settingsAny policy KL = .ok pp := by
  unfold settingsAtRef at h
  cases hS : polScan policy with
  | error e =>
    rw [hS] at h
    cases h
  | ok S =>
    rw [hS] at h
    have h' : (match firstOtherLine S with
      | some name => throw ("model-line-not-the-reference's: " ++ name)
      | none => settingsAny policy KL) = .ok pp := h
    cases h1 : firstOtherLine S with
    | some name =>
      rw [h1] at h'
      cases h'
    | none =>
      rw [h1] at h'
      exact h'

/-- Where settings are returned, the scan has returned and the test on the further lines held. -/
theorem settingsAtRef_held {policy KL : ByteArray} {pp : ScalesAndPolicy}
    (h : settingsAtRef policy KL = .ok pp) :
    ∃ S, polScan policy = .ok S ∧ otherLinesHeld S = true := by
  unfold settingsAtRef at h
  cases hS : polScan policy with
  | error e =>
    rw [hS] at h
    cases h
  | ok S =>
    rw [hS] at h
    have h' : (match firstOtherLine S with
      | some name => throw ("model-line-not-the-reference's: " ++ name)
      | none => settingsAny policy KL) = .ok pp := h
    refine ⟨S, rfl, ?_⟩
    unfold otherLinesHeld
    cases h1 : firstOtherLine S with
    | some name =>
      rw [h1] at h'
      cases h'
    | none => rfl

/-- The way back: where the scan returns, the test on the further lines holds and `settingsAny`
returns settings, `settingsAtRef` returns them. -/
theorem settingsAtRef_of {policy KL : ByteArray} {S : PolScan} {pp : ScalesAndPolicy}
    (hS : polScan policy = .ok S) (hh : otherLinesHeld S = true)
    (h : settingsAny policy KL = .ok pp) : settingsAtRef policy KL = .ok pp := by
  unfold settingsAtRef
  rw [hS]
  show (match firstOtherLine S with
    | some name => throw ("model-line-not-the-reference's: " ++ name)
    | none => settingsAny policy KL) = .ok pp
  unfold otherLinesHeld at hh
  cases h1 : firstOtherLine S with
  | some name =>
    rw [h1] at hh
    cases hh
  | none => exact h

/-- The settings that are returned are lawful. -/
theorem settingsAtRef_lawful {policy KL : ByteArray} {pp : ScalesAndPolicy}
    (h : settingsAtRef policy KL = .ok pp) : Lawful pp :=
  settingsAny_lawful (settingsAtRef_eq h)

/-- Where the test on the further lines holds, the file's number and the reference's agree in every
row of `otherLinesOf`. -/
theorem otherLinesHeld_all {S : PolScan} (h : otherLinesHeld S = true) :
    ∀ r ∈ otherLinesOf S, r.2.1 = r.2.2 := by
  intro r hr
  unfold otherLinesHeld firstOtherLine at h
  cases hf : (otherLinesOf S).find? fun r => r.2.1 != r.2.2 with
  | some x =>
    rw [hf] at h
    cases h
  | none =>
    have hn := List.find?_eq_none.1 hf r hr
    simpa using hn

/-- Four of the rows: the header's profile is 4 (the scan holds the line prof modulo 16), and the
acceptance policy's lines sh, sT, F are 8, 4, 24. -/
theorem otherLinesHeld_policy {S : PolScan} (h : otherLinesHeld S = true) :
    S.h.prof = 4 ∧ S.h.digSh = 8 ∧ S.h.tabS = 4 ∧ S.h.famF = 24 := by
  have a := otherLinesHeld_all h
  refine ⟨a ("prof", S.h.prof, 4) ?_, a ("sh", S.h.digSh, 8) ?_, a ("sT", S.h.tabS, 4) ?_,
    a ("F", S.h.famF, 24) ?_⟩ <;> simp [otherLinesOf]

/-- Where settings are returned, the scanned file has sh = 8, sT = 4, F = 24, and the settings'
policy is its lines C, theta, cap. -/
theorem settingsAtRef_lines {policy KL : ByteArray} {pp : ScalesAndPolicy}
    (h : settingsAtRef policy KL = .ok pp) :
    ∃ S, polScan policy = .ok S ∧ S.h.digSh = 8 ∧ S.h.tabS = 4 ∧ S.h.famF = 24 ∧
      pp.pol = ⟨S.h.clipC, S.h.theta, S.h.cap⟩ := by
  obtain ⟨S, hS, hh⟩ := settingsAtRef_held h
  obtain ⟨-, h8, h4, h24⟩ := otherLinesHeld_policy hh
  exact ⟨S, hS, h8, h4, h24, settingsAny_pol hS (settingsAtRef_eq h)⟩

end OnBytes.Flat

#print axioms OnBytes.Flat.settingsAny_iff
#print axioms OnBytes.Flat.settingsAny_parts
#print axioms OnBytes.Flat.settingsAny_lawful
#print axioms OnBytes.Flat.settingsAny_pol
#print axioms OnBytes.Flat.settingsAtRef_eq
#print axioms OnBytes.Flat.settingsAtRef_held
#print axioms OnBytes.Flat.settingsAtRef_of
#print axioms OnBytes.Flat.settingsAtRef_lawful
#print axioms OnBytes.Flat.otherLinesHeld_all
#print axioms OnBytes.Flat.otherLinesHeld_policy
#print axioms OnBytes.Flat.settingsAtRef_lines
