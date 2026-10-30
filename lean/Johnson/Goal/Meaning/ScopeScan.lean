-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ScopeScan.lean: the whole strict scan of `VerifierAndGoals.policyFile v`, in closed form,
for all values v of the eight free numbers.

Why. Johnson/Goal/Meaning/ScopeLines.lean gives the scan's values of the 86 fixed value lines. A
scan holds more: the values of the eleven free lines, what the first 32 lines say, the optional
lines, the 32 words of the tables' digests and the three lists of call lines. The layouts and plans
of all sub-proofs are functions of these, so a public hypothesis on a layout or a plan, at all files
in the goals' scope, starts here. Some theorems also ask, as a hypothesis, what the scan of a
second parameter file is (hs in OnBytes/Tie/PlanAtPolicyDry.lean and Johnson/Flat/DryAtPolicy.lean).

How.
  1, 2. While names are due, a step of the scan adds one value and turns nothing else
     (`polStep_value_rest`, `fold_values`). Behind the line F a step does not read the values
     (`lineAfterF_er`, `afterStep_er`, `fold_after`). So what the scan reads behind the line F is
     what it would read there with no values at all.
  3. That is a closed term: 55 lines, read from the start. Lean's kernel evaluates it (`tail_read`).
  4. `scan_rest`: the frame, the call lines, the optional lines and the table words.
  5. A number's decimal spelling spells the number (`spelled`), so at a free line's name the reader
  by
     name finds the number that was written (`polWord_free`), and so does the scan (`value_free`).
  6. The names are distinct, so the values by name fix the scan's list of values (`values_eq`).

Main theorems, each under "the strict scan returns P on `policyFile v`":
  `scan_closed`: P = `scanAt frameRef v`, a closed form in v. `frameRef` is what the frame's reader
    reads of the first 32 lines. (`scan_eq`: the same with P.frame for `frameRef`.)
  `scan_rest`, `value_free`, `values_eq`; `hdr_free`: the eight free numbers in the scan's record.
Beside them `hdrOf_pol`: the record reads the lines C, theta, cap in three fields alone.

What is not claimed. That the scan returns on `policyFile v`: it refuses a free line's number of
2^32 or more. The verifier program does not import this file.
-/
import Johnson.Goal.Meaning.ScopeLines

set_option autoImplicit false

namespace VerifierAndGoals.Lines

open OnBytes OnBytes.Model OnBytes.Model.Config
open OnBytes.Params (exc_bind exc_either)
open OnBytes.Model.ConfigReaders (refuseIf_ok)

/-! ## 1. One step of the scan, apart from the values -/

/-- What the scan has read so far, without the values of the lines from prof to F. -/
def er (s : PolState) : PolState := { s with vals := #[] }

/-- While a name is due, a step that passes adds one value and turns nothing else, but that the line
before is no line of the tables. -/
theorem polStep_value_rest {frame : Params.Lines} {prof : Nat} {names : Array String}
    {s s' : PolState} {line : List UInt8} {due : String} (hd : names[s.vals.size]? = some due)
    (h : polStep frame prof names s line = .ok s') :
    er s' = { er s with tblPrev := false } ∧ s'.vals.size = s.vals.size + 1 := by
  unfold polStep at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  dsimp only at h
  rw [hd] at h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := exc_bind h
  cases x with
  | none => cases h
  | some y =>
    obtain ⟨name, val⟩ := y
    dsimp only at h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, h⟩ := exc_either h
    cases h
    exact ⟨rfl, by simp⟩

/-- The scan's step on a line behind the line F. It does not read the values. -/
def afterStep (prof : Nat) (s : PolState) (line : List UInt8) : Except String PolState := do
  refuseIf (decide (1023 < line.length)) "policy-line-long"
  refuseIf (line.contains 0) "policy-zero-byte"
  lineAfterF prof s.tblPrev { s with tblPrev := false } line

/-- When no name is due any more, the scan's step is that step. -/
theorem polStep_none {frame : Params.Lines} {prof : Nat} {names : Array String} {s : PolState}
    (line : List UInt8) (hd : names[s.vals.size]? = none) :
    polStep frame prof names s line = afterStep prof s line := by
  unfold polStep afterStep
  dsimp only
  rw [hd]

/-- A function applied behind two steps is applied behind the second. -/
theorem map_bind {α β γ : Type} (f : β → γ) (x : Except String α) (k : α → Except String β) :
    (x >>= k).map f = x >>= fun a => (k a).map f := by
  cases x <;> rfl

theorem bind_congr' {α β : Type} {x : Except String α} {k k' : α → Except String β}
    (h : ∀ a, k a = k' a) : (x >>= k) = (x >>= k') := by
  cases x
  · rfl
  · exact h _

theorem map_pure' {β γ : Type} (f : β → γ) (b : β) :
    (pure b : Except String β).map f = pure (f b) := rfl

theorem map_error' {β γ : Type} (f : β → γ) (e : String) :
    (Except.error e : Except String β).map f = .error e := rfl

theorem ite_map {β γ : Type} (f : β → γ) {c : Prop} [Decidable c] {a b : Except String γ}
    {a' b' : Except String β} (h1 : a = a'.map f) (h2 : b = b'.map f) :
    (if c then a else b) = (if c then a' else b').map f := by
  split <;> assumption

/-- Reading a call line does not read the values. -/
theorem callLine_er (prof : Nat) (s : PolState) (line : List UInt8) :
    callLine prof (er s) line = (callLine prof s line).map er := by
  unfold callLine
  dsimp only [er]
  repeat' first
    | rfl
    | rw [map_bind]
    | (apply bind_congr'; intro _)
    | split

/-- Reading a line behind the line F does not read the values. -/
theorem lineAfterF_er (prof : Nat) (a : Bool) (s : PolState) (line : List UInt8) :
    lineAfterF prof a (er s) line = (lineAfterF prof a s line).map er := by
  unfold lineAfterF
  dsimp only [er, PolState.anyCall]
  repeat' first
    | rfl
    | exact callLine_er prof s line
    | rw [map_bind]
    | (apply bind_congr'; intro _)
    | apply ite_map
    | split

/-- The scan's step behind the line F does not read the values. -/
theorem afterStep_er (prof : Nat) (s : PolState) (line : List UInt8) :
    afterStep prof (er s) line = (afterStep prof s line).map er := by
  unfold afterStep
  rw [map_bind]
  apply bind_congr'
  intro _
  rw [map_bind]
  apply bind_congr'
  intro _
  exact lineAfterF_er prof s.tblPrev { s with tblPrev := false } line

/-! ## 2. Many steps -/

/-- While names are due: each line adds one value, and nothing else has been read. -/
theorem fold_values {frame : Params.Lines} {prof : Nat} {names : Array String} :
    ∀ (lines : List (List UInt8)) (s s' : PolState), er s = {} →
      s.vals.size + lines.length ≤ names.size →
      lines.foldlM (polStep frame prof names) s = .ok s' →
      er s' = {} ∧ s'.vals.size = s.vals.size + lines.length
  | [], s, s', h0, _, h => by
    cases h
    exact ⟨h0, rfl⟩
  | line :: lines, s, s', h0, hn, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := exc_bind h
    rw [List.length_cons] at hn
    have hlt : s.vals.size < names.size := by omega
    obtain ⟨e1, e2⟩ := polStep_value_rest (Array.getElem?_eq_getElem hlt) h1
    have h01 : er s1 = {} := by rw [e1, h0]
    obtain ⟨a, b⟩ := fold_values lines s1 s' h01 (by omega) h
    exact ⟨a, by rw [b, e2, List.length_cons]; omega⟩

/-- When no name is due any more: the steps are those that do not read the values. -/
theorem fold_after {frame : Params.Lines} {prof : Nat} {names : Array String} :
    ∀ (lines : List (List UInt8)) (s s' : PolState), names.size ≤ s.vals.size →
      lines.foldlM (polStep frame prof names) s = .ok s' →
      lines.foldlM (afterStep prof) (er s) = .ok (er s')
  | [], s, s', _, h => by
    cases h
    rfl
  | line :: lines, s, s', hn, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨s1, h1, h⟩ := exc_bind h
    have hd : names[s.vals.size]? = none := Array.getElem?_eq_none hn
    have hv := polStep_after hd h1
    rw [polStep_none line hd] at h1
    rw [afterStep_er, h1]
    exact fold_after lines s1 s' (by rw [hv]; exact hn) h

/-! ## 3. The lines behind the line F -/

deriving instance DecidableEq for PolState

/-- The eight lines call of the stored example: name, kind, segments. -/
def callsRef : List (List String) :=
  [["R16a", "R16", "G", "U"],
   ["R16b", "R16", "N1", "N1H", "N2", "N2H", "O", "D", "V"],
   ["R16c", "R16", "QK", "QKH", "XR", "LR", "LT", "DD"],
   ["R8", "R8", "GH", "UH", "OH", "DH", "VH", "ROW", "LH", "SEL", "L3", "G0"],
   ["FC", "FC", "CN1", "CN2", "CQK", "CV", "CLR"],
   ["FS", "FS", "MR", "CG"],
   ["FL", "FL", "F"],
   ["R16d", "R16", "UT"]]

/-- Its four lines callA. -/
def callsARef : List (List String) :=
  [["KR", "KR", "RM", "RD"], ["KFD", "KFD", "FM", "FD"], ["R16", "R16", "WL", "IX"],
   ["WH", "WH", "WH"]]

/-- Its six lines callH. -/
def callsHRef : List (List String) :=
  [["R16a", "R16", "NF", "NFH", "HD0"],
   ["R16b", "R16", "HD1"],
   ["R8", "R8", "ROW", "HD2"],
   ["FEa", "FE", "HE0"],
   ["FEb", "FE", "HE1"],
   ["FC", "FC", "CNF"]]

/-- The 32 words of its four tables' digests. -/
def tableWordsRef : List Nat :=
  [
   2048398297, 192427613, 2862900154, 2853881485, 2797826050, 1420723544, 3686369553, 2593882461,
   1965976300, 2359599336, 2246761285, 2426172242, 3869868832, 310049175, 339407438, 2601410768,
   786409086, 1563166184, 1100635208, 2272768750, 1260813977, 3744463197, 3300849996, 4050797957,
   3648852807, 2402568834, 4186852988, 523559909, 1873895626, 3042864545, 1726265496, 165292856]

/-- What the scan has read of the stored example's parameter file, apart from the values. -/
def restRef : PolState :=
  { lidb := some 28, nminH := some 27, rcl := true, gcl := true, xl := true,
    tbl := tableWordsRef.toArray, calls := callsRef.toArray, callsA := callsARef.toArray,
    callsH := callsHRef.toArray }

/-- The 55 lines behind the line F, read from the start. Lean's kernel evaluates it. -/
theorem tail_read : (fed (linesB.drop 4)).foldlM (afterStep 4) {} = .ok restRef := by
  have h : (match (fed (linesB.drop 4)).foldlM (afterStep 4) {} with
      | .ok s => decide (s = restRef)
      | .error _ => false) = true := by decide +kernel
  cases hf : (fed (linesB.drop 4)).foldlM (afterStep 4) {} with
  | error e =>
    rw [hf] at h
    cases h
  | ok s =>
    rw [hf] at h
    rw [of_decide_eq_true h]

/-! ## 4. The scan of `policyFile v`, apart from the values -/

/-- What a scan that returns has done, with every field of what it returns. -/
theorem polScan_all {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    ∃ frame rest prof s, Params.readLines pol = .ok (frame, rest) ∧
      prof = (polWord rest "prof").getD 0 % 16 ∧
      (linesOf rest.toList).foldlM (polStep frame prof (valueNames prof).toArray) {} = .ok s ∧
      P.frame = frame ∧ P.polCalls = s.calls.toList ∧ P.polCallsA = s.callsA.toList ∧
      P.polCallsH = s.callsH.toList ∧ P.lidb = s.lidb ∧ P.nminH = s.nminH ∧ P.eg = s.eg ∧
      P.smax = s.smax ∧ P.rcl = s.rcl ∧ P.gcl = s.gcl ∧ P.xl = s.xl ∧ P.tblPol = s.tbl := by
  unfold polScan at h
  cases hr : Params.readLines pol with
  | error e =>
    rw [hr] at h
    cases h
  | ok x =>
    rw [hr] at h
    obtain ⟨frame, rest⟩ := x
    dsimp only at h
    obtain ⟨w, hw, h⟩ := exc_bind h
    cases hw
    dsimp only at h
    obtain ⟨_, _, h⟩ := exc_bind h
    split at h
    · obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨s, hs, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      cases h
      exact ⟨frame, rest, _, s, rfl, rfl, hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl⟩
    · cases h

/-- What the reader of the frame's lines returns on `policyFile v`. -/
theorem readLines_policyFile (v : FreeLines) :
    ∃ fr, Params.lines (concatenatedWithLineFeeds frameLines) = .ok (fr, []) ∧
      Params.readLines (policyFile v) = .ok (fr, ⟨(bytesOf (behindText v)).toArray⟩) := by
  obtain ⟨fr, hfr⟩ := frame_read
  have e : (policyFile v).toList = concatenatedWithLineFeeds frameLines ++ bytesOf (behindText v) := by
    rw [← frame_bytes, policyFile_eq, K.Left.toList_data, K.Left.toList_data,
      ByteArray.data_append, Array.toList_append, ConfigReaders.bytesOf_data]
  refine ⟨fr, hfr, ?_⟩
  unfold Params.readLines
  rw [e, K.Left.keeps_lines _ _ (bytesOf (behindText v)) _ hfr]
  rfl

/-- The 97 value lines of `policyFile v`. -/
def valueLines (v : FreeLines) : List (List UInt8) :=
  fed linesA1 ++ (fls (free1 v) ++ (fed linesA2 ++ (fls (free2 v) ++
    (fed linesA3 ++ (fls (free3 v) ++ fed (linesB.take 4))))))

theorem linesAt_eq (v : FreeLines) : linesAt v = valueLines v ++ fed (linesB.drop 4) := by
  have e : fed linesB = fed (linesB.take 4) ++ fed (linesB.drop 4) := by
    unfold fed
    rw [← List.map_append, List.take_append_drop]
  unfold linesAt valueLines
  rw [e]
  simp only [List.append_assoc]

theorem valueLines_length (v : FreeLines) : (valueLines v).length = 97 := by
  have a1 : (fed linesA1).length = 12 := by decide +kernel
  have a2 : (fed linesA2).length = 56 := by decide +kernel
  have a3 : (fed linesA3).length = 14 := by decide +kernel
  have a4 : (fed (linesB.take 4)).length = 4 := by decide +kernel
  unfold valueLines
  simp only [List.length_append, a1, a2, a3, a4]
  rfl

/-- **Where the strict scan returns on `policyFile v`, whatever the eight free numbers: its frame is
what the frame's reader reads of the first 32 lines, and its call lines, optional lines and table
words are the stored example's.** -/
theorem scan_rest {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P) :
    Params.lines (concatenatedWithLineFeeds frameLines) = .ok (P.frame, []) ∧ P.polCalls = callsRef ∧
      P.polCallsA = callsARef ∧ P.polCallsH = callsHRef ∧ P.lidb = some 28 ∧
      P.nminH = some 27 ∧ P.eg = none ∧ P.smax = none ∧ P.rcl = true ∧ P.gcl = true ∧
      P.xl = true ∧ P.tblPol = tableWordsRef.toArray := by
  obtain ⟨frame, rest, prof, s, hr, hprof, hs, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ :=
    polScan_all h
  obtain ⟨fr, hfr, hr'⟩ := readLines_policyFile v
  rw [hr] at hr'
  cases hr'
  have h4 : prof = 4 := by
    rw [hprof, polWord_behind h hr, polWord_fixed v (p := ("prof", 20)) (by decide)]
    rfl
  subst h4
  rw [K.Left.toList_data] at hs
  have hl : linesOf (bytesOf (behindText v)) = valueLines v ++ fed (linesB.drop 4) := by
    rw [linesOf_behind, linesAt_eq]
  have hs' : (valueLines v ++ fed (linesB.drop 4)).foldlM
      (polStep frame 4 (valueNames 4).toArray) {} = .ok s := by
    rw [← hl]
    exact hs
  rw [List.foldlM_append] at hs'
  obtain ⟨s1, h1, h2⟩ := exc_bind hs'
  have hsz : (valueNames 4).toArray.size = 97 := by decide +kernel
  obtain ⟨a, b⟩ := fold_values (valueLines v) {} s1 rfl
    (by rw [valueLines_length, hsz]; exact Nat.le_refl _) h1
  have h3 := fold_after (fed (linesB.drop 4)) s1 s
    (by rw [b, valueLines_length, hsz]; exact Nat.le_refl _) h2
  rw [a, tail_read] at h3
  have e : er s = restRef := (Except.ok.inj h3).symm
  have f : ∀ {α : Type} (g : PolState → α), (∀ t, g (er t) = g t) → g s = g restRef :=
    fun g hg => by rw [← hg s, e]
  refine ⟨by rw [e0]; exact hfr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, f (·.calls) fun _ => rfl]
    rfl
  · rw [e2, f (·.callsA) fun _ => rfl]
    rfl
  · rw [e3, f (·.callsH) fun _ => rfl]
    rfl
  · rw [e4, f (·.lidb) fun _ => rfl]
    rfl
  · rw [e5, f (·.nminH) fun _ => rfl]
    rfl
  · rw [e6, f (·.eg) fun _ => rfl]
    rfl
  · rw [e7, f (·.smax) fun _ => rfl]
    rfl
  · rw [e8, f (·.rcl) fun _ => rfl]
    rfl
  · rw [e9, f (·.gcl) fun _ => rfl]
    rfl
  · rw [e10, f (·.xl) fun _ => rfl]
    rfl
  · rw [e11, f (·.tbl) fun _ => rfl]
    rfl

/-! ## 5. The free lines' values -/

/-- The bytes of a list of characters. -/
theorem bytesOf_ofList (l : List Char) :
    bytesOf (String.ofList l) = l.flatMap String.utf8EncodeChar := by
  rw [ConfigReaders.bytesOf_data, String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
    List.utf8Encode, List.toList_data_toByteArray]

/-- The one byte of a decimal digit. -/
theorem digit_byte : ∀ d, d < 10 →
    String.utf8EncodeChar (Nat.digitChar d) = [(48 + d).toUInt8] := by decide

/-- The bytes of a number's decimal spelling: those of the number without its last digit, and the
last digit's. -/
theorem bytes_step {x : Nat} (h : 10 ≤ x) :
    bytesOf (toString x) = bytesOf (toString (x / 10)) ++ [(48 + x % 10).toUInt8] := by
  rw [Nat.toString_eq_ofList_toDigits, Nat.toString_eq_ofList_toDigits, bytesOf_ofList,
    bytesOf_ofList, Nat.toDigits_of_base_le (by decide) h, List.flatMap_append,
    List.flatMap_singleton, digit_byte _ (Nat.mod_lt _ (by decide))]

theorem bytes_small {x : Nat} (h : x < 10) : bytesOf (toString x) = [(48 + x).toUInt8] := by
  rw [Nat.toString_eq_ofList_toDigits, bytesOf_ofList, Nat.toDigits_of_lt_base h,
    List.flatMap_singleton, digit_byte _ h]

theorem digit_facts : ∀ d, d < 10 →
    isDigit (48 + d).toUInt8 = true ∧ (48 + d).toUInt8.toNat - 0x30 = d := by decide

/-- **A number's decimal spelling is made of digits, is not empty, and spells the number.** -/
theorem spelled (x : Nat) : (bytesOf (toString x)).all isDigit = true ∧
    bytesOf (toString x) ≠ [] ∧ digitsValue (bytesOf (toString x)) = x := by
  induction x using Nat.strongRecOn with
  | _ x ih =>
    by_cases h : x < 10
    · rw [bytes_small h]
      obtain ⟨a, b⟩ := digit_facts x h
      refine ⟨by rw [List.all_cons, a]; rfl, List.cons_ne_nil _ _, ?_⟩
      show 10 * 0 + ((48 + x).toUInt8.toNat - 0x30) = x
      rw [b]
      omega
    · have h10 : 10 ≤ x := Nat.le_of_not_lt h
      obtain ⟨a, -, c⟩ := ih (x / 10) (by omega)
      obtain ⟨a', b'⟩ := digit_facts (x % 10) (Nat.mod_lt _ (by decide))
      rw [bytes_step h10]
      refine ⟨by rw [List.all_append, a, List.all_cons, a']; rfl, by simp, ?_⟩
      unfold digitsValue at c ⊢
      rw [List.foldl_append, c]
      show 10 * (x / 10) + ((48 + x % 10).toUInt8.toNat - 0x30) = x
      rw [b']
      omega

/-- What the reader by name gives at a free line of its name: the number, if it has at most ten
digits. -/
def hit (x : Nat) : Option Nat := if 10 < (bytesOf (toString x)).length then none else some x

/-- The reader by name at a free line of its name. -/
theorem findWord_hit {n q : String} (hq : bytesOf q = bytesOf n ++ [0x20])
    (hf : (bytesOf q).all (fun c => c != 0x0A) = true) (x : Nat) (rest : List (List UInt8)) :
    findWord n ((fl q x ++ [0x0A]) :: rest) = hit x := by
  obtain ⟨a, b, c⟩ := spelled x
  have e : (fl q x ++ [0x0A]).filter (fun c => c != 0x0A) =
      (bytesOf n ++ [0x20]) ++ bytesOf (toString x) := by
    rw [List.filter_append, List.filter_eq_self.2 fun c hc => by simpa using fl_feed hf x c hc]
    unfold fl
    rw [hq]
    simp
  rw [findWord, e, ConfigReaders.behind_append]
  dsimp only
  rw [if_neg (by simpa using b), a, c]
  unfold hit
  simp

/-- The reader by name in a list of free lines: it passes over those of other names. -/
theorem findWord_fls {n q : String} (hq : bytesOf q = bytesOf n ++ [0x20])
    (hf : (bytesOf q).all (fun c => c != 0x0A) = true) (x : Nat) {pre post : List (String × Nat)}
    (hp : clashAll n (pre.map Prod.fst) = true) (rest : List (List UInt8)) :
    findWord n (fls (pre ++ (q, x) :: post) ++ rest) = hit x := by
  have e : fls (pre ++ (q, x) :: post) ++ rest =
      fls pre ++ ((fl q x ++ [0x0A]) :: (fls post ++ rest)) := by
    simp [fls]
  rw [e, findWord_append_misses (fls_misses hp), findWord_hit hq hf]

/-- True if q is the name n with a space and holds no line feed. -/
def spaced (n q : String) : Bool :=
  bytesOf q == bytesOf n ++ [0x20] && (bytesOf q).all fun c => c != 0x0A

/-- A name of the first free lines. ns: the names, each with its space, of the free lines before
it. -/
theorem hit1 (v : FreeLines) {n q : String} {x : Nat} {pre post : List (String × Nat)}
    {ns : List String} (he : free1 v = pre ++ (q, x) :: post) (hn : pre.map Prod.fst = ns)
    (t : (spaced n q && (fed linesA1).all (misses n) && clashAll n ns) = true) :
    findWord n (linesAt v) = hit x := by
  simp only [spaced, Bool.and_eq_true, beq_iff_eq] at t
  obtain ⟨⟨⟨q1, q2⟩, a1⟩, c⟩ := t
  unfold linesAt
  rw [findWord_append_misses a1, he]
  exact findWord_fls q1 q2 x (by rw [hn]; exact c) _

/-- A name of the second free lines. -/
theorem hit2 (v : FreeLines) {n q : String} {x : Nat} {pre post : List (String × Nat)}
    {ns : List String} (he : free2 v = pre ++ (q, x) :: post) (hn : pre.map Prod.fst = ns)
    (t : (spaced n q && (fed linesA1).all (misses n) && clashAll n names1 &&
      (fed linesA2).all (misses n) && clashAll n ns) = true) :
    findWord n (linesAt v) = hit x := by
  simp only [spaced, Bool.and_eq_true, beq_iff_eq] at t
  obtain ⟨⟨⟨⟨⟨q1, q2⟩, a1⟩, c1⟩, a2⟩, c⟩ := t
  unfold linesAt
  rw [findWord_append_misses a1, findWord_append_misses (fls_misses c1),
    findWord_append_misses a2, he]
  exact findWord_fls q1 q2 x (by rw [hn]; exact c) _

/-- A name of the third free lines. -/
theorem hit3 (v : FreeLines) {n q : String} {x : Nat} {pre post : List (String × Nat)}
    {ns : List String} (he : free3 v = pre ++ (q, x) :: post) (hn : pre.map Prod.fst = ns)
    (t : (spaced n q && (fed linesA1).all (misses n) && clashAll n names1 &&
      (fed linesA2).all (misses n) && clashAll n names2 && (fed linesA3).all (misses n) &&
      clashAll n ns) = true) :
    findWord n (linesAt v) = hit x := by
  simp only [spaced, Bool.and_eq_true, beq_iff_eq] at t
  obtain ⟨⟨⟨⟨⟨⟨⟨q1, q2⟩, a1⟩, c1⟩, a2⟩, c2⟩, a3⟩, c⟩ := t
  unfold linesAt
  rw [findWord_append_misses a1, findWord_append_misses (fls_misses c1),
    findWord_append_misses a2, findWord_append_misses (fls_misses c2),
    findWord_append_misses a3, he]
  exact findWord_fls q1 q2 x (by rw [hn]; exact c) _

/-- The eleven free value lines of `policyFile v`: name and number. -/
def freeValues (v : FreeLines) : List (String × Nat) :=
  [("eps1_lo", v.eps1 % 2 ^ 32), ("eps1_hi", v.eps1 / 2 ^ 32), ("eps2_lo", v.eps2 % 2 ^ 32),
   ("eps2_hi", v.eps2 / 2 ^ 32), ("MF", v.MF), ("KF", v.KF), ("epsF_lo", v.epsF % 2 ^ 32),
   ("epsF_hi", v.epsF / 2 ^ 32), ("C", v.C), ("theta", v.theta), ("cap", v.cap)]

/-- **On `policyFile v` the reader by name finds, at each free line's name, the number that was
written, if it has at most ten digits.** -/
theorem polWord_free (v : FreeLines) {p : String × Nat} (hp : p ∈ freeValues v) :
    polWord (policyFile v) p.1 = hit p.2 := by
  rw [polWord_policyFile]
  simp only [freeValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hit1 v (n := "eps1_lo") (q := "eps1_lo ") (x := v.eps1 % 2 ^ 32) (pre := (free1 v).take 0)
      (post := (free1 v).drop 1) (ns := names1.take 0) rfl rfl (by decide +kernel)
  · exact hit1 v (n := "eps1_hi") (q := "eps1_hi ") (x := v.eps1 / 2 ^ 32) (pre := (free1 v).take 1)
      (post := (free1 v).drop 2) (ns := names1.take 1) rfl rfl (by decide +kernel)
  · exact hit1 v (n := "eps2_lo") (q := "eps2_lo ") (x := v.eps2 % 2 ^ 32) (pre := (free1 v).take 2)
      (post := (free1 v).drop 3) (ns := names1.take 2) rfl rfl (by decide +kernel)
  · exact hit1 v (n := "eps2_hi") (q := "eps2_hi ") (x := v.eps2 / 2 ^ 32) (pre := (free1 v).take 3)
      (post := (free1 v).drop 4) (ns := names1.take 3) rfl rfl (by decide +kernel)
  · exact hit2 v (n := "MF") (q := "MF ") (x := v.MF) (pre := (free2 v).take 0)
      (post := (free2 v).drop 1) (ns := names2.take 0) rfl rfl (by decide +kernel)
  · exact hit2 v (n := "KF") (q := "KF ") (x := v.KF) (pre := (free2 v).take 1)
      (post := (free2 v).drop 2) (ns := names2.take 1) rfl rfl (by decide +kernel)
  · exact hit2 v (n := "epsF_lo") (q := "epsF_lo ") (x := v.epsF % 2 ^ 32) (pre := (free2 v).take 2)
      (post := (free2 v).drop 3) (ns := names2.take 2) rfl rfl (by decide +kernel)
  · exact hit2 v (n := "epsF_hi") (q := "epsF_hi ") (x := v.epsF / 2 ^ 32) (pre := (free2 v).take 3)
      (post := (free2 v).drop 4) (ns := names2.take 3) rfl rfl (by decide +kernel)
  · exact hit3 v (n := "C") (q := "C ") (x := v.C) (pre := (free3 v).take 0)
      (post := (free3 v).drop 1) (ns := names3.take 0) rfl rfl (by decide +kernel)
  · exact hit3 v (n := "theta") (q := "theta ") (x := v.theta) (pre := (free3 v).take 1)
      (post := (free3 v).drop 2) (ns := names3.take 1) rfl rfl (by decide +kernel)
  · exact hit3 v (n := "cap") (q := "cap ") (x := v.cap) (pre := (free3 v).take 2)
      (post := (free3 v).drop 3) (ns := names3.take 2) rfl rfl (by decide +kernel)

/-- **Where the strict scan returns on `policyFile v`, its value of every free line is the number
that was written.** -/
theorem value_free {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P)
    {p : String × Nat} (hp : p ∈ freeValues v) : P.value p.1 = p.2 := by
  have e4 : P.h.prof = 4 := by
    have a := value_fixed h (p := ("prof", 20)) (by decide)
    have b := polScan_prof h
    have a' : P.value "prof" = 20 := a
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
  · exact (Option.some.inj a).symm

/-! ## 6. The whole scan in closed form -/

/-- In a list of pairs with distinct first members, the search for a member's first finds its
second. -/
theorem lookup_of_mem : ∀ {l : List (String × Nat)}, (l.map Prod.fst).Nodup → ∀ p ∈ l,
    l.lookup p.1 = some p.2
  | [], _, _, hp => by cases hp
  | q :: l, hn, p, hp => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hp with rfl | hp'
    · simp [List.lookup]
    · have hne : p.1 ≠ q.1 := fun e => hn.1 (e ▸ List.mem_map_of_mem hp')
      rw [List.lookup_cons, show (p.1 == q.1) = false from by simpa using hne]
      exact lookup_of_mem hn.2 p hp'

/-- Two lists of pairs with the same distinct first members are equal if the search in the one finds
the other's second members. -/
theorem pairs_ext {l l' : List (String × Nat)} (hf : l.map Prod.fst = l'.map Prod.fst)
    (hn : (l.map Prod.fst).Nodup) (h : ∀ p ∈ l', (l.lookup p.1).getD 0 = p.2) : l = l' := by
  have hlen : l.length = l'.length := by
    have := congrArg List.length hf
    simpa using this
  apply List.ext_getElem hlen
  intro i h1 h2
  have k : l[i].1 = l'[i].1 := by
    have a : (l.map Prod.fst)[i]'(by simpa using h1) =
        (l'.map Prod.fst)[i]'(by simpa using h2) := by
      simp only [hf]
    simpa using a
  have a := lookup_of_mem hn l[i] (List.getElem_mem h1)
  have b := h l'[i] (List.getElem_mem h2)
  rw [← k, a] at b
  exact Prod.ext k b

/-- The 97 value lines of `policyFile v`, name and number, in the file's order. -/
def valuesAt (v : FreeLines) : List (String × Nat) :=
  valuesA1 ++ (freeValues v).take 4 ++ valuesA2 ++ ((freeValues v).drop 4).take 4 ++ valuesA3 ++
    (freeValues v).drop 8 ++ valuesB

theorem valuesAt_names (v : FreeLines) : (valuesAt v).map Prod.fst = valueNames 4 := rfl

theorem mem_valuesAt {v : FreeLines} {p : String × Nat} (hp : p ∈ valuesAt v) :
    p ∈ fixedValues ∨ p ∈ freeValues v := by
  unfold valuesAt at hp
  unfold fixedValues
  simp only [List.mem_append] at hp ⊢
  rcases hp with (((((h | h) | h) | h) | h) | h) | h
  · exact .inl (.inl (.inl (.inl h)))
  · exact .inr (List.mem_of_mem_take h)
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inr (List.mem_of_mem_drop (List.mem_of_mem_take h))
  · exact .inl (.inl (.inr h))
  · exact .inr (List.mem_of_mem_drop h)
  · exact .inl (.inr h)

/-- **The scan's list of values.** -/
theorem values_eq {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P) :
    P.values = valuesAt v := by
  have e4 : P.h.prof = 4 := by
    have a : P.value "prof" = 20 := value_fixed h (p := ("prof", 20)) (by decide)
    have b := polScan_prof h
    omega
  have hf : P.values.map Prod.fst = (valuesAt v).map Prod.fst := by
    rw [polScan_names h, e4, valuesAt_names]
  refine pairs_ext hf (by rw [hf, valuesAt_names]; exact ConfigReaders.valueNames_nodup 4) ?_
  intro p hp
  rcases mem_valuesAt hp with hp | hp
  · exact value_fixed h hp
  · exact value_free h hp

/-- The scan of `policyFile v`, in closed form. fr: what the first 32 lines say. -/
def scanAt (fr : Params.Lines) (v : FreeLines) : PolScan :=
  { frame := fr, values := valuesAt v, h := hdrOf fun n => ((valuesAt v).lookup n).getD 0,
    polCalls := callsRef, polCallsA := callsARef, polCallsH := callsHRef, lidb := some 28,
    nminH := some 27, eg := none, smax := none, rcl := true, gcl := true, xl := true,
    tblPol := tableWordsRef.toArray }

/-- **Where the strict scan returns on `policyFile v`, it returns `scanAt`, whatever the eight free
numbers.** -/
theorem scan_eq {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P) :
    P = scanAt P.frame v := by
  obtain ⟨-, c1, c2, c3, l1, l2, l3, l4, b1, b2, b3, tb⟩ := scan_rest h
  have hv := values_eq h
  have hh : P.h = hdrOf fun n => ((valuesAt v).lookup n).getD 0 := by
    rw [ConfigReaders.polScan_h h, ← hv]
    rfl
  cases P
  simp only at c1 c2 c3 l1 l2 l3 l4 b1 b2 b3 tb hv hh
  subst c1 c2 c3 l1 l2 l3 l4 b1 b2 b3 tb hv hh
  rfl

/-- What the first 32 lines of the stored example's parameter file say: what the frame's reader
reads of them. -/
def frameRef : Params.Lines :=
  match Params.lines (concatenatedWithLineFeeds frameLines) with
  | .ok x => x.1
  | .error _ => default

/-- The scan's frame is that, at all v. -/
theorem frame_eq {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P) :
    P.frame = frameRef := by
  unfold frameRef
  rw [(scan_rest h).1]

/-- **The whole scan, with nothing of P on the right.** -/
theorem scan_closed {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P) :
    P = scanAt frameRef v := by
  rw [← frame_eq h]
  exact scan_eq h

/-- The eight free numbers in the scan's record. -/
theorem hdr_free {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P) :
    P.h.eps = #[v.eps1, v.eps2] ∧ P.h.MF = v.MF ∧ P.h.KF = v.KF ∧ P.h.epsF = v.epsF ∧
      P.h.clipC = v.C ∧ P.h.theta = v.theta ∧ P.h.cap = v.cap := by
  have V : ∀ (n : String) (k : Nat), (n, k) ∈ freeValues v → P.value n = k :=
    fun n k hp => value_free h hp
  have w : ∀ x : Nat, x % 2 ^ 32 + 2 ^ 32 * (x / 2 ^ 32) = x := fun x => Nat.mod_add_div x _
  have s1 : "eps1" ++ "_lo" = "eps1_lo" := by decide +kernel
  have s2 : "eps1" ++ "_hi" = "eps1_hi" := by decide +kernel
  have s3 : "eps2" ++ "_lo" = "eps2_lo" := by decide +kernel
  have s4 : "eps2" ++ "_hi" = "eps2_hi" := by decide +kernel
  have s5 : "epsF" ++ "_lo" = "epsF_lo" := by decide +kernel
  have s6 : "epsF" ++ "_hi" = "epsF_hi" := by decide +kernel
  rw [ConfigReaders.polScan_h h]
  simp only [hdrOf, s1, s2, s3, s4, s5, s6]
  rw [V "eps1_lo" (v.eps1 % 2 ^ 32) (by simp [freeValues]),
    V "eps1_hi" (v.eps1 / 2 ^ 32) (by simp [freeValues]),
    V "eps2_lo" (v.eps2 % 2 ^ 32) (by simp [freeValues]),
    V "eps2_hi" (v.eps2 / 2 ^ 32) (by simp [freeValues]), V "MF" v.MF (by simp [freeValues]),
    V "KF" v.KF (by simp [freeValues]), V "epsF_lo" (v.epsF % 2 ^ 32) (by simp [freeValues]),
    V "epsF_hi" (v.epsF / 2 ^ 32) (by simp [freeValues]), V "C" v.C (by simp [freeValues]),
    V "theta" v.theta (by simp [freeValues]), V "cap" v.cap (by simp [freeValues]), w, w, w]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The record of the value lines reads the lines C, theta and cap in three fields alone: two
readings by name that agree at all other names give records that agree in all other fields. -/
theorem hdrOf_pol {g g' : String → Nat}
    (h : ∀ n, n ≠ "C" → n ≠ "theta" → n ≠ "cap" → g' n = g n) :
    hdrOf g' = { hdrOf g with clipC := g' "C", theta := g' "theta", cap := g' "cap" } := by
  have k : ∀ n, (n != "C" && n != "theta" && n != "cap") = true → g' n = g n := fun n hn => by
    simp only [Bool.and_eq_true, bne_iff_ne] at hn
    exact h n hn.1.1 hn.1.2 hn.2
  have w : (["qk", "v", "o", "g", "u", "gs", "us", "gr", "ur", "dn", "dnr", "r"].map
      fun x => g' ("wb_" ++ x)) =
      ["qk", "v", "o", "g", "u", "gs", "us", "gr", "ur", "dn", "dnr", "r"].map
        fun x => g ("wb_" ++ x) := by
    simp only [List.map_cons, List.map_nil]
    rw [k ("wb_" ++ "qk") (by decide), k ("wb_" ++ "v") (by decide), k ("wb_" ++ "o") (by decide),
      k ("wb_" ++ "g") (by decide), k ("wb_" ++ "u") (by decide), k ("wb_" ++ "gs") (by decide),
      k ("wb_" ++ "us") (by decide), k ("wb_" ++ "gr") (by decide), k ("wb_" ++ "ur") (by decide),
      k ("wb_" ++ "dn") (by decide), k ("wb_" ++ "dnr") (by decide), k ("wb_" ++ "r") (by decide)]
  have i8 : ((List.range 8).map fun c => g' ("iota_" ++ toString c)) =
      (List.range 8).map fun c => g ("iota_" ++ toString c) := by
    apply List.map_congr_left
    intro c hc
    have : ∀ c, c < 8 → (("iota_" ++ toString c) != "C" && ("iota_" ++ toString c) != "theta" &&
        ("iota_" ++ toString c) != "cap") = true := by decide
    exact k _ (this c (List.mem_range.1 hc))
  have i6 : ((List.range 6).map fun c => g' ("iotaH_" ++ toString c)) =
      (List.range 6).map fun c => g ("iotaH_" ++ toString c) := by
    apply List.map_congr_left
    intro c hc
    have : ∀ c, c < 6 → (("iotaH_" ++ toString c) != "C" && ("iotaH_" ++ toString c) != "theta" &&
        ("iotaH_" ++ toString c) != "cap") = true := by decide
    exact k _ (this c (List.mem_range.1 hc))
  simp only [hdrOf, w, i8, i6]
  rw [k "prof" (by decide), k "lt" (by decide), k "L" (by decide), k "ll" (by decide),
    k "d" (by decide), k "H" (by decide), k "G" (by decide), k "dh" (by decide), k "f" (by decide),
    k "fe" (by decide), k "NE" (by decide), k "V" (by decide), k "cs" (by decide),
    k "hq" (by decide), k "hv" (by decide), k "ho" (by decide), k "hgD" (by decide),
    k "huD" (by decide), k "hdD" (by decide), k "hr" (by decide), k "ut" (by decide),
    k "la" (by decide), k "nmin" (by decide), k "D" (by decide), k "tau" (by decide),
    k "lmaf" (by decide), k "NAf" (by decide), k "lmad" (by decide), k "NAd" (by decide),
    k "lmar" (by decide), k "lmb" (by decide), k "lmq" (by decide), k "lmx" (by decide),
    k "lB" (by decide), k "S" (by decide), k "rx" (by decide), k "kFM" (by decide),
    k "kFD" (by decide), k "lmS" (by decide), k "NAs" (by decide), k "lmh" (by decide),
    k "lmo" (by decide), k "lmbA" (by decide), k "iotaA_0" (by decide), k "MF" (by decide),
    k "KF" (by decide), k "toksrc" (by decide), k "lmhf" (by decide), k "NHf" (by decide),
    k "lmhd" (by decide), k "lmhr" (by decide), k "lmbH" (by decide), k "wb_emb" (by decide),
    k "wb_head" (by decide), k "s" (by decide), k "sh" (by decide), k "sT" (by decide),
    k "F" (by decide), k ("eps1" ++ "_lo") (by decide), k ("eps1" ++ "_hi") (by decide),
    k ("eps2" ++ "_lo") (by decide), k ("eps2" ++ "_hi") (by decide),
    k ("theta0" ++ "_lo") (by decide), k ("theta0" ++ "_hi") (by decide),
    k ("seed" ++ "_lo") (by decide), k ("seed" ++ "_hi") (by decide),
    k ("epsF" ++ "_lo") (by decide), k ("epsF" ++ "_hi") (by decide)]

end VerifierAndGoals.Lines

#print axioms VerifierAndGoals.Lines.scan_rest
#print axioms VerifierAndGoals.Lines.spelled
#print axioms VerifierAndGoals.Lines.value_free
#print axioms VerifierAndGoals.Lines.values_eq
#print axioms VerifierAndGoals.Lines.scan_eq
#print axioms VerifierAndGoals.Lines.scan_closed
#print axioms VerifierAndGoals.Lines.hdr_free
