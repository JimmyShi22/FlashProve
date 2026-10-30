-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Ladder/FilesReadLaws.lean: the reader of the public files (`readFiles`, Ladder.lean) and the test of
scope (`InScope`) brought to tests that Lean's kernel can evaluate at small cost. Definitions,
statements and proofs, for all files: nothing is evaluated here. The tests at the two named sets of
files are in Johnson/Goal/Files/FilesReadChecks.lean, the theorem `VerifierAndGoals.filesRead` in
Johnson/Goal/Files/FilesReadProof.lean.

Why. `FilesRead` (Ladder.lean) says that the two named sets of files are in scope and are read as
expected; without it `G3'pol` asks nothing. Ladder/Guards.lean checks it by evaluation,
which is no proof. A plain `decide` at the reader did not go through in our trials: it took tens of
GiB and failed. By these trials the cost lies in the reader's walks over arrays of bytes and of
words, recursions that the kernel unfolds at great cost (`ByteArray.toList`, `Array.range`,
`Array.map`); in its reading the scan's header anew at every word of the scale file; and in reaching
each byte of the scale file by a walk from the file's start. Here these are taken out by lemmas;
what is left runs on lists and numbers.

Main names (namespace `VerifierAndGoals.Read`).
  `toList_eq`: the bytes of an array of bytes as a list, without the walk.
  `polWordL`, `polScanL`, **`polScan_eq`**: the strict scan of the parameter file
    (`polScan`, OnBytes/Model/Config.lean) is the same text on the list of the file's bytes.
  `words_getD`, `words_size`, `klFileN`, `linesOfHdr`, **`klFileOf_eq`**: the scale file's reader
    (`klFileOf`, Johnson/Flat/SettingsRead.lean) reads each word at once, and reads of the scan's
    header nine numbers alone: the number of layers and the eight free numbers.
  `lawful_of_ref`: a table with the reference's words and final normalisation and a policy in range
    is lawful (`Cm.lawful_sRef`, Cm/Rel2Guards.lean). So `Lawful` is not decided by evaluation.
  `tableOf`, `wordsAt`, `w_of_table`: the table off the scale file and the free numbers; a layer's
    words off the scale file and two of the free numbers alone.
  `checkPol`: the first half of the test, on the parameter file's bytes. `CheckKL` (`restOK` and
    `rowsOK`): the second half, on the scale file and the free numbers.
  **`read_of_check`**, **`scope_of_check`**: the two halves give that the files are in scope and
    are read, with the policy of the free numbers.
  `bytes4`, `flat_getD`, `byteAt_wordsFile`, **`klWord_wordsFile`**: a word of a file that is
    written as a list of words (`wordsFile`, OnBytes/Tie/Pv/Plan/PlanKits.lean) is the list's entry
    modulo 2^32.
  `wordL`, `wordsL`, `rowsL`, **`rowsOK_wordsFile`**: so at such a file `rowsOK` is a test on the
  list.
  `gapLines`: the free numbers of the second named set of files.

Limits. The second half asks that the scale file's table IS the reference table: it says yes at no
other table. So `scope_of_check` is of no use at files in scope with another table: another scale
file's, or other values of the five free numbers that enter the table. At the reference table it
serves at every policy in `Lawful`'s range with 2^8 ≤ theta. Nothing is said of the layout file but
that it is the stored one. Nothing on a verifier.

-/
import Ladder
import Ladder.Guards
import OnBytes.Model.ConfigReaders
import Cm.Rel2Guards

set_option autoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifierAndGoals.Read
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Flat Inst.Model OnBytes.Tie.Pv.Plan

/-- The bytes of an array of bytes, as a list: without the walk. -/
theorem toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  unfold ByteArray.toList
  rw [ConfigReaders.toList_loop b _ 0 [] rfl]
  rfl

/-- The bytes of the array of bytes that is made of a list are the list. -/
theorem toList_mk (l : List UInt8) : (ByteArray.mk l.toArray).toList = l := by
  rw [toList_eq]

/-- `polWord` on a list of bytes. -/
def polWordL (whole : List UInt8) (name : String) : Option Nat :=
  match Params.lines whole with
  | .ok x => findWord name (linesOf x.2)
  | .error _ => if begins "version " whole then none else findWord name (linesOf whole)

/-- `polWord` is `polWordL` on the list of the file's bytes. -/
theorem polWord_eq (b : ByteArray) (name : String) :
    polWord b name = polWordL b.data.toList name := by
  unfold polWord polWordL Params.readLines
  rw [toList_eq]
  cases h : Params.lines b.data.toList with
  | error e => rfl
  | ok x =>
    show findWord name (linesOf (ByteArray.mk x.2.toArray).toList) = _
    rw [toList_mk]

/-- `polScan` on a list of bytes. -/
def polScanL (pol : List UInt8) : Except String PolScan := do
  let (frame, rest) ←
    match Params.lines pol with
    | .ok x => pure x
    | .error fault => .error (frameRefusal fault)
  let pp := polWordL rest "prof"
  let pts := polWordL rest "toksrc"
  refuseIf ((pp.map (· / 16)) != some 1 || pts != some 1) "statement-required"
  let plt ←
    match polWordL rest "lt" with
    | some x => pure x
    | none => .error "policy-name-lt"
  refuseIf (decide (plt < 4) || decide (16 < plt)) "shape-words"
  let prof := pp.getD 0 % 16
  let names := valueNames prof
  let s ← (linesOf rest).foldlM (polStep frame prof names.toArray) {}
  refuseIf (s.vals.size != names.length) "policy-length"
  refuseIf (s.tbl.size != 0 && s.tbl.size != 32) "policy-tables"
  let values := names.zip s.vals.toList
  pure { frame := frame, values := values, h := hdrOf fun n => (values.lookup n).getD 0,
         polCalls := s.calls.toList, polCallsA := s.callsA.toList, polCallsH := s.callsH.toList,
         lidb := s.lidb, nminH := s.nminH, eg := s.eg, smax := s.smax, rcl := s.rcl, gcl := s.gcl,
         xl := s.xl, tblPol := s.tbl }

/-- **The strict scan is `polScanL` on the list of the file's bytes**, at every file. -/
theorem polScan_eq (b : ByteArray) : polScan b = polScanL b.data.toList := by
  unfold polScan polScanL Params.readLines
  rw [toList_eq]
  cases h : Params.lines b.data.toList with
  | error e => rfl
  | ok x =>
    obtain ⟨frame, rest⟩ := x
    simp only [Except.map, bind, Except.bind, pure, Except.pure, polWord_eq, toList_mk]
    rfl


/-- The eight free numbers, compared one by one. -/
def sameLines (a b : FreeLines) : Bool :=
  a.eps1 == b.eps1 && a.eps2 == b.eps2 && a.epsF == b.epsF && a.MF == b.MF && a.KF == b.KF &&
    a.C == b.C && a.theta == b.theta && a.cap == b.cap

/-- A yes of `sameLines` gives equality. -/
theorem sameLines_eq {a b : FreeLines} (h : sameLines a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := b
  simp only [sameLines, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8
  rfl

/-- A word of the scale file as `klFileOf` reads it: without the two walks over arrays. Beyond the
file's end both sides are 0. -/
theorem words_getD (KL : ByteArray) (i : Nat) :
    ((Model.fileWords KL).map (·.toUInt32)).getD i 0 = (Model.klWord KL i).toUInt32 := by
  unfold Model.fileWords
  by_cases h : i < KL.size / 4
  · simp [Array.getD, h]
  · have h0 : Model.klWord KL i = 0 := by
      unfold Model.klWord
      rw [if_neg (by omega)]
    simp [Array.getD, h, h0]

/-- The number of the scale file's words, without the two walks. -/
theorem words_size (KL : ByteArray) :
    ((Model.fileWords KL).map (·.toUInt32)).size = KL.size / 4 := by
  simp [Model.fileWords]

/-- `klFileOf`, each word read at once, from the nine numbers of the header that it reads: the
number of layers n and the eight free numbers v. -/
def klFileN (n : Nat) (v : FreeLines) (KL : ByteArray) : Option KLFile :=
  if n ≤ 48 ∧ KL.size % 4 = 0 ∧ KL.size / 4 = 13 * n + 3 * (n / 2) then
    some
      { lay := fun L j =>
          if L.val < n then ((Model.klWord KL (13 * L.val + j.val)).toUInt32).toNat
          else (refRecord L.val).getD j.val 0
        moe := fun e j =>
          if 2 * e.val + 1 < n then ((Model.klWord KL (13 * n + 3 * e.val + j.val)).toUInt32).toNat
          else [17, 16, 20].getD j.val 0
        eps1 := v.eps1
        eps2 := v.eps2
        MF := v.MF
        KF := v.KF
        epsF := v.epsF
        C := v.C
        theta := v.theta
        cap := v.cap }
  else none

/-- The eight free numbers as the header has them. -/
def linesOfHdr (h : Model.Hdr) : FreeLines :=
  ⟨h.eps.getD 0 0, h.eps.getD 1 0, h.epsF, h.MF, h.KF, h.clipC, h.theta, h.cap⟩

/-- **The scale file's reader is `klFileN`** at the header's number of layers and its eight free
numbers, at every header and file. -/
theorem klFileOf_eq (h : Model.Hdr) (KL : ByteArray) :
    klFileOf h KL = klFileN h.L (linesOfHdr h) KL := by
  unfold klFileOf klFileN linesOfHdr
  simp only [words_getD, words_size]

/-- A table whose words and final normalisation are the reference's, with a policy in the range that
`Lawful` asks, is lawful: the reference table is (`Cm.lawful_sRef`). -/
theorem lawful_of_ref {pp : ScalesAndPolicy} (hw : ∀ L, pp.w L = Cm.sRef.w L) (hn : pp.nf = Cm.sRef.nf)
    (hp : pp.pol.C < 2 ^ 32 ∧ pp.pol.theta ≤ pp.pol.C ∧ pp.pol.cap ≤ 1024) : Lawful pp := by
  obtain ⟨w, nf, p⟩ := pp
  have hw' : w = Cm.sRef.w := funext hw
  subst hw' hn
  have hs := Cm.lawful_sRef.toPP
  exact ⟨⟨hs.ff, hs.sh, hs.one, hs.nf, hp⟩, hs.km⟩

/-- The first half of the test, on the parameter file's bytes: the scan says yes; every further line
is the reference's; the header has 48 layers and the free numbers v. -/
def checkPol (pol : List UInt8) (v : FreeLines) : Bool :=
  match polScanL pol with
  | .error _ => false
  | .ok S => (firstOtherLine S).isNone && S.h.L == 48 && sameLines (linesOfHdr S.h) v

/-- The table off the scale file and the free numbers v alone, at 48 layers. -/
def tableOf (KL : ByteArray) (v : FreeLines) : Option ScalesAndPolicy := (klFileN 48 v KL).bind ofKL

/-- Word j of layer L's record in the scale file, at 48 layers. -/
def layAt (KL : ByteArray) (L : Fin 48) (j : Nat) : Nat :=
  ((Model.klWord KL (13 * L.val + j)).toUInt32).toNat

/-- Word j of the record e of a layer with experts, at 48 layers. -/
def moeAt (KL : ByteArray) (e j : Nat) : Nat :=
  ((Model.klWord KL (13 * 48 + 3 * e + j)).toUInt32).toNat

/-- The words of layer L as the reader lays them (`KLFile.words`, Inst/Model/ProgTests.lean), off
the scale file and the two constants e1, e2 alone. -/
def wordsAt (KL : ByteArray) (e1 e2 : Nat) (L : Fin 48) : Words where
  kq := layAt KL L 0
  kk := layAt KL L 1
  kv := layAt KL L 2
  ko := layAt KL L 3
  kg := layAt KL L 4
  ku := layAt KL L 5
  kd := layAt KL L 6
  kr := if L.val % 2 = 1 then moeAt KL (L.val / 2) 0 else 17
  kg' := if L.val % 2 = 1 then moeAt KL (L.val / 2) 1 else 16
  ku' := if L.val % 2 = 1 then moeAt KL (L.val / 2) 2 else 20
  n1 := ⟨layAt KL L 7, layAt KL L 8, e1⟩
  n2 := ⟨layAt KL L 9, layAt KL L 10, e2⟩
  sh := layAt KL L 11

/-- The table's words are `wordsAt`. -/
theorem w_of_table {KL : ByteArray} {v : FreeLines} {pp : ScalesAndPolicy} (h : tableOf KL v = some pp)
    (L : Fin 48) : pp.w L = wordsAt KL v.eps1 v.eps2 L := by
  unfold tableOf klFileN at h
  split at h
  · simp only [Option.bind_some, ofKL] at h
    split at h
    · cases h
      have hL : L.val < 48 := L.isLt
      have hm : L.val % 2 = 1 → 2 * (L.val / 2) + 1 < 48 := fun _ => by omega
      unfold wordsAt layAt moeAt
      by_cases ho : L.val % 2 = 1
      · simp only [KLFile.words, if_pos hL, if_pos ho, if_pos (hm ho)]
        rfl
      · simp only [KLFile.words, if_pos hL, if_neg ho]
        rfl
    · cases h
  · cases h

/-- At the layers of a list the words off the scale file are the reference's. -/
def rowsOK (ls : List (Fin 48)) (KL : ByteArray) (e1 e2 : Nat) : Bool :=
  ls.all fun L => decide (wordsAt KL e1 e2 L = Cm.sRef.w L)

/-- The rest: the final normalisation is the reference's; the policy is in `Lawful`'s range; the
free numbers that the reader lays are v; 2^8 ≤ theta. -/
def restOK (KL : ByteArray) (v : FreeLines) : Bool :=
  match tableOf KL v with
  | none => false
  | some pp =>
    decide (pp.nf = Cm.sRef.nf) &&
      decide (pp.pol.C < 2 ^ 32 ∧ pp.pol.theta ≤ pp.pol.C ∧ pp.pol.cap ≤ 1024) &&
      sameLines (freeLinesOf pp) v && decide (2 ^ 8 ≤ pp.pol.theta)

/-- The second half, as a proposition. -/
def CheckKL (KL : ByteArray) (v : FreeLines) : Prop :=
  restOK KL v = true ∧ rowsOK (List.finRange 48) KL v.eps1 v.eps2 = true

/-- What the two halves give of the reader. -/
theorem read_of_check {pol KL : ByteArray} {v : FreeLines} (h : checkPol pol.data.toList v = true)
    (h' : CheckKL KL v) :
    ∃ pp, settingsAtRef pol KL = .ok pp ∧ freeLinesOf pp = v ∧ 2 ^ 8 ≤ pp.pol.theta := by
  unfold checkPol at h
  obtain ⟨hrest, hrows⟩ := h'
  unfold restOK at hrest
  cases hS : polScanL pol.data.toList with
  | error e => rw [hS] at h; cases h
  | ok S =>
    rw [hS] at h
    have hP : polScan pol = .ok S := (polScan_eq pol).trans hS
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h0, hL⟩, hv0⟩ := h
    cases hk : tableOf KL v with
    | none => rw [hk] at hrest; cases hrest
    | some pp =>
      rw [hk] at hrest
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
      obtain ⟨⟨⟨hnf, hpol⟩, hv⟩, ht⟩ := hrest
      have hw : ∀ L, pp.w L = Cm.sRef.w L := by
        intro L
        have hr := hrows
        unfold rowsOK at hr
        simp only [List.all_eq_true, decide_eq_true_eq] at hr
        rw [w_of_table hk L]
        exact hr L (List.mem_finRange L)
      refine ⟨pp, ?_, sameLines_eq hv, ht⟩
      have hn : firstOtherLine S = none := Option.isNone_iff_eq_none.1 h0
      have hk' : (klFileOf S.h KL).bind ofKL = some pp := by
        rw [klFileOf_eq, hL, sameLines_eq hv0]
        exact hk
      have ha : settingsAny pol KL = .ok pp :=
        settingsAny_iff.2 ⟨S, hP, hk', lawful_of_ref hw hnf hpol⟩
      unfold settingsAtRef
      rw [hP]
      show (match firstOtherLine S with
        | some name => (throw ("model-line-not-the-reference's: " ++ name) : Except String ScalesAndPolicy)
        | none => settingsAny pol KL) = .ok pp
      rw [hn]
      exact ha

/-- The files Z with the stored layout file and the parameter file written at v are in scope and are
read, with v's policy, if the test says yes. -/
theorem scope_of_check {Z : PublicFiles} {v : FreeLines} (hlay : Z.lay = storedPublicFiles.lay)
    (hpol : Z.pol = policyFile v) (h : checkPol Z.pol.data.toList v = true)
    (h' : CheckKL Z.KL v) :
    InScope Z = true ∧ ∃ pp, readFiles Z = .ok pp ∧ pp.pol = ⟨v.C, v.theta, v.cap⟩ := by
  obtain ⟨pp, hr, hv, ht⟩ := read_of_check h h'
  have hr' : readFiles Z = .ok pp := hr
  refine ⟨?_, pp, hr', ?_⟩
  · unfold InScope
    rw [hr']
    show (decide (Z.lay = storedPublicFiles.lay) &&
      (decide (Z.pol = policyFile (freeLinesOf pp)) && decide (2 ^ 8 ≤ pp.pol.theta))) = true
    rw [hv]
    simp only [hlay, hpol, decide_true, Bool.true_and, decide_eq_true_eq]
    exact ht
  · rw [← hv]
    rfl


/-! ## A scale file that is written as a list of words -/

/-- The four bytes of a word, the lowest first, as `wordsFile` writes them. -/
def bytes4 (w : Nat) : List UInt8 :=
  [w % 256, w / 256 % 256, w / 65536 % 256, w / 16777216 % 256].map (·.toUInt8)

/-- The bytes of a file of words. -/
theorem wordsFile_data (l : List Nat) : (wordsFile l).data = (l.flatMap bytes4).toArray := rfl

/-- Four bytes a word. -/
theorem length_flat (l : List Nat) : (l.flatMap bytes4).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    show 4 + 4 * l.length = 4 * (l.length + 1)
    omega

/-- The size of a file of words. -/
theorem size_wordsFile (l : List Nat) : (wordsFile l).size = 4 * l.length := by
  show (wordsFile l).data.size = _
  rw [wordsFile_data, List.size_toArray, length_flat]

/-- Byte k of word i. -/
theorem flat_getD : ∀ (l : List Nat) (i k : Nat), k < 4 →
    (l.flatMap bytes4).getD (4 * i + k) 0 = (bytes4 (l.getD i 0)).getD k 0
  | [], i, k, hk => by
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rw [List.flatMap_nil, List.getD_nil, List.getD_nil]
    rcases this with rfl | rfl | rfl | rfl <;> rfl
  | w :: l, 0, k, hk => by
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by exact hk)]
    rfl
  | w :: l, i + 1, k, hk => by
    have e : 4 * (i + 1) + k = (bytes4 w).length + (4 * i + k) := by
      show _ = 4 + (4 * i + k)
      omega
    rw [List.flatMap_cons, e, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, flat_getD l i k hk]
    rfl

/-- An entry of the array that is made of a list is the list's. -/
theorem toArray_getD (l : List UInt8) (i : Nat) : l.toArray.getD i 0 = l.getD i 0 := by
  by_cases h : i < l.length
  · simp [Array.getD, List.getD, h]
  · simp [Array.getD, List.getD, h]

/-- Byte k of word i of a file of words. -/
theorem byteAt_wordsFile (l : List Nat) (i k : Nat) (hk : k < 4) :
    Fmt.byteAt (wordsFile l) (4 * i + k) = (bytes4 (l.getD i 0)).getD k 0 := by
  rw [Fmt.byteAt_eq, wordsFile_data, toArray_getD, flat_getD l i k hk]

/-- **A word of a file of words is the list's entry, modulo 2^32**; 0 beyond the end. -/
theorem klWord_wordsFile (l : List Nat) (i : Nat) :
    Model.klWord (wordsFile l) i = l.getD i 0 % 4294967296 := by
  unfold Model.klWord
  rw [size_wordsFile]
  by_cases h : i < l.length
  · rw [if_pos (by omega)]
    have b0 := byteAt_wordsFile l i 0 (by omega)
    have b1 := byteAt_wordsFile l i 1 (by omega)
    have b2 := byteAt_wordsFile l i 2 (by omega)
    have b3 := byteAt_wordsFile l i 3 (by omega)
    rw [Nat.add_zero] at b0
    show (Fmt.byteAt (wordsFile l) (4 * i)).toNat + 256 * ((Fmt.byteAt (wordsFile l) (4 * i +
    1)).toNat +
      256 * ((Fmt.byteAt (wordsFile l) (4 * i + 1 + 1)).toNat +
        256 * ((Fmt.byteAt (wordsFile l) (4 * i + 1 + 1 + 1)).toNat + 256 * 0))) = _
    rw [b0, show 4 * i + 1 + 1 = 4 * i + 2 from rfl, show 4 * i + 2 + 1 = 4 * i + 3 from rfl, b1,
    b2, b3]
    generalize l.getD i 0 = w
    show (w % 256).toUInt8.toNat + 256 * ((w / 256 % 256).toUInt8.toNat +
      256 * ((w / 65536 % 256).toUInt8.toNat + 256 * ((w / 16777216 % 256).toUInt8.toNat + 256 *
      0))) = _
    simp only [Nat.toUInt8, UInt8.toNat_ofNat']
    omega
  · rw [if_neg (by omega), List.getD_eq_default _ _ (Nat.le_of_not_lt h)]

/-- A word as the reader takes it, off the list. -/
def wordL (l : List Nat) (i : Nat) : Nat := ((l.getD i 0 % 4294967296).toUInt32).toNat

/-- `wordsAt` off the list of the file's words. -/
def wordsL (l : List Nat) (e1 e2 : Nat) (L : Fin 48) : Words where
  kq := wordL l (13 * L.val + 0)
  kk := wordL l (13 * L.val + 1)
  kv := wordL l (13 * L.val + 2)
  ko := wordL l (13 * L.val + 3)
  kg := wordL l (13 * L.val + 4)
  ku := wordL l (13 * L.val + 5)
  kd := wordL l (13 * L.val + 6)
  kr := if L.val % 2 = 1 then wordL l (13 * 48 + 3 * (L.val / 2) + 0) else 17
  kg' := if L.val % 2 = 1 then wordL l (13 * 48 + 3 * (L.val / 2) + 1) else 16
  ku' := if L.val % 2 = 1 then wordL l (13 * 48 + 3 * (L.val / 2) + 2) else 20
  n1 := ⟨wordL l (13 * L.val + 7), wordL l (13 * L.val + 8), e1⟩
  n2 := ⟨wordL l (13 * L.val + 9), wordL l (13 * L.val + 10), e2⟩
  sh := wordL l (13 * L.val + 11)

/-- At a file of words a layer's words are `wordsL` of the list. -/
theorem wordsAt_wordsFile (l : List Nat) (e1 e2 : Nat) (L : Fin 48) :
    wordsAt (wordsFile l) e1 e2 L = wordsL l e1 e2 L := by
  unfold wordsAt wordsL layAt moeAt wordL
  simp only [klWord_wordsFile]

/-- The test on the layers' words, off the list. -/
def rowsL (ls : List (Fin 48)) (l : List Nat) (e1 e2 : Nat) : Bool :=
  ls.all fun L => decide (wordsL l e1 e2 L = Cm.sRef.w L)

/-- **At a file of words the test on the layers' words is the test on the list.** -/
theorem rowsOK_wordsFile (ls : List (Fin 48)) (l : List Nat) (e1 e2 : Nat) :
    rowsOK ls (wordsFile l) e1 e2 = rowsL ls l e1 e2 := by
  unfold rowsOK rowsL
  simp only [wordsAt_wordsFile]

/-- The free numbers of the second named set of files. -/
def gapLines : FreeLines := { storedLines with C := 25856, theta := 512, cap := 1 }

end VerifierAndGoals.Read
