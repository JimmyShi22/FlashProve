-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ScopeLines.lean: what the strict scan of the parameter file returns for the
fixed value lines of `VerifierAndGoals.policyFile v`, for all values v of the eight free numbers.

Why. The goals' scope (`VerifierAndGoals.InScope`, Ladder.lean) fixes the parameter file's bytes but for eight
free numbers: in scope the file is `policyFile v` for some v (Ladder/Stored.lean). The theorems on
the verifier speak of numbers of the scanned file: the model's sizes, the sizes of the committed
matrices and so on. This file is the step from the bytes to these numbers. Since v is free, no
evaluation of the scan on one file can give it.

How. `polWord_of_prof` (OnBytes/Model/ConfigReadersBehind.lean) says that where the strict scan
returns, its value of a line is what the reader by name (`Config.polWord`) finds on the file. The
reader by name is simple: behind the first 32 lines it takes the first line that begins with the
name and a space. So it is enough to know the file's lines.
  1. A text is cut into lines at its line feeds (`linesOf_cons`, `linesOf_joined`).
  2. The reader by name passes over a line that begins otherwise, and what it finds in a list of
     lines it finds in every longer list (`findWord_append_misses`, `findWord_append_some`).
  3. A number's decimal spelling holds no line feed (`feed_not_mem`), so each free line is one line,
     whatever its number.
  4. So the lines behind the first 32 are four fixed chunks with the eleven free lines between them
     (`linesOf_behind`).
  5. The reader of the first 32 lines leaves exactly what stands behind them (`frame_read`, with
     `keeps_lines` of OnBytes/K/Left/SaysLinesPrefix.lean), so the reader by name searches these
     lines (`polWord_policyFile`).
  6. Four tests on closed terms say of each fixed name: no earlier fixed line and no earlier free
  line
     begins with it, and in its own chunk the reader by name finds its number. Lean's kernel
     evaluates them (`decide +kernel`: no compiled code, no axiom).

Main theorems:
  `polWord_fixed`: on `policyFile v` the reader by name finds every fixed value line's number.
  `value_fixed`: where the strict scan returns on `policyFile v`, its value of every fixed value
    line is the stored example's. `fixedValues` lists the 86 names and numbers.

What is not claimed. That the scan returns on `policyFile v`: it refuses, for one, a free number of
2^32 or more. Nothing on the eleven free lines' values, on the first 32 lines' values, on the
optional lines (lidb to xl), the tables' lines or the call lines. The program does not import this
file.
-/
import Johnson.Goal.Meaning.ScopeBytes
import OnBytes.K.Left.SaysLinesPrefix

set_option autoImplicit false

namespace VerifierAndGoals.Lines

open OnBytes OnBytes.Model OnBytes.Model.Config
open OnBytes.Model.ConfigReaders (polWord_of_name)

/-! ## 1. A text as lines -/

/-- The lines that are complete stand before what the walk adds. -/
theorem linesLoop_acc : ∀ (t cur : List UInt8) (acc : List (List UInt8)),
    linesLoop t cur acc = acc.reverse ++ linesLoop t cur []
  | [], cur, acc => by
    unfold linesLoop
    split <;> simp
  | c :: t, cur, acc => by
    unfold linesLoop
    split
    · rw [linesLoop_acc t [] (_ :: acc), linesLoop_acc t [] [_]]
      simp
    · exact linesLoop_acc t (c :: cur) acc

/-- The walk over a text that ends in a line feed, with more text behind it. -/
theorem linesLoop_feed : ∀ (a cur : List UInt8) (acc : List (List UInt8)) (t : List UInt8),
    linesLoop (a ++ 0x0A :: t) cur acc = linesLoop (a ++ [0x0A]) cur acc ++ linesOf t
  | [], cur, acc, t => by
    show linesLoop (0x0A :: t) cur acc = linesLoop [0x0A] cur acc ++ linesOf t
    rw [linesLoop, linesLoop, if_pos (by decide), if_pos (by decide), linesLoop_acc t, linesLoop]
    simp [linesOf]
  | c :: a, cur, acc, t => by
    show linesLoop (c :: (a ++ 0x0A :: t)) cur acc = linesLoop (c :: (a ++ [0x0A])) cur acc ++ _
    unfold linesLoop
    split
    · exact linesLoop_feed a [] _ t
    · exact linesLoop_feed a (c :: cur) acc t

/-- Behind a line feed the lines begin anew. -/
theorem linesOf_feed (a t : List UInt8) :
    linesOf (a ++ 0x0A :: t) = linesOf (a ++ [0x0A]) ++ linesOf t :=
  linesLoop_feed a [] [] t

/-- The walk over bytes among which is no line feed, and a line feed. -/
theorem linesLoop_line : ∀ (l cur : List UInt8), (∀ c ∈ l, c ≠ 0x0A) →
    linesLoop (l ++ [0x0A]) cur [] = [cur.reverse ++ l ++ [0x0A]]
  | [], cur, _ => by
    show linesLoop [0x0A] cur [] = _
    rw [linesLoop, if_pos (by decide), linesLoop]
    simp
  | c :: l, cur, h => by
    show linesLoop (c :: (l ++ [0x0A])) cur [] = _
    unfold linesLoop
    rw [if_neg (by simpa using h c List.mem_cons_self),
      linesLoop_line l (c :: cur) fun x hx => h x (List.mem_cons_of_mem _ hx)]
    simp

/-- Bytes among which is no line feed, and a line feed, are one line. -/
theorem linesOf_cons {l : List UInt8} (h : ∀ c ∈ l, c ≠ 0x0A) (t : List UInt8) :
    linesOf (l ++ 0x0A :: t) = (l ++ [0x0A]) :: linesOf t := by
  rw [linesOf_feed]
  show linesLoop (l ++ [0x0A]) [] [] ++ _ = _
  rw [linesLoop_line l [] h]
  rfl

/-- Lines without a line feed inside, each with its line feed, one behind the other, and more text:
the walk finds these lines again. -/
theorem linesOf_joined : ∀ {ls : List (List UInt8)},
    ls.all (fun l => l.all fun c => c != 0x0A) = true → ∀ t : List UInt8,
    linesOf (concatenatedWithLineFeeds ls ++ t) = fed ls ++ linesOf t
  | [], _, _ => rfl
  | l :: ls, h, t => by
    rw [List.all_cons, Bool.and_eq_true] at h
    show linesOf (((l ++ [0x0A]) ++ concatenatedWithLineFeeds ls) ++ t) = (l ++ [0x0A]) :: (fed ls ++ linesOf t)
    have hl : ∀ c ∈ l, c ≠ 0x0A := fun c hc => by simpa using List.all_eq_true.1 h.1 c hc
    rw [← linesOf_joined h.2 t, ← linesOf_cons hl]
    simp

/-! ## 2. The reader by name -/

/-- True if the line, without its line feed, does not begin with the name and a space. -/
def misses (n : String) (line : List UInt8) : Bool :=
  (Params.behind (bytesOf n ++ [0x20]) (line.filter fun c => c != 0x0A)).isNone

/-- The reader by name passes over such a line. -/
theorem findWord_cons_misses {n : String} {line : List UInt8} (h : misses n line = true)
    (rest : List (List UInt8)) : findWord n (line :: rest) = findWord n rest := by
  unfold misses at h
  rw [findWord]
  cases hb : Params.behind (bytesOf n ++ [0x20]) (line.filter fun c => c != 0x0A) with
  | none => rfl
  | some v =>
    rw [hb] at h
    cases h

/-- It passes over a list of such lines. -/
theorem findWord_append_misses {n : String} : ∀ {l : List (List UInt8)},
    l.all (misses n) = true → ∀ rest, findWord n (l ++ rest) = findWord n rest
  | [], _, _ => rfl
  | line :: l, h, rest => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, findWord_cons_misses h.1, findWord_append_misses h.2]

/-- What it finds in a list of lines it finds in every longer list. -/
theorem findWord_append_some {n : String} {k : Nat} : ∀ {l : List (List UInt8)},
    findWord n l = some k → ∀ rest, findWord n (l ++ rest) = some k
  | [], h, _ => by cases h
  | line :: l, h, rest => by
    rw [List.cons_append, findWord]
    rw [findWord] at h
    cases hb : Params.behind (bytesOf n ++ [0x20]) (line.filter fun c => c != 0x0A) with
    | none =>
      rw [hb] at h
      exact findWord_append_some h rest
    | some v =>
      rw [hb] at h
      dsimp only at h ⊢
      split
      · rename_i hv
        rw [if_pos hv] at h
        exact findWord_append_some h rest
      · rename_i hv
        rw [if_neg hv] at h
        exact h

/-- True if the two lists differ at a place that both have. -/
def clash : List UInt8 → List UInt8 → Bool
  | a :: p, b :: q => a != b || clash p q
  | _, _ => false

/-- Then no list that begins with the second begins with the first. -/
theorem behind_of_clash : ∀ {p q : List UInt8}, clash p q = true → ∀ r,
    Params.behind p (q ++ r) = none
  | [], _, h, _ => by simp [clash] at h
  | _ :: _, [], h, _ => by simp [clash] at h
  | a :: p, b :: q, h, r => by
    rw [clash, Bool.or_eq_true] at h
    rw [List.cons_append, Params.behind]
    split
    · rename_i hab
      rcases h with h | h
      · exact absurd (by simpa using hab) (by simpa using h)
      · exact behind_of_clash h r
    · rfl

/-- A line that begins with bytes which differ from the name and a space. -/
theorem misses_of_clash {n : String} {q : List UInt8}
    (h : clash (bytesOf n ++ [0x20]) (q.filter fun c => c != 0x0A) = true) (r : List UInt8) :
    misses n (q ++ r) = true := by
  unfold misses
  rw [List.filter_append, behind_of_clash h]
  rfl

/-! ## 3. A number in decimal holds no line feed -/

theorem bytesOf_append (s t : String) : bytesOf (s ++ t) = bytesOf s ++ bytesOf t := by
  rw [ConfigReaders.bytesOf_data, ConfigReaders.bytesOf_data, ConfigReaders.bytesOf_data]
  simp [String.toByteArray_append, ByteArray.data_append]

/-- No byte of a number's decimal spelling is a line feed. -/
theorem feed_not_mem (x : Nat) : ∀ c ∈ bytesOf (toString x), c ≠ 0x0A := by
  intro c hc
  rw [ConfigReaders.bytesOf_data, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray,
    List.mem_flatMap] at hc
  obtain ⟨ch, hch, hc⟩ := hc
  have hd := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hch
  simp only [Char.isDigit, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq] at hd
  have l1 : 48 ≤ ch.val.toNat := by simpa [UInt32.le_iff_toNat_le] using hd.1
  have l2 : ch.val.toNat ≤ 57 := by simpa [UInt32.le_iff_toNat_le] using hd.2
  have h1 : ch.utf8Size = 1 := by
    unfold Char.utf8Size
    rw [if_pos (by rw [UInt32.le_iff_toNat_le]; exact Nat.le_trans l2 (by decide))]
  rw [String.utf8EncodeChar_eq_singleton h1, List.mem_singleton] at hc
  intro e
  rw [hc] at e
  have e' := congrArg UInt8.toNat e
  rw [UInt32.toNat_toUInt8] at e'
  have : (0x0A : UInt8).toNat = 10 := rfl
  omega

/-! ## 4. The parameter file, cut at its free lines -/

/-- A free line without its line feed: the name with its space, and the number in decimal. -/
def fl (q : String) (x : Nat) : List UInt8 := bytesOf q ++ bytesOf (toString x)

/-- Free lines, each with its line feed. -/
def fls (l : List (String × Nat)) : List (List UInt8) := l.map fun p => fl p.1 p.2 ++ [0x0A]

/-- The four free lines of a layer's two normalisations. -/
def free1 (v : FreeLines) : List (String × Nat) :=
  [("eps1_lo ", v.eps1 % 2 ^ 32), ("eps1_hi ", v.eps1 / 2 ^ 32), ("eps2_lo ", v.eps2 % 2 ^ 32),
   ("eps2_hi ", v.eps2 / 2 ^ 32)]

/-- The four free lines of the final normalisation. -/
def free2 (v : FreeLines) : List (String × Nat) :=
  [("MF ", v.MF), ("KF ", v.KF), ("epsF_lo ", v.epsF % 2 ^ 32), ("epsF_hi ", v.epsF / 2 ^ 32)]

/-- The three free lines of the acceptance policy. -/
def free3 (v : FreeLines) : List (String × Nat) :=
  [("C ", v.C), ("theta ", v.theta), ("cap ", v.cap)]

/-- The lines of `policyFile v` behind its first 32. -/
def linesAt (v : FreeLines) : List (List UInt8) :=
  fed linesA1 ++ (fls (free1 v) ++ (fed linesA2 ++ (fls (free2 v) ++
    (fed linesA3 ++ (fls (free3 v) ++ fed linesB)))))

/-- The text of `policyFile v` behind its first 32 lines. -/
def behindText (v : FreeLines) : String :=
  behindA1 ++
      s!"eps1_lo {v.eps1 % 2 ^ 32}\neps1_hi {v.eps1 / 2 ^ 32}\n" ++
      s!"eps2_lo {v.eps2 % 2 ^ 32}\neps2_hi {v.eps2 / 2 ^ 32}\n" ++ behindA2 ++
      s!"MF {v.MF}\nKF {v.KF}\n" ++
      s!"epsF_lo {v.epsF % 2 ^ 32}\nepsF_hi {v.epsF / 2 ^ 32}\n" ++ behindA3 ++
      s!"C {v.C}\ntheta {v.theta}\ncap {v.cap}\n" ++ behindB

theorem policyFile_eq (v : FreeLines) :
    policyFile v = OnBytes.Tie.Pv.Plan.textOf lines32 ++ (behindText v).toUTF8 := rfl

/-- A free line holds no line feed before its end. -/
theorem fl_feed {q : String} (hq : (bytesOf q).all (fun c => c != 0x0A) = true) (x : Nat) :
    ∀ c ∈ fl q x, c ≠ 0x0A := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · simpa using List.all_eq_true.1 hq c h
  · exact feed_not_mem x c h

theorem feed_text : bytesOf "\n" = [0x0A] := by decide +kernel

/-- A free line, with more text behind it, is one line. -/
theorem linesOf_free {q : String} (hq : (bytesOf q).all (fun c => c != 0x0A) = true) (x : Nat)
    (t : List UInt8) :
    linesOf (bytesOf q ++ (bytesOf (Nat.repr x) ++ 0x0A :: t)) =
      (fl q x ++ [0x0A]) :: linesOf t := by
  rw [← List.append_assoc]
  exact linesOf_cons (fl_feed hq x) t

theorem bytesA1 : bytesOf behindA1 = concatenatedWithLineFeeds linesA1 := by
  rw [textA1]
  exact bytesOf_asText _ (by decide +kernel)

theorem bytesA2 : bytesOf behindA2 = concatenatedWithLineFeeds linesA2 := by
  rw [textA2]
  exact bytesOf_asText _ (by decide +kernel)

theorem bytesA3 : bytesOf behindA3 = concatenatedWithLineFeeds linesA3 := by
  rw [textA3]
  exact bytesOf_asText _ (by decide +kernel)

theorem bytesB : bytesOf behindB = concatenatedWithLineFeeds linesB := by
  rw [textB]
  exact bytesOf_asText _ (by decide +kernel)

/-- **The lines of the text behind the first 32 lines.** -/
theorem linesOf_behind (v : FreeLines) : linesOf (bytesOf (behindText v)) = linesAt v := by
  have e1 : "\neps1_hi " = "\n" ++ "eps1_hi " := by decide +kernel
  have e2 : "\neps2_hi " = "\n" ++ "eps2_hi " := by decide +kernel
  have e3 : "\nKF " = "\n" ++ "KF " := by decide +kernel
  have e4 : "\nepsF_hi " = "\n" ++ "epsF_hi " := by decide +kernel
  have e5 : "\ntheta " = "\n" ++ "theta " := by decide +kernel
  have e6 : "\ncap " = "\n" ++ "cap " := by decide +kernel
  have eB : concatenatedWithLineFeeds linesB = concatenatedWithLineFeeds linesB ++ [] := (List.append_nil _).symm
  unfold behindText
  simp only [toString, e1, e2, e3, e4, e5, e6, bytesOf_append, feed_text, bytesA1, bytesA2,
    bytesA3, bytesB, List.append_assoc, List.cons_append, List.nil_append]
  rw [linesOf_joined (by decide +kernel), linesOf_free (by decide +kernel),
    linesOf_free (by decide +kernel), linesOf_free (by decide +kernel),
    linesOf_free (by decide +kernel), linesOf_joined (by decide +kernel),
    linesOf_free (by decide +kernel), linesOf_free (by decide +kernel),
    linesOf_free (by decide +kernel), linesOf_free (by decide +kernel),
    linesOf_joined (by decide +kernel), linesOf_free (by decide +kernel),
    linesOf_free (by decide +kernel), linesOf_free (by decide +kernel), eB,
    linesOf_joined (by decide +kernel)]
  show _ = linesAt v
  unfold linesAt
  simp [fls, free1, free2, free3, linesOf, linesLoop]

/-! ## 5. The reader by name on the parameter file -/

/-- The bytes of texts laid one behind the other. -/
theorem bytesOf_foldl : ∀ (l : List String) (r : String),
    bytesOf (l.foldl (fun r s => r ++ s) r) = bytesOf r ++ (l.map bytesOf).flatten
  | [], r => by simp
  | s :: l, r => by
    rw [List.foldl_cons, bytesOf_foldl l (r ++ s), bytesOf_append]
    simp

/-- The bytes of the first 32 lines. -/
theorem frame_bytes : (OnBytes.Tie.Pv.Plan.textOf lines32).toList = concatenatedWithLineFeeds frameLines := by
  have h : frameLines.all (fun l => l.all fun b => decide (b < 128)) = true := by decide +kernel
  show bytesOf (String.join (lines32.map (· ++ "\n"))) = _
  rw [String.join, bytesOf_foldl, frame_text]
  have e0 : bytesOf "" = [] := by decide +kernel
  rw [e0, List.nil_append, List.map_map, List.map_map]
  unfold concatenatedWithLineFeeds fed
  congr 1
  apply List.map_congr_left
  intro l hl
  show bytesOf (asText l ++ "\n") = _
  rw [bytesOf_append, feed_text, bytesOf_asText l (List.all_eq_true.1 h l hl)]

/-- The reader of the frame's lines reads the first 32 lines and leaves nothing of them. -/
theorem frame_read : ∃ fr, Params.lines (concatenatedWithLineFeeds frameLines) = .ok (fr, []) := by
  have h : (match Params.lines (concatenatedWithLineFeeds frameLines) with
      | .ok x => x.2.isEmpty
      | .error _ => false) = true := by decide +kernel
  cases hl : Params.lines (concatenatedWithLineFeeds frameLines) with
  | error e =>
    rw [hl] at h
    cases h
  | ok x =>
    rw [hl] at h
    obtain ⟨fr, t⟩ := x
    have ht : t = [] := by simpa using h
    exact ⟨fr, by rw [ht]⟩

/-- **On `policyFile v` the reader by name searches the lines `linesAt v`.** -/
theorem polWord_policyFile (v : FreeLines) (n : String) :
    polWord (policyFile v) n = findWord n (linesAt v) := by
  obtain ⟨fr, hfr⟩ := frame_read
  have e : (policyFile v).toList = concatenatedWithLineFeeds frameLines ++ bytesOf (behindText v) := by
    rw [← frame_bytes, policyFile_eq, K.Left.toList_data, K.Left.toList_data,
      ByteArray.data_append, Array.toList_append, ConfigReaders.bytesOf_data]
  have hr : Params.readLines (policyFile v) = .ok (fr, ⟨(bytesOf (behindText v)).toArray⟩) := by
    unfold Params.readLines
    rw [e, K.Left.keeps_lines _ _ (bytesOf (behindText v)) _ hfr]
    rfl
  unfold polWord
  rw [hr]
  show findWord n (linesOf (ByteArray.toList ⟨(bytesOf (behindText v)).toArray⟩)) = _
  rw [K.Left.toList_data, linesOf_behind]

/-! ## 6. The fixed value lines -/

/-- The value lines before the first free lines: name and number. -/
def valuesA1 : List (String × Nat) :=
  [("prof", 20), ("lt", 10), ("L", 48), ("ll", 2), ("d", 5120), ("H", 40), ("G", 8), ("dh", 128),
   ("f", 16384), ("fe", 8192), ("NE", 128), ("V", 202048)]

/-- The value lines between the first and the second free lines. -/
def valuesA2 : List (String × Nat) :=
  [("cs", 12), ("theta0_lo", 500000), ("theta0_hi", 0), ("hq", 2), ("hv", 1), ("ho", 1),
   ("hgD", 1), ("huD", 1), ("hdD", 1), ("hr", 1), ("ut", 1), ("la", 16), ("nmin", 20),
   ("D", 2048), ("tau", 128), ("lmaf", 16), ("NAf", 3), ("lmad", 15), ("NAd", 1), ("lmar", 13),
   ("lmb", 16), ("lmq", 16), ("lmx", 16), ("wb_qk", 13), ("wb_v", 13), ("wb_o", 13), ("wb_g", 13),
   ("wb_u", 13), ("wb_gs", 13), ("wb_us", 13), ("wb_gr", 13), ("wb_ur", 13), ("wb_dn", 13),
   ("wb_dnr", 13), ("wb_r", 13), ("iota_0", 1), ("iota_1", 1), ("iota_2", 1), ("iota_3", 2),
   ("iota_4", 1), ("iota_5", 1), ("iota_6", 0), ("iota_7", 0), ("seed_lo", 1), ("seed_hi", 0),
   ("lB", 6), ("S", 12), ("rx", 8), ("kFM", 15), ("kFD", 16), ("lmS", 16), ("NAs", 1),
   ("lmh", 13), ("lmo", 16), ("lmbA", 14), ("iotaA_0", 57)]

/-- The value lines between the second and the third free lines. -/
def valuesA3 : List (String × Nat) :=
  [("toksrc", 1), ("lmhf", 16), ("NHf", 4), ("lmhd", 14), ("lmhr", 13), ("lmbH", 15),
   ("wb_emb", 21), ("wb_head", 13), ("iotaH_0", 1), ("iotaH_1", 1), ("iotaH_2", 1),
   ("iotaH_3", 0), ("iotaH_4", 0), ("iotaH_5", 0)]

/-- The value lines behind the third free lines. -/
def valuesB : List (String × Nat) :=
  [("s", 15), ("sh", 8), ("sT", 4), ("F", 24)]

/-- True if each of the texts qs differs from the searched name and a space at a place that both
have. -/
def clashAll (n : String) (qs : List String) : Bool :=
  qs.all fun q => clash (bytesOf n ++ [0x20]) ((bytesOf q).filter fun c => c != 0x0A)

/-- The reader by name passes over free lines of other names. -/
theorem fls_misses {n : String} : ∀ {l : List (String × Nat)},
    clashAll n (l.map Prod.fst) = true → (fls l).all (misses n) = true
  | [], _ => rfl
  | p :: l, h => by
    unfold clashAll at h
    rw [List.map_cons, List.all_cons, Bool.and_eq_true] at h
    show (misses n (fl p.1 p.2 ++ [0x0A]) && (fls l).all (misses n)) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, fls_misses h.2⟩
    unfold fl
    rw [List.append_assoc]
    exact misses_of_clash h.1 _

/-- The names of the first four free lines, each with its space. -/
def names1 : List String := ["eps1_lo ", "eps1_hi ", "eps2_lo ", "eps2_hi "]

/-- The names of the next four free lines, each with its space. -/
def names2 : List String := ["MF ", "KF ", "epsF_lo ", "epsF_hi "]

/-- The names of the last three free lines, each with its space. -/
def names3 : List String := ["C ", "theta ", "cap "]

/-! Four tests on closed terms. Each says of every name of a chunk: no line of an earlier chunk and
no earlier free line begins with it, and in its own chunk the reader by name finds its number. -/

def test1 : Bool := valuesA1.all fun p => findWord p.1 (fed linesA1) == some p.2

def test2 : Bool := valuesA2.all fun p =>
  (fed linesA1).all (misses p.1) && clashAll p.1 names1 && findWord p.1 (fed linesA2) == some p.2

def test3 : Bool := valuesA3.all fun p =>
  (fed linesA1).all (misses p.1) && clashAll p.1 names1 && (fed linesA2).all (misses p.1) &&
    clashAll p.1 names2 && findWord p.1 (fed linesA3) == some p.2

def test4 : Bool := valuesB.all fun p =>
  (fed linesA1).all (misses p.1) && clashAll p.1 names1 && (fed linesA2).all (misses p.1) &&
    clashAll p.1 names2 && (fed linesA3).all (misses p.1) && clashAll p.1 names3 &&
    findWord p.1 (fed linesB) == some p.2

theorem test1_holds : test1 = true := by decide +kernel

theorem test2_holds : test2 = true := by decide +kernel

theorem test3_holds : test3 = true := by decide +kernel

theorem test4_holds : test4 = true := by decide +kernel

/-- A name of the first chunk. -/
theorem find1 (v : FreeLines) {p : String × Nat} (hp : p ∈ valuesA1) :
    findWord p.1 (linesAt v) = some p.2 := by
  have h := List.all_eq_true.1 test1_holds p hp
  exact findWord_append_some (by simpa using h) _

/-- A name of the second chunk. -/
theorem find2 (v : FreeLines) {p : String × Nat} (hp : p ∈ valuesA2) :
    findWord p.1 (linesAt v) = some p.2 := by
  have h := List.all_eq_true.1 test2_holds p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨a1, c1⟩, f⟩ := h
  unfold linesAt
  rw [findWord_append_misses a1, findWord_append_misses (fls_misses c1)]
  exact findWord_append_some f _

/-- A name of the third chunk. -/
theorem find3 (v : FreeLines) {p : String × Nat} (hp : p ∈ valuesA3) :
    findWord p.1 (linesAt v) = some p.2 := by
  have h := List.all_eq_true.1 test3_holds p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨a1, c1⟩, a2⟩, c2⟩, f⟩ := h
  unfold linesAt
  rw [findWord_append_misses a1, findWord_append_misses (fls_misses c1),
    findWord_append_misses a2, findWord_append_misses (fls_misses c2)]
  exact findWord_append_some f _

/-- A name of the last chunk. -/
theorem find4 (v : FreeLines) {p : String × Nat} (hp : p ∈ valuesB) :
    findWord p.1 (linesAt v) = some p.2 := by
  have h := List.all_eq_true.1 test4_holds p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨a1, c1⟩, a2⟩, c2⟩, a3⟩, c3⟩, f⟩ := h
  unfold linesAt
  rw [findWord_append_misses a1, findWord_append_misses (fls_misses c1),
    findWord_append_misses a2, findWord_append_misses (fls_misses c2),
    findWord_append_misses a3, findWord_append_misses (fls_misses c3)]
  exact f

/-- The 86 fixed value lines of `policyFile v`: name and number. The other eleven value lines are
the free lines. -/
def fixedValues : List (String × Nat) := valuesA1 ++ valuesA2 ++ valuesA3 ++ valuesB

/-- **On `policyFile v`, whatever the eight free numbers, the reader by name finds every fixed value
line's number.** -/
theorem polWord_fixed (v : FreeLines) {p : String × Nat} (hp : p ∈ fixedValues) :
    polWord (policyFile v) p.1 = some p.2 := by
  rw [polWord_policyFile]
  unfold fixedValues at hp
  simp only [List.mem_append] at hp
  rcases hp with ((h | h) | h) | h
  · exact find1 v h
  · exact find2 v h
  · exact find3 v h
  · exact find4 v h

/-- **Where the strict scan returns on `policyFile v`, its value of every fixed value line is the
stored example's.** -/
theorem value_fixed {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P)
    {p : String × Nat} (hp : p ∈ fixedValues) : P.value p.1 = p.2 := by
  have e20 : P.value "prof" = 20 := by
    have a := polWord_of_name h (n := "prof") (by simp [valueNames])
    rw [polWord_fixed v (p := ("prof", 20)) (by decide)] at a
    exact (Option.some.inj a).symm
  have e4 : P.h.prof = 4 := by
    have := polScan_prof h
    omega
  have hn : p.1 ∈ valueNames P.h.prof := by
    rw [e4]
    have : fixedValues.all (fun p => (valueNames 4).contains p.1) = true := by decide +kernel
    simpa using List.all_eq_true.1 this p hp
  have a := polWord_of_prof h hn
  rw [polWord_fixed v hp] at a
  exact (Option.some.inj a).symm

end VerifierAndGoals.Lines

#print axioms VerifierAndGoals.Lines.linesOf_behind
#print axioms VerifierAndGoals.Lines.polWord_policyFile
#print axioms VerifierAndGoals.Lines.polWord_fixed
#print axioms VerifierAndGoals.Lines.value_fixed
