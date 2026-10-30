-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/ServedFreeItem.lean: what the stage of the request finds out about the item `request`
hangs on the request's length alone.

The stage forms the item (`Proof.requestItem`, OnBytes/Proof/RequestItem.lean: 177 words) and
compares it with the public part (`Verify.statementHeld`, OnBytes/Model/VerifyStatement.lean). The
request's file enters the item in two ways: its length is tested, and its digest (`secondHashFunctionTree`) is
eight of the words. The proof of `itemStep_free` finds that 652 bytes stand in front of these eight,
so that they are the words 163 to 170; `statementHeld_congr` shows that the comparison reads none of
them; `isSome_olderTK` shows that whether the digest can be made hangs on the length alone.

  `size_olderTK`, `isSome_olderTK`   a digest has 32 bytes; it can be made of one string exactly
                          if of another of the same length.
  `wordsAt_front`, `wordsAt_back`   the words of P ++ (D ++ S) in front of D and behind it do not
                          hang on D, at one length of D.
  `namesFit`            the four lists of names have 27, 34, 11 and 25 names.
  `statementHeld_congr`   the comparison says the same of two strings of one length that agree in
                          front of byte 652 and from byte 684 on.
  `itemWith`, `itemWith_shape`   the item with the request's length and digest as letters; it is
                          never made, or at the digest D it is P ++ (D ++ S), with S of 24 bytes,
                          if that has 708 bytes, and else none is made.
  `itemStep_free`       for two requests of one length the two steps give the same: they return
                          at both, or refuse at both with one name.

How the places are found. No law on the lengths of the item's earlier pieces is used: an item has
708 bytes, the digest 32, what stands behind it 24, so 652 stand in front. That the comparison stays
clear of the words 163 to 170 needs the number of names in each list. `decide` does not get through
`String.splitOn`; in `namesFit` the simplifier walks it step by step.

Not claimed. That an item is made at any files. Anything on what the digest is. Anything on the
other steps of the stage. For proofs only; the program does not import this file.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Model.VerifyStages
import OnBytes.Model.VerifyStatement
import Run.Blake2b.SaltedThm
import Fmt.ParsedReadLaws
import Fmt.Rules1Laws

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Verify

/-! ## Lengths -/

/-- The second hash function gives 32 bytes. -/
theorem size_olderK (num : Nat) (w : ByteArray) : (secondHashFunction num w).size = 32 :=
  Run.Blake2b.size_bytes _ 32 (by decide)

/-- n strings of 32 bytes, one behind the other, have 32 n bytes. -/
theorem size_foldAppend (g : Nat → ByteArray) (hg : ∀ i, (g i).size = 32) :
    ∀ n : Nat, (Nat.fold n (fun i _ acc => acc ++ g i) ByteArray.empty).size = 32 * n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.fold_succ, ByteArray.size_append, size_foldAppend g hg n, hg]
    omega

/-- The length of one level of the tree hash hangs on the length of the level before alone. -/
theorem size_olderLevel (num : Nat) (w : ByteArray) :
    (secondHashFunctionTreeLevel num w).size = 32 * ((w.size + 511) / 512) :=
  size_foldAppend (fun i => secondHashFunction num (w.extract (512 * i) (512 * (i + 1))))
    (fun _ => size_olderK _ _) _

/-- What the levels return has 32 bytes. -/
theorem size_olderLevels :
    ∀ (k num : Nat) (w d : ByteArray), secondHashFunctionTreeLevels k num w = some d → d.size = 32
  | 0, _, _, _, h => by cases h
  | k + 1, num, w, d, h => by
    unfold secondHashFunctionTreeLevels at h
    dsimp only at h
    split at h
    · rename_i hs
      cases h
      exact beq_iff_eq.1 hs
    · exact size_olderLevels k 11 _ d h

/-- Whether the levels return hangs on the string's length alone. -/
theorem isSome_olderLevels : ∀ (k num num' : Nat) (w w' : ByteArray), w.size = w'.size →
    (secondHashFunctionTreeLevels k num w).isSome = (secondHashFunctionTreeLevels k num' w').isSome
  | 0, _, _, _, _, _ => rfl
  | k + 1, num, num', w, w', h => by
    have e : (secondHashFunctionTreeLevel num w).size = (secondHashFunctionTreeLevel num' w').size := by
      rw [size_olderLevel, size_olderLevel, h]
    unfold secondHashFunctionTreeLevels
    dsimp only
    rw [e]
    by_cases hc : ((secondHashFunctionTreeLevel num' w').size == 32) = true
    · rw [if_pos hc, if_pos hc]
      rfl
    · rw [if_neg hc, if_neg hc]
      exact isSome_olderLevels k 11 11 _ _ e

/-- A digest of the tree hash has 32 bytes. -/
theorem size_olderTK {w d : ByteArray} (h : secondHashFunctionTree w = some d) : d.size = 32 := by
  unfold secondHashFunctionTree at h
  split at h
  · cases h
  · exact size_olderLevels _ _ _ _ h

/-- Whether the tree hash returns hangs on the string's length alone. -/
theorem isSome_olderTK {w w' : ByteArray} (h : w.size = w'.size) :
    (secondHashFunctionTree w).isSome = (secondHashFunctionTree w').isSome := by
  unfold secondHashFunctionTree
  rw [h]
  split
  · rfl
  · exact isSome_olderLevels _ _ _ _ _ h

/-- A word has four bytes. -/
theorem size_word32 (x : Nat) : (word32 x).size = 4 := Fmt.size_lowBytes 4 x (by decide)

/-- The last five words have 20 bytes. -/
theorem size_lastWords {L : ParamLines} {S : ByteArray} (h : L.lastWords = some S) :
    S.size = 20 := by
  unfold ParamLines.lastWords at h
  split at h
  · cases h
    simp only [List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append,
      size_word32]
    rfl
  · cases h

/-! ## The words of a string in three parts -/

/-- A piece that ends inside the first of two strings is a piece of the first. -/
theorem extract_append_left (A B : ByteArray) (i j : Nat) (h : j ≤ A.size) :
    (A ++ B).extract i j = A.extract i j := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  have e : j - A.data.size = 0 := by
    have : A.data.size = A.size := rfl
    omega
  rw [e]
  simp

/-- A piece that begins behind the first of two strings is a piece of the second. -/
theorem extract_append_right (A B : ByteArray) (i j : Nat) (h : A.size ≤ i) :
    (A ++ B).extract i j = B.extract (i - A.size) (j - A.size) := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  have e : A.data.extract i j = #[] := by
    rw [Array.extract_eq_empty_iff]
    have : A.data.size = A.size := rfl
    omega
  rw [e]
  simp

/-- Words that end inside P do not hang on what stands behind P. -/
theorem wordsAt_front (P Q Q' : ByteArray) (i n : Nat) (h : 4 * (i + n) ≤ P.size) :
    wordsAt (P ++ Q) i n = wordsAt (P ++ Q') i n := by
  unfold wordsAt
  rw [extract_append_left _ _ _ _ h, extract_append_left _ _ _ _ h]

/-- Words that begin behind D do not hang on D, at one length of D. -/
theorem wordsAt_back (P D D' S : ByteArray) (hD : D.size = D'.size) (i n : Nat)
    (h : P.size + D.size ≤ 4 * i) :
    wordsAt (P ++ (D ++ S)) i n = wordsAt (P ++ (D' ++ S)) i n := by
  unfold wordsAt
  rw [extract_append_right P _ _ _ (by omega), extract_append_right P _ _ _ (by omega),
    extract_append_right D _ _ _ (by omega), extract_append_right D' _ _ _ (by omega), hD]

/-! ## The comparison reads no word of the request's digest -/

/-- The comparison of a list of names says the same of two strings that agree in the words that
it reads: one word for each name, from the word `first` on. -/
theorem namesHeld_congr (Pn : PolScan) (a b : ByteArray) (first : Nat) (names : String)
    (h : ∀ k, k < (names.splitOn " ").length →
      wordsAt a (first + k) 1 = wordsAt b (first + k) 1) :
    namesHeld Pn a first names = namesHeld Pn b first names := by
  unfold namesHeld
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro H x hx
    have hk := List.snd_lt_of_mem_zipIdx hx
    rw [← h x.2 (by simpa using hk)]
    exact H x hx
  · intro H x hx
    have hk := List.snd_lt_of_mem_zipIdx hx
    rw [h x.2 (by simpa using hk)]
    exact H x hx

/-- The four lists of names have the lengths that the places of the comparison suppose. -/
def NamesFit : Prop :=
  (names2.splitOn " ").length = 27 ∧ (names37.splitOn " ").length = 34 ∧
    (names103.splitOn " ").length = 11 ∧ (names130.splitOn " ").length = 25

section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- They have these lengths. -/
theorem namesFit : NamesFit := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp (decide := true) (maxSteps := 10000000)
      [names2, String.splitOn, String.splitOnAux.eq_def]
  · simp (decide := true) (maxSteps := 10000000)
      [names37, String.splitOn, String.splitOnAux.eq_def]
  · simp (decide := true) (maxSteps := 10000000)
      [names103, String.splitOn, String.splitOnAux.eq_def]
  · simp (decide := true) (maxSteps := 10000000)
      [names130, String.splitOn, String.splitOnAux.eq_def]

end

/-- The comparison with the public part says the same of two strings of one length that agree in
front of byte 652 and from byte 684 on: so it reads none of the words 163 to 170. -/
theorem statementHeld_congr (X : Public) (a b : ByteArray) (hs : a.size = b.size)
    (hf : ∀ i n, 4 * (i + n) ≤ 652 → wordsAt a i n = wordsAt b i n)
    (hb : ∀ i n, 684 ≤ 4 * i → wordsAt a i n = wordsAt b i n) :
    statementHeld X a = statementHeld X b := by
  obtain ⟨n2, n37, n103, n130⟩ := namesFit
  have e2 := namesHeld_congr X.P a b 2 names2 (fun k hk => hf _ _ (by omega))
  have e37 := namesHeld_congr X.P a b 37 names37 (fun k hk => hf _ _ (by omega))
  have e103 := namesHeld_congr X.P a b 103 names103 (fun k hk => hf _ _ (by omega))
  have e130 := namesHeld_congr X.P a b 130 names130 (fun k hk => hf _ _ (by omega))
  unfold statementHeld tableWordsHeld
  simp only [hs, e2, e37, e103, e130, hf 29 8 (by omega), hf 71 8 (by omega), hf 79 8 (by omega),
    hf 87 8 (by omega), hf 114 8 (by omega), hf 122 8 (by omega), hf 155 8 (by omega),
    hb 172 1 (by omega), hb 173 1 (by omega), hb 174 1 (by omega), hb 175 1 (by omega),
    hb 176 1 (by omega)]

/-! ## The item with the request's length and digest as letters -/

/-- `Proof.requestItem`, written again with the request's length and its digest as letters. -/
def itemWith (pol KL : ByteArray) (sz : Nat) (tk : Option ByteArray) : Option ByteArray := do
  let L := ParamLines.read pol
  let version ← (L.values "version").bind (·.head?)
  let prof ← L.value "prof"
  let ne ← L.value "NE"
  let lt ← L.value "lt"
  if version.length != 4 || prof != 20 || ne == 0 || sz != 4 * (2 ^ lt + 2) then none
  let w := Fmt.cat [
    word32 0x4D363100, ⟨version.toArray⟩, ← L.words names2, ← L.calls "call",
    ← L.words names37,
    ← L.eight "tsilu", ← L.eight "tsig", ← L.eight "trope", ← secondHashFunctionTree KL,
    ← L.words names103, ← L.eight "texp", ← L.calls "callA", ← L.words names130,
    ← L.calls "callH" (some callHIfNone), ← tk, word32 0, ← L.lastWords]
  if w.size == 708 then some w else none

/-- The item is `itemWith` at the request's own length and digest, by unfolding. -/
theorem requestItem_eq_itemWith (pol KL req : ByteArray) :
    requestItem pol KL req = itemWith pol KL req.size (secondHashFunctionTree req) := rfl

/-- At given files and a given length no item is made whatever the digest, or there are P, and S of
24 bytes, such that at a digest D the item is P ++ (D ++ S) if that has 708 bytes, and else none is
made. -/
theorem itemWith_shape (pol KL : ByteArray) (sz : Nat) :
    (∀ tk, itemWith pol KL sz tk = none) ∨
      ∃ P S : ByteArray, S.size = 24 ∧ ∀ D, itemWith pol KL sz (some D) =
        if (P ++ (D ++ S)).size == 708 then some (P ++ (D ++ S)) else none := by
  rcases h0 : ((ParamLines.read pol).values "version").bind (·.head?) with _ | version
  · exact Or.inl fun tk => by simp [itemWith, h0]
  rcases h1 : (ParamLines.read pol).value "prof" with _ | prof
  · exact Or.inl fun tk => by simp [itemWith, h0, h1]
  rcases h2 : (ParamLines.read pol).value "NE" with _ | ne
  · exact Or.inl fun tk => by simp [itemWith, h0, h1, h2]
  rcases h3 : (ParamLines.read pol).value "lt" with _ | lt
  · exact Or.inl fun tk => by simp [itemWith, h0, h1, h2, h3]
  rcases hc : (version.length != 4 || prof != 20 || ne == 0 || sz != 4 * (2 ^ lt + 2)) with _ | _
  rotate_left
  · exact Or.inl fun tk => by
      simp only [itemWith, Option.bind_eq_bind, h0, h1, h2, h3, hc, Option.bind_some,
        Option.bind_none, if_true]
  rcases g1 : (ParamLines.read pol).words names2 with _ | a1
  · exact Or.inl fun tk => by simp [itemWith, h0, h1, h2, h3, g1]
  rcases g2 : (ParamLines.read pol).calls "call" with _ | a2
  · exact Or.inl fun tk => by simp [itemWith, h0, h1, h2, h3, g1, g2]
  rcases g3 : (ParamLines.read pol).words names37 with _ | a3
  · exact Or.inl fun tk => by simp [itemWith, h0, h1, h2, h3, g1, g2, g3]
  rcases g4 : (ParamLines.read pol).eight "tsilu" with _ | a4
  · exact Or.inl fun tk => by simp [itemWith, h0, h1, h2, h3, g1, g2, g3, g4]
  rcases g5 : (ParamLines.read pol).eight "tsig" with _ | a5
  · exact Or.inl fun tk => by simp [itemWith, h0, h1, h2, h3, g1, g2, g3, g4, g5]
  rcases g6 : (ParamLines.read pol).eight "trope" with _ | a6
  · exact Or.inl fun tk => by simp [itemWith, h0, h1, h2, h3, g1, g2, g3, g4, g5, g6]
  rcases g7 : secondHashFunctionTree KL with _ | a7
  · exact Or.inl fun tk => by simp [itemWith, h0, h1, h2, h3, g1, g2, g3, g4, g5, g6, g7]
  rcases g8 : (ParamLines.read pol).words names103 with _ | a8
  · exact Or.inl fun tk => by simp [itemWith, h0, h1, h2, h3, g1, g2, g3, g4, g5, g6, g7, g8]
  rcases g9 : (ParamLines.read pol).eight "texp" with _ | a9
  · exact Or.inl fun tk => by
      simp [itemWith, h0, h1, h2, h3, g1, g2, g3, g4, g5, g6, g7, g8, g9]
  rcases g10 : (ParamLines.read pol).calls "callA" with _ | a10
  · exact Or.inl fun tk => by
      simp [itemWith, h0, h1, h2, h3, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10]
  rcases g11 : (ParamLines.read pol).words names130 with _ | a11
  · exact Or.inl fun tk => by
      simp [itemWith, h0, h1, h2, h3, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11]
  rcases g12 : (ParamLines.read pol).calls "callH" (some callHIfNone) with _ | a12
  · exact Or.inl fun tk => by
      simp [itemWith, h0, h1, h2, h3, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12]
  rcases gS : (ParamLines.read pol).lastWords with _ | S
  · exact Or.inl fun tk => by
      simp [itemWith, h0, h1, h2, h3, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, gS]
  refine Or.inr ⟨Fmt.cat [word32 0x4D363100, ⟨version.toArray⟩, a1, a2, a3, a4, a5, a6, a7, a8, a9,
    a10, a11, a12], word32 0 ++ S, ?_, fun D => ?_⟩
  · rw [ByteArray.size_append, size_word32, size_lastWords gS]
  · have ecat : Fmt.cat [word32 0x4D363100, ⟨version.toArray⟩, a1, a2, a3, a4, a5, a6, a7, a8, a9,
        a10, a11, a12, D, word32 0, S] =
        Fmt.cat [word32 0x4D363100, ⟨version.toArray⟩, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
          a11, a12] ++ (D ++ (word32 0 ++ S)) := by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.append_assoc, ByteArray.append_empty]
    simp only [itemWith, Option.bind_eq_bind, h0, h1, h2, h3, hc, g1, g2, g3, g4, g5, g6, g7, g8,
      g9, g10, g11, g12, gS, Option.bind_some, Bool.false_eq_true, if_false, ecat]
    generalize Fmt.cat [word32 0x4D363100, ⟨version.toArray⟩, a1, a2, a3, a4, a5, a6, a7, a8, a9,
      a10, a11, a12] ++ (D ++ (word32 0 ++ S)) = w
    rfl

/-! ## The two steps of the request's stage -/

/-- For two requests of one length the steps "form the item" and "compare it with the public
part" give the same: they return at both, or refuse at both in the same way. The term is the body
of `itemStep` (OnBytes/K/ServedFree.lean), which writes out two steps of `requestFound`
(OnBytes/K/Served.lean). -/
theorem itemStep_free (X : Public) (pol KL req req' : ByteArray) (h : req.size = req'.size) :
    (named (match requestItem pol KL req with
      | some w => pure w
      | none => throw "internal-request-item") >>= fun item => named (statementHeld X item)) =
    (named (match requestItem pol KL req' with
      | some w => pure w
      | none => throw "internal-request-item") >>= fun item => named (statementHeld X item)) := by
  have hs := isSome_olderTK h
  rw [requestItem_eq_itemWith, requestItem_eq_itemWith, h]
  rcases hd : secondHashFunctionTree req with _ | D <;> rcases hd' : secondHashFunctionTree req' with _ | D'
  · rfl
  · rw [hd, hd'] at hs
    simp at hs
  · rw [hd, hd'] at hs
    simp at hs
  · rcases itemWith_shape pol KL req'.size with hn | ⟨P, S, hS, hP⟩
    · rw [hn, hn]
    · rw [hP, hP]
      have hD := size_olderTK hd
      have hD' := size_olderTK hd'
      have e : (P ++ (D ++ S)).size = (P ++ (D' ++ S)).size := by
        simp only [ByteArray.size_append, hD, hD']
      rw [e]
      by_cases hc : ((P ++ (D' ++ S)).size == 708) = true
      · rw [if_pos hc, if_pos hc]
        have hP652 : P.size = 652 := by
          have h708 := beq_iff_eq.1 hc
          simp only [ByteArray.size_append, hD', hS] at h708
          omega
        have key := statementHeld_congr X (P ++ (D ++ S)) (P ++ (D' ++ S)) e
          (fun i n hi => wordsAt_front P _ _ i n (by omega))
          (fun i n hi => wordsAt_back P D D' S (by omega) i n (by omega))
        show named (statementHeld X (P ++ (D ++ S))) = named (statementHeld X (P ++ (D' ++ S)))
        rw [key]
      · rw [if_neg hc, if_neg hc]

end OnBytes.K
