-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Item/HeldOfParts.lean: the item "request" is made and its comparison with the public
part accepts, from sixteen facts on two readers of one parameter file. General laws: nothing is
evaluated, and no hash.

The verifier's description forms the item "request" (177 words) from the parameter file, the scale
file and the request, and compares it with the public part (`Verify.statementHeld`,
OnBytes/Model/VerifyStatement.lean). Its text names `Fmt.requestItem o`; at the format's second
hash function that is `Proof.requestItem` (OnBytes/Proof/RequestItem.lean) on all files (`requestItem_eq`,
OnBytes/Tie/Decl/RequestItemLaw.lean). This file's statements speak of `OnBytes.K.itemWith`
(OnBytes/K/ServedFreeItem.lean), which is `requestItem` with the request's length and digest given
as arguments (`requestItem_eq_itemWith`). The item's reader is `ParamLines`; the public part's is
`PolScan`.

Main names.
* `Parts X L sz`: what is asked of the lines L, the public part X and the request's length sz, in
  sixteen fields. The form that `requestItem` asks (the lines version, prof and NE; the length); the
  two readers agree on the 97 named numbers, on the four tables' digests and on the last five words;
  the three digests of call lines in the item are those in the public part. A list of premises under
  one name: it states no goal.
* `held_of_parts`: under `Parts`, where the scale file's tree hash returns, at every 32 bytes r in
  the place of the request's digest the item is made and the comparison accepts.
* `none_of_length`: under `Parts`, at another length of the request no item is made.
* `clauses_of_held`, `word_of_names`: the other direction. What an accept of the comparison says,
  clause by clause: every word that it reads is the public part's. So the comparison can refuse.

Limits. Implications: `Parts` is shown at no file here. At the format's second hash function
(`OnBytes.secondHashFunction`), of which only "32 bytes" is used. Nothing on the other tests on an instance. No
soundness is claimed.
-/
import Johnson.AtFull.Item.Windows
import Johnson.AtFull.Item.Names

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Item
open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Verify OnBytes.K

/-- All values of a list in which none is missing. -/
theorem allOfFrom_somes {α : Type} : ∀ (l seen : List α),
    Params.allOfFrom seen (l.map some) = some (seen.reverse ++ l)
  | [], seen => by simp [Params.allOfFrom]
  | a :: l, seen => by
    rw [List.map_cons]
    show Params.allOfFrom (a :: seen) (l.map some) = _
    rw [allOfFrom_somes l (a :: seen)]
    simp

/-- Where no entry is missing, `Params.allOf` returns the entries. -/
theorem allOf_somes {α : Type} (l : List α) : Params.allOf (l.map some) = some l := by
  unfold Params.allOf
  rw [allOfFrom_somes]
  rfl

/-- What "all values" returns is as long as the list. -/
theorem allOfFrom_length {α : Type} : ∀ (l : List (Option α)) (seen r : List α),
    Params.allOfFrom seen l = some r → r.length = seen.length + l.length
  | [], seen, r, h => by
    cases h
    simp
  | none :: _, _, _, h => by cases h
  | some a :: l, seen, r, h => by
    have := allOfFrom_length l (a :: seen) r h
    simp only [List.length_cons] at this ⊢
    omega

/-- The words of a list of names, where the lines' reader gives the scan's values. -/
theorem words_of_values {L : ParamLines} {P : PolScan} {names : String}
    (h : ∀ n ∈ names.splitOn " ", L.value n = some (P.value n)) :
    L.words names = some (Fmt.cat (((names.splitOn " ").map P.value).map word32)) := by
  unfold ParamLines.words
  have e : (names.splitOn " ").map L.value = ((names.splitOn " ").map P.value).map some := by
    rw [List.map_map]
    exact List.map_congr_left h
  rw [e, allOf_somes]
  rfl

/-- Eight words have 32 bytes. -/
theorem size_eight {L : ParamLines} {name : String} {d : ByteArray} (h : L.eight name = some d) :
    d.size = 32 := by
  unfold ParamLines.eight at h
  rcases hl : Params.allOf ((List.range 8).map fun i => L.value (name ++ toString i)) with _ | l
  · rw [hl] at h
    cases h
  · rw [hl] at h
    cases h
    have := allOfFrom_length _ [] l hl
    rw [size_words, this]
    rfl

/-- A digest of call lines has 32 bytes. -/
theorem size_calls {L : ParamLines} {name : String} {ifNone : Option String} {d : ByteArray}
    (h : L.calls name ifNone = some d) : d.size = 32 := by
  unfold ParamLines.calls at h
  dsimp only at h
  split at h
  · rw [← Option.some.inj h]
    exact size_olderK _ _
  · cases ifNone with
    | none => exact absurd h (by simp)
    | some s =>
      rw [← Option.some.inj h]
      exact size_olderK _ _

/-- The last five words of the item, as the public part has them: the security target, and four
numbers of the weight table. -/
def lastFive (X : Public) : List Nat :=
  [X.P.hb, X.P.lkW, X.P.frame.tableRowsLog, X.P.frame.tableLogN, X.P.frame.tableRandom]

/-- What is asked of the parameter file's lines L, the public part X and the request's length sz. A
list of premises under one name: it states no goal. -/
structure Parts (X : Public) (L : ParamLines) (sz : Nat) : Prop where
  version : ∃ v, (L.values "version").bind (·.head?) = some v ∧ v.length = 4
  prof : L.value "prof" = some 20
  ne : ∃ n, L.value "NE" = some n ∧ n ≠ 0
  lt : ∃ t, L.value "lt" = some t ∧ sz = 4 * (2 ^ t + 2)
  n2 : ∀ n ∈ names2.splitOn " ", L.value n = some (X.P.value n)
  n37 : ∀ n ∈ names37.splitOn " ", L.value n = some (X.P.value n)
  n103 : ∀ n ∈ names103.splitOn " ", L.value n = some (X.P.value n)
  n130 : ∀ n ∈ names130.splitOn " ", L.value n = some (X.P.value n)
  silu : ∃ d, L.eight "tsilu" = some d ∧ X.P.tableExpected .silu = some d
  sigmoid : ∃ d, L.eight "tsig" = some d ∧ X.P.tableExpected .sigmoid = some d
  rope : ∃ d, L.eight "trope" = some d ∧ X.P.tableExpected .rope = some d
  exp : ∃ d, L.eight "texp" = some d ∧ X.P.tableExpected .exp = some d
  call : L.calls "call" = some X.digests.hCalls
  callA : L.calls "callA" = some X.digests.hCallsA
  callH : L.calls "callH" (some callHIfNone) = some X.digests.hCallsH
  last : L.lastWords = some (Fmt.cat ((lastFive X).map word32))

/-- An option of a string passes the test == with itself. -/
theorem some_beq_self (a : ByteArray) : (some a == some a) = true := by
  show (a == a) = true
  exact Fmt.bytes_beq_self a

/-- **The comparison accepts a string of seventeen pieces**: the named numbers as the scan has them,
the tables' digests as the scan expects them, the public part's own three digests and last five
words, and any strings of the right lengths at the five places that the comparison does not read. -/
theorem held_of_pieces (X : Public) (p0 pv d1 d2 d3 d4 s r pz : ByteArray)
    (z0 : p0.size = 4) (zv : pv.size = 4) (z4 : d1.size = 32) (z5 : d2.size = 32)
    (z6 : d3.size = 32) (z9 : d4.size = 32) (z7 : s.size = 32) (hr : r.size = 32)
    (z14 : pz.size = 4) (z2 : X.digests.hCalls.size = 32) (z10 : X.digests.hCallsA.size = 32)
    (z12 : X.digests.hCallsH.size = 32)
    (x4 : X.P.tableExpected .silu = some d1) (x5 : X.P.tableExpected .sigmoid = some d2)
    (x6 : X.P.tableExpected .rope = some d3) (x9 : X.P.tableExpected .exp = some d4) :
    (Fmt.cat
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz,
       (Fmt.cat ((lastFive X).map word32))]).size = 708 ∧
    statementHeld X (Fmt.cat
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz,
       (Fmt.cat ((lastFive X).map word32))]) = .ok () := by
  obtain ⟨f2, f37, f103, f130⟩ := namesFit
  have z1 : (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)).size = 108 := by
    rw [size_words, List.length_map, f2]
  have z3 : (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)).size = 136 := by
    rw [size_words, List.length_map, f37]
  have z8 : (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)).size = 44 := by
    rw [size_words, List.length_map, f103]
  have z11 : (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)).size = 100 := by
    rw [size_words, List.length_map, f130]
  have z15 : (Fmt.cat ((lastFive X).map word32)).size = 20 := by
    rw [size_words]
    rfl
  have ze : ByteArray.empty.size = 0 := rfl
  have c1 : (Fmt.cat
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz,
       (Fmt.cat ((lastFive X).map word32))]).size = 708 := by
    simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6, z7,
      z8, z9, z10, z11, z12, hr, z14, z15, ze]
  have c2 := namesHeld_cat X.P
      [p0, pv]
      [X.digests.hCalls, (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2,
       d3, s, (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4,
       X.digests.hCallsA, (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)),
       X.digests.hCallsH, r, pz, (Fmt.cat ((lastFive X).map word32))]
      2 names2 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, ze])
  have c3 := wordsAt_piece
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32))]
      X.digests.hCalls
      [(Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz,
       (Fmt.cat ((lastFive X).map word32))]
      29 8 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, ze]) z2
  have c4 := namesHeld_cat X.P
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls]
      [d1, d2, d3, s, (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4,
       X.digests.hCallsA, (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)),
       X.digests.hCallsH, r, pz, (Fmt.cat ((lastFive X).map word32))]
      37 names37 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, ze])
  have c5 := wordsAt_piece
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32))]
      d1
      [d2, d3, s, (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4,
       X.digests.hCallsA, (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)),
       X.digests.hCallsH, r, pz, (Fmt.cat ((lastFive X).map word32))]
      71 8 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, ze]) z4
  have c6 := wordsAt_piece
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1]
      d2
      [d3, s, (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4,
       X.digests.hCallsA, (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)),
       X.digests.hCallsH, r, pz, (Fmt.cat ((lastFive X).map word32))]
      79 8 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, ze]) z5
  have c7 := wordsAt_piece
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2]
      d3
      [s, (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz,
       (Fmt.cat ((lastFive X).map word32))]
      87 8 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, ze])
      z6
  have c8 := namesHeld_cat X.P
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s]
      [d4, X.digests.hCallsA, (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)),
       X.digests.hCallsH, r, pz, (Fmt.cat ((lastFive X).map word32))]
      103 names103 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6,
        z7, ze])
  have c9 := wordsAt_piece
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32))]
      d4
      [X.digests.hCallsA, (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)),
       X.digests.hCallsH, r, pz, (Fmt.cat ((lastFive X).map word32))]
      114 8 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6,
        z7, z8, ze]) z9
  have c10 := wordsAt_piece
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4]
      X.digests.hCallsA
      [(Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz,
       (Fmt.cat ((lastFive X).map word32))]
      122 8 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6,
        z7, z8, z9, ze]) z10
  have c11 := namesHeld_cat X.P
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA]
      [X.digests.hCallsH, r, pz, (Fmt.cat ((lastFive X).map word32))]
      130 names130 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6,
        z7, z8, z9, z10, ze])
  have c12 := wordsAt_piece
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32))]
      X.digests.hCallsH
      [r, pz, (Fmt.cat ((lastFive X).map word32))]
      155 8 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6,
        z7, z8, z9, z10, z11, ze]) z12
  have c13 := (wordsAt_cat
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz]
      (Fmt.cat ((lastFive X).map word32)) [] 172 0 1 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6,
        z7, z8, z9, z10, z11, z12, hr, z14, ze])
      (by rw [z15]; omega)).trans (wordsAt_words (lastFive X) 0 (by show 0 < 5; omega))
  have c14 := (wordsAt_cat
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz]
      (Fmt.cat ((lastFive X).map word32)) [] 172 1 1 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6,
        z7, z8, z9, z10, z11, z12, hr, z14, ze])
      (by rw [z15]; omega)).trans (wordsAt_words (lastFive X) 1 (by show 1 < 5; omega))
  have c15 := (wordsAt_cat
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz]
      (Fmt.cat ((lastFive X).map word32)) [] 172 2 1 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6,
        z7, z8, z9, z10, z11, z12, hr, z14, ze])
      (by rw [z15]; omega)).trans (wordsAt_words (lastFive X) 2 (by show 2 < 5; omega))
  have c16 := (wordsAt_cat
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz]
      (Fmt.cat ((lastFive X).map word32)) [] 172 3 1 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6,
        z7, z8, z9, z10, z11, z12, hr, z14, ze])
      (by rw [z15]; omega)).trans (wordsAt_words (lastFive X) 3 (by show 3 < 5; omega))
  have c17 := (wordsAt_cat
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz]
      (Fmt.cat ((lastFive X).map word32)) [] 172 4 1 (by
      simp only [Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, z0, zv, z1, z2, z3, z4, z5, z6,
        z7, z8, z9, z10, z11, z12, hr, z14, ze])
      (by rw [z15]; omega)).trans (wordsAt_words (lastFive X) 4 (by show 4 < 5; omega))
  simp only [List.cons_append, List.nil_append] at c2 c3 c4 c5 c6 c7 c8 c9 c10
  simp only [List.cons_append, List.nil_append] at c11 c12 c13 c14 c15 c16 c17
  refine ⟨c1, ?_⟩
  revert c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17
  generalize Fmt.cat
      [p0, pv, (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r, pz,
       (Fmt.cat ((lastFive X).map word32))] = w
  intro c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17
  have e13 : wordsAt w 172 1 = word32 X.P.hb := c13
  have e14 : wordsAt w 173 1 = word32 X.P.lkW := c14
  have e15 : wordsAt w 174 1 = word32 X.P.frame.tableRowsLog := c15
  have e16 : wordsAt w 175 1 = word32 X.P.frame.tableLogN := c16
  have e17 : wordsAt w 176 1 = word32 X.P.frame.tableRandom := c17
  unfold statementHeld tableWordsHeld
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, e13, e14, e15, e16, e17, x4, x5, x6,
    x9, some_beq_self, Fmt.bytes_beq_self, beq_self_eq_true, Bool.and_self, if_true]
  rfl

/-- **The item is made and the comparison accepts**, under `Parts`, where the scale file's tree hash
returns, at every 32 bytes in the place of the request's digest. -/
theorem held_of_parts {X : Public} {pol KL s r : ByteArray} {sz : Nat}
    (H : Parts X (ParamLines.read pol) sz) (hs : secondHashFunctionTree KL = some s) (hr : r.size = 32) :
    ∃ it, itemWith pol KL sz (some r) = some it ∧ statementHeld X it = .ok () := by
  obtain ⟨v, hv, hv4⟩ := H.version
  obtain ⟨ne, hne, hne0⟩ := H.ne
  obtain ⟨t, ht, hsz⟩ := H.lt
  obtain ⟨d1, g4, x4⟩ := H.silu
  obtain ⟨d2, g5, x5⟩ := H.sigmoid
  obtain ⟨d3, g6, x6⟩ := H.rope
  obtain ⟨d4, g9, x9⟩ := H.exp
  have zv : (⟨v.toArray⟩ : ByteArray).size = 4 := by
    show v.toArray.size = 4
    rw [List.size_toArray]
    exact hv4
  obtain ⟨c1, c2⟩ := held_of_pieces X (word32 0x4D363100) ⟨v.toArray⟩ d1 d2 d3 d4 s r (word32 0)
    (size_word32 _) zv (size_eight g4) (size_eight g5) (size_eight g6) (size_eight g9)
    (size_olderTK hs) hr (size_word32 _) (size_calls H.call) (size_calls H.callA)
    (size_calls H.callH) x4 x5 x6 x9
  have hc : (v.length != 4 || (20 : Nat) != 20 || ne == 0 || sz != 4 * (2 ^ t + 2)) = false := by
    rw [hv4, hsz]
    simp only [bne_self_eq_false, Bool.false_or, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
    exact hne0
  refine ⟨_, ?_, c2⟩
  unfold itemWith
  simp only [Option.bind_eq_bind, hv, H.prof, hne, ht, hc, words_of_values H.n2, H.call,
    words_of_values H.n37, g4, g5, g6, hs, words_of_values H.n103, g9, H.callA,
    words_of_values H.n130, H.callH, H.last, Option.bind_some, Bool.false_eq_true, if_false]
  clear c2
  revert c1
  generalize Fmt.cat
      [word32 0x4D363100, ⟨v.toArray⟩,
       (Fmt.cat (((names2.splitOn " ").map X.P.value).map word32)), X.digests.hCalls,
       (Fmt.cat (((names37.splitOn " ").map X.P.value).map word32)), d1, d2, d3, s,
       (Fmt.cat (((names103.splitOn " ").map X.P.value).map word32)), d4, X.digests.hCallsA,
       (Fmt.cat (((names130.splitOn " ").map X.P.value).map word32)), X.digests.hCallsH, r,
       word32 0, (Fmt.cat ((lastFive X).map word32))] = w
  intro c1
  show (if (w.size == 708) = true then some w else none) = some w
  rw [c1]
  rfl

/-- **At another length no item is made**, under `Parts`. -/
theorem none_of_length {X : Public} {pol KL : ByteArray} {sz sz' : Nat}
    (H : Parts X (ParamLines.read pol) sz) (h : sz' ≠ sz) (tk : Option ByteArray) :
    itemWith pol KL sz' tk = none := by
  obtain ⟨v, hv, -⟩ := H.version
  obtain ⟨ne, hne, -⟩ := H.ne
  obtain ⟨t, ht, hsz⟩ := H.lt
  have hc : (v.length != 4 || (20 : Nat) != 20 || ne == 0 || sz' != 4 * (2 ^ t + 2)) = true := by
    rw [← hsz, bne_iff_ne.2 h]
    simp
  unfold itemWith
  simp only [Option.bind_eq_bind, hv, H.prof, hne, ht, hc, Option.bind_some, if_true,
    Option.bind_none]

/-- An option that passes the test == with a string is that string. -/
theorem some_of_beq {a : Option ByteArray} {b : ByteArray} (h : (a == some b) = true) :
    a = some b := by
  cases a with
  | none => cases h
  | some x => exact congrArg some (Fmt.eq_of_bytes_beq x b h)

/-- **What an accept of the comparison says, clause by clause**: the string has 708 bytes, and every
word that the comparison reads is the public part's. So a string that parts from the public part in
one of these words is refused. -/
theorem clauses_of_held {X : Public} {it : ByteArray} (h : statementHeld X it = .ok ()) :
    it.size = 708 ∧ namesHeld X.P it 2 names2 = true ∧ wordsAt it 29 8 = X.digests.hCalls ∧
      namesHeld X.P it 37 names37 = true ∧ X.P.tableExpected .silu = some (wordsAt it 71 8) ∧
      X.P.tableExpected .sigmoid = some (wordsAt it 79 8) ∧
      X.P.tableExpected .rope = some (wordsAt it 87 8) ∧
      namesHeld X.P it 103 names103 = true ∧ X.P.tableExpected .exp = some (wordsAt it 114 8) ∧
      wordsAt it 122 8 = X.digests.hCallsA ∧ namesHeld X.P it 130 names130 = true ∧
      wordsAt it 155 8 = X.digests.hCallsH ∧ wordsAt it 172 1 = word32 X.P.hb ∧
      wordsAt it 173 1 = word32 X.P.lkW ∧ wordsAt it 174 1 = word32 X.P.frame.tableRowsLog ∧
      wordsAt it 175 1 = word32 X.P.frame.tableLogN ∧
      wordsAt it 176 1 = word32 X.P.frame.tableRandom := by
  unfold statementHeld tableWordsHeld at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩,
      c15⟩, c16⟩, c17⟩ := hc
    exact ⟨eq_of_beq c1, c2, Fmt.eq_of_bytes_beq _ _ c3, c4, some_of_beq c5, some_of_beq c6,
      some_of_beq c7, c8, some_of_beq c9, Fmt.eq_of_bytes_beq _ _ c10, c11,
      Fmt.eq_of_bytes_beq _ _ c12, Fmt.eq_of_bytes_beq _ _ c13, Fmt.eq_of_bytes_beq _ _ c14,
      Fmt.eq_of_bytes_beq _ _ c15, Fmt.eq_of_bytes_beq _ _ c16, Fmt.eq_of_bytes_beq _ _ c17⟩
  · cases h

/-- Where the comparison of a list of names accepts, the word at a name's place is the scan's value
of that name, as one 32-bit word (`word32` takes it modulo 2 ^ 32). -/
theorem word_of_names {P : PolScan} {it : ByteArray} {first : Nat} {names : String}
    {l : List String} (hl : names.splitOn " " = l) (h : namesHeld P it first names = true)
    (k : Nat) (hk : k < l.length) : wordsAt it (first + k) 1 = word32 (P.value l[k]) := by
  unfold namesHeld at h
  rw [hl, List.all_eq_true] at h
  exact Fmt.eq_of_bytes_beq _ _ (h (l[k], k) (by
    rw [List.mk_mem_zipIdx_iff_getElem?]
    exact List.getElem?_eq_getElem hk))

end Johnson.AtFull.Item

#print axioms Johnson.AtFull.Item.allOfFrom_somes
#print axioms Johnson.AtFull.Item.allOf_somes
#print axioms Johnson.AtFull.Item.allOfFrom_length
#print axioms Johnson.AtFull.Item.words_of_values
#print axioms Johnson.AtFull.Item.size_eight
#print axioms Johnson.AtFull.Item.size_calls
#print axioms Johnson.AtFull.Item.some_beq_self
#print axioms Johnson.AtFull.Item.held_of_pieces
#print axioms Johnson.AtFull.Item.held_of_parts
#print axioms Johnson.AtFull.Item.none_of_length
#print axioms Johnson.AtFull.Item.some_of_beq
#print axioms Johnson.AtFull.Item.clauses_of_held
#print axioms Johnson.AtFull.Item.word_of_names
#print axioms Johnson.AtFull.Item.lastFive
#print axioms Johnson.AtFull.Item.Parts
#print axioms Johnson.AtFull.Item.Parts.mk
#print axioms Johnson.AtFull.Item.Parts.version
#print axioms Johnson.AtFull.Item.Parts.prof
#print axioms Johnson.AtFull.Item.Parts.ne
#print axioms Johnson.AtFull.Item.Parts.lt
#print axioms Johnson.AtFull.Item.Parts.n2
#print axioms Johnson.AtFull.Item.Parts.n37
#print axioms Johnson.AtFull.Item.Parts.n103
#print axioms Johnson.AtFull.Item.Parts.n130
#print axioms Johnson.AtFull.Item.Parts.silu
#print axioms Johnson.AtFull.Item.Parts.sigmoid
#print axioms Johnson.AtFull.Item.Parts.rope
#print axioms Johnson.AtFull.Item.Parts.exp
#print axioms Johnson.AtFull.Item.Parts.call
#print axioms Johnson.AtFull.Item.Parts.callA
#print axioms Johnson.AtFull.Item.Parts.callH
#print axioms Johnson.AtFull.Item.Parts.last
