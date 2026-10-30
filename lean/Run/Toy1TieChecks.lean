-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Toy1TieChecks.lean: under the hypotheses below, the checks that the compiled verifier forms
from a parser's openings are the list `checksOf` of Run/Toy1TieTree.lean; and a small toy of this
library's own meets that file's hypothesis on how a leaf's symbol is spelled. (`checksOf`,
Run/Toy1TieTree.lean: the checks that a parser's opening calls for, position by position.)

Definitions, statements as theorems, and proofs. The file is about openings of Merkle trees. The
compiled verifier is `verifyOneProtocol` (Compile/Batch/Verifier.lean): a computation that queries oracles
and accepts or rejects one argument string of a protocol. A check (`Check`, in that file) is the
data of one test of an opened leaf: the leaf's input, the leaf's number, a path, the root, and the
tree's depth. The verifier forms its checks by `checksComp`, which goes over all 2^a numbers of a
tree of depth a; this is so for the trees over the prover's messages. A parser's opening (`OpenB`,
Run/ParseBS.lean) is what a reader of a proof file holds of the opening of one tree; `OpenB.at`
makes of it the typed opening at a position, or none. A spelling (`PageD`, Run/CodingFn.lean) says
what is hashed for typed data; its field `leaf` gives, for a symbol, what stands in the tree's
place of the leaf's label (see `Fmt.leafPlace`), the number that the hash call takes as its index,
and the first bytes of the leaf's hash call.

Sources. The leaf's label (Fmt.leafPlace) was written against the format page
(docs/format/FORMAT.md, R2.1); this file has not been held against the page as it ships, and may
differ from it.



1. What the file contains. `sy1` (a definition), `colBytes3` (a lemma on the bytes of a column of
three words): the small toy's symbols and columns (the toy: Run/ToyQ.lean, Run/ParseToy1.lean). The
small toy is an example protocol of three rounds (`QT`). In round 1 the prover sends one oracle of
16 symbols, of three 64-bit words each; its Merkle tree has depth 4.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   Generic (any round r, any ambient interface L). `checksComp_of`, `checksComp_at`.
   At the small toy.
     `toy_leaf`: for x below 2^4 and a column of three words, the toy's spelling `PD.leaf` of the
       symbol sy1 x col is (Fmt.leafPlace 0 3 5: tree 0, three words, a salt of five words;
       2^4 + x; the column of three words with its empty fill). This is the hypothesis `hleaf` of
       `forestV_checksOf` and `forestV_reader`.
     `toy_checks`: `checksComp_at` at the toy's terms; its doc comment lists them.
     `toy_forest`: `forestV_reader` at the toy: if the values of O, the run's value and the sent
       root have 32 bytes each, then on what the page's reader (`Fmt.readOpeningW`) returns for the
       toy's tree, `forestV` at famOf O PD 2 on `checksOf` = decide (the reader's root = the sent
       root).

4. What is not claimed.
   This file does not claim that the verifier's run at the toy reaches exactly the call of
   `checksComp` that `toy_checks` names, with isRead "the number is listed". The terms were written
   after a reading of the verifier's definition, and no theorem here unfolds `Toy1.V`.
   Nothing on the chain's queries, on the decision, or on refusals of a reader.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.Toy1TieTree
import Run.ParseToy1
import Fmt.Rules1Laws

namespace Run.TieTree
open Iop Rom Compile Compile.Batch Octopus Run.WalkTie

/-! ### A list of numbers in a row, and a table with increasing keys -/

theorem lookup_none_of_lt {β : Type} :
    ∀ (es : List (ℕ × β)) (s : ℕ), (∀ e ∈ es, s < e.1) → es.lookup s = none
  | [], _, _ => rfl
  | (k, v) :: es, s, h => by
    have hk : s < k := h (k, v) (by simp)
    rw [List.lookup_cons, show (s == k) = false from by simp; omega]
    exact lookup_none_of_lt es s fun e he => h e (by simp [he])

theorem filterMap_lookup {β γ : Type} (mk : ℕ → β → γ) :
    ∀ (n s : ℕ) (es : List (ℕ × β)), (es.map Prod.fst).Pairwise (· < ·) →
      (∀ e ∈ es, s ≤ e.1 ∧ e.1 < s + n) →
      (List.range' s n).filterMap (fun j => (es.lookup j).map (mk j)) = es.map fun e => mk e.1 e.2
  | 0, s, es, _, hb => by
    cases es with
    | nil => rfl
    | cons e es => exact absurd (hb e (by simp)) (by omega)
  | n + 1, s, [], _, _ => by
    rw [List.filterMap_eq_nil_iff.2 (fun j _ => by simp)]
    rfl
  | n + 1, s, (k, v) :: es, hp, hb => by
    have hk := hb (k, v) (by simp)
    have hp' : (es.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.1 hp).2
    have hgt : ∀ e ∈ es, k < e.1 := fun e he =>
      (List.pairwise_cons.1 hp).1 e.1 (List.mem_map_of_mem he)
    rw [List.range'_succ, List.filterMap_cons]
    by_cases e : k = s
    · subst e
      have h1 : ((k, v) :: es).lookup k = some v := by simp
      rw [h1]
      simp only [Option.map_some, List.map_cons]
      congr 1
      rw [← filterMap_lookup mk n (k + 1) es hp' fun e he =>
          ⟨hgt e he, by have := (hb e (by simp [he])).2; omega⟩]
      refine List.filterMap_congr fun j hj => ?_
      have hj' : k + 1 ≤ j := (List.mem_range'_1.1 hj).1
      rw [List.lookup_cons, show (j == k) = false from by simp; omega]
    · have h1 : ((k, v) :: es).lookup s = none := lookup_none_of_lt _ s fun e he => by
        rcases List.mem_cons.1 he with rfl | he
        · exact lt_of_le_of_ne hk.1 (Ne.symm e)
        · exact lt_of_le_of_lt hk.1 (hgt _ he)
      rw [h1]
      simp only [Option.map_none]
      exact filterMap_lookup mk n (s + 1) ((k, v) :: es) hp fun e' he' => by
        have := hb e' he'
        rcases List.mem_cons.1 he' with rfl | he''
        · exact ⟨Nat.succ_le_of_lt (lt_of_le_of_ne hk.1 (Ne.symm e)), by omega⟩
        · exact ⟨Nat.succ_le_of_lt (lt_of_le_of_lt hk.1 (hgt _ he'')), by omega⟩

theorem lookup_isSome_of_mem {β : Type} :
    ∀ (es : List (ℕ × β)) (s : ℕ), s ∈ es.map Prod.fst → ∃ v, es.lookup s = some v ∧ (s, v) ∈ es
  | (k, v) :: es, s, h => by
    by_cases e : s = k
    · subst e
      exact ⟨v, by simp, by simp⟩
    · have h' : s ∈ es.map Prod.fst := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h e
        · exact h
      obtain ⟨w, h1, h2⟩ := lookup_isSome_of_mem es s h'
      exact ⟨w, by rw [List.lookup_cons, show (s == k) = false from by simpa using e]; exact h1,
        by simp [h2]⟩

theorem lookup_none_of_not_mem {β : Type} :
    ∀ (es : List (ℕ × β)) (s : ℕ), s ∉ es.map Prod.fst → es.lookup s = none
  | [], _, _ => rfl
  | (k, v) :: es, s, h => by
    have h1 : s ≠ k := fun e => h (by simp [e])
    have h2 : s ∉ es.map Prod.fst := fun e =>
      h (by simp only [List.map_cons, List.mem_cons]; exact Or.inr e)
    rw [List.lookup_cons, show (s == k) = false from by simpa using h1]
    exact lookup_none_of_not_mem es s h2

/-! ### The verifier's checks at a parser's openings -/

section
variable {I X : Type} {L : BatchProtocol I X} {r : Round}

/-- The verifier's list of checks, if at every number of the list it is known what happens: every j
in js is the number of a position p (`posAt j`), and either p is read, `f p` is an opening, the
table es has an entry e at j, and the check formed from that opening is `mk j e`; or p is not read
and es has no entry at j. -/
theorem checksComp_of {β : Type} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig 256)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening 256 (r.Sym p)))
    (es : List (ℕ × β)) (mk : ℕ → β → Check 256 L) :
    ∀ js : List ℕ,
      (∀ j ∈ js, ∃ p,
        posAt j = some p ∧
        ((isRead p = true ∧
            ∃ op e,
              f p = some op ∧
              es.lookup j = some e ∧
              (⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩ : Check 256 L) = mk j e) ∨
          (isRead p = false ∧ es.lookup j = none))) →
      checksComp posAt depth emb rt isRead f js =
        some (js.filterMap fun j => (es.lookup j).map (mk j))
  | [], _ => rfl
  | j :: js, h => by
    have ih := checksComp_of posAt depth emb rt isRead f es mk js fun i hi => h i (by simp [hi])
    obtain ⟨p, hp, hc⟩ := h j (by simp)
    rw [checksComp, List.filterMap_cons]
    simp only [hp]
    rcases hc with ⟨hr, op, e, hf, hl, hm⟩ | ⟨hr, hl⟩
    · simp only [hr, if_true, hf, ih, hl, Option.map_some, hm]
    · simp only [hr, Bool.false_eq_true, if_false, ih, hl, Option.map_none]

/-- The checks that the verifier forms from a parser's openings are `checksOf`, under these
hypotheses, where place p is the number of a position p and a is Ob.a. `hok`: Ob passes the
parser's own test. `hpos`: every number below 2^a is a position's, and posAt gives that position.
`hread`: a position is read exactly if its number is listed. `hsym`: sym turns each of the
opening's columns into a symbol whose body is sy's. -/
theorem checksComp_at {tg : Tag} (posAt : ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : Dig 256) (isRead : r.Pos → Bool) (place : r.Pos → ℕ)
    (sym : (p : r.Pos) → List UInt64 → Option (r.Sym p))
    (sy : ℕ → List UInt64 → SymAny (shapeOf L tg)) (run : ByteArray) (Ob : OpenB) (sb W : ℕ)
    (hok : Ob.ok sb W = true) (hpos : ∀ j, j < 2 ^ Ob.a → ∃ p, posAt j = some p ∧ place p = j)
    (hread : ∀ p, isRead p = decide (place p ∈ Ob.idx))
    (hsym : ∀ p col,
      col ∈ Ob.cols → ∃ y, sym p col = some y ∧ emb p y = some (.inr ⟨tg, sy (place p) col⟩)) :
    checksComp posAt Ob.a emb rt isRead
        (fun p => Ob.at (sym p) run (place p)) (List.range (2 ^ Ob.a)) =
      some (checksOf sy run rt Ob) := by
  obtain ⟨hc, hs, -, -, -⟩ := ok_spec Ob sb W hok
  obtain ⟨hp, hb, hcw⟩ := ok_list Ob sb W hok
  have hpl : Ob.paths.length = Ob.idx.length := length_fill _ _ _
  have hkeys : (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))).map Prod.fst = Ob.idx :=
    List.map_fst_zip (by simp only [List.length_zip]; omega)
  rw [checksComp_of posAt Ob.a emb rt isRead _ (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths)))
      (fun j e =>
        (⟨⟨some (.inr ⟨tg, sy j e.1⟩), leafSalt run e.2.1⟩, j, e.2.2, rt, Ob.a⟩ : Check 256 L))]
  · rw [List.range_eq_range',
      filterMap_lookup _ (2 ^ Ob.a) 0 _ (by rw [hkeys]; exact hp) fun e he =>
        ⟨Nat.zero_le _, by rw [Nat.zero_add]; exact hb _ (List.of_mem_zip he).1⟩]
    rfl
  · intro j hj
    obtain ⟨p, h1, h2⟩ := hpos j (List.mem_range.1 hj)
    refine ⟨p, h1, ?_⟩
    by_cases hm : j ∈ Ob.idx
    · left
      obtain ⟨v, hv, hmem⟩ := lookup_isSome_of_mem
        (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))) j (by rw [hkeys]; exact hm)
      obtain ⟨y, hy, he⟩ := hsym p v.1 (List.of_mem_zip (List.of_mem_zip hmem).2).1
      refine ⟨by rw [hread, h2]; simpa using hm, ⟨y, leafSalt run v.2.1, v.2.2⟩, v, ?_, hv, ?_⟩
      · unfold OpenB.at OpenB.atP
        rw [h2, hv]
        simp only [hy, Option.map_some]
      · simp only [he, h2]
    · right
      exact ⟨by rw [hread, h2]; simpa using hm,
        lookup_none_of_not_mem _ j (by rw [hkeys]; exact hm)⟩

end

/-! ### At the small toy -/

section
open Run.Toy1

/-- how a number and a column become a symbol of the toy's one oracle -/
def sy1 (x : ℕ) (col : List UInt64) : SymAny (shapeOf Lt .test) :=
  ⟨.inr (.inl ⟨x % 16, Nat.mod_lt _ (by decide)⟩), (col.getD 0 0, col.getD 1 0, col.getD 2 0)⟩

theorem colBytes3 (a b c : UInt64) :
    _root_.Fmt.colBytes [a, b, c] ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen 3 40) =
      _root_.Fmt.ext (a, b, c) := by
  apply ByteArray.ext
  simp [_root_.Fmt.colBytes, _root_.Fmt.cat, _root_.Fmt.ext, _root_.Fmt.zeroBytes,
    _root_.Fmt.fillLen, ByteArray.data_append]

/-- Under the hypotheses below, the toy spells a leaf as the page wants. -/
theorem toy_leaf (x : ℕ) (col : List UInt64) (hx : x < 2 ^ 4) (hc : col.length = 3) :
    PD.leaf (sy1 x col) =
      (_root_.Fmt.leafPlace 0 3 (40 / 8),
        2 ^ 4 + x,
        _root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen 3 40)) := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, col = [a, b, c] := by
    match col, hc with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  rw [colBytes3]
  show (_root_.Fmt.leafPlace 0 3 5, 16 + x % 16, extB (a, b, c)) = _
  rw [Nat.mod_eq_of_lt (by simpa using hx)]
  rfl

/-- `checksComp_at` at the toy's terms (the wire of round 1 with its proof of work, the embedding
of a symbol of round 1, the openings by the toy's typing), if Ob has the depth 4 (`ha`) and passes
the parser's own test (`hok`), and a position is read exactly if it is listed (`hread`). That the
verifier's run reaches this very call is not shown here. -/
theorem toy_checks (rt : Dig 256) (isRead : Fin 16 → Bool) (run : ByteArray) (Ob : OpenB)
    (ha : Ob.a = 4) (hok : Ob.ok 40 3 = true)
    (hread : ∀ p : Fin 16, isRead p = decide (p.val ∈ Ob.idx)) :
    checksComp (L := Lt) (r := r1.grind ℕ 8) (w1.grindLocal Dn 8).posAtJ 4
        (fun p a => some (.inr ⟨Tag.test, ⟨.inr (.inl p), a⟩⟩)) rt isRead
        (fun p => Ob.at (T.sym (.inr (.inl p))) run (T.place (.inr (.inl p))).2)
        (List.range (2 ^ 4)) =
      some (checksOf sy1 run rt Ob) := by
  have h := checksComp_at (L := Lt) (r := r1.grind ℕ 8) (w1.grindLocal Dn 8).posAtJ
    (fun p a => some (.inr ⟨Tag.test, ⟨.inr (.inl p), a⟩⟩)) rt isRead (fun p : Fin 16 => p.val)
    (fun p => T.sym (.inr (.inl p))) sy1 run Ob 40 3 hok ?_ hread ?_
  · rw [ha] at h
    exact h
  · intro j hj
    rw [ha] at hj
    exact ⟨⟨j, hj⟩, dif_pos hj, rfl⟩
  · intro p col hc
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, col = [a, b, c] := by
      have h3 := (ok_list Ob 40 3 hok).2.2 col hc
      match col, h3 with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    refine ⟨(a, b, c), rfl, ?_⟩
    have hp : (⟨p.val % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16) = p :=
      Fin.ext (Nat.mod_eq_of_lt p.isLt)
    unfold sy1
    rw [hp]
    rfl

/-- `forestV_reader` at the toy. -/
theorem toy_forest (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (run root : ByteArray) (hr : run.size = 32) (hroot : root.size = 32) (xs : List ℕ)
    (b : ByteArray) (i : ℕ) (o : _root_.Fmt.OpenOut)
    (e : _root_.Fmt.readOpeningW
        (m := Id) (_root_.Fmt.HO O) PD.cfg .two 40 ⟨4, 3, false, 0⟩ run xs b i = some o) :
    forestV 2 (famOf O PD 2) 4 (bytesToDig root)
        (checksOf sy1 run (bytesToDig root) ⟨4, xs, o.cols, o.salts, o.given⟩) =
      decide (o.root = root) :=
  forestV_reader O PD 2 hO sy1 run root hr hroot .two 40 4 3 0 xs b i o e toy_leaf

end

end Run.TieTree
