-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/OwesOf.lean: THE RECORDS OF WHAT THE PROVER DOES NOT MAKE (WholeOwes,
OnBytes/Prover/Print/Owed.lean; EntryOwes, Johnson/Prover/Print/OwedEntry.lean) FROM LESS: the
interactive verifier's accept, a record on the strategy, and a condition on each table with its
leaves' salts. For all data.

Main names.
  StratOwes ... bc π   ON THE STRATEGY ALONE: it has sent the coins' run2 and run3; the words of
    each round's plain part and of each opened column are below the prime.
  owes_key     at the key file's test on the silent rounds (silK): StratOwes · the string holds the
    transcript's plain parts · the accept · TableOwes at the table, the outer tree built by the
    prover's builder over leaves with these salts: THEN WholeOwes, and the front bears the record's
    answers and the copy's number 0.
  owes_proof   the like at the proof file's test (silP); the copy's number below 2^64 is asked.
  owes_entry   EntryOwes from TableOwes at both tables.

By: key_front, proof_front (OnBytes/Prover/Print/AcceptGives.lean) · outer_one, kept_inp, kept_path
(OnBytes/Prover/Print/OuterKept.lean) · okE_trAns (Johnson/Prover/Print/Member.lean).

Does not show: that a strategy meets StratOwes, that a table meets TableOwes, that a transcript is
accepted. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.OwedEntry
import Johnson.Prover.Print.Member
import OnBytes.Prover.Print.AcceptGives
import OnBytes.Prover.Print.OuterKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open Rom
open _root_.Run (bytesToBits)
open _root_.Run.PQ (View SgX CK XO weX)
open Compile.Joined (JoinMsg)
open _root_.Compile (pathOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃)
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open OnBytes.Prover OnBytes.Prover.Print

section Whole
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (run : Xi → View → View → View → Bool) {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- What is asked of the strategy alone, at a whole file. -/
structure StratOwes (bc : ByteCoins L)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) : Prop where
  run2 : (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.run = bc.run2
  run3 : (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 = bc.run3
  words₁ : WordsP C D.ds₁ (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2
  words₂ : WordsP C D.ds₂ (pls₂ (wholeDesc C D tF tJ t3 silent run) π).2
  words₃ : WordsP C D.ds₃ (pls₃ (wholeDesc C D tF tJ t3 silent run) π).2
  cols₁ : ∀ q op, op₁ C D tF tJ t3 silent run π q = some op →
    ∀ w ∈ colOfSym C D.ds₁ q op.sym, Carrier.okF w
  cols₂ : ∀ q op, op₂ C D tF tJ t3 silent run π q = some op →
    ∀ w ∈ colOfSym C D.ds₂ q op.sym, Carrier.okF w
  cols₃ : ∀ q op, op₃ C D tF tJ t3 silent run π q = some op →
    ∀ w ∈ colOfSym C D.ds₃ q op.sym, Carrier.okF w

variable {C D tF tJ t3 silent run}

/-- the record, its clauses on the fronts and on the outer tree given -/
theorem StratOwes.whole {bc : ByteCoins L}
    {π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch}
    (h : StratOwes C D tF tJ t3 silent run bc π) (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str) (K : ℕ)
    (g : Fam (typedOracleFamily 256 K L)) (inp : ℕ → LeafIn L)
    (sl : ℕ → Bits) (cfg : ByteArray) (τ : Tr (wholeDesc C D tF tJ t3 silent run).batch.loc.shape)
    (l : List (UInt64 × UInt64 × UInt64))
    (hans : (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers = l.map OnBytes.E.ofTriple)
    (hl : ∀ u ∈ l, Carrier.okE u) (hn : l.length < 2 ^ 64)
    (hag : (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.answers =
      (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers)
    (hc : (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.copy < 2 ^ 64)
    (hs : ∀ j, (inp j).salt = sl j) (ha : D.a < 2 ^ 64)
    (ht : TableOwes cfg y sl fun _ => True) :
    WholeOwes C D tF tJ t3 silent run x y (fun _ => (treeO (K := K) D.a inp).det g) bc cfg π τ where
  run2 := h.run2
  run3 := h.run3
  again := hag
  answers := fun e he => by
    rw [hans] at he
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 he
    exact hl u hu
  count := by rw [hans, List.length_map]; exact hn
  copy := hc
  words₁ := h.words₁
  words₂ := h.words₂
  words₃ := h.words₃
  cols₁ := h.cols₁
  cols₂ := h.cols₂
  cols₃ := h.cols₃
  outer := fun p _ => outer_one g D.a inp cfg y sl (fun _ => True) hs ha ht p trivial

end Whole

section Files
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {v lg s : ℕ} {I X : Type} {L : BatchProtocolWithLeafBody I X}
  (K : ℕ) (g : Fam (typedOracleFamily 256 K L)) (inp : ℕ → LeafIn L) (sl : ℕ → Bits) (cfg : ByteArray)
  (bc : ByteCoins L) (y : (oneExternalString (2 ^ D.a) SgX).Str)

/-- **The key file.** -/
theorem owes_key (run : RecP NZ v lg s → View → View → View → Bool) (rec : RecP NZ v lg s)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silK run).batch)
    (τ : Tr (wholeDesc C D tF tJ t3 silK run).batch.loc.shape)
    (h : StratOwes C D tF tJ t3 silK run bc π) (hp : π.plains = τ.plains)
    (hacc : (wholeDesc C D tF tJ t3 silK run).batch.loc.accept rec y τ = true)
    (hv : 2 ^ v * s < 2 ^ 64) (hs : ∀ j, (inp j).salt = sl j) (ha : D.a < 2 ^ 64)
    (ht : TableOwes cfg y sl fun _ => True) :
    WholeOwes C D tF tJ t3 silK run rec y (fun _ => (treeO (K := K) D.a inp).det g) bc cfg π τ ∧
      (pls₁ (wholeDesc C D tF tJ t3 silK run) π).1.answers =
        (trAns rec.2).map OnBytes.E.ofTriple ∧
      (pls₁ (wholeDesc C D tF tJ t3 silK run) π).1.copy = 0 := by
  obtain ⟨h1, h2, h3⟩ := key_front C D tF tJ t3 run rec y π τ hp hacc
  exact ⟨h.whole rec y K g inp sl cfg τ (trAns rec.2) h1 (okE_trAns rec.2)
    (by unfold trAns; rw [List.length_ofFn]; exact hv) h3 (by rw [h2]; decide) hs ha ht, h1, h2⟩

/-- **The proof file.** -/
theorem owes_proof {Y : Type} (run : Y × RecP NZ v lg s → View → View → View → Bool)
    (z : Y × RecP NZ v lg s) (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silP run).batch)
    (τ : Tr (wholeDesc C D tF tJ t3 silP run).batch.loc.shape)
    (h : StratOwes C D tF tJ t3 silP run bc π) (hp : π.plains = τ.plains)
    (hacc : (wholeDesc C D tF tJ t3 silP run).batch.loc.accept z y τ = true)
    (hc : (pls₁ (wholeDesc C D tF tJ t3 silP run) π).1.copy < 2 ^ 64)
    (hv : 2 ^ v * s < 2 ^ 64) (hs : ∀ j, (inp j).salt = sl j) (ha : D.a < 2 ^ 64)
    (ht : TableOwes cfg y sl fun _ => True) :
    WholeOwes C D tF tJ t3 silP run z y (fun _ => (treeO (K := K) D.a inp).det g) bc cfg π τ := by
  obtain ⟨h1, h3⟩ := proof_front C D tF tJ t3 run z y π τ hp hacc
  exact h.whole z y K g inp sl cfg τ (trAns z.2.2) h1 (okE_trAns z.2.2)
    (by unfold trAns; rw [List.length_ofFn]; exact hv) h3 hc hs ha ht

end Files

section Entry
variable (C : CK) (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {Y : Type}
  (dec : Y → View → Bool) {I X : Type} {L : BatchProtocolWithLeafBody I X} (K : ℕ) (g : Fam (typedOracleFamily 256 K L))

/-- **The entry's file.** -/
theorem owes_entry (x : Y) (y₀ y₁ : Fin (2 ^ a) → SgX) (inp₀ inp₁ : ℕ → LeafIn L)
    (sl₀ sl₁ : ℕ → Bits) (cfg : ByteArray) (τ : Tr (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)
    (hs₀ : ∀ j, (inp₀ j).salt = sl₀ j) (hs₁ : ∀ j, (inp₁ j).salt = sl₁ j) (ha : a < 2 ^ 64)
    (ht₀ : TableOwes cfg y₀ sl₀ fun _ => True) (ht₁ : TableOwes cfg y₁ sl₁ fun _ => True) :
    EntryOwes C ds a xs dec x (y₀, y₁)
      (fun k => if k = 0 then (treeO (K := K) a inp₀).det g else (treeO (K := K) a inp₁).det g)
      cfg τ := by
  intro p _
  cases p with
  | inl q =>
    obtain ⟨h1, h2, h3, -, h5⟩ := ht₀ q trivial
    show (SaltFrom cfg (((treeO (K := K) a inp₀).det g).inp q.val).salt ∧ (y₀ q).1 = q.val) ∧
      ((y₀ q).2.length < 2 ^ 64 ∧ (((treeO (K := K) a inp₀).det g).inp q.val).salt.length < 2 ^ 64 ∧
        (pathOf ((treeO (K := K) a inp₀).det g).lv q.val).length < 2 ^ 64)
    rw [kept_inp, hs₀, kept_path]
    exact ⟨⟨h1, h3⟩, h5, Nat.lt_of_le_of_lt h2 (by decide), ha⟩
  | inr q =>
    obtain ⟨h1, h2, h3, -, h5⟩ := ht₁ q trivial
    show (SaltFrom cfg (((treeO (K := K) a inp₁).det g).inp q.val).salt ∧ (y₁ q).1 = q.val) ∧
      ((y₁ q).2.length < 2 ^ 64 ∧ (((treeO (K := K) a inp₁).det g).inp q.val).salt.length < 2 ^ 64 ∧
        (pathOf ((treeO (K := K) a inp₁).det g).lv q.val).length < 2 ^ 64)
    rw [kept_inp, hs₁, kept_path]
    exact ⟨⟨h1, h3⟩, h5, Nat.lt_of_le_of_lt h2 (by decide), ha⟩

end Entry

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.StratOwes
#print axioms Johnson.Prover.Print.StratOwes.whole
#print axioms Johnson.Prover.Print.owes_key
#print axioms Johnson.Prover.Print.owes_proof
#print axioms Johnson.Prover.Print.owes_entry
