-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OkJoin.lean: THE PROMISE Ok ON WHAT IS FIXED BEFORE THE DRAW, ITS STATIC
HALF: four of the clauses that the laws on the approximate range proof's run ask of it (okBlocks,
okApart, okLooks: FullEq.lean; okCoef: FullFour.lean) AS ONE SENTENCE; THAT THE SENTENCE HANGS ON
SEVEN PLANNED READINGS OF THE STRUCTURE AND ON THE ARRAYS' LOOKS ALONE; AND THE SENTENCE AT A STATE,
FROM THREE FACTS. Definitions and theorems.
  `g9 tl`: the seven readings: the arrays' numbers, the number of matrices, the symbols' arrays, the
    number of combinations, the number of blocks, and each piece's array and virtual row, by call.
    `g9_blank`: none is one of the fourteen written fields.
  `ApartAt`, `StaticOk tl F`: the four clauses' bodies. `static_congr`: **two structures with the
    same seven readings and two ledgers whose arrays have the same looks have the clauses together**
    (`apartAt_congr`, `coefOK_congr`, with FullFour.lean's `coefOK_frame`).
  `OkK8 π q`: the static half of Ok: a snapshot is there, and the clauses hold of the fixed
    structure and the snapshot's ledger. `okK8_blocks`, `okK8_apart`, `okK8_looks`, `okK8_coef`:
    **the four clauses to the letter, for every Ok that gives `OkK8`.**
  `okK8_at`: **`OkK8 π (fixed9 φ s)`** where a part is open at s (h0), the structure's seven
    readings are tlP's (h1), the snapshot's arrays have FP's looks (h2), and `StaticOk tlP FP` (H:
    at a link's planned structure and ledger it is a matter of tests with code).
Limits. h0, h1, h2 ARE SHOWN OF NO STATE HERE, H OF NO PLAN. THE OTHER CLAUSES OF Ok ARE NOT HERE:
okPos (it reads the list of tables, which is laid in the run), okEnts and hOk4 (they read what was
heard, and filled slots), and the other kinds' demands. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FullFour
import OnBytes.Tie.Pv.Tail.EndWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail (reads_tree)
open OnBytes.Tie.Pv.Tail.Port (readsList uOf)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open _root_.Fo (CoefOK allPieces HasRow Frame)

/-! ## 1 The static clauses, as one sentence -/

/-- **What the static clauses read of the approximate range proof's structure.** -/
def g9 (tl : HTailF2) : T2Map × ℕ × Array ℕ × ℕ × ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (tl.ix, tl.NM, tl.gtTree, tl.tau, tl.blocks.size,
    tl.z1.pieces.toList.map (fun p => (p.tree, p.row)),
    tl.z2.pieces.toList.map (fun p => (p.tree, p.row)))

/-- It reads none of the fourteen written fields. -/
theorem g9_blank (u tl : HTailF2) : g9 (blank u tl) = g9 tl := rfl

/-- The array t is one of the four vectors, and another than the digits', the planes', the symbols'
and the pieces'. -/
def ApartAt (tl : HTailF2) (t : ℕ) : Prop :=
  ∃ n0, n0 < 4 ∧ tl.ix.U.getD n0 none = some t ∧ tl.ix.ZZ ≠ t ∧ tl.ix.BZ ≠ t ∧
    (∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ t) ∧
    ∀ k p, p ∈ (tl.zOf k).pieces.toList → p.tree ≠ t

/-- **THE STATIC CLAUSES.** -/
structure StaticOk (tl : HTailF2) (F : Fork) : Prop where
  blocks : tl.wants.map (·.1) = some tl.zzBlocks
  apart : ∀ Fn : HFun, Fn.tree = 0 ∨ Fn.tree = 2 → ApartAt tl (uOf tl Fn)
  units : ∀ Fn : HFun, unitLook (F.trees.toList.map look) (uOf tl Fn) = true
  coef : CoefOK tl F

section Congr
variable {tl tl' : HTailF2}

theorem g9_parts (h : g9 tl = g9 tl') :
    tl.ix = tl'.ix ∧ tl.NM = tl'.NM ∧ tl.gtTree = tl'.gtTree ∧ tl.tau = tl'.tau ∧
      tl.blocks.size = tl'.blocks.size ∧
      tl.z1.pieces.toList.map (fun p => (p.tree, p.row)) =
        tl'.z1.pieces.toList.map (fun p => (p.tree, p.row)) ∧
      tl.z2.pieces.toList.map (fun p => (p.tree, p.row)) =
        tl'.z2.pieces.toList.map (fun p => (p.tree, p.row)) := by
  unfold g9 at h
  simp only [Prod.mk.injEq] at h
  exact h

/-- The pieces' places, in the routine's order. -/
theorem places_all (tl : HTailF2) : (allPieces tl).map (fun a => (a.2.tree, a.2.row)) =
    tl.z1.pieces.toList.map (fun p => (p.tree, p.row)) ++
      tl.z2.pieces.toList.map (fun p => (p.tree, p.row)) := by
  unfold allPieces
  simp only [List.map_append, List.map_map]
  rfl

theorem places_congr (h : g9 tl = g9 tl') : (allPieces tl).map (fun a => (a.2.tree, a.2.row)) =
    (allPieces tl').map fun a => (a.2.tree, a.2.row) := by
  obtain ⟨_, _, _, _, _, e1, e2⟩ := g9_parts h
  rw [places_all, places_all, e1, e2]

/-- A piece of the one stands where a piece of the other stands. -/
theorem piece_congr (h : g9 tl = g9 tl') (a : ℕ × Piece) (ha : a ∈ allPieces tl) :
    ∃ a' ∈ allPieces tl', a'.2.tree = a.2.tree ∧ a'.2.row = a.2.row := by
  have hm : (a.2.tree, a.2.row) ∈ (allPieces tl).map fun a => (a.2.tree, a.2.row) :=
    List.mem_map.2 ⟨a, ha, rfl⟩
  rw [places_congr h] at hm
  obtain ⟨a', ha', e⟩ := List.mem_map.1 hm
  exact ⟨a', ha', congrArg Prod.fst e, congrArg Prod.snd e⟩

/-- A piece of a call is one of all pieces. -/
theorem piece_all (tl : HTailF2) (k : ℕ) (p : Piece) (hp : p ∈ (tl.zOf k).pieces.toList) :
    ∃ a ∈ allPieces tl, a.2 = p := by
  unfold allPieces
  unfold HTailF2.zOf at hp
  by_cases hk : (k == 0) = true
  · rw [if_pos hk] at hp
    exact ⟨(0, p), List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩), rfl⟩
  · rw [if_neg hk] at hp
    exact ⟨(1, p), List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩), rfl⟩

theorem all_piece (tl : HTailF2) (a : ℕ × Piece) (ha : a ∈ allPieces tl) :
    ∃ k, a.2 ∈ (tl.zOf k).pieces.toList := by
  unfold allPieces at ha
  rcases List.mem_append.1 ha with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact ⟨0, hp⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact ⟨1, hp⟩

theorem apartAt_congr (h : g9 tl = g9 tl') {t : ℕ} (H : ApartAt tl' t) : ApartAt tl t := by
  obtain ⟨e1, e2, e3, _, _, _, _⟩ := g9_parts h
  obtain ⟨n0, a1, a2, a3, a4, a5, a6⟩ := H
  refine ⟨n0, a1, by rw [e1]; exact a2, by rw [e1]; exact a3, by rw [e1]; exact a4,
    fun mu hmu => by rw [e3]; exact a5 mu (e2 ▸ hmu), fun k p hp => ?_⟩
  obtain ⟨a, ha, rfl⟩ := piece_all tl k p hp
  obtain ⟨a', ha', et, _⟩ := piece_congr h a ha
  obtain ⟨k', hk'⟩ := all_piece tl' a' ha'
  rw [← et]
  exact a6 k' a'.2 hk'

theorem coefOK_congr (h : g9 tl = g9 tl') {F : Fork} (T : CoefOK tl' F) : CoefOK tl F := by
  obtain ⟨e1, e2, e3, _, e5, _, _⟩ := g9_parts h
  have eR : tl.zzRowReads = tl'.zzRowReads := by
    unfold HTailF2.zzRowReads HTailF2.zzBlocks
    rw [e5]
  have eT : tl.zzRowTies = tl'.zzRowTies := by
    unfold HTailF2.zzRowTies HTailF2.zzBlocks
    rw [e5]
  refine ⟨by rw [e1]; exact T.bz, by rw [e1]; exact T.bzR,
    fun mu hmu => by rw [e1, e3]; exact T.mats mu (e2 ▸ hmu),
    by rw [places_congr h]; exact T.apart, fun a ha => ?_⟩
  obtain ⟨a', ha', et, er⟩ := piece_congr h a ha
  obtain ⟨p1, p2, p3, p4, p5⟩ := T.piece a' ha'
  rw [et, er] at p1 p2 p3
  rw [et] at p4
  refine ⟨p1, by rw [e1, eR]; exact p2, by rw [e1, eT]; exact p3, by rw [e1]; exact p4,
    fun mu hmu => ?_⟩
  have k := p5 mu (e2 ▸ hmu)
  rw [et, er] at k
  rw [e3]
  exact k

/-- Lists of looks, as arrays. -/
theorem looks_array {F F' : Fork} (h : F.trees.toList.map look = F'.trees.toList.map look) :
    F.trees.map look = F'.trees.map look :=
  Array.toList_inj.1 (by simpa using h)

/-- **THE STATIC CLAUSES HANG ON THE SEVEN READINGS AND THE LOOKS ALONE.** -/
theorem static_congr (hg : g9 tl = g9 tl') {F F' : Fork}
    (hl : F.trees.toList.map look = F'.trees.toList.map look) (H : StaticOk tl' F') :
    StaticOk tl F := by
  obtain ⟨e1, _, _, e4, e5, _, _⟩ := g9_parts hg
  have eU : ∀ Fn, uOf tl Fn = uOf tl' Fn := fun Fn => by
    unfold uOf
    rw [e1]
  refine ⟨?_, fun Fn hFn => ?_, fun Fn => ?_, ?_⟩
  · have k := H.blocks
    unfold HTailF2.wants HTailF2.zzBlocks at k ⊢
    rw [e4, e5]
    by_cases hc : (tl'.tau - 2 ^ Nat.log2 tl'.tau != 0 &&
        !isPow2 (tl'.tau - 2 ^ Nat.log2 tl'.tau)) = true
    · simp only [hc, if_true] at k
      exact nomatch k
    · simp only [hc, Bool.false_eq_true, if_false, Option.map_some] at k ⊢
      exact k
  · rw [eU]
    exact apartAt_congr hg (H.apart Fn hFn)
  · rw [eU, hl]
    exact H.units Fn
  · exact coefOK_congr hg (coefOK_frame (frame_of_looks (looks_array hl)) H.coef)

end Congr

/-! ## 2 The one Ok's static half, and the four clauses out of it -/

section
variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun))

/-- **THE STATIC HALF OF Ok.** -/
def OkK8 (q : α × Option Pub9) : Prop :=
  q.2.isSome = true ∧ ∀ tlb v, (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F

variable (Ok : α × Option Pub9 → Prop) (hOk : ∀ q, Ok q → OkK8 π q)
include hOk

theorem okK8_blocks : ∀ q tlb, Ok q → (π q.1).1 = some tlb →
    tlb.wants.map (·.1) = some tlb.zzBlocks := fun q tlb h h1 => by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hOk q h).1
  exact ((hOk q h).2 tlb v h1 hv).blocks

theorem okK8_apart : ∀ q tlb funs, Ok q → π q.1 = (some tlb, some funs) →
    ∀ x ∈ readsList tlb funs, ∃ n0, n0 < 4 ∧ tlb.ix.U.getD n0 none = some (uOf tlb x.1) ∧
      tlb.ix.ZZ ≠ uOf tlb x.1 ∧ tlb.ix.BZ ≠ uOf tlb x.1 ∧
      (∀ mu, mu < tlb.NM → tlb.gtTree.getD mu 0 ≠ uOf tlb x.1) ∧
      ∀ k p, p ∈ (tlb.zOf k).pieces.toList → p.tree ≠ uOf tlb x.1 := fun q tlb funs h h1 x hx => by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hOk q h).1
  exact ((hOk q h).2 tlb v (by rw [h1]) hv).apart x.1 (reads_tree tlb funs x hx)

theorem okK8_looks : ∀ q tlb funs v, Ok q → π q.1 = (some tlb, some funs) → q.2 = some v →
    ∀ x ∈ readsList tlb funs, unitLook (v.F.trees.toList.map look) (uOf tlb x.1) = true :=
  fun q tlb _ v h h1 hv x _ => ((hOk q h).2 tlb v (by rw [h1]) hv).units x.1

theorem okK8_coef : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → CoefOK tlb v.F :=
  fun q tlb v h h1 hv => ((hOk q h).2 tlb v h1 hv).coef

end

/-! ## 3 At a state -/

/-- **THE STATIC HALF OF Ok AT WHAT IS FIXED AT A STATE**: where a part is open, the structure's
seven readings are the plan's, the snapshot's arrays have the plan's looks, and the plan has the
clauses. -/
theorem okK8_at {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α)
    (u : HTailF2) (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (s : S) (tlP : HTailF2)
    (FP : Fork) (h0 : (atS.get? s).isSome = true) (h1 : ∀ tl, s.tl? = some tl → g9 tl = g9 tlP)
    (h2 : ∀ p, atS.get? s = some p →
      (pubOf p).F.trees.toList.map look = FP.trees.toList.map look)
    (H : StaticOk tlP FP) : OkK8 π (fixed9 φ s) := by
  refine ⟨by simpa [fixed9] using h0, fun tlb v e1 e2 => ?_⟩
  have e1' : s.tl?.map (blank u) = some tlb := by
    have k := congrArg Prod.fst (hπ s)
    exact k.symm.trans e1
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 e1'
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 (show (atS.get? s).map pubOf = some v from e2)
  exact static_congr ((g9_blank u tl).trans (h1 tl htl)) (h2 p hp) H

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.static_congr
#print axioms VerifiableInference.Desc.LinkJoin.okK8_blocks
#print axioms VerifiableInference.Desc.LinkJoin.okK8_apart
#print axioms VerifiableInference.Desc.LinkJoin.okK8_looks
#print axioms VerifiableInference.Desc.LinkJoin.okK8_coef
#print axioms VerifiableInference.Desc.LinkJoin.okK8_at
