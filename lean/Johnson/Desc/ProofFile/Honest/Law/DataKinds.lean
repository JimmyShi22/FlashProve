-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/DataKinds.lean: what the data that `FileDescription.data`
(Johnson/Desc/BlockSlot.lean) computes from a description keep of its declared rounds: entry and
kind, round by round; and what its tests say of the first chain's last declared round. The
main lemma, `kinds_of_data`, proves four of the six hypotheses of `due_typed` (Honest/Law/Due.lean).

  `round_kind`, `zip_kind`  a declared round and the written round that is computed from it
  `forall₂_last`            on lists
  `seal_of_fits`            the first chain's last written round, by the sixth clause of
                            `Whole.fits` (OnBytes/Three/Data.lean)
  `kinds_of_data`           the main lemma
  `dataFits_at`             the same data at a depth that is written again and is the same number

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.BlockSlotProofs
import Johnson.EntryRec.OkcFiles
import Johnson.Desc.ProofFile.Honest.Law.Due

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes OnBytes.Maker
open OnBytes.Three (rdOf rdsFromL)

variable {Xi : Type}

theorem round_kind {e : List (List ByteArray × ByteArray)} {r : Fmt.DeclaredRound} {y : Fmt.Round}
    (h : r.round e = some y) : Fmt.kindOf r.entry.name = some y.kind := by
  unfold Fmt.DeclaredRound.round at h
  cases hk : Fmt.kindOf r.entry.name with
  | none =>
    rw [hk] at h
    cases h
  | some k =>
    rw [hk] at h
    have h' : Option.map (fun os => (⟨r.entry, k, r.items, os⟩ : Fmt.Round))
        (r.opens.mapM fun (o : Fmt.Shape × Fmt.TreeSource) => (o.2.src e).map fun s => (o.1, s)) =
        some y := h
    obtain ⟨os, -, rfl⟩ := Option.map_eq_some_iff.1 h'
    rfl

theorem zip_kind (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    {e : List (List ByteArray × ByteArray)} {l : List Fmt.DeclaredRound} {R : Params.Rounds}
    (hw : List.Forall₂ (Written e) l R) : ∀ L : List ℕ, L.length = R.length →
    List.Forall₂ KindFits ((List.zipWith (rdOf all t₁ t₂ here base first) R L).map rdtOf) l := by
  induction hw with
  | nil =>
    intro L _
    rw [List.zipWith_nil_left]
    exact .nil
  | @cons r x l R hd _ ih =>
    intro L hL
    cases L with
    | nil => cases hL
    | cons n L =>
      rw [List.zipWith_cons_cons, List.map_cons]
      obtain ⟨y, hy, rfl⟩ := hd
      exact .cons ⟨(round_ok hy).1, round_kind hy⟩ (ih L (Nat.succ.inj hL))

theorem forall₂_last {α β : Type} {P : α → β → Prop} : ∀ {A : List α} {B : List β},
    List.Forall₂ P A B → ∀ b, B.getLast? = some b → ∃ a, A.getLast? = some a ∧ P a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons (a := a) h .nil, b, hb => by
    have e : some _ = some b := hb
    cases e
    exact ⟨a, rfl, h⟩
  | _, _, .cons _ (.cons h' t), b, hb => by
    rw [List.getLast?_cons_cons] at hb
    obtain ⟨a, ha, hp⟩ := forall₂_last (.cons h' t) b hb
    exact ⟨a, by rw [List.getLast?_cons_cons]; exact ha, hp⟩

/-- The first chain's last written round is of the kind "sealed", has no item, and draws nothing. -/
theorem seal_of_fits {R₁ R₂ R₃ : Params.Rounds} {m : ℕ}
    (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    ∃ r, R₁.getLast? = some r ∧ r.1.kind = .sealed ∧ r.1.items = [] ∧ r.1.entry.roots = 0 ∧
      r.1.entry.drawE = 0 ∧ r.1.entry.drawNZ = 0 ∧ r.1.entry.poss = 0 ∧ r.1.entry.trits = 0 := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, c5⟩, -⟩ := h
  have c := List.all_eq_true.1 c5 R₁ (by simp)
  cases hl : R₁.getLast? with
  | none =>
    rw [hl] at c
    cases c
  | some r =>
    rw [hl] at c
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at c
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨q1, -⟩, q3⟩, -⟩, q5⟩, -⟩, q7⟩, q8⟩, q9⟩, q10⟩ := c
    exact ⟨r, rfl, q1, q5, q3, q7, q8, q9, q10⟩

theorem kinds_of_data {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D) :
    List.Forall₂ KindFits D.ds₁ F.roundsDeclaredByBlocks.1.dropLast ∧ List.Forall₂ KindFits D.ds₂ F.roundsDeclaredByBlocks.2.1 ∧
      List.Forall₂ KindFits D.ds₃ F.roundsDeclaredByBlocks.2.2 ∧
      ∃ d, F.roundsDeclaredByBlocks.1.getLast? = some d ∧ drawFit d ⟨[], [], [], none⟩ = true := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, rfl⟩ := data_ok h
  obtain ⟨w₁, w₂, w₃⟩ := writtenOf_ok hR
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hk).fits
  have k₁ : List.Forall₂ KindFits ((Three.Whole.of R₁ R₂ R₃).ds₁.map rdtOf) F.roundsDeclaredByBlocks.1 :=
    zip_kind _ _ _ _ _ _ w₁ _ (sentBefore_length R₁)
  have k₂ : List.Forall₂ KindFits ((Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf) F.roundsDeclaredByBlocks.2.1 :=
    zip_kind _ _ _ _ _ _ w₂ _ (sentBefore_length R₂)
  have k₃ : List.Forall₂ KindFits ((Three.Whole.of R₁ R₂ R₃).ds₃.map rdtOf) F.roundsDeclaredByBlocks.2.2 :=
    zip_kind _ _ _ _ _ _ w₃ _ (sentBefore_length R₃)
  refine ⟨?_, k₂, k₃, ?_⟩
  · have k := forall₂_dropLast k₁
    rw [← List.map_dropLast] at k
    exact k
  · obtain ⟨r, hr, q1, -, -, q7, -, q9, q10⟩ := seal_of_fits hf
    obtain ⟨d, hd, y, hy, rfl⟩ := forall₂_last w₁ r hr
    have e := (round_ok hy).1
    have hkd := round_kind hy
    have q1' : y.kind = .sealed := q1
    have q7' : y.entry.drawE = 0 := q7
    have q9' : y.entry.poss = 0 := q9
    have q10' : y.entry.trits = 0 := q10
    rw [e] at q7' q9' q10'
    rw [q1'] at hkd
    refine ⟨d, hd, ?_⟩
    simp [drawFit, drawsMarkedNonzeroHaveNonzeroWords, q7', q9', q10', hkd]

theorem dataFits_at {F : FileDescription Xi} {D : WholeD} (h : DataFits F D) {a : Nat} (ha : a = D.a) :
    DataFits F (D.at a) := by
  subst ha
  exact h

end ProofFile.Honest

#print axioms ProofFile.Honest.round_kind
#print axioms ProofFile.Honest.zip_kind
#print axioms ProofFile.Honest.forall₂_last
#print axioms ProofFile.Honest.seal_of_fits
#print axioms ProofFile.Honest.kinds_of_data
#print axioms ProofFile.Honest.dataFits_at
