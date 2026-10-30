-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadFitsOf.lean: what OnBytes/Maker/AcceptAt.lean asks of the data and of the reading
(`ReadFits`, seventeen fields), from the equations by which the verifier program describes and reads
the three chains of a file.

The program makes each chain's description from rounds that a dry run of a block has stated
(`Params.describeWith`), and reads the chain under it (`readChain`). The plain data of a file are
made from three such lists of rounds (`Three.Whole.of`), the third at made-up names of the trees
that the third chain takes over. OnBytes/Maker/ReadFacts.lean and ReadSpecs.lean say what a
description holds and what a reading gives. This file lays these laws together.

WHICH READING. r is the file as the reader returns it, with all openings. Before it decides on a
proof file the program hands on a lighter form of the first chain, without its openings
(`ChainRead.light`, OnBytes/Proof/File.lean: `proofRefusal`). Of that form the equation `e₁` does
not hold, and the tables of OnBytes/Maker/Tables.lean return nothing at it.

Main theorems.
  `storedFit_depth`: what the test `storedFit` says of the stored tables' depths.
  `readIn_chain`: a reading within a verdict is a reading of the chain's reader.
  `bareSeal_of_fits`: the test `bareSeal` on the last of the first chain's rounds, from
    `Three.Whole.fits`.
  `zipWith_opens`, `sealBare_of_fits`: the test `sealBare` on the data, from `Three.Whole.fits`.
  `readFits_chain`: `ReadFits`, from three equations of describing, three of reading, three on the
    views, `StoredAlike` of the third chain's two lists of rounds, and three tests on the data.
  `sealedLast_chain`: the first view as read ends in a sealing round, from `bareSeal`.
  `t₁_chain`: the first chain as read has as many roots as the data count.
No other file calls `readIn_chain`.

What is not claimed. That the program's own text gives these equations at any file. That the tests
pass. Nothing on soundness.


-/
import OnBytes.Maker.AcceptAt
import OnBytes.Maker.SmallTies
import OnBytes.Maker.RoundsAtTags

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.TwoLaws

/-- What `storedFit` says of the depths: every stored table that a chain opens has the depth a. -/
theorem storedFit_depth {a : ℕ} {W : Three.Whole} (h : storedFit a W = true) :
    (∀ d ∈ W.ds₁, ∀ t ∈ d.stored, t.sh.a = a) ∧ (∀ d ∈ W.ds₂, ∀ t ∈ d.stored, t.sh.a = a) ∧
      ∀ d ∈ W.ds₃, ∀ t ∈ d.stored, t.sh.a = a := by
  unfold storedFit at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_append, List.isEmpty_iff,
    beq_iff_eq] at h
  refine ⟨fun d hd t ht => ?_, fun d hd t ht => (h.2 d hd t ht).1, fun d hd t ht => ?_⟩
  · rw [h.1 d (Or.inl hd)] at ht
    cases ht
  · rw [h.1 d (Or.inr hd)] at ht
    cases ht

/-- A reading within a verdict is a reading of the chain's reader. -/
theorem readIn_chain (S : Fmt.SpecX) (b : ByteArray) (i : ℕ) (s s' : Session) (c : ChainRead)
    (e : readIn S b i s = some (c, s')) : readChain S s.seen b i = some (c.out, c.next) := by
  unfold readIn at e
  cases hr : readChain S s.seen b i with
  | none => rw [hr] at e; cases e
  | some z =>
    rw [hr] at e
    obtain ⟨o, j⟩ := z
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    rfl

/-- The last of the first chain's rounds passes `bareSeal`, where the three lists of rounds pass the
test `Three.Whole.fits`. -/
theorem bareSeal_of_fits {R₁ R₂ R₃ : Params.Rounds} {m : ℕ}
    (h : Three.Whole.fits R₁ R₂ R₃ m = true) (x : Fmt.Round × List Fmt.Stored)
    (hx : R₁.getLast? = some x) : bareSeal x.1 = true := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  have h5 := List.all_eq_true.1 h.1.2 R₁ List.mem_cons_self
  simp only [hx, Bool.and_eq_true] at h5
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨k, -⟩, -⟩, -⟩, it⟩, -⟩, dE⟩, dN⟩, po⟩, tr⟩ := h5
  unfold bareSeal
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨k, it⟩, po⟩, dE⟩, dN⟩, tr⟩

/-- The trees that the rounds' data open are those that the rounds' openings name. -/
theorem zipWith_opens (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ) :
    ∀ (R : Params.Rounds) (L : List ℕ), L.length = R.length →
      (List.zipWith (Three.rdOf all t₁ t₂ here base first) R L).map (·.opens) =
        R.map fun r => r.1.opens.filterMap fun o => (Three.named here o.2).map (Three.wholeNo t₁ t₂)
  | [], _, _ => by simp
  | _ :: _, [], e => by cases e
  | r :: R, n :: L, e => by
    rw [List.zipWith_cons_cons, List.map_cons, List.map_cons,
      zipWith_opens all t₁ t₂ here base first R L (Nat.succ.inj e)]
    rfl

/-- **The test `sealBare` on the data follows from the test `Three.Whole.fits` on the rounds of
which they are made.** -/
theorem sealBare_of_fits {R₁ R₂ R₃ : Params.Rounds} {m : ℕ}
    (h : Three.Whole.fits R₁ R₂ R₃ m = true) : sealBare (Three.Whole.of R₁ R₂ R₃) = true := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  have h5 := List.all_eq_true.1 h.1.2 R₁ List.mem_cons_self
  cases hx : R₁.getLast? with
  | none => simp only [hx] at h5; cases h5
  | some x =>
    simp only [hx, Bool.and_eq_true, List.isEmpty_iff] at h5
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, ho⟩, -⟩, hs⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h5
    have e1 := congrArg List.getLast? (stored_ds₁ R₁ R₂ R₃)
    have e2 := congrArg List.getLast? (zipWith_opens
      (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁) (Three.rootsIn R₂) 0 0 0 R₁
      (Three.sentBefore R₁) (sentBefore_length R₁))
    rw [List.getLast?_map, List.getLast?_map, hx] at e1 e2
    unfold sealBare
    cases hd : (Three.Whole.of R₁ R₂ R₃).ds₁.getLast? with
    | none => rw [hd] at e1; cases e1
    | some d =>
      have hd' : (List.zipWith (Three.rdOf (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁)
          (Three.rootsIn R₂) 0 0 0) R₁ (Three.sentBefore R₁)).getLast? = some d := hd
      rw [hd] at e1
      rw [hd'] at e2
      have s1 : d.stored = x.2 := Option.some.inj e1
      have s2 : d.opens = x.1.opens.filterMap fun o =>
          (Three.named 0 o.2).map (Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂)) :=
        Option.some.inj e2
      simp only [Bool.and_eq_true, List.isEmpty_iff]
      exact ⟨by rw [s1, hs], by rw [s2, ho]; rfl⟩

section
variable {g₁ g₂ g₃ : Params.Given} {l₁ l₂ l₃ : ℕ} {x₁ x₂ x₃ : ByteArray} {n₁ n₂ n₃ : Fmt.Rand}
  {R₁ R₂ R₃ R₃' : Params.Rounds} {S₁ S₂ S₃ : Fmt.SpecX} {r : Proof.TailRead}
  {b₁ b₂ b₃ : ByteArray} {i₁ i₂ i₃ : ℕ} {q₁ q₂ q₃ : Fmt.Seen}

/-- **The first chain as read has as many roots as the data count.** -/
theorem t₁_chain (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁)
    (e₁ : readChain S₁ q₁ b₁ i₁ = some (r.first.out, r.first.next)) :
    (Three.Whole.of R₁ R₂ R₃).t₁ = r.first.roots.length :=
  t₁_roots hS₁ q₁ b₁ i₁ r.first e₁ R₂ R₃

/-- **What is asked of the data and of the reading.** R₃': the third chain's rounds at the file's
own roots, under which it is read. R₃: the same at made-up names, of which the data are made. -/
theorem readFits_chain (a : ℕ) (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁)
    (hS₂ : Params.describeWith g₂ l₂ x₂ n₂ R₂ 0 = some S₂)
    (hS₃ : Params.describeWith g₃ l₃ x₃ n₃ R₃' (Proof.secondFirstTree r.first) = some S₃)
    (e₁ : readChain S₁ q₁ b₁ i₁ = some (r.first.out, r.first.next))
    (e₂ : readChain S₂ q₂ b₂ i₂ = some (r.shared.out, r.shared.next))
    (e₃ : readChain S₃ q₃ b₃ i₃ = some (r.second.out, r.second.next))
    (v₁ : r.first.view = OnBytes.viewOf S₁ r.first.out)
    (v₂ : r.shared.view = OnBytes.viewOf S₂ r.shared.out)
    (v₃ : r.second.view = OnBytes.viewOf S₃ r.second.out) (hA : StoredAlike R₃' R₃)
    (hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true)
    (hsh : shapesFit a (Three.Whole.of R₁ R₂ R₃) = true)
    (hb : sealBare (Three.Whole.of R₁ R₂ R₃) = true) :
    ReadFits a (Three.Whole.of R₁ R₂ R₃) r S₁ S₂ S₃ := by
  have t1 := spec_stored hS₁ (rfl : StoredAlike R₁ R₁) (stored_ds₁ R₁ R₂ R₃)
  have t2 := spec_stored hS₂ (rfl : StoredAlike R₂ R₂) (stored_ds₂ R₁ R₂ R₃)
  have t3 := spec_stored hS₃ hA (stored_ds₃ R₁ R₂ R₃)
  obtain ⟨a1, a2, a3⟩ := storedFit_depth hst
  exact
    { shape := hsh
      bare := hb
      st₁ := t1
      st₂ := t2
      st₃ := t3
      ft₁ := (describeWith_facts hS₁).2.2
      ft₂ := (describeWith_facts hS₂).2.2
      ft₃ := (describeWith_facts hS₃).2.2.trans
        (firstTree₃ R₁ R₂ R₃ r.first (t₁_chain (R₂ := R₂) (R₃ := R₃) hS₁ e₁).symm)
      ls₁ := readChain_asDrawn a _ S₁ q₁ b₁ i₁ _ _ e₁ t1 a1
      ls₂ := readChain_asDrawn a _ S₂ q₂ b₂ i₂ _ _ e₂ t2 a2
      ls₃ := readChain_asDrawn a _ S₃ q₃ b₃ i₃ _ _ e₃ t3 a3
      v₁ := v₁.trans (viewOf_eq S₁ _)
      v₂ := v₂.trans (viewOf_eq S₂ _)
      v₃ := v₃.trans (viewOf_eq S₃ _)
      pw₁ := readChain_within _ S₁ q₁ b₁ i₁ _ _ e₁ t1
      pw₂ := readChain_within _ S₂ q₂ b₂ i₂ _ _ e₂ t2
      pw₃ := readChain_within _ S₃ q₃ b₃ i₃ _ _ e₃ t3 }

/-- **The first view as read ends in a sealing round.** -/
theorem sealedLast_chain (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁)
    (e₁ : readChain S₁ q₁ b₁ i₁ = some (r.first.out, r.first.next))
    (v₁ : r.first.view = OnBytes.viewOf S₁ r.first.out) (x : Fmt.Round × List Fmt.Stored)
    (hx : R₁.getLast? = some x) (hb : bareSeal x.1 = true) : SealedLast r.first.view := by
  rw [v₁, viewOf_eq]
  obtain ⟨f1, f2, -⟩ := describeWith_facts hS₁
  refine sealedLast_read S₁ q₁ b₁ i₁ r.first.out r.first.next e₁ x ?_ hb
  rw [f1, f2, zip_fst_snd]
  exact hx

end

end OnBytes.Maker
