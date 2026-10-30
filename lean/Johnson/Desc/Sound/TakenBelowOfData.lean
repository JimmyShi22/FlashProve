-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/TakenBelowOfData.lean: A TREE THAT THE LAST CHAIN TAKES OVER IS ONE THAT ITS
  CHAIN
SENDS, AT EVERY DESCRIPTION WHOSE DATA ARE MADE: so its number over the file is below the number at
which the last chain's own trees begin.

Why. Johnson/Desc/BlockSlotOpens.lean (`opensOfData`) says, round by round, that the data's rounds
  open
the declared openings by their numbers over the file (`numAt`). A law of a block of the last chain
wants besides: each tree that it takes over was sent in front of the block's stretch. The last
chain's own test on taken sources compares sets of pairs (chain, number) and does not hold the
  number
below the sending chain's count. `FileDescription.data`'s yes does: `writtenOf` refuses a round that takes
over a tree which the earlier chain does not send.
  `src_sent`            a declared source that the stand-ins bear: if taken, its chain is 0 or 1 and
    its
                        number there is below that chain's count
  `counts_of_data`      D.t₁ = F.t₁ and D.t₂ = F.t₂
  `taken_sent_of_data`  **at every opening "taken c n" of the last chain's declared rounds:
                        c = 0 ∧ n < F.t₁, or c = 1 ∧ n < F.t₂**
  `taken_below_of_data` **numAt F.t₁ F.t₂ 2 (its source) < F.t₁ + F.t₂**
  `own_from`            an own tree's number is at least t₁ + t₂
Limits. Facts on numbers of trees; nothing on soundness. Nothing says which trees a description
declares, in which round, in which order or how often. That an own tree's number is below the file's
count of trees is not said.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.BlockSlotOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Maker
open OnBytes.Three (tagRoot tagRun rootsIn)

theorem get_tags {n p : ℕ} {r : ByteArray} (h : ((List.range n).map tagRoot)[p]? = some r) :
    p < n := by
  rw [List.getElem?_map] at h
  obtain ⟨q, hq, -⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.1 hq
  rw [List.length_range] at hl
  exact hl

/-- A declared source that the stand-ins bear: a taken tree is one that its chain sends. -/
theorem src_sent {D : Johnson.G.OfPlan.Decl3} {c n : ℕ} {x : Fmt.Src}
    (h : (Fmt.TreeSource.taken c n).src (standIns D) = some x) :
    (c = 0 ∧ n < Johnson.G.OfPlan.rootsOf D.1) ∨ (c = 1 ∧ n < Johnson.G.OfPlan.rootsOf D.2.1) := by
  match c, h with
  | 0, h =>
    have h' : (((List.range (Johnson.G.OfPlan.rootsOf D.1)).map tagRoot)[n]?).map
        (fun r => Fmt.Src.given r (tagRun 1)) = some x := h
    obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.1 h'
    exact Or.inl ⟨rfl, get_tags hr⟩
  | 1, h =>
    have h' : (((List.range (Johnson.G.OfPlan.rootsOf D.2.1)).map tagRoot)[n]?).map
        (fun r => Fmt.Src.given r (tagRun 2)) = some x := h
    obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.1 h'
    exact Or.inr ⟨rfl, get_tags hr⟩
  | c + 2, h => exact nomatch h

theorem forall₂_left {α β : Type} {P : α → β → Prop} : ∀ {l : List α} {m : List β},
    List.Forall₂ P l m → ∀ a ∈ l, ∃ b, P a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons (b := b) h t, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, h⟩
    · exact forall₂_left t a ha

variable {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}

/-- The data's two counts of trees are the description's. -/
theorem counts_of_data (h : F.data file = .ok D) : D.t₁ = F.t₁ ∧ D.t₂ = F.t₂ := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, rfl⟩ := data_ok h
  obtain ⟨w₁, w₂, -⟩ := writtenOf_ok hR
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hk).fits
  have hcn : countsFit F.tableDepth (Three.Whole.of R₁ R₂ R₃) = true := (okAt_parts hk).counts
  unfold countsFit at hcn
  simp only [Bool.and_eq_true, beq_iff_eq] at hcn
  exact ⟨hcn.1.trans (rootsIn_eq w₁ (fits_roots hf (0, R₁) (by simp))),
    hcn.2.trans (rootsIn_eq w₂ (fits_roots hf (1, R₂) (by simp)))⟩

/-- **A tree that the last chain takes over is one that its chain sends.** -/
theorem taken_sent_of_data (h : F.data file = .ok D) (r : Fmt.DeclaredRound) (hr : r ∈ F.roundsDeclaredByBlocks.2.2)
    (o : Fmt.Shape × Fmt.TreeSource) (ho : o ∈ r.opens) (c n : ℕ) (e : o.2 = .taken c n) :
    (c = 0 ∧ n < F.t₁) ∨ (c = 1 ∧ n < F.t₂) := by
  obtain ⟨R, hR, -, -⟩ := data_ok h
  obtain ⟨-, -, w₃⟩ := writtenOf_ok hR
  obtain ⟨x, y, hy, -⟩ := forall₂_left w₃ r hr
  obtain ⟨p, hp, -⟩ := forall₂_left (round_ok hy).2.2 o ho
  rw [e] at hp
  exact src_sent hp

/-- **So its number over the file is below the number at which the last chain's own trees begin.**
-/
theorem taken_below_of_data (h : F.data file = .ok D) (r : Fmt.DeclaredRound) (hr : r ∈ F.roundsDeclaredByBlocks.2.2)
    (o : Fmt.Shape × Fmt.TreeSource) (ho : o ∈ r.opens) (c n : ℕ) (e : o.2 = .taken c n) :
    numAt F.t₁ F.t₂ 2 o.2 < F.t₁ + F.t₂ := by
  rw [e]
  rcases taken_sent_of_data h r hr o ho c n e with ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · show 0 + n < F.t₁ + F.t₂
    omega
  · show F.t₁ + n < F.t₁ + F.t₂
    omega

/-- An own tree's number over the file is at least t₁ + t₂. -/
theorem own_from (t₁ t₂ n : ℕ) : t₁ + t₂ ≤ numAt t₁ t₂ 2 (.own n) := Nat.le_add_right _ _

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.src_sent
#print axioms VerifiableInference.Desc.counts_of_data
#print axioms VerifiableInference.Desc.taken_sent_of_data
#print axioms VerifiableInference.Desc.taken_below_of_data
