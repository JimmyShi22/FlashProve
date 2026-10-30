-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadSizes.lean: of the openings of the trees of a file as the program's reader has
read it: every vertex that was met has a value of 32 bytes; all openings are what the reader of an
opening hands out at one configuration's digest, if the three descriptions have one; and the opened
leaves' digests stand at the bottom, hashed at the start that the tables lay.

Statements and proofs. They gather, at the members of `ownRowsW` (OnBytes/Maker/Tables.lean), what
OnBytes/Maker/ReadWalks.lean, ReadNodes.lean, OneRoot.lean and TableChain.lean say of one opening.

Main names:
  `walked_given`: the given digests of an opening that was read have 32 bytes each.
  `walked_size`: so has every value among the vertices met, at a hash whose answers have the
    format's lengths. `walked_size_H`: at the format's hash.
  `own_walked`: every member of `ownRowsW` is `Walked` at the one digest cfg of the three
    descriptions.
  `own_size`: every vertex met in a member of `ownRowsW` has a value of 32 bytes.
  `opensTree_leaves`: at each listed position the bottom level holds the leaf's digest, made at the
    start `runOfTree W r j`.
Limits: that the three descriptions have one configuration's digest is a premise of `own_walked`.
Nothing on soundness (index binding included), what a root fixes, opening-form binding, no two
openings of a commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.TableChain
import Fmt.Rules23Laws

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ _root_.Run.WalkTie Octopus
open OnBytes.Three (rootsIn)
open OnBytes.Params (Rounds)

section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray)

/-- The given digests of an opening that was read have 32 bytes each. -/
theorem walked_given {y : OpenedY} (W : Walked h cfg y) : ∀ g ∈ y.2.2.given, g.size = 32 := by
  obtain ⟨f, salt, start, b, i, e⟩ := W
  obtain ⟨hl, cs, hp, -, -⟩ := readOpening_some h cfg f salt y.1 start y.2.1 b i y.2.2 e
  have ok := open_ok f salt y.1 y.2.1 b i cs y.2.2.given y.2.2.next hp hl
  unfold OpenB.ok at ok
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ok
  exact ok.2

/-- **Every value among the vertices met has 32 bytes.** -/
theorem walked_size (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = Fmt.dlen n) {y : OpenedY}
    (W : Walked h cfg y) : ∀ u ∈ y.2.2.seen, u.2.2.size = 32 := by
  have hg := walked_given h cfg W
  obtain ⟨f, salt, start, b, i, e⟩ := W
  obtain ⟨hl, r1, r2, r3, r4, r5⟩ := reader_seen h cfg f salt y.1 start y.2.1 b i y.2.2 e
  have hn : need y.1.a y.2.1 ≤ y.2.2.given.length := le_of_eq r3.symm
  intro u hu
  rw [r5] at hu
  exact InLv_all (fun l r => h 166 0 0 cfg (l ++ r)) (fun x => x.size = 32)
    (fun a b => hz 166 0 0 cfg (a ++ b))
    (TieTree.size_stepF _ (fun a b => hz 166 0 0 cfg (a ++ b))) y.1.a y.2.1 _ y.2.2.given hn
    (leafV_size h hz y.1 start y.2.1 _) hg u.1 (u.2.1, u.2.2) ((mem_seen_iff _ _ _ _ _ u).1 hu)

end

/-- The same at the format's hash. -/
theorem walked_size_H (cfg : ByteArray) {y : OpenedY} (W : Walked Fmt.formatHash cfg y) :
    ∀ u ∈ y.2.2.seen, u.2.2.size = 32 :=
  walked_size Fmt.formatHash cfg Fmt.size_H W

/-- **Every opening of a tree, at one configuration's digest.** -/
theorem own_walked (W : Three.Whole) (cfg : ByteArray) (S₁ S₂ S₃ : Fmt.SpecX) (r : Proof.TailRead)
    (b : ByteArray) (n₁ n₂ n₃ : Fmt.Seen) (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ)
    (e₁ : readChain S₁ n₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ n₃ b i₃ = some (r.second.out, j₃)) (c₁ : S₁.base.cfg = cfg)
    (c₂ : S₂.base.cfg = cfg) (c₃ : S₃.base.cfg = cfg) :
    ∀ z ∈ ownRowsW W r, Walked Fmt.formatHash cfg z.2 := by
  obtain ⟨w₁, -⟩ := readChain_entered S₁ n₁ b i₁ _ j₁ e₁
  obtain ⟨w₂, -⟩ := readChain_entered S₂ n₂ b i₂ _ j₂ e₂
  obtain ⟨w₃, -⟩ := readChain_entered S₃ n₃ b i₃ _ j₃ e₃
  rw [c₁] at w₁
  rw [c₂] at w₂
  rw [c₃] at w₃
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · obtain ⟨ro, hro, hy⟩ := own_mem hz
    exact w₁ ro hro z.2 hy
  · rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨ro, hro, hy⟩ := own_mem hz
      exact w₂ ro hro z.2 hy
    · obtain ⟨ro, hro, hy⟩ := own_mem hz
      exact w₃ ro hro z.2 hy

/-- **Every vertex met in an opening of a tree has a value of 32 bytes.** -/
theorem own_size (W : Three.Whole) (S₁ S₂ S₃ : Fmt.SpecX) (r : Proof.TailRead) (b : ByteArray)
    (n₁ n₂ n₃ : Fmt.Seen) (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ)
    (e₁ : readChain S₁ n₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ n₃ b i₃ = some (r.second.out, j₃)) :
    ∀ z ∈ ownRowsW W r, ∀ u ∈ z.2.2.2.seen, u.2.2.size = 32 := by
  obtain ⟨w₁, -⟩ := readChain_entered S₁ n₁ b i₁ _ j₁ e₁
  obtain ⟨w₂, -⟩ := readChain_entered S₂ n₂ b i₂ _ j₂ e₂
  obtain ⟨w₃, -⟩ := readChain_entered S₃ n₃ b i₃ _ j₃ e₃
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · obtain ⟨ro, hro, hy⟩ := own_mem hz
    exact walked_size_H _ (w₁ ro hro z.2 hy)
  · rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨ro, hro, hy⟩ := own_mem hz
      exact walked_size_H _ (w₂ ro hro z.2 hy)
    · obtain ⟨ro, hro, hy⟩ := own_mem hz
      exact walked_size_H _ (w₃ ro hro z.2 hy)

/-- **The opened leaves' digests, at the start that the tables lay.** -/
theorem opensTree_leaves {R₁ R₂ R₃ : Rounds} {r : Proof.TailRead}
    (h₁ : rootsIn R₁ = r.first.roots.length) (h₂ : rootsIn R₂ = r.shared.roots.length)
    (h₃ : rootsIn R₃ = r.second.roots.length) {x : ℕ × Opened}
    (O : OpensTree (Three.Whole.of R₁ R₂ R₃) r x) :
    ∃ start, runOfTree (Three.Whole.of R₁ R₂ R₃) r x.1 = some start ∧
      ∀ c ∈ x.2.2.1.zip (leafV Fmt.formatHash x.2.1 start x.2.2.1 (x.2.2.2.cols.zip x.2.2.2.salts)),
        seenAt x.2.2.2.seen x.2.1.a c.1 = some c.2 := by
  obtain ⟨start, hs, cfg, f, salt, b, i, e⟩ := opensTree_run h₁ h₂ h₃ O
  exact ⟨start, hs, (opening_nodes Fmt.formatHash cfg f salt x.2.1 start x.2.2.1 b i x.2.2.2 e).2.1⟩

end OnBytes.Maker
