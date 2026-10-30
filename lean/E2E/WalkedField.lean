-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/WalkedField.lean: along a walk (`WalkedFrom`, E2E/WalkedFrom.lean) the field `opened` of a state holds what the
thread's columns say, at every set of tables that the thread's clause on tables allows.

Why. A half behind the guard needs the field, and the last chain's door reads it at the last borders of the first two
chains. The field is laid by `Mid.took`, one sub-protocol at a time.

Main names.
  `hand_next`: behind a sub-protocol's rounds the clause on tables holds at the next border, at the rounds' tables,
    where the sub-protocol's new trees show what the thread names.
  `walked_field`: the field at every border of a walk.

What stays open. As premises: `hfit`: the thread's tests; `hO`, `hD`: every source that a round opens is at hand, with
its depth; `hTrees`: at each sub-protocol below the border its new trees show what the thread names: this is the last
clause of `Plays`, and it is no consequence of the letter. `hBegun`: the field at the start.

No law over coins.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.WalkedFrom
import Johnson.Desc.ProofFile.Honest.Thread.ThrFieldNext
import Johnson.Desc.ProofFile.Honest.Thread.ThrFieldStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Cl V W X Pb}

/-- **The clause on tables, at the next border.** -/
theorem hand_next {n b : Nat} (hfit : T.fits n = true) (hb : b < n) {k : Coins Bk} {s : S}
    {m : Mid W X} {E : Env} {l : List (Step W X)} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
    (hy : play l ds [] m = .ok y) (hFresh : T.Trees (T.fresh b) k y.2 (E.add y.1)) :
    T.Hand (b + 1) k (y.2.took cols) (E.add y.1) := by
  obtain ⟨⟨hSt, hTr⟩, hF0, -, -, hM0, -, -⟩ := hT
  obtain ⟨-, -, -, hTi, -⟩ := hM0
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hlen := T.heard_length hF0
  obtain ⟨hfx, -⟩ := T.fits_parts hfit
  refine ⟨fun i x => ?_, fun σ hσ => ?_⟩
  · show E.stored i x = T.stored y.2.st.input i x
    rw [ei]
    exact hSt i x
  · by_cases ho : σ ∈ T.hand b
    · refine T.handAt_next (m := m) ei eh ?_ hTi (hTr σ ho)
      rw [hlen]
      exact hfx b (Nat.le_of_lt hb) σ ho
    · have hm : σ ∈ T.fresh b := List.mem_filter.2 ⟨hσ, by simp [ho]⟩
      exact hFresh σ hm

variable {Begun : Coins Bk → Mid W X → Prop}

/-- **The field along a walk.** -/
theorem walked_field {n : Nat} {base : List OpenedColumn} (hfit : T.fits n = true)
    (hO : ∀ b, b ≤ n → T.opensAvailable b = true)
    (hD : ∀ b, b ≤ n → ∀ k m, DepthsAt T b k m)
    (hTrees : ∀ b, b < n → ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, Thr T b k s m E →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1))
    (hBegun : ∀ k m, Begun k m → m.opened = some base) {b : Nat} {k : Coins Bk} {m : Mid W X}
    (hb : b ≤ n) (h : WalkedFrom T Begun b k m) :
    ∀ E, T.Hand b k m E → T.Field base b m E := by
  induction h with
  | begun h₀ =>
    intro E _
    exact (T.field_zero_iff base _ E).2 (hBegun _ _ h₀)
  | @next b blk k s m E ds y cols _ hblk hT hd hM ih =>
    intro E' hE'
    have hF := ih (by omega) E hT.1
    have hF₁ := T.field_next hblk hT hF hM
    obtain ⟨⟨l, hl, hp⟩, hc⟩ := id hM
    have hH := hand_next (cols := cols) hfit (by omega) hT hp
      (hTrees b (by omega) blk hblk k s m E ds y cols hT hM)
    obtain ⟨c, hc₁, ho⟩ := (field_iff T base _ _ _).1 hF₁
    refine (field_iff T base _ _ _).2 ⟨c, ?_, ho⟩
    rw [← T.colsTo_congr_at hH hE' (hO _ hb) (hD _ hb _ _)]
    exact hc₁

end ProofFile.Honest

#print axioms ProofFile.Honest.hand_next
#print axioms ProofFile.Honest.walked_field
