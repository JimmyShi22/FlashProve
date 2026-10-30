-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Gap.lean: a part is handed the columns opened so far (`Seen.opened`,
from `Mid.opened`). This file proves, for every description and prover, where that field is filled
and where it is not.

  1  `play_opened`, `midIn_opened`   `play` and `midIn` leave the field as it is
  2  `midAt_none`, `midSharedAt_none`   **a state made by `midAt` or `midSharedAt` has
     `opened = none`**
  3  `midInW_some`, `midAtW_some`, `midSharedAtW_some`   **a state made by `midAtW` or
     `midSharedAtW` (MidW.lean) has `opened = some …`**
  4  `midAt_ne_midAtW`   so the two are never the same state
  5  `took_opened`, `append_self`, `field_at_play`, `field_at_took`   after a sub-protocol that has
     read columns `cols ≠ []`: the state that `play` returns does not have them in its field, and
     `Mid.took` of it has. This holds at every sub-protocol

What follows for `Good` (Side.lean). `Good.plays` says `B` at `y.2.took cols`, where `y` is what
`play` returns. At `y.2` itself a `B` that says "the field holds the columns up to here" is false
after every sub-protocol that reads a column (`field_at_play`). At `y.2.took cols` it holds
(`field_at_took`).

Limits.
  * Nothing is said on whether `midAt` and `midAtW` agree in their other fields. They need not: a
    part that reads the field may say another message.
  * Which columns the field holds is not said here (WalkOpened.lean).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.MidW
import Johnson.Desc.ProofFile.Honest.WalkOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription OpenedColumn)

variable {S Cl Xi W₀ Rc Ky Tr X₀ X W Y : Type}

/-! ## 1 `play` leaves the field -/

theorem play_opened : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W Y) (y : List Played × Mid W Y), play ss ds back m = .ok y → y.2.opened = m.opened
  | [], [], _, m, y, h => by
    rw [play] at h
    obtain rfl := Except.ok.inj h
    rfl
  | s :: ss, d :: ds, back, m, y, h => by
    rw [play] at h
    obtain ⟨x, -, h⟩ := of_bind_ok h
    obtain ⟨m', h1, h⟩ := of_bind_ok h
    obtain ⟨y', h2, rfl⟩ := map_ok h
    exact (play_opened ss ds back.tail m' y' h2).trans (hear_opened h1)
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h

theorem midIn_opened {steps : List (Step W Y)} {ds : List Fmt.Drawn} {back : List Fmt.RoundView}
    {m m' : Mid W Y} {a : Addr} (h : midIn steps ds back m a = .ok m') : m'.opened = m.opened := by
  unfold midIn at h
  split at h
  · cases h
  · obtain ⟨y, hy, rfl⟩ := map_ok h
    exact play_opened _ _ _ _ _ hy

/-! ## 2 The states by `play` -/

/-- **A state made by `midAt` hands no columns.** -/
theorem midAt_none {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {c : Coins B} {ρ : Draws} {a : Addr} {m : Mid (Local W₀ Rc Xi Tr) X}
    (h : midAt F B H w₀ rc x c ρ a = .ok m) : m.opened = none := by
  unfold midAt at h
  obtain ⟨R, -, h⟩ := of_bind_ok h
  split at h
  · exact midIn_opened h
  · obtain ⟨r, -, h⟩ := of_bind_ok h
    exact midIn_opened h

theorem midSharedAt_none {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws} {a : Addr} {m : Mid (Common W₀ Rc Ky) X₀}
    (h : midSharedAt F B H w₀ rc x c ρ a = .ok m) : m.opened = none := by
  unfold midSharedAt at h
  obtain ⟨R, -, h⟩ := of_bind_ok h
  exact midIn_opened h

/-! ## 3 The states by the walk -/

theorem midInW_some {L : Lay} {front : List OpenedColumn} {steps : List (Step W Y)} {ds : List Fmt.Drawn}
    {z : ChainProgress S Cl W Y} {a : Addr} {m : Mid W Y} (hz : z.Inv front)
    (h : midInW L steps ds z a = .ok (some m)) : ∃ cs, m.opened = some (front ++ cs) := by
  unfold midInW at h
  split at h
  · cases h
  · obtain ⟨z', hw, e⟩ := map_ok h
    exact ⟨z'.cols, walk_inv L front _ _ z z' hz hw m e⟩

/-- **A state made by `midAtW` hands columns.** -/
theorem midAtW_some {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws} {a : Addr} {m : Mid (Local W₀ Rc Xi Tr) X}
    (h : midAtW F B H w₀ rc x c ρ a = .ok (some m)) : ∃ cs, m.opened = some cs := by
  unfold midAtW at h
  obtain ⟨R, -, h⟩ := of_bind_ok h
  obtain ⟨a₁, s1, h⟩ := of_bind_ok h
  split at h
  · obtain ⟨cs, e⟩ := midInW_some (start_inv s1) h
    exact ⟨_, e⟩
  · obtain ⟨z₁, -, h⟩ := of_bind_ok h
    split at h
    · cases h
    · obtain ⟨a₂, -, h⟩ := of_bind_ok h
      obtain ⟨z₂, -, h⟩ := of_bind_ok h
      obtain ⟨a₃, s3, h⟩ := of_bind_ok h
      obtain ⟨cs, e⟩ := midInW_some (start_inv s3) h
      exact ⟨_, e⟩

theorem midSharedAtW_some {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws} {a : Addr} {m : Mid (Common W₀ Rc Ky) X₀}
    (h : midSharedAtW F B H w₀ rc x c ρ a = .ok (some m)) : ∃ cs, m.opened = some cs := by
  unfold midSharedAtW at h
  obtain ⟨R, -, h⟩ := of_bind_ok h
  obtain ⟨a₂, s2, h⟩ := of_bind_ok h
  obtain ⟨cs, e⟩ := midInW_some (start_inv s2) h
  exact ⟨_, e⟩

/-! ## 4 The two are never one -/

theorem midAt_ne_midAtW {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws} {a : Addr} {m m' : Mid (Local W₀ Rc Xi Tr) X}
    (h : midAt F B H w₀ rc x c ρ a = .ok m) (h' : midAtW F B H w₀ rc x c ρ a = .ok (some m')) :
    m ≠ m' := by
  rintro rfl
  obtain ⟨cs, e⟩ := midAtW_some h'
  rw [midAt_none h] at e
  cases e

/-! ## 5 After a sub-protocol that reads columns -/

theorem took_opened (m : Mid W Y) (cols : List OpenedColumn) :
    (m.took cols).opened = m.opened.map (· ++ cols) := rfl

theorem append_self {α : Type} {a b : List α} (h : a = a ++ b) : b = [] := by
  have e := congrArg List.length h
  rw [List.length_append] at e
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- **The state that `play` returns does not have the sub-protocol's own columns in its field.** -/
theorem field_at_play {ss : List (Step W Y)} {ds : List Fmt.Drawn} {m : Mid W Y}
    {y : List Played × Mid W Y} {c₀ cols : List OpenedColumn} (h : play ss ds [] m = .ok y)
    (hm : m.opened = some c₀) (hc : cols ≠ []) : y.2.opened ≠ some (c₀ ++ cols) := by
  rw [play_opened _ _ _ _ _ h, hm]
  exact fun e => hc (append_self (Option.some.inj e))

/-- **`Mid.took` of it has them.** -/
theorem field_at_took {ss : List (Step W Y)} {ds : List Fmt.Drawn} {m : Mid W Y}
    {y : List Played × Mid W Y} {c₀ : List OpenedColumn} (cols : List OpenedColumn) (h : play ss ds [] m = .ok y)
    (hm : m.opened = some c₀) : (y.2.took cols).opened = some (c₀ ++ cols) := by
  rw [took_opened, play_opened _ _ _ _ _ h, hm]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.play_opened
#print axioms ProofFile.Honest.midIn_opened
#print axioms ProofFile.Honest.midAt_none
#print axioms ProofFile.Honest.midSharedAt_none
#print axioms ProofFile.Honest.midInW_some
#print axioms ProofFile.Honest.midAtW_some
#print axioms ProofFile.Honest.midSharedAtW_some
#print axioms ProofFile.Honest.midAt_ne_midAtW
#print axioms ProofFile.Honest.took_opened
#print axioms ProofFile.Honest.append_self
#print axioms ProofFile.Honest.field_at_play
#print axioms ProofFile.Honest.field_at_took
