-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/FirstOpensAll.lean: EVERY OPENING OF THE PROXIMITY TEST's ROUNDS THAT IS OF A TREE TAKEN OVER
STANDS IN THE FIRST SWITCH's CUT: by the make of the place's declared rounds, from the block's own test on
the plan (`open_top`, `Dealt`, `listsOf`: Johnson/Desc/K12/OpenLaws.lean).

Why. It is the premise `all` of `firstOpens_at_last` (Johnson/Desc/K12/Coin/FirstOpensAtLast.lean).
How. The rounds behind "BAT" open `fill (quiet …) (listsOf π.nums)`: each of these lists is empty or a
member of `listsOf π.nums`; its head is what the first switch's cut opens (`opensOf_lists`); every other
member is one tree of the test's own ("own n"). "BAT"'s round opens none.
  `fill_mem`     a list that `fill` lays is empty or one of the lists handed in
  `later_own`    a member of the tail of `listsOf N` holds own trees alone
  `foldl_ge`, `bat_none`   a block without openings: none of its rounds opens a tree (kin:
                 `flat_nil`, Coin/Src.lean, of a cut whose rounds open no stored table)
  `all_taken`    **the premise `all`**
Limits. A fact of make. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.FirstOpensTaken
import Johnson.Desc.K12.Law.StepGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- A list that `fill` lays is empty or one of the lists handed in. -/
theorem fill_mem : ∀ (bs : List Bool) (L : List (List Told)) (y : List Told),
    y ∈ fill bs L → y = [] ∨ y ∈ L
  | [], _, _, h => nomatch h
  | true :: bs, L, y, h => by
    rcases List.mem_cons.1 h with e | h
    · exact Or.inl e
    · exact fill_mem bs L y h
  | false :: bs, x :: L, y, h => by
    rcases List.mem_cons.1 h with e | h
    · exact Or.inr (e ▸ List.mem_cons_self)
    · exact (fill_mem bs L y h).imp id (List.mem_cons_of_mem _)
  | false :: bs, [], y, h => by
    rcases List.mem_cons.1 h with e | h
    · exact Or.inl e
    · exact fill_mem bs [] y h

/-- A member of the tail of the lists that the rounds' maker lays in holds own trees alone. -/
theorem later_own (N : H2U.TestNums) (y : List Told) (hy : y ∈ (listsOf N).tail) :
    ∀ o ∈ y, ∃ n, o.2 = .own n := by
  simp only [listsOf, List.tail_cons, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  intro o ho
  have e : o = x := List.mem_singleton.1 ho
  rw [e]
  have hx' : x ∈ N.sent.zipIdx.map fun t => N.own t.1.1 t.1.2 (N.free + t.2) := by
    split at hx
    · exact List.mem_of_mem_drop hx
    · exact hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx'
  exact ⟨_, rfl⟩

theorem foldl_ge (rs : List Fmt.DeclaredRound) : ∀ a : ℕ,
    a ≤ rs.foldl (fun n r => n + r.stored.length + r.opens.length) a := by
  induction rs with
  | nil => exact fun a => Nat.le_refl a
  | cons r rs ih =>
    intro a
    exact Nat.le_trans (by omega) (ih (a + r.stored.length + r.opens.length))

/-- A block without openings: none of its rounds opens a tree. -/
theorem bat_none {S Cl : Type} (b : Block S Cl) (h : b.openings = 0) : ∀ r ∈ b.rounds, r.opens = [] := by
  unfold Block.openings at h
  generalize b.rounds = rs at h
  induction rs with
  | nil => exact fun _ hr => nomatch hr
  | cons r rs ih =>
    rw [List.foldl_cons] at h
    have g := foldl_ge rs (0 + r.stored.length + r.opens.length)
    rw [h] at g
    have z : r.opens.length = 0 := by omega
    have z' : 0 + r.stored.length + r.opens.length = 0 := by omega
    rw [z'] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact List.length_eq_zero_iff.1 z
    · exact ih h x hx

/-- **Every opening of the block's rounds that is of a tree taken over stands in the first switch's
cut.** -/
theorem all_taken (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) :
    ∀ s rest, π.nums.stages = s :: rest →
      ∀ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, ∀ o ∈ r.opens,
        (∃ c n, o.2 = .taken c n) → o ∈ H2K.First.opensOf π s.k := by
  intro s rest hs r hr o ho ⟨c, n, e⟩
  obtain ⟨first, rest', ds, hs', hds, hbat, hd⟩ := open_top (Cl := Unit) guardedProximityTestParts π hp
  rw [hs] at hs'
  obtain ⟨rfl, rfl⟩ := List.cons.inj hs'
  cases rest with
  | nil =>
    unfold H2U.roundsOfNums at hds
    rw [hs] at hds
    exact nomatch hds
  | cons next rest =>
    rw [H2K.Sw.k12_rounds _ _ hp] at hr
    unfold H2K.JointK.laidOf at hr
    rw [hds, Option.getD_some] at hr
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hr
    rw [← List.take_append_drop 1 (ds.zip π.oracles)] at hy
    rcases List.mem_append.1 hy with hy | hy
    · have z := bat_none _ hbat y.1 (List.mem_map.2 ⟨y, hy, rfl⟩)
      rw [z] at ho
      exact nomatch ho
    · have m : y.1.opens ∈ fill (quiet s (next :: rest)) (listsOf π.nums) := by
        rw [← hd.opens]
        exact List.mem_map.2 ⟨y, hy, rfl⟩
      rcases fill_mem _ _ _ m with z | m
      · rw [z] at ho
        exact nomatch ho
      · rcases List.mem_cons.1 (show y.1.opens ∈ _ :: (listsOf π.nums).tail from m) with z | m
        · rw [opensOf_lists π hp s next rest hs, ← z]
          exact ho
        · obtain ⟨k, hk⟩ := later_own π.nums _ m o ho
          rw [e] at hk
          exact nomatch hk

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.fill_mem
#print axioms VerifiableInference.Desc.K12.Coin.later_own
#print axioms VerifiableInference.Desc.K12.Coin.bat_none
#print axioms VerifiableInference.Desc.K12.Coin.all_taken
