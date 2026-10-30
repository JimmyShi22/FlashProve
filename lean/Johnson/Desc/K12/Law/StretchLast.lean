-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/StretchLast.lean: closed facts on the first chain's last proximity test (the
kind K12) at the full size: the declared rounds of the closed place `piLFull`, as readers take them,
are a stretch of the written list of the proof file's first chain; and in that list the
test's names begin at one place alone. By the kernel.

Why. StretchFull.lean has the like for the three later places; there the place of a stretch is found
by counting the rounds named "BAT" in front. On the first chain every link has such a round, and
what stands behind the last test is other kinds' text. Here the place is found by the names: the
test's 33 names, in a row, stand in the list's 48,293 names once.
Main names:
  `occE nm i l acc`: the places at which the list nm begins in l, by one walk; `occE_acc`,
    `occE_mem`: every such place is found.
  `xsFirst`: what readers take of the first chain's written list. `namesL`: the names of `piLFull`'s
    declared rounds.
  `rounds_LFull`, `stretch_LFull`, `stretch_LFull_no`: `piLFull` has declared rounds; readers take
    of them the stretch from round 48,237 on; a control: not the stretch from 48,238 on.
  `occ_LFull`: `namesL` begins in the list's names at 48,237 and nowhere else.
  `names_kept`, `at_one_place`: so a list of declared rounds pre ++ (ds ++ post) of which readers
    take `xsFirst`, with ds bearing `namesL`, has 48,237 rounds in pre.
  `roots_front_LFull`: the rounds in front send 77 roots. `none_behind_LFull`: no round behind
    number 48,237 is named "BAT".
  `places_ownL`: `placesOfMade` lays the last test's place without an own mask.
Each long walk makes its number before the next step (`force`, Johnson/G/Eager.lean), so that the
kernel gets through; three lines set `maxRecDepth` as `dryProofFull_length` does.
Limits: the written lists are themselves what a print showed (Johnson/G/DryProofLit.lean). That a
made place's declared rounds bear `namesL` hangs on its stages and bits of work: not shown here. The
full size only. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.StretchFull

set_option autoImplicit false
namespace H2K.Member
open Johnson.G (dryProofFull)
open H2U (roundsOfNums placesOfMade Places4)

/-! ## Where a list of names begins in a longer one -/

/-- The places at which the list nm begins in l, counted from i; the last found stands first. -/
def occE (nm : List String) : Nat → List String → List Nat → List Nat
  | _, [], acc => acc
  | i, x :: xs, acc =>
    Johnson.G.force (i + 1) fun j =>
      occE nm j xs (if nm.isPrefixOf (x :: xs) then i :: acc else acc)

theorem occE_acc (nm : List String) : ∀ (l : List String) (i : Nat) (acc : List Nat) (n : Nat),
    n ∈ acc → n ∈ occE nm i l acc
  | [], _, _, _, h => h
  | x :: xs, i, acc, n, h => by
    simp only [occE, Johnson.G.force_eq]
    refine occE_acc nm xs (i + 1) _ n ?_
    split
    · exact List.mem_cons_of_mem _ h
    · exact h

/-- Every place at which nm begins is found. -/
theorem occE_mem (nm : List String) : ∀ (l : List String) (i : Nat) (acc : List Nat) (a : Nat),
    a < l.length → nm.isPrefixOf (l.drop a) = true → i + a ∈ occE nm i l acc
  | [], _, _, a, h, _ => by simp at h
  | x :: xs, i, acc, 0, _, hp => by
    simp only [occE, Johnson.G.force_eq]
    refine occE_acc nm xs (i + 1) _ _ ?_
    rw [List.drop_zero] at hp
    rw [if_pos hp]
    exact List.mem_cons_self
  | x :: xs, i, acc, a + 1, h, hp => by
    simp only [occE, Johnson.G.force_eq]
    have := occE_mem nm xs (i + 1) (if nm.isPrefixOf (x :: xs) then i :: acc else acc) a
      (by simpa using h) (by simpa using hp)
    have e : i + (a + 1) = i + 1 + a := by omega
    rw [e]
    exact this

/-! ## The closed facts -/

/-- What readers take of the first chain's written list. -/
def xsFirst : List Fmt.Round := dryProofFull.1.map (·.1)

/-- The names of the closed place's declared rounds. -/
def namesL : List String := (dsOf piLFull).map (·.entry.name)

theorem rounds_LFull : roundsOfNums piLFull.nums = some (dsOf piLFull) := by decide +kernel

theorem namesL_length : namesL.length = 33 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem stretch_LFull : (dsOf piLFull).mapM (·.round []) =
    some ((xsFirst.drop 48237).take (dsOf piLFull).length) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: one round later the stretch is another. -/
theorem stretch_LFull_no : ((dsOf piLFull).mapM (·.round []) ==
    some ((xsFirst.drop 48238).take (dsOf piLFull).length)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- In the first chain's written list the test's names begin at one place. -/
theorem occ_LFull : occE namesL 0 (xsFirst.map (·.entry.name)) [] = [48237] := by decide +kernel

set_option maxRecDepth 1000000 in
theorem roots_front_LFull : ((xsFirst.take 48237).map (·.entry.roots)).sum = 77 := by
  have h : rootsE 0 (dryProofFull.1.take 48237) = 77 := by decide +kernel
  rw [rootsE_eq] at h
  unfold xsFirst
  rw [← List.map_take]
  omega

set_option maxRecDepth 1000000 in
theorem none_behind_LFull :
    ((xsFirst.map (·.entry)).drop 48238).filter (fun e => e.name == "BAT") = [] := by
  decide +kernel

/-! ## At one place -/

/-- Readers keep the names. -/
theorem names_kept (e : List (List ByteArray × ByteArray)) :
    ∀ (ds : List Fmt.DeclaredRound) (xs : List Fmt.Round), ds.mapM (·.round e) = some xs →
    xs.map (·.entry.name) = ds.map (·.entry.name)
  | [], xs, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | r :: ds, xs, h => by
    rw [List.mapM_cons] at h
    cases hr : r.round e with
    | none => simp [hr] at h
    | some x =>
      cases hl : ds.mapM (·.round e) with
      | none => simp [hr, hl] at h
      | some ys =>
        simp [hr, hl] at h
        subst h
        rw [List.map_cons, List.map_cons, names_kept e ds ys hl, (H2K.Pub.round_keeps hr).1]

/-- **The test's rounds stand at one place of the first chain.** -/
theorem at_one_place {pre ds post : List Fmt.DeclaredRound} {e : List (List ByteArray × ByteArray)}
    (hx : (pre ++ (ds ++ post)).mapM (·.round e) = some xsFirst)
    (hn : ds.map (·.entry.name) = namesL) : pre.length = 48237 := by
  have h := names_kept e _ _ hx
  rw [List.map_append, List.map_append, hn] at h
  have hl : (pre.map (·.entry.name)).length = pre.length := List.length_map _
  have hp : namesL.isPrefixOf ((xsFirst.map (·.entry.name)).drop pre.length) = true := by
    rw [h, ← hl, List.drop_left]
    exact List.isPrefixOf_iff_prefix.2 ⟨_, rfl⟩
  have hlt : pre.length < (xsFirst.map (·.entry.name)).length := by
    rw [h, List.length_append, List.length_append, hl, namesL_length]
    omega
  have hm := occE_mem namesL _ 0 [] pre.length hlt hp
  rw [occ_LFull] at hm
  simpa using hm

/-! ## The made place -/

/-- `placesOfMade` lays the last test's place without an own mask. -/
theorem places_ownL (m : Johnson.G.OfPlan.Made) (X : Places4) (h : placesOfMade m = .ok X) :
    X.L.nums.ownMask = false := by
  unfold placesOfMade at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          rfl

end H2K.Member

#print axioms H2K.Member.occE_mem
#print axioms H2K.Member.stretch_LFull
#print axioms H2K.Member.occ_LFull
#print axioms H2K.Member.roots_front_LFull
#print axioms H2K.Member.none_behind_LFull
#print axioms H2K.Member.at_one_place
#print axioms H2K.Member.places_ownL
