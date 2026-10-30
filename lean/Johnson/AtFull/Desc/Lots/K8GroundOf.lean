-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K8GroundOf.lean: THE SMALLNESS TEST'S LOT, ITS FIRST ROW: ITS FOURTH
HYPOTHESIS `k8GroundB G = true` PARTED IN TWO: one half follows from the second row's hypothesis by
arithmetic; the other comes down, in the goals' scope, to ONE CLOSED TEST ON THE PUBLIC PART. No
soundness is claimed.

Why. `k8_row_at` (Johnson/AtFull/Desc/Lots/K8Row.lean) stands under hn : `k8GroundB G = true`: at
each built link "a matrix, a column and a combination are there" (`k8PreB`) and "no family of tables
is empty or sums over no row" (`k8AsksB`). It is one test over several fields of the ground. Here it
is said what each half reads.
  `k8PreB X` reads the link's matrices' numbers of columns and its number of combinations: what the
    second row's test `k8TritsB` (Johnson/AtFull/Rounds/K8.lean) reads. That test says that their
    product is a written number above 0: so the sum is not 0, the number is not 0, and a matrix is
    there.
  `k8AsksB G X` reads of the built link its kind and its group's number alone, and all else of the
    ground's public part. In the goals' scope the 25 links' kinds and groups are known
    (`IM.ground_named`, Johnson/IMR/PureJoin.lean), and the ground's public part is the public
    value's (`ProofFile.Law.blankBy_W`).

Main names.
  `k8AsksW W kind g`: the lot's families of tables, with the public part, the kind and the group as
    letters. `k8Asks_is`: by definition it is `ProofFile.k8Asks`.
  `k8OkL l`: the list is NOT EMPTY, and no family in it is empty or sums over no row. STRICTER THAN
    THE ROW ASKS: `k8AsksOn` accepts the empty list.
  `k8AsksWB W`: **THE ONE CLOSED TEST ON THE PUBLIC PART**: `k8OkL` at the output head's list; and
    at each group below 12: an attention plan is there, and `k8OkL` at the attention's and at the
    feed-forward link's list.
  `k8PreOn_of_pos`, `k8PreB_of_trits`: the first half, by arithmetic.
  `k8AsksB_of_test`: the second half, in scope, from a yes of that test.
  `k8GroundB_of_asks`: **in scope, the files read, `ProofFile.pubPlain` and `ProofFile.blankBy` returned:
    `k8TritsB G = true` and `k8AsksWB Z.p.X = true` give `k8GroundB G = true`.**
  `k8OkL_bent`: on plain numbers: it can fail in three ways; the empty list is one.

Limits. THE TWO HYPOTHESES ARE SHOWN AT NO GROUND AND NO PUBLIC PART HERE. The test is stricter than
what it pays: where it says no, the row's hypothesis may still hold. At the second hash function
alone. The full size alone. No soundness is claimed.

-/
import Johnson.AtFull.Rounds.K8
import Johnson.IMR.PureJoin
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8L
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.First (K8.Asks.head K8.Asks.attention K8.Asks.layers)

/-! ### plain data -/

/-- The lot's families of tables, with the public part, the kind and the group as letters. -/
def k8AsksW (W : Verify.Public) (kind g : Nat) : List (Nat × Nat × Nat) :=
  if kind == 2 then K8.Asks.head W.hS
  else if kind == 1 then ((W.A[g]?).map fun P => K8.Asks.attention P.S).getD []
  else K8.Asks.layers W.y W.layers.rd g

/-- By definition. -/
theorem k8Asks_is (G : ProofFile.Ground) (X : LinkH) : ProofFile.k8Asks G X = k8AsksW G.W X.kind X.g := rfl

/-- Not empty, and no family in it is empty or sums over no row. -/
def k8OkL (l : List (Nat × Nat × Nat)) : Bool := !l.isEmpty && k8AsksOn l

/-- It can fail: the empty list; an empty family; a family that sums over no row. -/
theorem k8OkL_bent :
    k8OkL [(0, 2, 8)] = true ∧ k8OkL [] = false ∧ k8OkL [(0, 0, 8)] = false ∧
      k8OkL [(0, 2, 0)] = false := by decide

/-- **The one closed test on the public part.** -/
def k8AsksWB (W : Verify.Public) : Bool :=
  k8OkL (k8AsksW W 2 0) && (List.range 12).all fun g =>
    (W.A[g]?).isSome && k8OkL (k8AsksW W 1 g) && k8OkL (k8AsksW W 0 g)

/-! ### the first half -/

/-- Where the product is above 0: a matrix, a column and a combination are there. -/
theorem k8PreOn_of_pos (ks : List Nat) (tau : Nat) (h : 0 < ks.foldl (· + ·) 0 * tau) :
    k8PreOn ks tau = true := by
  have hs : ks.foldl (· + ·) 0 ≠ 0 := fun e => by
    rw [e, Nat.zero_mul] at h
    exact absurd h (Nat.lt_irrefl 0)
  have ht : tau ≠ 0 := fun e => by
    rw [e, Nat.mul_zero] at h
    exact absurd h (Nat.lt_irrefl 0)
  cases ks with
  | nil => exact absurd rfl hs
  | cons a t =>
    unfold k8PreOn
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨rfl, bne_iff_ne.2 hs⟩, bne_iff_ne.2 ht⟩

/-- The written numbers are above 0. -/
theorem k8TritsW_pos (kind : Nat) : 0 < k8TritsW kind := by
  unfold k8TritsW
  split
  · omega
  · split <;> omega

/-- The first half at a link, from the second row's equation there. -/
theorem k8PreB_of_trits {X : LinkH} (h : k8TritsOf X = k8TritsW X.kind) : k8PreB X = true :=
  k8PreOn_of_pos _ _ (by
    have e : (X.tl.mats.toList.map (·.k)).foldl (· + ·) 0 * X.tl.tau = k8TritsW X.kind := h
    rw [e]
    exact k8TritsW_pos X.kind)

/-! ### the second half -/

theorem k8AsksOn_of_ok {l : List (Nat × Nat × Nat)} (h : k8OkL l = true) : k8AsksOn l = true := by
  unfold k8OkL at h
  rw [Bool.and_eq_true] at h
  exact h.2

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}

/-- The second half, in scope, from a yes of the test on the public part. -/
theorem k8AsksB_of_test (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (hw : k8AsksWB Z.p.X = true) :
    ∀ X ∈ G.built.toList, k8AsksB G X = true := by
  have eW : G.W = Z.p.X := ProofFile.Law.blankBy_W hG
  obtain ⟨h25, -⟩ := IM.ground_gets hS hR hZ hG
  obtain ⟨nLA, lH, nH, kH, -⟩ := IM.ground_named hS hR hZ hG
  unfold k8AsksWB at hw
  rw [Bool.and_eq_true] at hw
  obtain ⟨hH, hA⟩ := hw
  intro X hXm
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hXm
  have hl25 : l < 25 := by
    rw [Array.length_toList, h25] at hl
    exact hl
  have hat : G.built[l]? = some G.built.toList[l] := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hl]
  generalize G.built.toList[l] = X at hat
  unfold k8AsksB
  rw [k8Asks_is, eW]
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : X = lH := Option.some.inj (hat.symm.trans nH)
    rw [kH]
    exact k8AsksOn_of_ok hH
  · obtain ⟨a0, a1, n0, k0, g0, -, n1, k1, g1, -⟩ := nLA (l / 2) (by omega)
    have hg := List.all_eq_true.1 hA (l / 2) (List.mem_range.2 (by omega))
    rw [Bool.and_eq_true, Bool.and_eq_true] at hg
    rcases Nat.mod_two_eq_zero_or_one l with ev | od
    · rw [show 2 * (l / 2) = l by omega] at n0
      obtain rfl : X = a0 := Option.some.inj (hat.symm.trans n0)
      rw [k0, g0]
      exact k8AsksOn_of_ok hg.2
    · rw [show 2 * (l / 2) + 1 = l by omega] at n1
      obtain rfl : X = a1 := Option.some.inj (hat.symm.trans n1)
      rw [k1, g1]
      exact k8AsksOn_of_ok hg.1.2

/-! ### the hypothesis -/

/-- **The first row's fourth hypothesis, from the second row's and one test on the public part.** -/
theorem k8GroundB_of_asks (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (ht : k8TritsB G = true)
    (hw : k8AsksWB Z.p.X = true) : k8GroundB G = true := by
  unfold k8GroundB
  rw [List.all_eq_true]
  intro X hX
  rw [Bool.and_eq_true]
  exact ⟨k8PreB_of_trits (eq_of_beq (List.all_eq_true.1 ht X hX)),
    k8AsksB_of_test hS hR hZ hG hw X hX⟩

end P1K8L

#print axioms P1K8L.k8Asks_is
#print axioms P1K8L.k8OkL_bent
#print axioms P1K8L.k8PreOn_of_pos
#print axioms P1K8L.k8TritsW_pos
#print axioms P1K8L.k8PreB_of_trits
#print axioms P1K8L.k8AsksOn_of_ok
#print axioms P1K8L.k8AsksB_of_test
#print axioms P1K8L.k8GroundB_of_asks
