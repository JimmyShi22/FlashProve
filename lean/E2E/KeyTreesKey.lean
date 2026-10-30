-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyTreesKey.lean: the fields `treesU`, `treesO` of `K14Asks` at the written value, where a tree's
table is fixed after the round that sends it, as the key's shared thread has it (`fixedOwn`,
E2E/KeyThreadBase.lean).

Why. The library pays these fields at `fullOver` (Honest/K14/Thread2Full.lean), whose `fixed` is 1 at
every source. The key's thread counts each tree's own round, and it has to keep `keyProver`'s halves,
which `fullOver` writes over. So the two clauses are asked again here, and the fixed clause can say
no.

Main names.
  `declOf`: the rounds of the eight at a value.
  `sends_closed`: at `QK`: the trees of «send o_u» are sent in round 1, those of «send o_omega» in round
    4, and all of them within the eight. By Lean's kernel.
  `tbKey`: a tree's table, by the two sendings; a letter at a taken tree, and a letter at the tests' own
    trees.
  `rounds_five`: four rounds stand in front of the second sending.
  `treesU_of`, `treesO_of`: the two fields, at any `Others` whose `fixed` is `sentIn` at a list that begins
    with the eight's rounds and whose `table` at an own tree is `tbKey`'s.

What stays open. That the key's `decl₂` has that form is `decl₂_front`'s business, in the file that
lays it at the key. Nothing says that a thread stands.

No statement here names a coin of the committer: `k` enters only as a letter of a table's function.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyShapeSharedTies
import E2E.KeyThreadBase
import Johnson.Desc.ProofFile.Honest.K14.Thread2Full

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.KeyTreesKey
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (OracleNotice TreeLay TableKey)
open VerifiableInference.Desc (Block Place)
open _root_.Desc.K14 (P14 St blocks blocksOr)
open _root_.Desc.K14.Honest (Eight FlatOf flatOf_carried)
open AtPublicFiles.AtFiles.Full (QK blocksOr_eight)
open AtPublicFiles.KeyThread (sentIn sendRound_append rootsOf)

/-- The rounds of the eight, at a value. -/
def declOf (Q : P14) : List Fmt.DeclaredRound := (blocksOr Q).flatMap (·.rounds)

/-- How many trees the second sending declares, at a value. -/
def treesOf5 (Q : P14) : Nat :=
  ((blocksOr Q).map fun b => (b.oracles.flatMap id).length).getD 4 0

/-- **The closed facts at the written value.** -/
theorem sends_closed : 0 < treesU QK ∧ 0 < treesOf5 QK ∧
    treesU QK + treesOf5 QK ≤ rootsOf (declOf QK) ∧
    (List.range (treesU QK)).all (fun i => sentIn (declOf QK) i == 1) = true ∧
    (List.range (treesOf5 QK)).all (fun i => sentIn (declOf QK) (treesU QK + i) == 4) = true ∧
    (blocksOr QK).map (·.rounds.length) = [1, 2, 0, 1, 2, 0, 1, 1] := by
  decide +kernel

/-- A tree sent within the first list of rounds is sent in the same round of a longer one. -/
theorem sentIn_prefix (l₁ l₂ : List Fmt.DeclaredRound) (j : Nat) (h : j < rootsOf l₁) :
    sentIn (l₁ ++ l₂) j = sentIn l₁ j := by
  unfold sentIn
  rw [sendRound_append l₁ l₂ j h]

/-- Four rounds stand in front of the second sending. -/
theorem rounds_five {Cl : Type} {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains}
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (h1 : b1.rounds.length = 1) (h2 : b2.rounds.length = 2) (h3 : b3.rounds.length = 0)
    (h4 : b4.rounds.length = 1) : roundsTo xs 5 = 4 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have r0 : x0.rounds = [] := l0.rounds
  have a1 : x1.rounds.length = 1 := by rw [l1.rounds]; exact h1
  have a2 : x2.rounds.length = 2 := by rw [l2.rounds]; exact h2
  have a3 : x3.rounds.length = 0 := by rw [l3.rounds]; exact h3
  have a4 : x4.rounds.length = 1 := by rw [l4.rounds]; exact h4
  simp [roundsTo, declsTo, r0, a1, a2, a3, a4]

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type}

/-- **A tree's table, by the two sendings.** -/
def tbKey (Q : P14) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (tk : Nat → Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (tt : Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table) :
    Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table
  | .own n =>
    if n < treesU Q then sendTable (jobU ⟨Q, 0⟩) (witOf Q weights rand) (sendPlace 2) 1 n
    else if n < treesU Q + treesOf5 Q then
      sendTable (jobOmega ⟨Q, 0⟩) (witOf Q weights rand) (sendPlace 5) 1 (n - treesU Q)
    else tt n
  | .taken a b => tk a b

variable {sentU : Array OracleNotice} {layO : TreeLay} {O : Others Bk W₀ Rc X₀ P₁ Wt}
  {weights : W₀ → Weights} {rand : Rc → TableRand}
  {tk : Nat → Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table}
  {tt : Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table}

/-- **The field at «send o_u».** -/
theorem treesU_of (hQ : Plan2 QK sentU layO) (Cl : Type) (rest : List Fmt.DeclaredRound)
    (hfx : ∀ j, O.fixed (.own j) = sentIn (declOf QK ++ rest) j)
    (htb : O.table = tbKey QK weights rand tk tt) :
    TreesLaid (letters2 QK sentU O Cl).thread 2 (jobU ⟨QK, 0⟩) (witOf QK weights rand) := by
  obtain ⟨B⟩ := hQ.eight
  have F := flatOf_carried (Cl := Cl) O.c QK B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨t2, -, r2, -⟩ := flat_counts F B.made
  obtain ⟨-, pU, -, -⟩ := send_declares QK 0 B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
  obtain ⟨-, -, hroots, hU, -, -⟩ := sends_closed
  have t2' : treesTo (letters2 QK sentU O Cl).thread.bs 2 = 0 := t2
  have one : ∀ i, i < treesU QK → O.fixed (.own i) = 1 := by
    intro i hi
    rw [hfx, sentIn_prefix _ _ _ (by omega)]
    have := List.all_eq_true.1 hU i (List.mem_range.2 hi)
    simpa using this
  refine ⟨fun blk hblk i hi => ?_, fun blk hblk i hi => ?_⟩
  · have L := F.at2 hblk
    rw [L.oracles, trees_b2 B.made] at hi
    show O.fixed (.own (treesTo _ 2 + i)) ≤ 0 + roundsTo _ 2 ∧
      (jobU ⟨QK, 0⟩).readsBelow (O.fixed (.own (treesTo _ 2 + i)))
    rw [t2', Nat.zero_add, Nat.zero_add, one i hi]
    exact ⟨r2, jobU_readsBelow ⟨QK, 0⟩⟩
  · have L := F.at2 hblk
    rw [L.oracles, trees_b2 B.made] at hi
    show O.table (.own (treesTo _ 2 + i)) = _
    rw [t2', Nat.zero_add, L.place, pU, htb]
    show (if i < treesU QK then _ else _) = _
    rw [if_pos hi]
    rfl

/-- **The field at «send o_omega».** -/
theorem treesO_of (hQ : Plan2 QK sentU layO) (Cl : Type) (rest : List Fmt.DeclaredRound)
    (hfx : ∀ j, O.fixed (.own j) = sentIn (declOf QK ++ rest) j)
    (htb : O.table = tbKey QK weights rand tk tt) :
    TreesLaid (letters2 QK sentU O Cl).thread 5 (jobOmega ⟨QK, 0⟩) (witOf QK weights rand) := by
  obtain ⟨B⟩ := hQ.eight
  have F := flatOf_carried (Cl := Cl) O.c QK B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨-, t5, -, -⟩ := flat_counts F B.made
  obtain ⟨-, -, -, pO⟩ := send_declares QK 0 B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
  obtain ⟨-, -, hroots, -, hO, hr⟩ := sends_closed
  rw [blocksOr_eight B] at hr
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
  obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := hr
  have r5 : roundsTo (letters2 QK sentU O Cl).thread.bs 5 = 4 := rounds_five F h1 h2 h3 h4
  have t5' : treesTo (letters2 QK sentU O Cl).thread.bs 5 = treesU QK := t5.trans (trees_b2 B.made)
  have cnt : (B.b5.oracles.flatMap id).length = treesOf5 QK := by
    unfold treesOf5
    rw [blocksOr_eight B]
    rfl
  have four : ∀ i, i < treesOf5 QK → O.fixed (.own (treesU QK + i)) = 4 := by
    intro i hi
    rw [hfx, sentIn_prefix _ _ _ (by omega)]
    have := List.all_eq_true.1 hO i (List.mem_range.2 hi)
    simpa using this
  refine ⟨fun blk hblk i hi => ?_, fun blk hblk i hi => ?_⟩
  · have L := F.at5 hblk
    rw [L.oracles, cnt] at hi
    show O.fixed (.own (treesTo _ 5 + i)) ≤ 0 + roundsTo _ 5 ∧
      (jobOmega ⟨QK, 0⟩).readsBelow (O.fixed (.own (treesTo _ 5 + i)))
    rw [t5', r5, four i hi]
    exact ⟨by omega, readsBelow_mono (jobOmega_readsBelow ⟨QK, 0⟩) (by decide)⟩
  · have L := F.at5 hblk
    show O.table (.own (treesTo _ 5 + i)) = _
    rw [t5', L.place, pO, htb]
    have hi' : i < treesOf5 QK := by
      rw [L.oracles, cnt] at hi
      exact hi
    show (if treesU QK + i < treesU QK then _ else
      if treesU QK + i < treesU QK + treesOf5 QK then _ else _) = _
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    rfl

end

end AtPublicFiles.KeyTreesKey

#print axioms AtPublicFiles.KeyTreesKey.sends_closed
#print axioms AtPublicFiles.KeyTreesKey.sentIn_prefix
#print axioms AtPublicFiles.KeyTreesKey.rounds_five
#print axioms AtPublicFiles.KeyTreesKey.treesU_of
#print axioms AtPublicFiles.KeyTreesKey.treesO_of
