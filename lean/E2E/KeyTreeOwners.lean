-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyTreeOwners.lean: whose the trees of the shared chain are, by number.

Why. `tbKey` (E2E/KeyTreesKey.lean) has a letter for the tests' own trees. Which numbers those are, and whose, is
held here, by Lean's kernel, and tied to the thread's own numbering.

Main names.
  `owners`, `ownerAt`: each block's place with its count of trees, at the written value; whose tree a number is.
  `eight_owners`, `tests_owners`: own 0 to 2 are the sendings'; own 3 to 10 the two tests': four at G_u, four at
    G_omega; own 11 is nobody's in this list. By Lean's kernel.
  `sendings_count`: the two sendings send the first three trees.
  `chain_counts`: the thread's `treesTo` at 9, 10, 11 is 3, 7, 11: so `owners`, a list by hand, numbers as the
    chain does.

What stays open. No table's place is tried here, and nothing plays a test.

No statement here names a coin of the committer: `k` enters only as a letter of a table's function.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyTreesKey
import E2E.KeyFreshTreePlace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.KeyTblTrial
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (OracleNotice TreeLay TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Claim sharedTests keyAsProof)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open _root_.Desc.K14 (P14 St blocks blocksOr)
open _root_.Desc.K14.Honest (Eight FlatOf flatOf_carried)
open AtPublicFiles.AtFiles.Full (QK PF blocksOr_eight)
open AtPublicFiles.KeyBook (foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyThread (sentIn sendRound_append rootsOf)
open AtPublicFiles.KeyTreesKey (declOf treesOf5 sends_closed sentIn_prefix rounds_five)

/-- Each block's place with its count of trees, in the chain's order, the eight then the tests. -/
def owners : List (Place × Nat) :=
  ((blocksOr QK).map fun b => (b.place, (b.oracles.flatMap id).length)) ++
    (((H2K.JointK.keyGu PF).place, ((H2K.JointK.keyGu PF).oracles.flatMap id).length) ::
      (PF.O.toList.map H2K.JointK.keyOmega).map fun b => (b.place, (b.oracles.flatMap id).length))

/-- Whose tree a number is. -/
def ownerAt : List (Place × Nat) → Nat → Option Place
  | [], _ => none
  | (p, c) :: t, n => if n < c then some p else ownerAt t (n - c)

/-- **Own 0 to 2 are the two sendings'.** By Lean's kernel. -/
theorem eight_owners :
    (List.range 3).all (fun n => ownerAt owners n == some (sendPlace 2) ||
      ownerAt owners n == some (sendPlace 5)) = true := by
  decide +kernel

/-- The two sendings send the trees in front of the tests. -/
theorem sendings_count : treesU QK + treesOf5 QK = 3 := by
  decide +kernel

/-- Own 3 to 6 at G_u, own 7 to 10 at G_omega, and no other. -/
theorem tests_owners :
    (List.range 4).all (fun i => ownerAt owners (3 + i) == some foldedTestPlace) = true ∧
    (List.range 4).all (fun i => ownerAt owners (7 + i) == some omegaTestPlace) = true ∧
    ownerAt owners 11 = none := by
  decide +kernel

/-- The counts of trees of the last three of the eight, at the written value. -/
theorem rest_zero : ((blocksOr QK).map fun b => (b.oracles.flatMap id).length).drop 5 = [0, 0, 0] := by
  decide +kernel

/-- The counts of the two tests' blocks, at the written value. -/
theorem tests_count : ((H2K.JointK.keyGu PF).oracles.flatMap id).length = 4 ∧
    (PF.O.toList.map H2K.JointK.keyOmega).map (fun b => (b.oracles.flatMap id).length) = [4] := by
  decide +kernel

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **The thread's own numbering, at the written places**: three trees in front of member 9, seven in
front of member 10, eleven behind it. So `owners` is the chain's. -/
theorem chain_counts (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF)) :
    treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 9 = 3 ∧
    treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 10 = 7 ∧
    treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 11 = 11 := by
  have h9 := (AtPublicFiles.KeyDoorNine.seat_nine Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w B).1
  have F := flatOf_carried (Cl := Claim) (keyAsProof Xs.chains) (parKey Xs PF) B.b1 B.b2 B.b3 B.b4 B.b5
    B.b6 B.b7 B.b8 (sharedTests PF) VerifiableInference.Desc.K12.Seat.last B.made
  obtain ⟨-, t5, -, -⟩ := flat_counts F B.made
  have t5' : treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 5 = treesU (parKey Xs PF) := t5.trans (trees_b2 B.made)
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, hxs, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have hbs : (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := hxs
  have g5 : (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs[5]? = some x5 := by rw [hbs]; rfl
  have g6 : (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs[6]? = some x6 := by rw [hbs]; rfl
  have g7 : (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs[7]? = some x7 := by rw [hbs]; rfl
  have g8 : (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs[8]? = some x8 := by rw [hbs]; rfl
  have hb : blocksOr (parKey Xs PF) = [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] := by
    unfold blocksOr
    rw [B.made]
    rfl
  have rz := rest_zero
  rw [← e, hb] at rz
  simp only [List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero, List.cons.injEq,
    and_true] at rz
  obtain ⟨z6, z7, z8⟩ := rz
  have c5 : (B.b5.oracles.flatMap id).length = treesOf5 (parKey Xs PF) := by
    unfold treesOf5
    rw [hb]
    rfl
  have sc := sendings_count
  rw [← e] at sc
  have t6 : treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 6 = treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 5 + (x5.oracles.flatMap id).length :=
    AtPublicFiles.KeyFreshTrial.treesTo_succ g5
  have t7 : treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 7 = treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 6 + (x6.oracles.flatMap id).length :=
    AtPublicFiles.KeyFreshTrial.treesTo_succ g6
  have t8 : treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 8 = treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 7 + (x7.oracles.flatMap id).length :=
    AtPublicFiles.KeyFreshTrial.treesTo_succ g7
  have t9 : treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 9 = treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 8 + (x8.oracles.flatMap id).length :=
    AtPublicFiles.KeyFreshTrial.treesTo_succ g8
  rw [l5.oracles, c5] at t6
  rw [l6.oracles, z6] at t7
  rw [l7.oracles, z7] at t8
  rw [l8.oracles, z8] at t9
  have n9 : treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 9 = 3 := by omega
  have t10 : treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 10 =
      treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 9 + ((H2K.JointK.keyGu PF).oracles.flatMap id).length :=
    AtPublicFiles.KeyFreshTrial.treesTo_succ h9
  obtain ⟨cg, co⟩ := tests_count
  rw [cg] at t10
  have h10 : ∃ x, (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs[10]? = some x ∧ (x.oracles.flatMap id).length = 4 := by
    have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w
    rw [hO.bs]
    show ∃ x, (AtPublicFiles.AtFiles.flat₂ Xs.chains PF)[10]? = some x ∧ _
    rw [AtPublicFiles.AtFiles.flat₂_cut]
    cases hl : PF.O.toList with
    | nil =>
      rw [hl] at co
      cases co
    | cons a t =>
      rw [hl] at co
      simp only [List.map_cons, List.cons.injEq] at co
      refine ⟨H2K.JointK.keyOmega a, ?_, co.1⟩
      have hp : (H2K.JointK.keySharedPre Xs.chains PF ++ [H2K.JointK.keyGu PF]).length = 10 := by
        unfold H2K.JointK.keySharedPre
        rw [List.length_append, List.length_cons, List.length_map, AtPublicFiles.AtFiles.Full.blocksOr_eight B]
        rfl
      have := AtPublicFiles.KeyDoorNine.get_at (H2K.JointK.keySharedPre Xs.chains PF ++ [H2K.JointK.keyGu PF])
        (H2K.JointK.keyOmega a)
        (t.map H2K.JointK.keyOmega ++ [H2K.JointK.keySharedEnd Xs.chains PF]) 10 hp
      simpa using this
  obtain ⟨x, hx, cx⟩ := h10
  have t11 : treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 11 = treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 10 + (x.oracles.flatMap id).length :=
    AtPublicFiles.KeyFreshTrial.treesTo_succ hx
  rw [cx] at t11
  exact ⟨n9, by omega, by omega⟩

end

end AtPublicFiles.KeyTblTrial

#print axioms AtPublicFiles.KeyTblTrial.eight_owners
#print axioms AtPublicFiles.KeyTblTrial.sendings_count
#print axioms AtPublicFiles.KeyTblTrial.tests_owners
#print axioms AtPublicFiles.KeyTblTrial.rest_zero
#print axioms AtPublicFiles.KeyTblTrial.tests_count
#print axioms AtPublicFiles.KeyTblTrial.chain_counts
