-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/TreesAtShared.lean: the fields `treesU`, `treesO` of `K14Asks`
(Honest/K14/Asks.lean) at a shared thread whose table is `tableShared` (TableShared.lean): at each of the
two sendings the thread's trees are fixed in the sending's round, and its table is the sending's.

  `counts_written`, `counts_bent`   what the written list declares in front of the two sendings, with a
                 control
  `treesU_written`   the first sending has one tree, at the typed sizes
  `treesU_at_shared`, `treesO_at_shared`   the two fields

The thread. Any `Others` (Honest/K14/Thread2Full.lean) whose list is alike to the written one, whose field
`table` is `tableShared`, and whose count at own 0 is 1 and at own 1 and 2 is 4: `fixedShared` at the list's
rounds, by `sent_shared` (TableLines.lean). Not the field written over by `fullOver`: there the count is 1 at
every source, and the trees of the tests need their own rounds.

Limits. A tree's count and table: nothing on what a run sends. Two sendings alone. Nothing on completeness, on
soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TableShared
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensLines
import Johnson.Desc.ProofFile.Honest.K14.Thread2Full

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (OracleNotice TreeLay TableKey)
open VerifiableInference.Desc (Block Place Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open _root_.Desc.K14 (P14 St blocks)
open _root_.Desc.K14.Honest (Eight FlatOf flatOf_carried)
open ProofFile.Honest.K12 (TestJob)
open P2Law.ProofPlan (WP)

/-- What the written list declares in front of the two sendings and at the second. -/
theorem counts_written :
    ((sharedR.take 2).map (·.2)).sum = 0 ∧ ((sharedR.take 5).map (·.2)).sum = 1 ∧
      ((sharedR.take 2).flatMap (·.1)).length = 1 ∧ ((sharedR.take 5).flatMap (·.1)).length = 4 ∧
      (sharedR[5]?).map (·.2) = some 2 := by
  decide +kernel

/-- Control: in front of the second sending stand no five rounds. -/
theorem counts_bent : ((sharedR.take 5).flatMap (·.1)).length ≠ 5 := by decide +kernel

/-- The first sending has one tree. -/
theorem treesU_written : (realSized.all fun q =>
    treesU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape).P == 1) = true := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem treesU_head (h : P5J.AtMg o Z D r Zp Np cF) : treesU (K1.qAt Zp Np) = 1 := by
  obtain ⟨x, hx, Wr⟩ := ProofFile.Honest.K12.Light.written_at_head h
  have k := treesU_written
  rw [hx] at k
  simp only [Option.all_some, beq_iff_eq] at k
  rw [ProofFile.Honest.K12.Light.qAt_written Wr Np]
  exact k

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}
  {O : Others Bk W₀ Rc X₀ P₁ Wt} {weights : W₀ → Weights} {rand : Rc → TableRand}
  {JU JO : TestJob (Common W₀ Rc TableKey) X₀} {own₀ : X₀}

/-- **The field at «send o_u».** -/
theorem treesU_at_shared (hu : treesU Q = 1) (hQ : Plan2 Q sentU layO) (Cl : Type)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder (letters2 Q sentU O Cl).thread.bs)
    (h0 : O.fixed (.own 0) = 1) (htb : O.table = tableShared Q weights rand JU JO own₀) :
    TreesLaid (letters2 Q sentU O Cl).thread 2 (jobU ⟨Q, 0⟩) (witOf Q weights rand) := by
  obtain ⟨B⟩ := hQ.eight
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨-, pU, -, -⟩ := send_declares Q 0 B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
  obtain ⟨c2, -, r2, -, -⟩ := counts_written
  have t2' : treesTo (letters2 Q sentU O Cl).thread.bs 2 = 0 := by
    rw [trees_rounds, ← rounds_alike hl]
    exact c2
  have r2' : roundsTo (letters2 Q sentU O Cl).thread.bs 2 = 1 := by
    unfold roundsTo
    rw [decls_rounds, ← rounds_alike hl]
    exact r2
  refine ⟨fun blk hblk i hi => ?_, fun blk hblk i hi => ?_⟩
  · have L := F.at2 hblk
    rw [L.oracles, trees_b2 B.made, hu] at hi
    obtain rfl : i = 0 := by omega
    show O.fixed (.own (treesTo _ 2 + 0)) ≤ 0 + roundsTo _ 2 ∧
      (jobU ⟨Q, 0⟩).readsBelow (O.fixed (.own (treesTo _ 2 + 0)))
    rw [t2', r2', Nat.zero_add, h0]
    exact ⟨by omega, jobU_readsBelow ⟨Q, 0⟩⟩
  · have L := F.at2 hblk
    rw [L.oracles, trees_b2 B.made] at hi
    show O.table (.own (treesTo _ 2 + i)) = _
    rw [t2', Nat.zero_add, L.place, pU, htb]
    show (if i < treesU Q then _ else _) = _
    rw [if_pos hi]
    rfl

/-- **The field at «send o_omega».** -/
theorem treesO_at_shared (hu : treesU Q = 1) (hQ : Plan2 Q sentU layO) (Cl : Type)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder (letters2 Q sentU O Cl).thread.bs)
    (h1 : ∀ i, i < 2 → O.fixed (.own (1 + i)) = 4)
    (htb : O.table = tableShared Q weights rand JU JO own₀) :
    TreesLaid (letters2 Q sentU O Cl).thread 5 (jobOmega ⟨Q, 0⟩) (witOf Q weights rand) := by
  obtain ⟨B⟩ := hQ.eight
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨-, -, -, pO⟩ := send_declares Q 0 B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
  obtain ⟨-, c5, -, r5, m5⟩ := counts_written
  have t5' : treesTo (letters2 Q sentU O Cl).thread.bs 5 = 1 := by
    rw [trees_rounds, ← rounds_alike hl]
    exact c5
  have r5' : roundsTo (letters2 Q sentU O Cl).thread.bs 5 = 4 := by
    unfold roundsTo
    rw [decls_rounds, ← rounds_alike hl]
    exact r5
  have cnt : ∀ blk, (letters2 Q sentU O Cl).thread.bs[5]? = some blk →
      (blk.oracles.flatMap id).length = 2 := fun blk hblk => by
    have e : sharedR = (letters2 Q sentU O Cl).thread.bs.map roundsTrees := rounds_alike hl
    rw [e, List.getElem?_map, hblk] at m5
    exact Option.some.inj m5
  refine ⟨fun blk hblk i hi => ?_, fun blk hblk i hi => ?_⟩
  · rw [cnt blk hblk] at hi
    show O.fixed (.own (treesTo _ 5 + i)) ≤ 0 + roundsTo _ 5 ∧
      (jobOmega ⟨Q, 0⟩).readsBelow (O.fixed (.own (treesTo _ 5 + i)))
    rw [t5', r5', h1 i hi]
    exact ⟨by omega, readsBelow_mono (jobOmega_readsBelow ⟨Q, 0⟩) (show (0 : ℕ) + 1 ≤ 4 by omega)⟩
  · have L := F.at5 hblk
    rw [cnt blk hblk] at hi
    show O.table (.own (treesTo _ 5 + i)) = _
    rw [t5', L.place, pO, htb]
    show (if 1 + i < treesU Q then _ else if 1 + i < 3 then _ else _) = _
    rw [if_neg (by omega), if_pos (by omega), hu, Nat.add_sub_cancel_left]
    rfl

end

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.counts_written
#print axioms ProofFile.Honest.K12.AtFile.counts_bent
#print axioms ProofFile.Honest.K12.AtFile.treesU_written
#print axioms ProofFile.Honest.K12.AtFile.treesU_head
#print axioms ProofFile.Honest.K12.AtFile.treesU_at_shared
#print axioms ProofFile.Honest.K12.AtFile.treesO_at_shared
