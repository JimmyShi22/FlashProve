-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WJointTaken.lean: NOT IN FRONT OF A LAW OVER COINS. The
clause taken of what a stand of the last chain's proximity test owes (StandRest.taken, WTable.lean):
tree number 2, Omega's.

  send_col_at          a sending's table at a place whose coins are cut: its column is columnOf
  cut_same_due             a cut at two equal dues hands the same coins
  omega_data_behind     Omega's data at a later number and the challenges in front read the same
  OmegaAtW             the public facts of Omega's member at the job, each under its name
  taken_omega          TakenIs at tree 2

By what. tree_third_column (WJointOmega.lean), col_sent (K12/TableIsColumn.lean).

Limits.
  * OmegaAtW is public; that it holds at the written place is another statement.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointOmega
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAtHead
import Johnson.Desc.ProofFile.Honest.K14.SendingsPaid
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Members

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Place)
open ProofFile.Honest.K14 (SendJob SendPub jobOmega Ask columnOf sendTable sendingPart sendTablesAt)
open ProofFile.Honest.K12.AtProof (senderO)
open ProofFile.Honest.K12.AtFile (TakenIs)

variable {W X : Type} {Bk : ProverCoinCounts}

/-- **A sending's table, at a place whose coins are cut: its column is columnOf.** -/
theorem send_col_at {W' : Type} (Jd : SendJob) (wit : W' → Ask) (pl : Place) (k : Coins Bk) (c : W')
    (h : List Fmt.Drawn) {own : Cs (sendingPart Jd).takes}
    (hcut : (k.look 1 ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (sendingPart Jd).takes = some own)
    (hw : widthFits Jd 0 = true) (x : ℕ) :
    (sendTable Jd wit pl 1 0 k c h).2.col x =
      columnOf Jd.Q.codes Jd.Q.sent (Jd.rows ⟨wit c, h, ()⟩ (coinsE own).toArray) 0 x := by
  obtain ⟨Tt, hT, hc⟩ := col_sent Jd (Jd.rows ⟨wit c, h, ()⟩ (coinsE own).toArray) 0 hw
  have e : (sendTable Jd wit pl 1 0 k c h).2 = Tt := by
    unfold sendTable
    simp only [hcut]
    unfold sendTablesAt
    rw [List.getD_eq_getElem?_getD, hT]
    rfl
  rw [e]
  exact hc x

/-- A cut at two equal dues hands the same coins. -/
theorem cut_same_due {d : Due} {X₀ : Cs d} {a : Due} {n n' : Due} (e : n = n') {own : Cs n}
    (h : X₀.cut a n = some own) : ∃ own' : Cs n', X₀.cut a n' = some own' ∧
      coinsE own' = coinsE own := by
  subst e
  exact ⟨own, h, rfl⟩

/-- **Omega's data at a later number, and the challenges from there on, read the same.** -/
theorem omega_data_behind (P : Desc.K14.P14) (n₁ p f : ℕ) (a a' : Ask) (hr : a.rows = a'.rows)
    (H : List Fmt.Drawn) (hf : p + 1 ≤ f) :
    (jobOmega ⟨P, n₁ + p⟩).data ⟨a, H, ()⟩ 0 =
      (jobOmega ⟨P, p⟩).data ⟨a', (H.take (n₁ + f)).drop n₁, ()⟩ 0 := by
  have e : (H.drop (n₁ + p)).take 1 = (((H.take (n₁ + f)).drop n₁).drop p).take 1 := by
    rw [List.drop_drop, List.drop_take, List.take_take]
    refine congrArg (fun i => List.take i (H.drop (n₁ + p))) ?_
    omega
  show Desc.K14.Honest.omegaAtE P.S (ProofFile.Honest.K14.elems ((H.drop (n₁ + p)).take 1)) a.rows =
    Desc.K14.Honest.omegaAtE P.S (ProofFile.Honest.K14.elems ((((H.take (n₁ + f)).drop n₁).drop p).take 1)) a'.rows
  rw [e, hr]

/-- **The public facts of Omega's member at the job.** -/
structure OmegaAtW (M : ManyJob W X) (mA mB : Mem W X) (An : SendPub) (n : ℕ)
    (fs : Option ℕ × Option ℕ) (ask : W → Ask) : Prop where
  mems : M.mems = [mA, mB, memOfSending (jobOmega ⟨An.P, n⟩) senderO 0 fs ask none]
  tree : M.trees[2]? = some (22, [.main 2])
  stage : M.s₀.h ≤ M.s₀.k
  code : sameCode ((jobOmega An).Q.codes.base.getD (shapeAt (jobOmega An) 0).code default)
    M.s₀.C = true
  base : (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) senderO 0 fs ask none).shape.base = false
  room : (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) senderO 0 fs ask none).shape.mainFirst +
    (shapeAt (jobOmega An) 0).mainRows ≤ 2 ^ M.s₀.k
  clear₀ : ∀ r < (shapeAt (jobOmega An) 0).mainRows, ¬ (mA.shape.mainFirst ≤
      (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) senderO 0 fs ask none).shape.mainFirst + r ∧
    (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) senderO 0 fs ask none).shape.mainFirst + r <
      mA.shape.mainFirst + mA.shape.mainRows)
  clear₁ : ∀ r < (shapeAt (jobOmega An) 0).mainRows, ¬ (mB.shape.mainFirst ≤
      (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) senderO 0 fs ask none).shape.mainFirst + r ∧
    (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) senderO 0 fs ask none).shape.mainFirst + r <
      mB.shape.mainFirst + mB.shape.mainRows)
  mine : mineOf (jobOmega An) 0 = [0]
  noMask : (shapeAt (jobOmega An) 0).maskRows = 0
  width : widthFits (jobOmega An) 0 = true

/-- **TakenIs at tree 2, from the table's arm and the tree's column.** -/
theorem taken_omega {S Cl V Pb W₂ : Type} (T : Thread Bk S Cl V W X Pb) (k : Coins Bk)
    (m : ProofFile.Honest.Mid W X) (T₀ : List Tree) (Jd : SendJob) (wit : W₂ → Ask) (pl : Place) (r₁ : ℕ)
    (toCommon : W → W₂)
    (harm : T.table (.taken 1 1) = fun k w h => sendTable Jd wit pl 1 0 k (toCommon w) (h.drop r₁))
    {own : Cs (sendingPart Jd).takes}
    (hcut : (k.look 1 ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (sendingPart Jd).takes = some own)
    (hw : widthFits Jd 0 = true)
    (hdep : (T₀.getD 2 (0, fun _ => [])).1 = (T.tableAt (.taken 1 1) k m).2.logLength)
    (hcol : ∀ x, (T₀.getD 2 (0, fun _ => [])).2 x =
      columnOf Jd.Q.codes Jd.Q.sent (Jd.rows ⟨wit (toCommon m.st.input),
        (m.st.heard.take (T.fixed (.taken 1 1))).drop r₁, ()⟩ (coinsE own).toArray) 0 x) :
    TakenIs T k m T₀ 2 (.taken 1 1) := by
  refine ⟨hdep, fun x _ => ?_⟩
  have e : (T.tableAt (.taken 1 1) k m) = sendTable Jd wit pl 1 0 k (toCommon m.st.input)
      ((m.st.heard.take (T.fixed (.taken 1 1))).drop r₁) := by
    show T.table (.taken 1 1) k m.st.input (m.st.heard.take (T.fixed (.taken 1 1))) = _
    rw [harm]
  rw [e, send_col_at Jd wit pl k _ _ hcut hw, hcol x]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.send_col_at
#print axioms ProofFile.Honest.K12.Light.cut_same_due
#print axioms ProofFile.Honest.K12.Light.omega_data_behind
#print axioms ProofFile.Honest.K12.Light.OmegaAtW
#print axioms ProofFile.Honest.K12.Light.taken_omega
