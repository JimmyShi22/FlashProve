-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the public numbers of the request's own test at the proof file, and where its senders stand.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/PublicAtW.lean: what a row at the request's own test asks of public numbers, as Sim2/RowOwnKeyPub.lean has it at the key file: at the proof file's first sending (message 4,
the index-mask message, tree 1), W's sending, Omega's plan and the written place piWFull, by Lean's kernel; and, under the head, where the three senders stand. The book's tests are not here. Also planOkOwn at the written finish.

  ownS, PIw, PWw, rideIw, rideWw, shIw, shWw   the test's first stage; the two sendings; their rides; their trees
  ownP_numbers, ownP_I_full, ownP_W_full, ownP_O_full, ownP_shapes   closed facts
  ownP_I_at, ownP_W_at     the two sendings' numbers at every plan at the written codes and messages
  ownP_cut                 under the head, where the three senders stand, and the trees and rounds in front
  finish_planOkOwn         planOkOwn (parL p) at the written finish

Limits. Numbers alone: nothing on a run. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.PublicAtU
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW
import Johnson.SendSim.Seat.ReadsAtWritten
import Johnson.SendSim.At.FastBook
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobL
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesLCol
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain Alike₂ FileDescription Place)
open VerifiableInference.Desc.K1 (qFull firstPar parW realSized)
open VerifiableInference.Desc.K13.Law (gpFull wMsgFull)
open H2K.Member (piWFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K14 (jobOmega sendingsFit sendPlace)
open Johnson.Prover.Send (shapeAt)
open Johnson.G.OfPlan (rootsOf)
open OnBytes.Slice (codeOf)
open P2Law.ProofPlan (WP)

/-- The test's first stage. -/
abbrev ownS : Fmt.M1.Stage := piWFull.nums.stages.headD default
abbrev PIw : VerifiableInference.Desc.K1.Par := firstPar qFull gpFull
abbrev PWw : VerifiableInference.Desc.K1.Par := parW qFull gpFull 4 wMsgFull
abbrev rideIw : ℕ → Option K1.Ride := K1.rideOf (K1.firstFold qFull)
abbrev rideWw : ℕ → Option K1.Ride := K1.rideOf (K1.wFold qFull.lin)
abbrev shIw : OnBytes.TreeShape := PIw.trees.getD 1 {}
abbrev shWw : OnBytes.TreeShape := PWw.trees.getD 0 {}

theorem ownP_numbers : ownS.h ≤ ownS.k ∧ 2 * ownS.k + 1 ≤ ownS.h + ownS.Z.l ∧
    [13, 22, 22] = piWFull.nums.first.map (·.1.a) ∧
    piWFull.nums.first.map (fun o => ProofFile.Honest.srcOf 2 o.2) = [(0, 1), (0, 82), (1, 1)] ∧
    (treesW piWFull).map (·.1) = [13, 22, 22] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- The index-mask message of the first sending: its own tree 1, message 4. -/
theorem ownP_I_full : PIw.trees[1]? = some shIw ∧
    columnWidth PIw 1 = shIw.mainWidth + shIw.maskWidth ∧ PIw.sent.size = 5 ∧
    (shapeAt PIw 4).mainRows = 0 ∧ (shapeAt PIw 4).maskRows = 1 ∧
    codeOf (PIw.codes.mask.getD (shapeAt PIw 4).maskCode default) = ownS.Z ∧
    (List.range PIw.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade PIw.codes PIw.sent).getD {}).tree[k]? == some 1) = [4] ∧
    0 < (K1.dueR PIw rideIw).f + (K1.dueR PIw rideIw).e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- W's sending. -/
theorem ownP_W_full : PWw.trees[0]? = some shWw ∧
    columnWidth PWw 0 = shWw.mainWidth + shWw.maskWidth ∧ PWw.sent.size = 2 ∧
    rideWw 1 = some ⟨ownS.k, ownS.h⟩ ∧ ((shapeAt PWw 1).mainDeg == 3) = false ∧
    2 * ownS.k + 1 + 2 ^ ownS.h * ownS.Z.r ≤ (K1.dueMsg PWw.codes (shapeAt PWw 1) (rideWw 1)).e ∧
    (shapeAt PWw 0).mainDeg = 3 ∧
    codeOf (PWw.codes.base.getD (shapeAt PWw 0).code default) = ownS.C ∧
    codeOf (PWw.codes.mask.getD (shapeAt PWw 0).maskCode default) = ownS.Z ∧
    codeOf (PWw.codes.mask.getD (shapeAt PWw 1).maskCode default) = ownS.Z ∧
    (shapeAt PWw 1).maskRows = 2 ^ ownS.h ∧ (shapeAt PWw 1).mainRows = 0 ∧
    (List.range PWw.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade PWw.codes PWw.sent).getD {}).tree[k]? == some 0) = [0, 1] ∧
    0 < (K1.dueR PWw rideWw).f + (K1.dueR PWw rideWw).e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- Omega's sending, at the written plan. -/
theorem ownP_O_full : (realSized.all fun q =>
    let A := ProofFile.Honest.K12.Light.planOf q.2 q.1.shape
    sendingsFit A.P && widthFits (jobOmega A) 0 &&
    sameCode ((jobOmega A).Q.codes.base.getD (Light.shapeAt (jobOmega A) 0).code default) ownS.C &&
    (mineOf (jobOmega A) 0 == [0]) && ((Light.shapeAt (jobOmega A) 0).maskRows == 0) &&
    decide (0 < (ProofFile.Honest.K14.takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort).f +
      (ProofFile.Honest.K14.takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort).e)) = true := by
  decide +kernel

/-- The three members' shapes, at the written plan. -/
theorem ownP_shapes : (realSized.all fun q =>
    let sO := ((jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).Q.sent.getD 0 default).shape
    ((shapesW PIw PWw sO).zipIdx.map fun x => memShape x.1 ((firstsOf (shapesW PIw PWw sO)).getD x.2 (none, none))) ==
      [⟨0, 0, 0, 1, true⟩, ⟨16, 1, 1, 1, false⟩, ⟨0, 12, 0, 0, false⟩]) = true := by
  decide +kernel

/-- At the written finish. -/
theorem finish_planOkOwn : ((ProofFile.Honest.K2.Law.placesW.find? fun p => p.place.link.isNone).map fun p =>
    VerifiableInference.Desc.K1.planOkOwn (parL p)) = some true := by
  decide +kernel

theorem ownP_shapeAt_congr {P P' : VerifiableInference.Desc.K1.Par} (hs : P.sent = P'.sent) (k : ℕ) :
    shapeAt P k = shapeAt P' k := by
  simp only [Johnson.Prover.Send.shapeAt, hs]

theorem ownP_dueR_congr {P P' : VerifiableInference.Desc.K1.Par} (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) (ride : ℕ → Option K1.Ride) : K1.dueR P ride = K1.dueR P' ride := by
  have e1 : ∀ j, K1.dueMsg P.codes (shapeAt P j) (ride j) = K1.dueMsg P'.codes (shapeAt P' j) (ride j) :=
    fun j => by simp only [Johnson.Prover.Send.shapeAt, hc, hs]
  have e2 : ∀ j, K1.startR P ride j = K1.startR P' ride j := fun j => by
    unfold K1.startR
    simp only [e1]
  unfold K1.dueR
  rw [e2, hs]

theorem ownP_trees_congr {P P' : VerifiableInference.Desc.K1.Par} (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) : P.trees = P'.trees := by
  unfold VerifiableInference.Desc.K1.Par.trees
  rw [hc, hs]

theorem ownP_width_congr {P P' : VerifiableInference.Desc.K1.Par} (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) (t : ℕ) : columnWidth P t = columnWidth P' t := by
  have e : ∀ k, shapeAt P k = shapeAt P' k := ownP_shapeAt_congr hs
  unfold columnWidth
  simp only [e, hc, hs]

/-- **The index-mask message, at every plan at the written codes and messages.** -/
theorem ownP_I_at {P : VerifiableInference.Desc.K1.Par} (hc : P.codes = PIw.codes) (hs : P.sent = PIw.sent) :
    P.trees[1]? = some shIw ∧ columnWidth P 1 = shIw.mainWidth + shIw.maskWidth ∧ P.sent.size = 5 ∧
    (shapeAt P 4).mainRows = 0 ∧ (shapeAt P 4).maskRows = 1 ∧
    codeOf (P.codes.mask.getD (shapeAt P 4).maskCode default) = ownS.Z ∧
    (List.range P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? == some 1) = [4] ∧
    0 < (K1.dueR P rideIw).f + (K1.dueR P rideIw).e := by
  rw [ownP_trees_congr hc hs, ownP_width_congr hc hs, ownP_dueR_congr hc hs, ownP_shapeAt_congr hs, hc, hs]
  exact ownP_I_full

/-- **W's sending, at every plan at the written codes and messages.** -/
theorem ownP_W_at {P : VerifiableInference.Desc.K1.Par} (hc : P.codes = PWw.codes) (hs : P.sent = PWw.sent) :
    P.trees[0]? = some shWw ∧ columnWidth P 0 = shWw.mainWidth + shWw.maskWidth ∧ P.sent.size = 2 ∧
    rideWw 1 = some ⟨ownS.k, ownS.h⟩ ∧ ((shapeAt P 1).mainDeg == 3) = false ∧
    2 * ownS.k + 1 + 2 ^ ownS.h * ownS.Z.r ≤ (K1.dueMsg P.codes (shapeAt P 1) (rideWw 1)).e ∧
    (shapeAt P 0).mainDeg = 3 ∧
    codeOf (P.codes.base.getD (shapeAt P 0).code default) = ownS.C ∧
    codeOf (P.codes.mask.getD (shapeAt P 0).maskCode default) = ownS.Z ∧
    codeOf (P.codes.mask.getD (shapeAt P 1).maskCode default) = ownS.Z ∧
    (shapeAt P 1).maskRows = 2 ^ ownS.h ∧ (shapeAt P 1).mainRows = 0 ∧
    (List.range P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? == some 0) = [0, 1] ∧
    0 < (K1.dueR P rideWw).f + (K1.dueR P rideWw).e := by
  rw [ownP_trees_congr hc hs, ownP_width_congr hc hs, ownP_dueR_congr hc hs, ownP_shapeAt_congr hs, ownP_shapeAt_congr hs, hc, hs]
  exact ownP_W_full

/-- The written rows around the three senders. -/
theorem ownP_rows : 356 < WP.first.blocksInOrder.length ∧
    (WP.first.blocksInOrder[2]?).map (·.place) = some ⟨1, some 0, 1, .K1⟩ ∧
    (WP.first.blocksInOrder[356]?).map (·.place) = some ⟨1, none, 4, .K1⟩ ∧
    (WP.first.blocksInOrder[2]?).any (fun b => !b.rounds.isEmpty) = true ∧
    (WP.first.blocksInOrder[356]?).any (fun b => !b.rounds.isEmpty) = true ∧
    ((WP.first.blocksInOrder.take 2).flatMap fun x => x.oracles.flatMap id).length = 0 ∧
    ((WP.first.blocksInOrder.take 356).flatMap fun x => x.oracles.flatMap id).length = 82 ∧
    5 < WP.shared.blocksInOrder.length ∧ (WP.shared.blocksInOrder[5]?).map (·.place) = some (sendPlace 5) ∧
    (WP.shared.blocksInOrder[5]?).any (fun b => !b.rounds.isEmpty) = true ∧
    ((WP.shared.blocksInOrder.take 5).map (·.rounds.length)).sum = 4 := by
  decide +kernel

attribute [local irreducible] P2Law.ProofPlan.WP

/-- Of two lists alike, a cut at n. -/
theorem split_alike {S Cl S' Cl' : Type} : ∀ (l : List (Block S Cl)) (l' : List (Block S' Cl'))
    (_ : List.Forall₂ Alike₂ l l') (n : ℕ), n < l.length →
    ∃ pre b t, l' = pre ++ b :: t ∧ pre.length = n ∧ List.Forall₂ Alike₂ (l.take n) pre ∧
      ∃ c, l[n]? = some c ∧ Alike₂ c b
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | a :: l, _, .cons ha A, 0, _ => ⟨[], _, _, rfl, rfl, .nil, a, rfl, ha⟩
  | a :: l, _, .cons (b := b) ha A, n + 1, h => by
    obtain ⟨pre, c, t, e, hl, F, d, hd, hc⟩ := split_alike l _ A n (Nat.lt_of_succ_lt_succ h)
    exact ⟨b :: pre, c, t, by rw [e]; rfl, by simp [hl], .cons ha F, d, hd, hc⟩

theorem oracles_alike {S Cl S' Cl' : Type} : ∀ (l : List (Block S Cl)) (l' : List (Block S' Cl')),
    List.Forall₂ Alike₂ l l' →
    (l.flatMap fun x => x.oracles.flatMap id).length = (l'.flatMap fun x => x.oracles.flatMap id).length
  | _, _, .nil => rfl
  | _, _, .cons (a := a) (b := b) ha A => by
    simp only [List.flatMap_cons, List.length_append]
    rw [ha.2.2.1, oracles_alike _ _ A]

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

local notation "𝔽" => P5J.F0T o Zp Np cF

theorem take_left_of {α : Type} (pre t : List α) (b : α) (n : ℕ) (h : pre.length = n) :
    (pre ++ b :: t).take n = pre := by
  subst h
  exact List.take_left' rfl

/-- **Where the three senders stand, under the head**, with the trees and rounds in front. -/
theorem ownP_cut (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    (∃ (pI : List (Block (𝔽).S₁ (𝔽).Cl)) (bI : Block (𝔽).S₁ (𝔽).Cl) (tI : List (Block (𝔽).S₁ (𝔽).Cl)),
      (𝔽).first.blocksInOrder = pI ++ bI :: tI ∧ bI.place = ⟨1, some 0, 1, .K1⟩ ∧ bI.rounds ≠ [] ∧
        treesTo (𝔽).first.blocksInOrder pI.length + 1 = 1) ∧
    (∃ (pW : List (Block (𝔽).S₁ (𝔽).Cl)) (bW : Block (𝔽).S₁ (𝔽).Cl) (tW : List (Block (𝔽).S₁ (𝔽).Cl)),
      (𝔽).first.blocksInOrder = pW ++ bW :: tW ∧ bW.place = ⟨1, none, 4, .K1⟩ ∧ bW.rounds ≠ [] ∧
        treesTo (𝔽).first.blocksInOrder pW.length + 0 = 82 ∧
        (pW.flatMap (·.rounds)).length = ((WP.first.blocksInOrder.take 356).flatMap (·.rounds)).length) ∧
    (∃ (pO : List (Block (𝔽).S₂ (𝔽).Cl)) (bO : Block (𝔽).S₂ (𝔽).Cl) (tO : List (Block (𝔽).S₂ (𝔽).Cl)),
      (𝔽).shared.blocksInOrder = pO ++ bO :: tO ∧ bO.place = sendPlace 5 ∧ bO.rounds ≠ [] ∧
        rootsOf (pO.flatMap (·.rounds)) + 0 = 1 ∧ (pO.flatMap (·.rounds)).length = 4) := by
  have A := ProofFile.Honest.K14.planAlike_at_laid h.scope h.laid
  obtain ⟨l1, p2, p356, r2, r356, t2, t356, l2, p5, r5, s5⟩ := ownP_rows
  have hne : ∀ {S Cl : Type} {c : Option (Block S Cl)} {b : Block S Cl}, c = some b →
      c.any (fun b => !b.rounds.isEmpty) = true → b.rounds ≠ [] := fun e k hn => by
    rw [e] at k
    simp [hn] at k
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨pre, b, t, e, hl, F, c, hc, hb⟩ := split_alike _ _ A.first 2 (by omega)
    refine ⟨pre, b, t, e, ?_, ?_, ?_⟩
    · rw [hc] at p2
      exact (Option.some.inj p2).symm.trans hb.1 |>.symm ▸ rfl
    · rw [← hb.2.1]
      exact hne hc r2
    · unfold treesTo
      rw [e, hl, take_left_of _ _ _ _ hl, ← oracles_alike _ _ F, t2]
  · obtain ⟨pre, b, t, e, hl, F, c, hc, hb⟩ := split_alike _ _ A.first 356 l1
    refine ⟨pre, b, t, e, ?_, ?_, ?_, ?_⟩
    · rw [hc] at p356
      exact (Option.some.inj p356).symm.trans hb.1 |>.symm ▸ rfl
    · rw [← hb.2.1]
      exact hne hc r356
    · unfold treesTo
      rw [e, hl, take_left_of _ _ _ _ hl, ← oracles_alike _ _ F, t356]
    · rw [VerifiableInference.Desc.alike₂_rounds _ _ F]
  · obtain ⟨pre, b, t, e, hl, F, c, hc, hb⟩ := split_alike _ _ A.shared 5 l2
    refine ⟨pre, b, t, e, ?_, ?_, ?_, ?_⟩
    · rw [hc] at p5
      exact (Option.some.inj p5).symm.trans hb.1 |>.symm ▸ rfl
    · rw [← hb.2.1]
      exact hne hc r5
    · rw [← VerifiableInference.Desc.alike₂_rounds _ _ F]
      exact roots_WP.2
    · rw [← VerifiableInference.Desc.alike₂_rounds _ _ F, List.length_flatMap]
      exact s5

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.ownP_numbers
#print axioms ProofFile.Honest.K12.Sim2.ownP_I_full
#print axioms ProofFile.Honest.K12.Sim2.ownP_W_full
#print axioms ProofFile.Honest.K12.Sim2.ownP_O_full
#print axioms ProofFile.Honest.K12.Sim2.ownP_shapes
#print axioms ProofFile.Honest.K12.Sim2.finish_planOkOwn
#print axioms ProofFile.Honest.K12.Sim2.ownP_I_at
#print axioms ProofFile.Honest.K12.Sim2.ownP_W_at
#print axioms ProofFile.Honest.K12.Sim2.ownP_cut
