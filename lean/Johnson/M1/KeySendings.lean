-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: the shared chain's two sendings, at their rows.
/-
Johnson/M1/KeySendings.lean: at the key file's description, at a cut of the shared chain at a block at the place of "send o_u" or of "send o_omega":
the count's bound, at the very list of positions that BudDebts' field bud₂ names, for the Par that K14's jobs hold, at every SendPub of the written
codes and shape: the count at the key file's first two sendings of the shared chain, as Johnson/M1/BudSendings.lean has them at the proof file.

  cut_front        at a cut of a list of blocks whose places are apart: roundsInFront is the rounds of the blocks in front.
  keyCodes_eq      keyFull's codes are the written ones.
  jobU_sent_same, jobOmega_sent_same, jobU_sent_full, jobOmega_sent_full   what the jobs send.
  budSendU, budSendOmega   the bound.

That the row's letter bud is budAt, and that a member stands there, stay with the row.
No property of the protocol is claimed here.
-/
import Johnson.M1.KeyRows
import E2E.KeyPlacesNamed
import E2E.KeyBookHeldHash

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open Lk6.AtPlan (keyFull)

section
variable {S Cl : Type}

theorem cut_front : ∀ (pre : List (Block S Cl)) (b : Block S Cl) (t : List (Block S Cl)),
    (∀ c ∈ pre, c.place ≠ b.place) →
    roundsInFront (pre ++ b :: t) b.place = some (pre.flatMap (·.rounds)).length
  | [], b, t, _ => by simp [roundsInFront]
  | c :: pre, b, t, h => by
    have hc : (c.place == b.place) = false := by
      simpa using h c (List.mem_cons_self ..)
    have ih := cut_front pre b t fun d hd => h d (List.mem_cons_of_mem _ hd)
    show roundsInFront (c :: (pre ++ b :: t)) b.place = _
    rw [roundsInFront, if_neg (by simp [hc]), ih, List.flatMap_cons, List.length_append]
    simp [Nat.add_comm]

end

set_option maxRecDepth 1000000 in
theorem keyCodes_eq : keyFull.codes = Johnson.G.keyCodesWritten := by decide +kernel

theorem jobU_sent_same (A B : ProofFile.Honest.K14.SendPub) (h : A.P.S = B.P.S) :
    (ProofFile.Honest.K14.jobU A).Q.sent = (ProofFile.Honest.K14.jobU B).Q.sent := by
  have e : ∀ C : ProofFile.Honest.K14.SendPub, (ProofFile.Honest.K14.jobU C).Q.sent =
      ((((Desc.K14.withU C.P.S).getD #[]).toList ++ []).toArray) := fun _ => rfl
  rw [e, e, h]

theorem jobOmega_sent_same (A B : ProofFile.Honest.K14.SendPub) (h : A.P.S = B.P.S) :
    (ProofFile.Honest.K14.jobOmega A).Q.sent = (ProofFile.Honest.K14.jobOmega B).Q.sent := by
  have e : ∀ C : ProofFile.Honest.K14.SendPub, (ProofFile.Honest.K14.jobOmega C).Q.sent =
      (((Desc.K14.withOmega C.P.S).toList ++ []).toArray) := fun _ => rfl
  rw [e, e, h]

set_option maxRecDepth 1000000 in
theorem jobU_sent_full : (ProofFile.Honest.K14.jobU AtPublicFiles.KeyBook.sendFull).Q.sent = (parK 1 0).sent := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem jobOmega_sent_full : (ProofFile.Honest.K14.jobOmega AtPublicFiles.KeyBook.sendFull).Q.sent = (parK 1 1).sent := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem shared_places_apart : (AtPublicFiles.KeyBook.fullShared.map (·.1)).Nodup := by decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}

/-- Apart, off the rows. -/
theorem shared_apart (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z X N P) :
    ((keyFileDescription X N P).shared.blocksInOrder.map (·.place)).Nodup := by
  have e : (keyFileDescription X N P).shared.blocksInOrder.map (·.place) = AtPublicFiles.KeyBook.fullShared.map (·.1) := by
    rw [← (AtPublicFiles.KeyBook.places_named scope h).2.1]
    unfold Johnson.RunOne.Sound.rowsOf
    rw [List.map_map]
    rfl
  rw [e]
  exact shared_places_apart

/-- The rounds in front of a block of the shared chain, by its place. -/
theorem front_shared (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z X N P)
    {pre : List (Block (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl)} {b : Block (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl}
    {t : List (Block (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl)} (hF : (keyFileDescription X N P).shared.blocksInOrder = pre ++ b :: t) :
    AtPublicFiles.KeyBook.startIn AtPublicFiles.KeyBook.fullShared b.place = some (pre.flatMap (·.rounds)).length := by
  have hn := shared_apart scope h
  rw [hF, List.map_append, List.map_cons] at hn
  have hp : ∀ c ∈ pre, c.place ≠ b.place := fun c hc e =>
    (List.nodup_append.1 hn).2.2 _ (List.mem_map_of_mem hc) _ (List.mem_cons_self ..) e
  rw [← AtPublicFiles.KeyBook.start_named₂ scope h, hF]
  exact cut_front pre b t hp

/-- **The count at "send o_u"'s row.** -/
theorem budSendU (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z X N P) (A : ProofFile.Honest.K14.SendPub)
    (hc : A.P.codes = keyFull.codes) (hS : A.P.S = keyFull.once.shape)
    {pre : List (Block (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl)} {b : Block (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl}
    {t : List (Block (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl)} (hF : (keyFileDescription X N P).shared.blocksInOrder = pre ++ b :: t)
    (hb : b.place = ⟨2, none, 2, .K1⟩) (ρ : Draws) (hρ : ρ.due (keyFileDescription X N P) = true) (rs : List Nat) :
    budAt (ProofFile.Honest.K14.jobU A).Q (asksFrom (treeAsks (keyFileDescription X N P) ρ 1) rs
            (((rowsOfChain (keyFileDescription X N P).shared.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length)).sum) := by
  have hn : (pre.flatMap (·.rounds)).length = roundOfK 1 0 := by
    have e := front_shared scope h hF
    rw [hb] at e
    have e2 : AtPublicFiles.KeyBook.startIn AtPublicFiles.KeyBook.fullShared ⟨2, none, 2, .K1⟩ = some (roundOfK 1 0) := by
      decide +kernel
    exact Option.some.inj (e.symm.trans e2)
  rw [hn]
  have hi : 0 < (sendsK 1).length := by rw [countK.2.1]; omega
  refine (budAt_congr ?_ ?_ _).2 (budRow₂ scope h hi ρ hρ rs)
  · exact hc.trans keyCodes_eq
  · exact (jobU_sent_same A AtPublicFiles.KeyBook.sendFull hS).trans jobU_sent_full

/-- **The count at "send o_omega"'s row.** -/
theorem budSendOmega (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z X N P) (A : ProofFile.Honest.K14.SendPub)
    (hc : A.P.codes = keyFull.codes) (hS : A.P.S = keyFull.once.shape)
    {pre : List (Block (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl)} {b : Block (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl}
    {t : List (Block (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl)} (hF : (keyFileDescription X N P).shared.blocksInOrder = pre ++ b :: t)
    (hb : b.place = ⟨2, none, 5, .K1⟩) (ρ : Draws) (hρ : ρ.due (keyFileDescription X N P) = true) (rs : List Nat) :
    budAt (ProofFile.Honest.K14.jobOmega A).Q (asksFrom (treeAsks (keyFileDescription X N P) ρ 1) rs
            (((rowsOfChain (keyFileDescription X N P).shared.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length)).sum) := by
  have hn : (pre.flatMap (·.rounds)).length = roundOfK 1 1 := by
    have e := front_shared scope h hF
    rw [hb] at e
    have e2 : AtPublicFiles.KeyBook.startIn AtPublicFiles.KeyBook.fullShared ⟨2, none, 5, .K1⟩ = some (roundOfK 1 1) := by
      decide +kernel
    exact Option.some.inj (e.symm.trans e2)
  rw [hn]
  have hi : 1 < (sendsK 1).length := by rw [countK.2.1]; omega
  refine (budAt_congr ?_ ?_ _).2 (budRow₂ scope h hi ρ hρ rs)
  · exact hc.trans keyCodes_eq
  · exact (jobOmega_sent_same A AtPublicFiles.KeyBook.sendFull hS).trans jobOmega_sent_full

end

end OnBytes.M1

#print axioms OnBytes.M1.cut_front
#print axioms OnBytes.M1.keyCodes_eq
#print axioms OnBytes.M1.budSendU
#print axioms OnBytes.M1.budSendOmega
