-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: BudDebts.bud₁ at the three sendings of the first chain.
/-
Johnson/M1/KeySenderBud.lean: at each of the three numbers that keyPars holds (the index-mask message, the multiplicities, W): the frame's field
BudDebts.bud₁ at that row: at every cut of the first chain at a block at the sending's place, at every due list, budAt at the positions that the
frame lays from the rows in front on. No input, no coin, no run. In scope, at a source that the public files name.
It is the library's test keyReadsB, cut as bud_of_keyReads cuts it; no count of this file's own.
No property of the protocol is claimed here.
-/
import Johnson.SendSim.Seat.KeyReadsAtLive
import E2E.KeyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription KeySourced)

/-- **BudDebts.bud₁ at the row of the number P.** -/
def SenderBudAtDraws {Xi : Type} (F : FileDescription Xi) (P : K1.Par) : Prop :=
  ∀ pre b t, F.first.blocksInOrder = pre ++ b :: t → b.place = P.place → ∀ ρ : Draws, ρ.due F = true →
    budAt P (asksFrom (treeAsks F ρ 0) ((b.rounds.zip b.oracles).map (·.2.length))
      (((rowsOfChain F.first.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length)).sum)

/-- From the library's test, at any source and numbers. -/
theorem senderBud_of_reads (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces)
    (h : keyReadsB (Key.descriptionFromSource Xs N Q) (keyPars Xs) = true)
    {x : K1.Par × (Nat → Option Ride)} (hx : x ∈ keyPars Xs) :
    SenderBudAtDraws (Key.descriptionFromSource Xs N Q) x.1 := by
  intro pre b t hF hb ρ hρ
  have h1 : readsWithinB (Key.descriptionFromSource Xs N Q) x.1 (treesOf (Key.descriptionFromSource Xs N Q).first.blocksInOrder
                       ((Key.descriptionFromSource Xs N Q).first.blocksInOrder.takeWhile (·.place != x.1.place))) = true :=
    List.all_eq_true.1 h x hx
  have hn := key_places_apart Xs N Q
  have h2 : (Key.descriptionFromSource Xs N Q).first.blocksInOrder.takeWhile (·.place != x.1.place) = pre := by
    rw [hF] at hn ⊢
    rw [← hb]
    exact takeWhile_split (·.place) pre b t hn
  rw [h2] at h1
  exact budAt_of_reads (readsWithinOf _ _ _ _ h1) ρ hρ _

/-- The same at any list of roots. -/
theorem senderBud_any {Z : VerifierAndGoals.PublicFiles} {Xs : Key.Source} {N : H2U.PlaceNums} {Pl : Key.LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {x : K1.Par × (Nat → Option Ride)} (hx : x ∈ keyPars Xs)
    {pre : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)} {b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl}
    {t : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)} (hF : (keyFileDescription Xs N Pl).first.blocksInOrder = pre ++ b :: t)
    (hb : b.place = x.1.place) (ρ : Draws) (hρ : ρ.due (keyFileDescription Xs N Pl) = true) (rs : List Nat) :
    budAt x.1 (asksFrom (treeAsks (keyFileDescription Xs N Pl) ρ 0) rs
      (((rowsOfChain (keyFileDescription Xs N Pl).first.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length)).sum) := by
  obtain ⟨X₀, m, hX, hm, r1, r2, r3⟩ := hs.source
  have h := keyReads_in_scope scope _ X₀ m Xs N Pl hX hm r1 r2 r3
  have h1 : readsWithinB (Key.descriptionFromSource Xs N Pl) x.1 (treesOf (Key.descriptionFromSource Xs N Pl).first.blocksInOrder
                       ((Key.descriptionFromSource Xs N Pl).first.blocksInOrder.takeWhile (·.place != x.1.place))) = true :=
    List.all_eq_true.1 h x hx
  have hn := key_places_apart Xs N Pl
  have h2 : (Key.descriptionFromSource Xs N Pl).first.blocksInOrder.takeWhile (·.place != x.1.place) = pre := by
    have hF' : (Key.descriptionFromSource Xs N Pl).first.blocksInOrder = pre ++ b :: t := hF
    rw [hF'] at hn ⊢
    rw [← hb]
    exact takeWhile_split (·.place) pre b t hn
  rw [h2] at h1
  exact budAt_of_reads (readsWithinOf _ _ _ _ h1) ρ hρ _

/-- **At a source that the public files name, in scope: the three numbers.** -/
theorem senderBud_sourced {Z : VerifierAndGoals.PublicFiles} {Xs : Key.Source} {N : H2U.PlaceNums} {Pl : Key.LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {x : K1.Par × (Nat → Option Ride)} (hx : x ∈ keyPars Xs) :
    SenderBudAtDraws (keyFileDescription Xs N Pl) x.1 := by
  obtain ⟨X₀, m, hX, hm, r1, r2, r3⟩ := hs.source
  exact senderBud_of_reads Xs N Pl (keyReads_in_scope scope _ X₀ m Xs N Pl hX hm r1 r2 r3) hx

end OnBytes.M1

#print axioms OnBytes.M1.senderBud_of_reads
#print axioms OnBytes.M1.senderBud_sourced
#print axioms OnBytes.M1.senderBud_any
