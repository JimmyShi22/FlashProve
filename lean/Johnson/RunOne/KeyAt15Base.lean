-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyAt15Base.lean: THEOREMS. **The open pins' trees lie in front of the maker's fifteenth piece (row 1.15; field r1_15): a public premise of the join of that row's two halves, in its own letters; and the row's five public premises together, in the goals' scope.**
WORDS. Key.descriptionFromSource X N P: the key file's IOP as written in Lean; a block: a sub-protocol; the verifier's state: what it carries between two sub-protocols.
OBJECT: the premise hbase of gives_of_halvesH (Johnson/RunOne/Law/K12Left15H.lean), at at_ := atSix and DK := the written data. USER: that theorem. LETTERS: X N P · c₁ k₁ (the first chain's flat list, cut at its head).
  base_two         the maker's base at the fifteenth piece is 2: base_15 (Johnson/RunOne/Law/K12Facts15A.lean: the base is the number of roots that the sub-protocols in front declare) · roots_in_front · two_written (the written data's first 18805 rounds send 2 trees)
  base_15_scope    **hbase**: at the pins 0 and 1, which alone are open at border 15: 0 < 2 and 1 < 2
  two_lookups      in scope's equations the key's range proof has two lookups
  at15_at          seven_at's seven premises and the cut of the flat list ⊢ hlog ∧ told · hseed at every reached state · horc · hnum · hbase
What is not claimed. That scope's premises hold at any files ([RAN] at the stored full-size public files). The other premises of the row's law and join. Nothing on soundness.

-/
import Johnson.RunOne.KeyAt15Seat
import Johnson.RunOne.Law.K12Facts15A

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyLetters
open Johnson.RunOne.KeyRows1 Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi FirstState)
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open Johnson.Pack (aOf)
open Johnson.Top.H (csKey shIdx shMul)
open Johnson.G (writtenKFull)
open Lk6.AtPlan (keyFull)
open LPFD (Hist₁ cutBase)
open Johnson.RunOne.Law.RoundsInFront (inFront)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Johnson.RunOne.Sound (rounds_in_scope)

/-- WholeD.at leaves the first chain's list of rounds as it is. -/
theorem ds₁_at (D : WholeD) (a : ℕ) : (D.at a).ds₁ = D.ds₁ := rfl

section
variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
  (c₁ : Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl) (k₁ : List (Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl))

/-- The maker's base at the fifteenth piece is 2. -/
theorem base_two (hp : (Key.descriptionFromSource X N P).planOk = true) (hD : (Key.descriptionFromSource X N P).data "key file" = .ok writtenKFull)
    (hL : (Key.descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁) (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁)
    (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2) :
    cutBase 0 writtenKFull.ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15 = 2 := by
  rw [Johnson.RunOne.Law.K12Facts15.base_15 X N P c₁ k₁ "key file" writtenKFull hD hp q₁ hl, ← q₁]
  have i15 : inFront (Key.descriptionFromSource X N P).first.blocksInOrder 15 = 18805 := (inFront_of _ _ hL 15).trans (by decide)
  have h := roots_in_front (Key.descriptionFromSource X N P) "key file" writtenKFull hD 15 (by rw [i15, len_written]; decide)
  rw [i15, two_written] at h
  exact h

/-- **hbase at atSix and the written data.** -/
theorem base_15_scope (hp : (Key.descriptionFromSource X N P).planOk = true) (hD : (Key.descriptionFromSource X N P).data "key file" = .ok writtenKFull)
    (hL : (Key.descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁) (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁)
    (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2) :
    ∀ k ∈ pinned (open₁ (n₁ (oneAt X)) 15), (atSix k).1 < cutBase 0 (writtenKFull.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15 := by
  intro k hk
  have hn : n₁ (oneAt X) = 2 := hl
  rw [hn] at hk
  have hpins : pinned (open₁ 2 15) = [0, 1] := by decide +kernel
  rw [hpins] at hk
  rw [ds₁_at, base_two X N P c₁ k₁ hp hD hL q₁ hl]
  rcases List.mem_cons.1 hk with rfl | hk
  · decide
  · obtain rfl := List.mem_singleton.1 hk
    decide

end

theorem two_full : (Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)).length = 2 := by decide +kernel

theorem two_lookups (X : Key.Source) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (hl : X.Y.k.oneTime.lin = keyFull.once.shape) :
    (Key.lookupsOf X.Y.k.oneTime).length = 2 := by
  unfold Key.lookupsOf
  rw [hr, hl]
  exact two_full

/-- **The row's five public premises, in scope.** -/
theorem at15_at {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (hm : Key.madeAt Z Zp.lay cfg = .ok m) (hX : Key.sourceOf m = .ok X) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hw : (Key.descriptionFromSource X N P).wantedOk = true) (hD : (Key.descriptionFromSource X N P).data "key file" = .ok writtenKFull)
    (c₁ : Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl) (k₁ : List (Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl))
    (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁) :
    ((∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix (⟨1, by decide⟩ : Fin six.length)).1 = some o → o.logLength = aOf csKey (six.get (⟨1, by decide⟩ : Fin six.length)).1) ∧
      ((Fk X N P).oracleAt (seatAt six numSix atSix (⟨1, by decide⟩ : Fin six.length)).1).isSome = true) ∧
    (∀ (D' : WholeD) (a : Xi × FirstState), Hist₁ (Fk X N P) D' 15 a → ∃ ρ y, K1.SeedIs csKey (six.get (⟨1, by decide⟩ : Fin six.length)).1 a.2.d.st 1 ρ y) ∧
    (plan₁ (oneAt X)).orc 1 = some 1 ∧ (plan₁ (oneAt X)).num 1 = some 1 ∧
    (∀ k ∈ pinned (open₁ (n₁ (oneAt X)) 15), (atSix k).1 < cutBase 0 (writtenKFull.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15) := by
  obtain ⟨-, hr, hl, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  exact ⟨seat_15_scope X N P hi hc hr, fun D' => seed_15_scope X N P hp hc hr D', orc_15 X, num_15 X,
    base_15_scope X N P c₁ k₁ hp hD (rounds_in_scope hZ hP hm hX hp hw).1 q₁ (two_lookups X hr hl)⟩

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.ds₁_at
#print axioms Johnson.RunOne.KeyLetters.base_two
#print axioms Johnson.RunOne.KeyLetters.base_15_scope
#print axioms Johnson.RunOne.KeyLetters.two_full
#print axioms Johnson.RunOne.KeyLetters.two_lookups
#print axioms Johnson.RunOne.KeyLetters.at15_at
