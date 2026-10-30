-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OrcBelow.lean: «THE READING BY KEY IS Strs.col» (`PlanAt`'s fourth
clause, FrontFitsOf.lean; hforc, HFOfDoor.lean) AS A LAW, GENERAL IN THE PUBLIC PART Z: no test, no
written term. Where the proof file's rounds have data, the first entry of the first chain's frame's
list whose key is k bears the number k itself, for every k below the first chain's number of trees:
`key_below`'s own proof (Johnson/Top/H0/Walk/FrameCarryKey.lean), up to there.
Theorems. No text already in the library turns.

  `first_below`: ProofFile.wholeAt Z = some D · k < D.t₁ ⊢ ((ProofFile.allAt Z).find? fun L => ProofFile.keyAt Z L.no
    == k).map (·.no) = some k.
  `orcY_below`: **so K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) Y k x = Y.col k x.**
  `planAt_below`: planPubB G t Lp o seat a · the plan's list places o in the seat's own tree · that
    tree is below D.t₁ ⊢ PlanAt G t Lp (K2.orcY …) Y o seat a.
Limits. That `ProofFile.wholeAt Z` has data and that the trees are below D.t₁ are premises. Nothing on
soundness.
-/
import Johnson.Desc.First.Link.Law.PlanKeyB
import Johnson.Top.H0.Walk.FrameCarryKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.First.K2 (first_of_data_at key_of_data)
open VerifiableInference.Desc.First.K2Caller

theorem first_below (Z : ProofFile.Pub) (D : WholeD) (hW : ProofFile.wholeAt Z = some D) (k : ℕ)
    (hk : k < D.t₁) :
    ((ProofFile.allAt Z).find? fun L => ProofFile.keyAt Z L.no == k).map (·.no) = some k := by
  obtain ⟨N, c, hD⟩ := whole_is_data Z D hW
  have h1 := first_of_data_at hD frS.P.T.a 0 D.t₁ [] (Nat.le_refl _) k hk
  have h2 : (D.at frS.P.T.a).key₁ k = k := key_of_data hD k hk
  dsimp only at h1
  rw [h2] at h1
  unfold ProofFile.allAt ProofFile.keyAt
  rw [hW]
  exact h1

/-- **THE READING BY KEY IS Strs.col, BELOW THE FIRST CHAIN's NUMBER OF TREES.** -/
theorem orcY_below (Z : ProofFile.Pub) (D : WholeD) (hW : ProofFile.wholeAt Z = some D) (k : ℕ)
    (hk : k < D.t₁) (Y : Strs) (x : ℕ) :
    First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) Y k x = Y.col k x := by
  obtain ⟨L, h1, h2⟩ := Option.map_eq_some_iff.1 (first_below Z D hW k hk)
  rw [orcY_at h1, h2]

/-- **PlanAt FROM ITS PUBLIC PART'S TEST AND THE LAW.** -/
theorem planAt_below {Xi : Type} {G : FileDescription Xi} {t : First.S}
    {Lp : VerifiableInference.Desc.K12.Door.Laid} {o : ℕ} {seat : ℕ × ℕ} {a : ℕ}
    (h1 : planPubB G t Lp o seat a = true) (Z : ProofFile.Pub) (D : WholeD)
    (hW : ProofFile.wholeAt Z = some D) (hq : Lp.places[o]? = some seat) (hs : seat.1 < D.t₁)
    (Y : Strs) : PlanAt G t Lp (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) Y) Y o seat a :=
  planAt_of_B h1 _ Y fun tp hq' x _ => by
    rw [hq] at hq'
    obtain rfl : seat.1 = tp := congrArg Prod.fst (Option.some.inj hq')
    exact orcY_below Z D hW _ hs Y x

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.first_below
#print axioms VerifiableInference.Desc.LinkJoin.orcY_below
#print axioms VerifiableInference.Desc.LinkJoin.planAt_below
