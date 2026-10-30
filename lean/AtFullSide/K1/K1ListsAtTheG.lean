-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/K1ListsAtTheG.lean: the shared "sending" (the kind K1): KindPays (theGOfReturn made h T K) .K1 IS NOT IDLE: at the base filling, in scope, at
EVERY value K of the kinds' rows, the named sides have 52 lists at places of the kind K1 in the first chain and 2 in the shared
chain. By the sides' own law (their prover is the return's: theGOfReturn_prover, E2E/TheG.lean), the tie k1_halves_at_base with rows_52,
and the base filling's shared halves (base_shared). Three theorems; no definition.

  length_filter_map a helper on lists
  k1_lists_first    52
  k1_lists_shared   2

Limits. A count of lists: that each has a side: side_at_return (first chain); the shared chain's: another house's six_at_atPure. No
property of the protocol is claimed.
-/
import AtFullSide.K1.K1LaidHasAMember
import Johnson.Desc.ProofFile.Honest.K1.Sim.HalvesAtReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K1
open VerifiableInference.Desc
open OnBytes (TableKey)
open ProofFile (Inst)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim ProofFile.Honest.Term
open ProofFile.Honest.K14 (simRows simPub simData randNow)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.TheSides AtPublicFiles.TheG

variable {files : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- Mapped lists filtered by a test that reads the image alone are equally long. -/
theorem length_filter_map {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    ((l.map f).filter p).length = (l.filter fun x => p (f x)).length := by
  rw [List.filter_map, List.length_map]
  rfl

/-- **52 lists in the first chain.** -/
theorem k1_lists_first (hS : VerifierAndGoals.InScope files = true) (made : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G) :
    ((theGOfReturn made h T K).first.filter fun L => L.place.kind == .K1).length = 52 := by
  have hp := congrArg (·.first) (theGOfReturn_prover made h T K)
  have e : (theGOfReturn made h T K).first.map (fun L => (⟨L.place, L.row.map (·.1)⟩ :
      Placed (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit)) = A.H.first := hp
  have c := length_filter_map (fun L : Lettered A.B A.F.S₁ A.F.Cl (Local FullSizeMatrix IndexCommitterCoins Inst Cells)
      (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst => (⟨L.place, L.row.map (·.1)⟩ :
                  Placed (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit))
    (fun x => x.place.kind == .K1) (theGOfReturn made h T K).first
  rw [e, k1_halves_at_base matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest made,
    List.length_map, (rows_52 hS matrixInput id id OnBytes.HonestTrace.Sz.ref openHonest made).1] at c
  exact c.symm

/-- **2 lists in the shared chain.** -/
theorem k1_lists_shared (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G) :
    ((theGOfReturn made h T K).shared.filter fun L => L.place.kind == .K1).length = 2 := by
  have hp := congrArg (·.shared) (theGOfReturn_prover made h T K)
  have e : (theGOfReturn made h T K).shared.map (fun L => (⟨L.place, L.row.map (·.1)⟩ :
      Placed Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit)) = A.H.shared := hp
  have c := length_filter_map (fun L : Lettered A.B A.F.S₂ A.F.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey)
      Unit TableKey => (⟨L.place, L.row.map (·.1)⟩ : Placed Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit))
    (fun x => x.place.kind == .K1) (theGOfReturn made h T K).shared
  obtain ⟨rest, hr, es⟩ := base_shared h
  have hsh : A.H.shared = (baseFilling files).shared A.Z A.G := (atPure_ok made).2.2.2.2.2.2.2.2.1
  have hn : (rest.filter fun x => x.place.kind == .K1) = [] :=
    List.filter_eq_nil_iff.2 fun x hx hk => by
      have := hr x hx
      rw [beq_iff_eq.1 hk] at this
      cases this
  rw [e, hsh, es, List.filter_append, hn, List.append_nil] at c
  rw [← c]
  have c2 := length_filter_map (fun r : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey =>
      r.place) (fun a => a.kind == .K1)
    (simRows (simData A.Z h.places) (simPub A.Z h.places) (matrixInput.weights A.Z)
      (randNow (VerifiableInference.Desc.K1.qAt A.Z h.places)))
  rw [ProofFile.Honest.K14.simRows_places h.head] at c2
  rw [length_filter_map]
  exact c2.symm.trans (by decide)

end AtFullSide.K1

#print axioms AtFullSide.K1.length_filter_map
#print axioms AtFullSide.K1.k1_lists_first
#print axioms AtFullSide.K1.k1_lists_shared
