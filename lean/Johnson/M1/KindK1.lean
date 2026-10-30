-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- what the kind K1 pays on the first chain, in the form that the rule asks.
/-
Johnson/M1/KindK1.lean: at a return of the maker, in the goals' scope where the gate accepts, at a list
of rows whose rows of the kind K1 are those of K1's own lot and of W's, every side of the kind K1 on the
first chain has Good at its own On and bud, under the public test on the book: the first clause of
`KindPays G .K1` (Johnson/T3/OwedOfKinds.lean), at G's first chain laid by `laySides`. The shared
chain's two places of the kind K1 are the kind K14's. No property of the protocol is claimed here.
-/
import Johnson.M1.K1Good
import Johnson.Desc.ProofFile.Honest.Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat

variable {W₀ W₀' Rc' : Type}

/-- **The first clause of `KindPays .K1`.** `book`: the public test on the book, at the description's
order of places. -/
theorem k1_first_pays {Tr X₀ : Type} {P : VerifierAndGoals.PublicFiles} {Fl : OnlineProverParts W₀' Rc' Tr X₀ Unit}
    {R : OnlineProverWithDescription W₀' Rc' Tr X₀ Unit} (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R)
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins)
    (T₁ : Local W₀' Rc' ProofFile.Inst Cells → Thread R.B R.F.S₁ R.F.Cl (Local W₀' Rc' ProofFile.Inst Cells)
      (Local W₀' Rc' ProofFile.Inst Cells) Unit ProofFile.Inst)
    (S₁ : Local W₀' Rc' ProofFile.Inst Cells → Nat → Coins R.B →
      Mid (Local W₀' Rc' ProofFile.Inst Cells) Unit → Prop)
    (r₁ : List (Unlettered (Local W₀' Rc' ProofFile.Inst Cells) (Local W₀' Rc' ProofFile.Inst Cells) Unit
      ProofFile.Inst)) (f₁ : List (Fall R.F.S₁))
    (hk : ∀ r ∈ r₁, r.place.kind = KindName.K1 →
      r ∈ (k1Lot (Pb := ProofFile.Inst) I OnBytes.secondHashFunction S g rd).rows R.Z R.G ∨
        r ∈ (wLot (Pb := ProofFile.Inst) I OnBytes.secondHashFunction O g rd).rows R.Z R.G)
    (book : ∀ e ∈ R.B.ahead, e.once = true → lotsMine R.Z R.G e.owner = true →
      lotsOkB R.Z R.G R.B (orderOf R.F) e.owner = true) :
    ∀ L ∈ r₁.map (fun r => r.lay T₁ S₁ R.F.first.blocksInOrder), L.place.kind = KindName.K1 →
      ∀ σ, L.side R.F.first.blocksInOrder f₁ = some σ →
        ∃ A' B', Good (preOf 0 0 (earlierOf R.F 0) R.F.first.blocksInOrder L.place) .own σ R.B
          (orderOf R.F) 0 0 A' B' L.On L.bud := by
  intro L hLm hkind σ hσ
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
  rcases hk r hr hkind with h1 | h1
  · exact (k1_owes hS hL h I S g rd .own (orderOf R.F) 0 0 T₁ S₁ f₁ r h1).2.1 book σ hσ
  · exact (w_owes hS hL h I O g rd .own (orderOf R.F) 0 0 T₁ S₁ f₁ r h1).2.1 book σ hσ

end Johnson.M1

#print axioms Johnson.M1.k1_first_pays
