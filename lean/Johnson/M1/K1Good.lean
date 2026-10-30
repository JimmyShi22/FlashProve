-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the rule's four premises at the term's filling, at K1's two lots.
/-
Johnson/M1/K1Good.lean: at a return of the maker, in the goals' scope where the gate accepts, every row
of K1's own lot and of W's lot of the term's filling owes what the rule asks: exact, fresh under the
public test on the book, and the two bodies on positions and on On. No property of the protocol is
claimed here.
-/
import Johnson.M1.Goal
import Johnson.M1.K1Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat

variable {W₀ W₀' Rc' Pb : Type}

section
variable {Tr X₀ : Type} {P : VerifierAndGoals.PublicFiles} {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)}
  {Fl : OnlineProverParts W₀' Rc' Tr X₀ Unit} {R : OnlineProverWithDescription W₀' Rc' Tr X₀ Unit}

/-- **K1's own lot.** -/
theorem k1_owes (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R)
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins)
    (φ : Face (Local W₀' Rc' ProofFile.Inst Cells) (Local W₀' Rc' ProofFile.Inst Cells) Pb) (ord : List Place)
    (chain ft : Nat)
    (T : Local W₀' Rc' ProofFile.Inst Cells → Thread R.B R.F.S₁ R.F.Cl (Local W₀' Rc' ProofFile.Inst Cells)
      (Local W₀' Rc' ProofFile.Inst Cells) Unit Pb)
    (Sd : Local W₀' Rc' ProofFile.Inst Cells → Nat → Coins R.B → Mid (Local W₀' Rc' ProofFile.Inst Cells) Unit → Prop)
    (fs : List (Fall R.F.S₁)) :
    ∀ r ∈ (k1Lot (Pb := Pb) I OnBytes.secondHashFunction S g rd).rows R.Z R.G,
      RowOwes R pre₀ φ ord chain ft T Sd fs r := by
  intro r hr
  refine rows_at_return (Xi := ProofFile.Inst) hS hL h φ (witThru I R.Z g rd)
    (lotNo OnBytes.secondHashFunction R.Z) (lotData S) ord chain ft T Sd fs r ?_
  exact List.mem_flatMap.2 ⟨_, List.mem_cons_self .., hr⟩

/-- **W's lot.** -/
theorem w_owes (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R)
    (I : WiderIn W₀) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins)
    (φ : Face (Local W₀' Rc' ProofFile.Inst Cells) (Local W₀' Rc' ProofFile.Inst Cells) Pb) (ord : List Place)
    (chain ft : Nat)
    (T : Local W₀' Rc' ProofFile.Inst Cells → Thread R.B R.F.S₁ R.F.Cl (Local W₀' Rc' ProofFile.Inst Cells)
      (Local W₀' Rc' ProofFile.Inst Cells) Unit Pb)
    (Sd : Local W₀' Rc' ProofFile.Inst Cells → Nat → Coins R.B → Mid (Local W₀' Rc' ProofFile.Inst Cells) Unit → Prop)
    (fs : List (Fall R.F.S₁)) :
    ∀ r ∈ (wLot (Pb := Pb) I OnBytes.secondHashFunction O g rd).rows R.Z R.G,
      RowOwes R pre₀ φ ord chain ft T Sd fs r := by
  intro r hr
  refine rows_at_return (Xi := ProofFile.Inst) hS hL h φ (witThru I R.Z g rd)
    (lotNo OnBytes.secondHashFunction R.Z) (K13.wDataAt O.pile) ord chain ft T Sd fs r ?_
  exact List.mem_flatMap.2 ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hr⟩

end

end Johnson.M1

#print axioms Johnson.M1.k1_owes
#print axioms Johnson.M1.w_owes
