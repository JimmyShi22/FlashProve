-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/SeatedOfReturn.lean: the head's test seated, at every return of the maker and every rows whose halves are the return's prover's. The maker returns only where no half
is astray (strays, atPure_tests), and that is seated. No file, no size, no filling is named; nothing on what a side plays, nor that each block has a row.

  seated_of_halves   a list of rows whose halves lie at places of the chain is seated there
  seated_of_return   G.seated, from the three equations that AtHonest and StoredFilesDebts hold in their fields first, shared, second
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.Rule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest VerifiableInference.Desc

/-- Rows whose halves are no strays have a side in the chain. -/
theorem seated_of_halves {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} (bs : List (Block S Cl))
    (ls : List (Lettered Bk S Cl V W Y Pb)) (hs : List (Placed V W Y))
    (h : hs = ls.map fun L => ⟨L.place, L.row.map (·.1)⟩) (hst : (strays bs hs).isEmpty = true) :
    ls.all (fun L => (L.side bs).isSome) = true := by
  refine List.all_eq_true.2 fun L hL => ?_
  have h1 : hs.filter (fun x => !(bs.any fun b => b.place == x.place)) = [] := by
    unfold strays at hst
    exact List.map_eq_nil_iff.1 (List.isEmpty_iff.1 hst)
  have hm : (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y) ∈ hs := by
    rw [h]
    exact List.mem_map.2 ⟨L, hL, rfl⟩
  have h2 := List.filter_eq_nil_iff.1 h1 _ hm
  have h3 : (bs.any fun b => b.place == L.place) = true := by
    simpa using h2
  unfold Lettered.side Side.seated
  simp only [Option.isSome_map]
  exact List.find?_isSome.2 (List.any_eq_true.1 h3)

/-- **At a return of the maker, rows whose halves are its prover's are seated.** -/
theorem seated_of_return {W₀ Rc Tr X₀ X : Type} {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X)
    (h₁ : A.H.first = G.first.map fun L => ⟨L.place, L.row.map (·.1)⟩)
    (h₂ : A.H.shared = G.shared.map fun L => ⟨L.place, L.row.map (·.1)⟩)
    (h₃ : A.H.second = G.second.map fun L => ⟨L.place, L.row.map (·.1)⟩) : G.seated = true := by
  obtain ⟨-, s₁, s₂, s₃, -⟩ := atPure_tests hA
  unfold Sides.seated
  rw [seated_of_halves _ _ _ h₁ s₁, seated_of_halves _ _ _ h₂ s₂, seated_of_halves _ _ _ h₃ s₃]
  rfl

end Johnson.M1

#print axioms Johnson.M1.seated_of_halves
#print axioms Johnson.M1.seated_of_return
