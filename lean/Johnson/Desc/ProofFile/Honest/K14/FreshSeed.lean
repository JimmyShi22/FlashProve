-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshSeed.lean: WHAT THE FRAME's TEST ON A CHALLENGE (drawFit,
Honest/Frame.lean) GIVES AT THE ROUND "SEND seed" OF THE SHARED SENDING: the first seed that is cut
off the challenge has a factor that does not read as 0, and a point of as many coordinates as the
place states. General in the sending's parameters.

  firstSeed_of_fit   **the two facts**, where the place has a seed
  elems_lately    the elements of the last challenge heard, as a sending's second move reads them

By the library's dsElems_place (Johnson/Prover/Send/Form.lean), zip_factors
(Johnson/Prover/Send/Factors.lean), cutSeeds_ok and okE_ofTriple (Johnson/Desc/K1/Law/OkView.lean)
and isZeroE_iff (OnBytes/Slice/ProgField.lean). The library's own factors_of_fit
(Johnson/Prover/Send/Form.lean) says, from its test roundsFit on two rounds, that no seed's factor
is SPELT by three words 0; here, from drawFit: the first seed's factor does not READ as 0.

What is not claimed. Nothing on how a challenge is sampled. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Parts
import Johnson.Prover.Send.Form
import Johnson.Desc.K1.Law.OkView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE isZeroE okE)
open OnBytes.Slice (readE isZeroE_iff)
open VerifiableInference.Desc (K1.Par K1.seedEntry K1.cutSeeds drawsMarkedNonzeroHaveNonzeroWords)

/-- **At a challenge that fits "SEND seed": the first seed's factor does not read as 0, and its
point has the place's number of coordinates.** -/
theorem firstSeed_of_fit (Q : K1.Par) (R : Fmt.Drawn) (h0 : Q.seeds ≠ 0)
    (h : drawFit { entry := K1.seedEntry Q } R = true) :
    readE ((K1.cutSeeds Q.coordinates Q.seeds (R.elems.map E.ofTriple)).getD 0 default).2 ≠ 0 ∧
      ((K1.cutSeeds Q.coordinates Q.seeds (R.elems.map E.ofTriple)).getD 0 default).1.length =
        Q.coordinates := by
  unfold drawFit at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, -⟩, -⟩, -⟩, -⟩, nz⟩, hw⟩, -⟩ := h
  have hlen' : R.elems.length = Q.seeds * (Q.coordinates + 1) := hlen
  unfold drawsMarkedNonzeroHaveNonzeroWords at nz
  have hkind : Fmt.kindOf (K1.seedEntry Q).name = some .seeds := by
    show Fmt.kindOf "SEND seed" = some .seeds
    decide
  rw [hkind] at nz
  simp only [Option.any_some] at nz
  rw [Johnson.Prover.Send.dsElems_place Q h0] at nz
  have hz := Johnson.Prover.Send.zip_factors Q.coordinates Q.seeds R.elems hlen' nz
  have hok := VerifiableInference.Desc.K1.cutSeeds_ok Q.coordinates Q.seeds
    (R.elems.map E.ofTriple) fun e he => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      exact VerifiableInference.Desc.K1.okE_ofTriple x (by
        simpa using List.all_eq_true.1 hw x hx)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
  rw [hn] at hz hok hlen' ⊢
  have hm : ((R.elems.map E.ofTriple).take Q.coordinates,
      ((R.elems.map E.ofTriple).drop Q.coordinates).headD zeroE) ∈
      K1.cutSeeds Q.coordinates (n + 1) (R.elems.map E.ofTriple) := List.mem_cons_self
  refine ⟨fun hr => ?_, ?_⟩
  · have h1 := (isZeroE_iff _ (hok _ hm)).2 hr
    rw [hz _ hm] at h1
    cases h1
  · show ((R.elems.map E.ofTriple).take Q.coordinates).length = Q.coordinates
    rw [List.length_take, List.length_map, hlen']
    have h1 : Q.coordinates ≤ n.succ * (Q.coordinates + 1) := by
      calc Q.coordinates ≤ Q.coordinates + 1 := Nat.le_succ _
        _ = 1 * (Q.coordinates + 1) := (Nat.one_mul _).symm
        _ ≤ n.succ * (Q.coordinates + 1) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le n))
    exact Nat.min_eq_left h1

/-- The elements of the last challenge heard. -/
theorem elems_lately {W X : Type} (a : W) (h : List Fmt.Drawn) (x₀ : Fmt.Drawn) (o : X) :
    elems ((⟨a, h ++ [x₀], o⟩ : State W X).lately 1) = x₀.elems.map E.ofTriple := by
  have hl : ((⟨a, h ++ [x₀], o⟩ : State W X).lately 1) = [x₀] := by
    unfold State.lately
    show (h ++ [x₀]).drop ((h ++ [x₀]).length - 1) = [x₀]
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.drop_left]
  rw [hl]
  show x₀.elems.map E.ofTriple ++ [] = _
  rw [List.append_nil]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.firstSeed_of_fit
#print axioms ProofFile.Honest.K14.elems_lately
