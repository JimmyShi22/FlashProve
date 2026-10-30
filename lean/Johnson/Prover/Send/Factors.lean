-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Send/Factors.lean: where the drawn triples of a round of seeds meet the format's
marks "never 0", no seed that K1's cut takes off them has a factor of three words 0. General in the
number of seeds, the number of coordinates and the list drawn: for every text that cuts seeds off a
round "SEND seed". Statements and proofs.

  isZeroE_ofTriple   a triple of words that are not all 0 spells an element whose words are not
                     all 0
  zip_factors        the format's list of n seeds of v coordinates (Fmt.dsSeeds n v,
                     Fmt/Rules6Draws.lean) marks each seed's last draw; K1.cutSeeds v n
                     (Johnson/Desc/K1/Own.lean) takes just that draw as the seed's factor

The premise on the marks is the clause that drawsMarkedNonzeroHaveNonzeroWords (Johnson/Desc/Block.lean) asks of a round, at the
list Fmt.dsSeeds n v.
Limits. On words: "not 0 in the field" wants every word below the prime beside it. Nothing on how a
round is drawn. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Send
open OnBytes VerifiableInference.Desc

/-- A triple of words that are not all 0 spells an element whose words are not all 0. -/
theorem isZeroE_ofTriple (t : Fmt.Ext3) (h : t ≠ (0, 0, 0)) : isZeroE (E.ofTriple t) = false := by
  obtain ⟨a, b, c⟩ := t
  cases hc : isZeroE (E.ofTriple (a, b, c)) with
  | false => rfl
  | true =>
    have h2 : (a == 0 && b == 0 && c == 0) = true := hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact absurd (by rw [h2.1.1, h2.1.2, h2.2]) h

/-- Seed by seed: where the format's list of a round of seeds marks the factors as never 0 and the
drawn triples meet the marks, no seed that is cut off them has a factor of three words 0. -/
theorem zip_factors (v : Nat) : ∀ (n : Nat) (l : List Fmt.Ext3), l.length = n * (v + 1) →
    ((Fmt.dsSeeds n v).zip l).all (fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true →
    ∀ s ∈ K1.cutSeeds v n (l.map E.ofTriple), isZeroE s.2 = false
  | 0, _, _, _, s, hs => by simp [K1.cutSeeds] at hs
  | n + 1, l, hl, h, s, hs => by
    have hds : Fmt.dsSeeds (n + 1) v =
        (List.replicate v Fmt.Draw.elem ++ [Fmt.Draw.elemNZ]) ++ Fmt.dsSeeds n v := by
      simp [Fmt.dsSeeds, List.replicate_succ]
    have hl' : l.length = n * (v + 1) + (v + 1) := by rw [hl, Nat.succ_mul]
    have hv : v < l.length := by omega
    obtain ⟨a, t, b, rfl, ha⟩ : ∃ a t b, l = a ++ t :: b ∧ a.length = v :=
      ⟨l.take v, l[v], l.drop (v + 1), by
        rw [List.getElem_cons_drop, List.take_append_drop], by
        rw [List.length_take]; omega⟩
    have hb : b.length = n * (v + 1) := by
      simp only [List.length_append, List.length_cons] at hl'
      omega
    have e1 : a ++ t :: b = (a ++ [t]) ++ b := by simp
    rw [hds, e1, List.zip_append (by simp [ha]), List.all_append, Bool.and_eq_true,
      List.zip_append (by simp [ha]), List.all_append, Bool.and_eq_true] at h
    have ht : t ≠ (0, 0, 0) := by
      have := h.1.2
      simpa using this
    have hd : ((a ++ t :: b).map E.ofTriple).drop v = E.ofTriple t :: b.map E.ofTriple := by
      rw [List.map_append, List.drop_left' (by rw [List.length_map, ha])]
      rfl
    have hd1 : ((a ++ t :: b).map E.ofTriple).drop (v + 1) = b.map E.ofTriple := by
      rw [← List.drop_drop, hd]
      rfl
    simp only [K1.cutSeeds, List.mem_cons] at hs
    rcases hs with rfl | hs
    · show isZeroE ((((a ++ t :: b).map E.ofTriple).drop v).headD zeroE) = false
      rw [hd]
      exact isZeroE_ofTriple t ht
    · rw [hd1] at hs
      exact zip_factors v n b hb h.2 s hs

end Johnson.Prover.Send

#print axioms Johnson.Prover.Send.isZeroE_ofTriple
#print axioms Johnson.Prover.Send.zip_factors
