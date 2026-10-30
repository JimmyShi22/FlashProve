-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/AtSeats/ToldLeftAtAll.lean
(the side lemma base_atAll that it calls stands in another file:
Johnson/Desc/K1/Law/RadiiAtAll.lean): three fields that the kind K1's named condition lists
(K1Left: ht, hT83, h4: what hTold_at [not in this library] leaves), each in the field's own type at
the closed constant's letters. A joining of what lies. A law file; no running text imports it.
  sum_dropLast_le, trees_le_of, roots_ge_of: over letters: the first chain's data send as many trees
      as the written rounds but the last have items "root"; that is at most the number of all such
      items
  drop_sum_written: at the written rounds that sum is 83 (t1_written and
      trees_written: no list is unfolded here)
  ht_atAll: 83 ≤ Three.rootsIn dryProofFull.1: NO PREMISE
  hT83_atAll a: nTrees (dataOf a dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2).ds₁ ≤ 83, at
      every depth a: NO PREMISE
  h4_atAll: the field h4, from the head hA, the opening O and the two pins

ON WHAT h4_atAll HANGS: hA (a member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side
library AtFullSide/Top/)) · O · (P1) madePinnedAt · (P2) cutIs. ht_atAll and
hT83_atAll hang on nothing. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.FromTheCut
import Johnson.Desc.K1.Law.RadiiAtAll
import Johnson.HB.LLHARD.TreesWritten
import Johnson.HB.LLHARD.HBaseWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (linksFull nTrees data_trees dataOf)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.K13.Law (countsFull trees_written)
open VerifiableInference.PlanWritten (madePinnedAt cutIs)
open _root_.Desc.K14.Law (seatZ secondAt)
open HashBuild (laidFull)
open ProofFile (Cl)
open IM (Open k1Ix)

theorem sum_dropLast_le : ∀ l : List ℕ, l.dropLast.sum ≤ l.sum
  | [] => Nat.le_refl _
  | [_] => Nat.zero_le _
  | a :: b :: l => by
    show (a :: (b :: l).dropLast).sum ≤ (a :: b :: l).sum
    rw [List.sum_cons, List.sum_cons (a := a)]
    exact Nat.add_le_add_left (sum_dropLast_le (b :: l)) a

theorem trees_le_of {R₁ R₂ R₃ : Rounds} {n : ℕ}
    (h : ((R₁.map fun r => r.1.items.countP (· == .root)).dropLast).sum = n) (a : ℕ) :
    nTrees (dataOf a R₁ R₂ R₃).ds₁ ≤ n := by
  unfold nTrees
  rw [data_trees, h]

theorem roots_ge_of {R₁ : Rounds} {n : ℕ}
    (h : ((R₁.map fun r => r.1.items.countP (· == .root)).dropLast).sum = n) :
    n ≤ Three.rootsIn R₁ := by
  rw [← h]
  exact sum_dropLast_le _

theorem t1_is (D : WholeD) : D.t₁ = (D.ds₁.map (·.trees.length)).sum := rfl

theorem drop_sum_written :
    ((dryProofFull.1.map fun r => r.1.items.countP (· == .root)).dropLast).sum = 83 := by
  have h := t1_written
  rw [t1_is, trees_written] at h
  exact h

/-- **The field ht.** -/
theorem ht_atAll : 83 ≤ Three.rootsIn dryProofFull.1 := roots_ge_of drop_sum_written

/-- **The field hT83**, at every depth. -/
theorem hT83_atAll (a : ℕ) :
    nTrees (dataOf a dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2).ds₁ ≤ 83 :=
  trees_le_of drop_sum_written a

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
  (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
include hA O hP1 hP2

/-- **The field h4.** -/
theorem h4_atAll : ∀ l, l < 25 → ∀ d : Bool, ∀ n,
    n < (layOf (parL Zp Bs.G₀ l d)).shapes.size →
    laidFull[nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF (noL l d))) + n]? =
      some (((layOf (parL Zp Bs.G₀ l d)).shapes.getD n {}).logN,
        ((layOf (parL Zp Bs.G₀ l d)).shapes.getD n {}).mainWidth +
          ((layOf (parL Zp Bs.G₀ l d)).shapes.getD n {}).maskWidth) :=
  h4_of (hc_atAll hA O hP1) (hs_atAll hA O hP1)
    (K13.Law.gpOf_in_scope hA.scope hA.laid.pub hP1)
    (fun l d => nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF (noL l d))))
    (fun l hl d => base_atAll hA O hP1 hP2 l hl d)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.drop_sum_written
#print axioms VerifiableInference.Desc.K1.ht_atAll
#print axioms VerifiableInference.Desc.K1.hT83_atAll
#print axioms VerifiableInference.Desc.K1.h4_atAll
