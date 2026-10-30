-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Rider/ForBUses.lean: three shapes of rider at the lookup of a sub-proof, the
picks in the places of the key point.

Statements and proofs. No protocol of its own. Each theorem is `forB_rider`
(OnBytes/Tie/Pv/Lookup/Rider/ForB.lean) at one shape of arrays and one pick of coordinates, by the
forms of Cb/G6/Rider/UsesK.lean.

The point. The output statement's claim on the keys has the point `pt`, of dT + rK places, place 0
at the top bit. Its first dT places are called the first part here, the last rK places the second
part. A call's point is the last iota places of the second part, then the first part; place j of it
is place `keyIx dT rK iota j` of pt (Cb/G6/Rider/Picks.lean).

Main names:
  `oneHot_forB`: for each member of a family, nE maps sum to 1 at every vertex; the pick is the last
    lt places of the first part.
  `two_lines_forB`: two conditions at the vertices that a public indicator marks; the same pick.
  `denom_forB`: a denominator equals a row sum over tiles; the pick goes through a call's point and
    skips one place; it names pt 0, the line's challenge, where iota < nb (`selAtt_line`).
In each, forB's own `KnowAt` is a premise, used as a black box. The same three in the arrays that a
caller holds: OnBytes/Tie/Pv/Lookup/Rider/ForBCalls.lean.

These are statements of form. Every map (sl; cost, l3, l4; den, wtM, wtD, rowOf) is a free letter.
None of the three has an inhabitant or a test against emptiness of its own in this file.

Limits: R0 is free in every statement and comes out as it went in. If R0, or the in-joint's own
claim, gives the source, the statement follows from the premise alone and says nothing
(`forB_hollow`). The two sentences named in ForB.lean's head are owed for each use. Nothing on
whether the programs' tests are these targets, on whether a later stage takes a target up, or on an
honest prover.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.Tie.Pv.Lookup.Rider.ForB

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks Cb.LdLkp Cb.LdLkp.Kn TWhole Cb.Fo Finset

/-- The first part lies inside the point. -/
theorem sh_dT_le (h : Sh) : h.dT ≤ FoNums.v' h + 1 := by
  have e : h.v = h.dT + h.rK := rfl
  unfold FoNums.v'
  omega

/-- The point has dT + rK places, if it has any. -/
theorem sh_v_eq {h : Sh} (hv : 1 ≤ h.v) : FoNums.v' h + 1 = h.dT + h.rK := by
  have e : h.v = h.dT + h.rK := rfl
  unfold FoNums.v'
  omega

variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
  {h : Sh} {L : Lay E St₀ J₀} {Ex : ExtSpec} {Kc M Wp : Type} {R0 : IOR.Rels Kc St₀ Ex (M × Wp)}
  {msg₀ : M → J₀ → E}

/-- "The entries sum to 1 at every vertex", for each member of a family, at the last lt places of
the first part of the key point. Source: for each lm and each X < 2^lt the nE values sum to 1.
Target: for each lm the nE multilinear extensions at those places sum to 1. Warning: R0 is free
(forB_hollow). -/
theorem oneHot_forB
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {Lm : Type} (lt nE : ℕ) (hlt : lt ≤ h.dT) (sl : Lm → St₀ → M → Fin nE → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a => ∀ lm, ∀ X < 2 ^ lt, ∑ k, sl lm a.1 m k X = 1)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ∀ lm, ∑ k, ext lt (sl lm b.1.1.1 m k) (fun t => b.1.2.1.pt (h.dT - lt + t)) = 1)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  oneHot_of (forB_rides hK) lt nE (h.dT - lt) (by have := sh_dT_le h; omega) sl

/-- Two conditions with a public indicator, at the last lt places of the first part of the key
point. Warning: R0 is free (forB_hollow). If no vertex counts the rider says nothing
(two_lines_none). -/
theorem two_lines_forB
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    (lt : ℕ) (hlt : lt ≤ h.dT) (cost : St₀ → ℕ → Bool) (l3 l4 : St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a =>
        ∀ X < 2 ^ lt, cost a.1 X = true → l3 a.1 m X = 0 ∧ l4 a.1 m X = 0)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ext lt (fun X => if cost b.1.1.1 X = true then l3 b.1.1.1 m X else 0)
            (fun t => b.1.2.1.pt (h.dT - lt + t)) = 0 ∧
          ext lt (fun X => if cost b.1.1.1 X = true then l4 b.1.1.1 m X else 0)
            (fun t => b.1.2.1.pt (h.dT - lt + t)) = 0)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  two_lines_of (forB_rides hK) lt (h.dT - lt) (by have := sh_dT_le h; omega) cost l3 l4

/-- "The denominator is the row sum at every block, head and position", at the places selAtt of the
key point: through a call's point of iota + dT places, one place skipped. Asked of h: the point has
at least one place. Warning: R0 is free (forB_hollow). -/
theorem denom_forB
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    (hv : 1 ≤ h.v) (iota nb lgk lt ldh nS nT B NP : ℕ) (h1 : iota ≤ h.rK)
    (hb : nb + 1 + lgk + lt + ldh = h.dT + iota) (hN : NP ≤ 2 ^ nb)
    (rowOf : ℕ → ℕ → ℕ) (den : St₀ → M → ℕ → ℕ → ℕ → E)
    (wtM : St₀ → M → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E) (wtD : St₀ → M → ℕ → ℕ → ℕ → ℕ → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a =>
        ∀ P < NP, ∀ g < 2 ^ lgk, ∀ i < 2 ^ lt,
          den a.1 m P g i = rowSumA nS nT B rowOf wtM wtD a.1 m P g i)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ext (nb + lgk + lt) (onPieces lgk lt NP (den b.1.1.1 m))
            (fun t => b.1.2.1.pt (selAtt h.dT h.rK iota nb t)) =
          ext (nb + lgk + lt) (onPieces lgk lt NP (rowSumA nS nT B rowOf wtM wtD b.1.1.1 m))
            (fun t => b.1.2.1.pt (selAtt h.dT h.rK iota nb t)))
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  denom_of (forB_rides hK) h.dT h.rK iota nb lgk lt ldh nS nT B NP (sh_v_eq hv) h1 hb hN rowOf den
    wtM wtD

end Cb.Rider

#print axioms Cb.Rider.oneHot_forB
#print axioms Cb.Rider.two_lines_forB
#print axioms Cb.Rider.denom_forB
