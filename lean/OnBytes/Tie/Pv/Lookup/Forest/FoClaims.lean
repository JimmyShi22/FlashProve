-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean.
The lookup of a sub-proof: its claims as a list of values, in the byte-level verifier's order and
sign.

A sub-proof adds all its claims up, claim number c under the c-th power of one drawn element. So a
caller of the lookup needs more than "these claims hold": it needs each claim as the value that
must be 0, with the sign that the byte-level verifier gives it, in the order in which the byte-level
verifier's routines make them. This file gives that list from the record of end values (Fo.endsOf).

Defines:
  claimsOf h lm jLK rs ν bit0 bit1 pin kf: the list
    - the claims on mask entries alone, in the order of the run (Forest.objects): the tie's steps,
      the key levels, the table's levels, the bits' sumcheck: each the row's form less its target;
    - the three claims on the planes, in the order of Forest.planeClaims: the row of the leaves'
      sumcheck (its form less its target); the value shown by the bits' sumcheck, less its mask's
      share, LESS the planes at zb1; the counts' sum less the number of keys that are not padding;
    - the join (Forest.join): the calls' terms, plus the trees of padding alone, LESS the form
      (cEndF, cEndC) for the end of the key side.
  ν reads the lookup's places. The caller's forms enter BY THEIR VALUES, as letters: bit0 col and
  bit1 col (the planes' column col under the weights of zb0, of zb1), pin col (under the powers of
  2), kf c (call c's key vector at its point).
States:
  claims_len: there are as many as the record has rows, and four.
  claims_row, claims_last: which value stands at which number of the list.
  claims_iff: all values of the list are 0 if and only if EndsHold
    (OnBytes/Tie/Pv/Lookup/Forest/FoOutAll.lean), where the
    letters are the values that EndsHold names.
  HCclaims, hcClaims: a closed proposition and its proof: what the typed verifier of the lookup
    puts out holds if and only if every value of the list is 0.
Premises: in claims_iff: the form cEnd has at μ the value that the record's form (cEndF, cEndC) has
at ν. In hcClaims: those of hcEnds (OnBytes/Tie/Pv/Lookup/Forest/FoOutAll.lean): FoNums.ok h = true;
5 ≤ lm ≤ kT + 5; the two equations on the layout; KFokAt AT THE READING AT WHICH THE CLAIM IS SAID,
which is a claim on the reading.
Not claimed here: that the forms which the byte-level routines make have these values, number by
number. claims_iff does not see a sign or an order. What sees them are equations of values: for the
join OnBytes/Tie/Pv/Lookup/Forest/FoClaimsPort.lean (join_claim); for the rows and the planes' three
OnBytes/Tie/Pv/Lookup/Forest/FoClaimsMeet.lean (rows_claim, planes_claim; the whole list:
claims_port).
Where each claim stands in the sub-proof's own numbering is the caller's to say.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoOutAll

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq Cb.Fo.Pin
open Finset

section
variable {K : Type} [CommRing K]

/-- The row of the leaves' sumcheck: its form less its target. -/
def claimLeaves (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K) (bit0 : ℕ → K) : K :=
  valS (hide (forN h lm jLK rs).ledE (dgE (forN h lm jLK rs)) (endsOf h lm jLK rs).lvXs) ν +
    (endsOf h lm jLK rs).lvEps * valS (endsOf h lm jLK rs).lvInc ν +
    (endsOf h lm jLK rs).lvEps *
      (leavesAK h (endsOf h lm jLK rs).theta (endsOf h lm jLK rs).alpha (endsOf h lm jLK rs).zb0 *
        planesK h lm (endsOf h lm jLK rs).zb0 bit0) -
    ((endsOf h lm jLK rs).lvFin - (endsOf h lm jLK rs).lvEps)

/-- The value shown by the bits' sumcheck, less its mask's share, less the planes at zb1. -/
def claimBits (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K) (bit1 : ℕ → K) : K :=
  ((forTrace h lm jLK rs).bits.v 0 -
      (forTrace h lm jLK rs).bits.be * ν ((forN h lm jLK rs).ledB.sh 0)) -
    planesK h lm (endsOf h lm jLK rs).zb1 bit1

/-- The join: the calls' terms, plus the trees of padding alone, less the form for the end of the
key side. -/
def claimJoin (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K) (kf : ℕ → K) : K :=
  AffK.val (joinK h (endsOf h lm jLK rs).theta (endsOf h lm jLK rs).alpha
    (eK h (endsOf h lm jLK rs).zy) (endsOf h lm jLK rs).zy (fun c => AffK.ofConst (kf c))
    ((endsOf h lm jLK rs).cEndF, (endsOf h lm jLK rs).cEndC)) ν

/-- The lookup's claims, each as the value that must be 0. -/
def claimsOf (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K)
    (bit0 bit1 pin kf : ℕ → K) : List K :=
  (endsOf h lm jLK rs).rows.map (rowRes ν) ++
    [claimLeaves h lm jLK rs ν bit0, claimBits h lm jLK rs ν bit1, countK h lm pin,
      claimJoin h lm jLK rs ν kf]

theorem claims_len (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K)
    (bit0 bit1 pin kf : ℕ → K) :
    (claimsOf h lm jLK rs ν bit0 bit1 pin kf).length = (endsOf h lm jLK rs).rows.length + 4 := by
  unfold claimsOf
  simp

/-- The first values are the rows', in the record's order. -/
theorem claims_row (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K)
    (bit0 bit1 pin kf : ℕ → K) (i : ℕ) (hi : i < (endsOf h lm jLK rs).rows.length) :
    (claimsOf h lm jLK rs ν bit0 bit1 pin kf)[i]? =
      ((endsOf h lm jLK rs).rows[i]?).map (rowRes ν) := by
  unfold claimsOf
  rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map]

/-- The last four, in this order: the leaves' row, the bits' value, the counts' sum, the join. -/
theorem claims_last (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K)
    (bit0 bit1 pin kf : ℕ → K) :
    (claimsOf h lm jLK rs ν bit0 bit1 pin kf).drop (endsOf h lm jLK rs).rows.length =
      [claimLeaves h lm jLK rs ν bit0, claimBits h lm jLK rs ν bit1, countK h lm pin,
        claimJoin h lm jLK rs ν kf] := by
  unfold claimsOf
  rw [List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp), List.nil_append]

/-- All values are 0 if and only if the claims hold. -/
theorem claims_iff {P : Type} (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (cEnd : AffK P K)
    (KF : ℕ → AffK P K) (ν : Pl → K) (μ : P → K)
    (hE : AffK.val cEnd μ =
      AffK.val ((endsOf h lm jLK rs).cEndF, (endsOf h lm jLK rs).cEndC) ν) :
    (∀ x ∈ claimsOf h lm jLK rs ν (colsK h lm (endsOf h lm jLK rs).zb0 ν)
        (colsK h lm (endsOf h lm jLK rs).zb1 ν) (pinColK lm ν) (fun c => AffK.val (KF c) μ),
      x = 0) ↔ EndsHold h lm jLK rs cEnd KF ν μ := by
  unfold claimsOf claimLeaves claimBits claimJoin EndsHold
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false, or_imp,
    forall_and, forall_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  have hJ : AffK.val (joinK h (endsOf h lm jLK rs).theta (endsOf h lm jLK rs).alpha
        (eK h (endsOf h lm jLK rs).zy) (endsOf h lm jLK rs).zy
        (fun c => AffK.ofConst (AffK.val (KF c) μ))
        ((endsOf h lm jLK rs).cEndF, (endsOf h lm jLK rs).cEndC)) ν =
      AffK.val (joinK h (endsOf h lm jLK rs).theta (endsOf h lm jLK rs).alpha
        (eK h (endsOf h lm jLK rs).zy) (endsOf h lm jLK rs).zy KF cEnd) μ := by
    rw [val_joinK, val_joinK, hE]
    simp only [AffK.val_ofConst]
  rw [hJ, sub_eq_zero]
  have hR : (∀ r ∈ (endsOf h lm jLK rs).rows, rowRes ν r = 0) ↔
      ∀ r ∈ (endsOf h lm jLK rs).rows, SRowHolds r ν :=
    forall_congr' fun r => imp_congr_right fun _ => sub_eq_zero
  rw [hR]

end

/-- What the typed verifier of a sub-proof's lookup puts out, as the list of values that must be 0:
a closed proposition. -/
def HCclaims : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh)
    (L : Lay E St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀),
    FoNums.ok h = true → 5 ≤ lm → lm ≤ h.kT + 5 → (∀ s, L.mkS s = mk (jLK + s)) →
    (∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2) →
    ∀ (Ex : ExtSpec) (a : St₀ × Ex.Str) (τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape),
      ∃ x : TX (St₀ × E) E (Option J₀),
        (forB E h L V₀ V₀C (Ex := Ex)).R.red.out a τ = some (x, a.2) ∧
        ∀ (KF : ℕ → AffK (Option J₀) E) (μ₀ : J₀ → E),
          KFokAt h (forK E L a.1) (fun c => (endsOf h lm jLK (forFl h L Ex τ)).zk.getD c []) KF
            (zext μ₀) →
            ((forA E h L).lk.out id id x (zext μ₀) ↔
              ∀ y ∈ claimsOf h lm jLK (forFl h L Ex τ) (fun p => zext μ₀ (placeOf mk pl p))
                (colsK h lm (endsOf h lm jLK (forFl h L Ex τ)).zb0
                  fun p => zext μ₀ (placeOf mk pl p))
                (colsK h lm (endsOf h lm jLK (forFl h L Ex τ)).zb1
                  fun p => zext μ₀ (placeOf mk pl p))
                (pinColK lm fun p => zext μ₀ (placeOf mk pl p))
                (fun c => AffK.val (KF c) (zext μ₀)), y = 0)

theorem hcClaims : HCclaims := by
  intro E _ _ St₀ J₀ _ _ h L lm jLK mk pl H h5 hlm hmk hbc Ex a τ
  obtain ⟨x, h1, h2⟩ := hcEnds E St₀ J₀ h L lm jLK mk pl H h5 hlm hmk hbc Ex a τ
  refine ⟨x, h1, fun KF μ₀ hKF => (h2 KF μ₀ hKF).trans (claims_iff h lm jLK _ _ KF _ _ ?_).symm⟩
  unfold AffK.val mapL
  simp only [List.map_map]
  rfl

end Fo
