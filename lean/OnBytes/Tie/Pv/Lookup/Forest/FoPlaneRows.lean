-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPlaneRows.lean.
The lookup of a sub-proof: its two end claims on the planes of counts, in the form in which the
byte-level verifier makes them.

The flat form of the lookup's verifier (TwV) hands on two rows that read the bits of the counts at a
point: the row of the leaves' sumcheck (TwV.rowEnd) and the row that says that the planes' value at
the bits' point is what the bits' sumcheck has shown (TwV.rowBitE). Both walk over all 2^(5 + d)
bits, and the first over all 2^d rows of the joined table. The byte-level verifier
(Forest.planeClaims, OnBytes/Model/Look.lean) computes closed forms instead.

States, for every shape h that passes FoNums.ok, every lm with 5 ≤ lm ≤ kT + 5, every trace t and
every reading μ of the places that reads "zero" as 0:
  ok_facts: the clauses of FoNums.ok that are used.
  tab_ext_g, plane_sum_g: the two lemmas on the table's end and on the planes, for a point given as
    one list of 5 + d coordinates.
  rowEnd_iff: TwV.rowEnd holds of μ if and only if the hiding polynomial's share, the incoming
    form's share and eps · (leavesA · planes at zb0) add up to fin - eps.
  rowBitE_iff: TwV.rowBitE holds of μ if and only if the value shown by the bits' sumcheck, less its
    mask's share, less the planes at zb1 is 0.
Here zb0, zb1 are the two points as arrays, the top bit first (the reversal of the point by
coordinate), leavesA is Fo.leavesAK and "planes at" is Fo.planesK of the columns' sums under
Fo.phiBK.
Does not say: that Forest.planeClaims makes forms with these values. That is planes_claim
(OnBytes/Tie/Pv/Lookup/Forest/FoClaimsMeet.lean), at the values of the caller's forms.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPlane

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset OnBytes.Model

section
variable {K : Type} [CommRing K]

/-- A sparse row holds of a reading. -/
def SRowHolds {P : Type} (r : SRow P K) (μ : P → K) : Prop := valS r.cf μ = r.tg

theorem valS_append {P : Type} (a b : List (P × K)) (μ : P → K) : valS (a ++ b) μ = valS a μ + valS
    b μ := by
  unfold valS
  rw [List.map_append, List.sum_append]

theorem valS_scale {P : Type} (c : K) (a : List (P × K)) (μ : P → K) : valS (scale c a) μ = c * valS
    a μ := by
  unfold valS scale
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun pc _ => ?_)
  show c * pc.2 * μ pc.1 = c * (pc.2 * μ pc.1)
  ring

/-- The clauses of FoNums.ok that the table's end uses. -/
theorem ok_facts (h : Sh) (hok : ok h = true) :
    1 ≤ h.NC ∧ h.NC ≤ 2 ^ h.cK ∧ h.calls.size = h.NC ∧ (∀ c < h.NC, kOf h c ≤ h.kT) ∧
      h.kT ≤ 16 := by
  unfold ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, h1⟩, h2⟩, _⟩, _⟩, _⟩, h3⟩, _⟩, h4⟩, _⟩, _⟩, h5⟩, _⟩, _⟩ := hok
  exact ⟨h1, h2, h3, fun c hc => (h4 c hc).1.1.2, h5⟩

omit [CommRing K] in
theorem split4 (g : List K) (a b c : ℕ) :
    g = g.take a ++ ((g.drop a).take b ++ (((g.drop a).drop b).take c ++ ((g.drop a).drop b).drop
        c)) := by
  rw [List.take_append_drop, List.take_append_drop, List.take_append_drop]

/-- The table's end, for a point given as one list, by coordinate. -/
theorem tab_ext_g (h : Sh) (hok : ok h = true) (θ lam : K) (g : List K)
    (hg : g.length = FoNums.w + h.d) :
    ((List.range (2 ^ h.d)).map fun r => eqN (g.drop FoNums.w) r * (lam - 1 - tabF h θ r)).sum =
      leavesAK h θ lam g.reverse := by
  obtain ⟨h1, _, h3, h4, h16⟩ := ok_facts h hok
  have h64 : h.kT < 64 := by omega
  have hd : h.d = h.kT + h.cK := rfl
  have hw : FoNums.w = 5 := rfl
  have e : g = g.take FoNums.w ++ ((g.drop FoNums.w).take h.cK ++ (g.drop FoNums.w).drop h.cK) := by
    rw [List.take_append_drop, List.take_append_drop]
  have := tab_ext h h1 h3 h4 h64 θ lam (g.take FoNums.w) ((g.drop FoNums.w).take h.cK)
    ((g.drop FoNums.w).drop h.cK) (by rw [List.length_take]; omega)
    (by rw [List.length_take, List.length_drop]; omega)
    (by rw [List.length_drop, List.length_drop]; omega)
  rwa [← e] at this

/-- The planes, for a point given as one list, by coordinate. -/
theorem plane_sum_g (h : Sh) (hok : ok h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (θ
    : K)
    (μ : Pl → K) (h0 : μ .zero = 0) (g : List K) (hg : g.length = FoNums.w + h.d) :
    valS (bitsForm (numsF h lm jLK θ) g) μ =
      planesK h lm g.reverse fun col =>
        ∑ row ∈ range (2 ^ lm), (phiBK h lm g.reverse).getD row 0 * μ (.cell row col) := by
  obtain ⟨_, h2, _, _, _⟩ := ok_facts h hok
  have hd : h.d = h.kT + h.cK := rfl
  have hw : FoNums.w = 5 := rfl
  have := plane_sum h lm jLK θ μ h0 h2 h5 hlm (g.take 5) ((g.drop 5).take h.cK)
    (((g.drop 5).drop h.cK).take (lm - 5)) (((g.drop 5).drop h.cK).drop (lm - 5))
    (by rw [List.length_take]; omega) (by rw [List.length_take, List.length_drop]; omega)
    (by rw [List.length_take, List.length_drop, List.length_drop]; omega)
    (by rw [List.length_drop, List.length_drop, List.length_drop]; omega)
  rwa [← split4 g 5 h.cK (lm - 5)] at this

theorem byVar_len (o : List ℕ) (xs : List K) : (byVar o xs).length = o.length := by
  unfold byVar
  rw [List.length_map, List.length_range]

theorem ordE_len (h : Sh) : (ordE h).length = FoNums.w + h.d := by
  unfold ordE
  rw [List.length_map, List.length_range]

theorem ordB_len (h : Sh) : (ordB h).length = FoNums.w + h.d := by
  unfold ordB
  rw [List.length_map, List.length_range]

/-- The columns' sums that the caller hands in, at the point z (an array, the top bit first). -/
def colsK (h : Sh) (lm : ℕ) (z : List K) (μ : Pl → K) : ℕ → K := fun col =>
  ∑ row ∈ range (2 ^ lm), (phiBK h lm z).getD row 0 * μ (.cell row col)

/-- The row of the leaves' sumcheck, as the byte-level verifier makes it. -/
theorem rowEnd_iff (h : Sh) (hok : ok h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) (θ : K) (μ : Pl → K) (h0 : μ .zero = 0) (t : Trace K) :
    SRowHolds (rowEnd (numsF h lm jLK θ) t) μ ↔
      valS (hide (numsF h lm jLK θ).ledE (dgE (numsF h lm jLK θ)) t.cls.xs) μ +
          t.cls.eps * valS (incTop (numsF h lm jLK θ).ledT (incT0 (numsF h lm jLK θ) t)
              t.tabl.reverse) μ +
          t.cls.eps * (leavesAK h θ t.lam (byVar (ordE h) t.cls.xs).reverse *
            planesK h lm (byVar (ordE h) t.cls.xs).reverse
              (colsK h lm (byVar (ordE h) t.cls.xs).reverse μ)) =
        t.cls.fin - t.cls.eps := by
  have hg : (byVar (ordE h) t.cls.xs).length = FoNums.w + h.d := by rw [byVar_len, ordE_len]
  unfold SRowHolds
  show valS (hide (numsF h lm jLK θ).ledE (dgE (numsF h lm jLK θ)) t.cls.xs ++
        scale t.cls.eps (incTop (numsF h lm jLK θ).ledT (incT0 (numsF h lm jLK θ) t) t.tabl.reverse)
            ++
        scale (t.cls.eps * ((List.range (2 ^ h.d)).map fun r =>
            eqN ((byVar (ordE h) t.cls.xs).drop FoNums.w) r * (t.lam - 1 - tabF h θ r)).sum)
          (bitsForm (numsF h lm jLK θ) (byVar (ordE h) t.cls.xs))) μ = t.cls.fin - t.cls.eps * 1 ↔ _
  rw [valS_append, valS_append, valS_scale, valS_scale, tab_ext_g h hok θ t.lam _ hg,
    plane_sum_g h hok lm jLK h5 hlm θ μ h0 _ hg, mul_one, mul_assoc]
  rfl

/-- The planes' value at the bits' point is what the bits' sumcheck has shown. -/
theorem rowBitE_iff (h : Sh) (hok : ok h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (θ
    : K)
    (μ : Pl → K) (h0 : μ .zero = 0) (t : Trace K) :
    SRowHolds (rowBitE (numsF h lm jLK θ) t) μ ↔
      (t.bits.v 0 - t.bits.be * μ ((numsF h lm jLK θ).ledB.sh 0)) -
          planesK h lm (byVar (ordB h) t.bits.xs).reverse
            (colsK h lm (byVar (ordB h) t.bits.xs).reverse μ) = 0 := by
  have hg : (byVar (ordB h) t.bits.xs).length = FoNums.w + h.d := by rw [byVar_len, ordB_len]
  unfold SRowHolds
  show valS (bitsForm (numsF h lm jLK θ) (byVar (ordB h) t.bits.xs) ++
      [((numsF h lm jLK θ).ledB.sh 0, t.bits.be)]) μ = t.bits.v 0 ↔ _
  rw [valS_append, plane_sum_g h hok lm jLK h5 hlm θ μ h0 _ hg]
  have e : valS [((numsF h lm jLK θ).ledB.sh 0, t.bits.be)] μ = t.bits.be * μ ((numsF h lm jLK
      θ).ledB.sh 0) := by
    simp [valS]
  rw [e]
  unfold colsK
  constructor
  · intro hh
    rw [← hh]
    ring
  · intro hh
    rw [← sub_eq_zero.mp hh]
    ring

end
end Fo
