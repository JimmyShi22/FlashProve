-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBitsPayAt.lean: the three premises of bits9_claim
(OnBytes/Tie/Pv/Lookup/Ends/FoTailBits.lean), paid at the smallness test's own lookup.

bits9_claim says what the three claims that HTailF2.linBits9 writes by hand are worth, at letters
bit0, bit1, pin under which planesK and countK give the sums of the three runs on the array BZ. Here
the letters are the columns' sums of the lookup's cells at lm = 5, colsK h 5 zb0 ν, colsK h 5 zb1 ν
and pinColK 5 ν, and the three premises are theorems.

 - cellsBZ_dig: at the entries that the caller names by en, and the virtual matrix plV tl en of the
   planes, the cells are BZ's entries (CellsBZ).
 - pinW_read: the third run's weights, read in a ring: 2^(i mod 32).
 - pay_run: the first two premises, for a point z and a virtual row e.
 - pay_pin: the third premise.
 - bits9_paid: bits9_claim with the three premises paid: the three claims that linBits9 writes are
   worth claimLeaves, claimBits and countK at these columns' sums.

Premises left: FoNums.ok; 2^cK = NC; 5 ≤ kT + cK; ν reads 0 at the place that is no cell; CellsBZ;
the point's length; and VirtRow for each of the three virtual rows of BZ: that row 0 and row 1
combine BZ's 32 rows under the equality weights of the first five coordinates of zb0 and of zb1, and
that row 2 adds them up.
bits9_paid keeps bits9_claim's own premises too: tl.f9 = g.shape; the run of pscRow on the leaves'
sumcheck returns from (F, c), with the form row, and leaves F1; HeardIs ρ g F0 (endsOf g.shape 5 jLK
rsK): the record g, with the state F0, holds the flat function's end values at the rounds rsK
(OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean); Later F0 F; Sized F; Later F1 H.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that VirtRow holds of a committed array.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoBitsPay
import OnBytes.Tie.Pv.Lookup.Ends.FoTailBits
import OnBytes.Tie.Pv.Lookup.Digits.PortEnds

set_option autoImplicit false

namespace Fo
open TwV Finset FoNums Cb.Fo Cb.Fo.Pin OnBytes OnBytes.Model OnBytes.DgP OnBytes.PscRun

section
variable {K : Type} [CommRing K]

/-- The cells of the digits' lookup are BZ's entries. -/
theorem cellsBZ_dig {J₀ : Type} (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) :
    CellsBZ tl.f9 (fun p => zext μ₀ (Cb.Fo.NumsEq.placeOf mk (plV tl en) p))
      (fun r i => μ₀ (en (tl.ix.BZ, r, i))) := by
  intro j t c _ ht _
  show μ₀ (bcJ tl en ((c * 2 ^ tl.f9.kT + t) % 2 ^ tl.f9.kT) ((c * 2 ^ tl.f9.kT + t) / 2 ^ tl.f9.kT)
    j) = _
  rw [Nat.mul_comm c, Nat.mul_add_mod, Nat.mod_eq_of_lt ht, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt ht, Nat.add_zero]
  rfl

variable (ρ : Reading K)

/-- The third run's weights, read. -/
theorem pinW_read (tl : HTailF2) (i : ℕ) (hi : i < tl.bzColumns) :
    (rdL ρ (pinW tl)).getD i 0 = (2 : K) ^ (i % 32) := by
  rw [← rdL_getD]
  have e : (pinW tl).getD i zeroE = ofNat (2 ^ (i % 32)) := by
    unfold pinW
    simp [Array.getD, hi]
  rw [e, natE_val, Nat.cast_pow, Nat.cast_ofNat]

/-- The first two premises. -/
theorem pay_run (tl : HTailF2) (h : FoNums.Sh) (hs : tl.f9 = h) (hok : ok h = true)
    (hfull : 2 ^ h.cK = h.NC) (ν : Pl → K) (h0 : ν .zero = 0) (B : ℕ → ℕ → K)
    (hB : CellsBZ h ν B) (z : List K) (hz : z.length = 5 + (h.kT + h.cK)) (W : World K) (e : ℕ)
    (hV : VirtRow W.entry tl.ix.BZ e (fun r => (eqTabK (z.take 5)).getD r 0) B 32 tl.bzColumns) :
    planesK h 5 z (colsK h 5 z ν) =
      runK W tl e fun i => (eqTabK (exL z 5 (5 + h.kT + h.cK))).getD i 0 := by
  subst hs
  exact pay_bits tl.f9 hok hfull ν h0 B hB z hz W.entry tl.ix.BZ e hV

/-- The third premise. -/
theorem pay_pin (tl : HTailF2) (h : FoNums.Sh) (hs : tl.f9 = h) (hok : ok h = true)
    (hfull : 2 ^ h.cK = h.NC) (h5 : 5 ≤ h.kT + h.cK) (ν : Pl → K) (h0 : ν .zero = 0)
    (B : ℕ → ℕ → K) (hB : CellsBZ h ν B) (W : World K)
    (hV : VirtRow W.entry tl.ix.BZ 2 (fun _ => 1) B 32 tl.bzColumns) :
    countK h 5 (pinColK 5 ν) = -((2 ^ h.v - h.padding : ℕ) : K) +
      runK W tl 2 fun i => (rdL ρ (pinW tl)).getD i 0 := by
  subst hs
  rw [pay_count tl.f9 hok hfull h5 ν h0 B hB W.entry tl.ix.BZ 2 hV]
  congr 1
  unfold runK
  rw [runSum_range, runSum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  show _ = (rdL ρ (pinW tl)).getD i 0 * W.entry tl.ix.BZ 2 i
  rw [pinW_read ρ tl i (Finset.mem_range.mp hi)]


theorem ends_zb0_len (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) :
    (endsOf h lm jLK rs).zb0.length = 5 + (h.kT + h.cK) := by
  show (byVar (ordE h) _).reverse.length = _
  rw [List.length_reverse]
  unfold byVar
  rw [List.length_map, List.length_range, ordE_len]
  rfl

theorem ends_zb1_len (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) :
    (endsOf h lm jLK rs).zb1.length = 5 + (h.kT + h.cK) := by
  show (byVar (ordB h) _).reverse.length = _
  rw [List.length_reverse]
  unfold byVar
  rw [List.length_map, List.length_range, ordB_len]
  rfl

/-- The three claims that linBits9 writes by hand are worth the lookup's three claims on the planes,
at the columns' sums of the lookup's own cells. F0: the state with which the record holds the end
values. F1: the state behind pscRow. -/
theorem bits9_paid (tl : HTailF2) (g : Forest.Heard) (jLK : ℕ) (rsK : Rounds K) (F0 F F1 : Fork)
    (c c1 : Ctx) (row : Aff) (p' : Psc) (hs : tl.f9 = g.shape)
    (h : pscRow g.leaves oneE {} F c = .ok (((row, p'), F1), c1))
    (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hF : Sized F) (hfull : 2 ^ g.shape.cK = g.shape.NC)
    (h5 : 5 ≤ g.shape.kT + g.shape.cK) (H : Fork) (hH : Later F1 H) (ν : Pl → K)
    (entry : ℕ → ℕ → ℕ → K) (B : ℕ → ℕ → K) (hz : ν .zero = 0) (hB : CellsBZ g.shape ν B)
    (hV0 : VirtRow entry tl.ix.BZ 0
      (fun r => (eqTabK ((endsOf g.shape 5 jLK rsK).zb0.take 5)).getD r 0) B 32 tl.bzColumns)
    (hV1 : VirtRow entry tl.ix.BZ 1
      (fun r => (eqTabK ((endsOf g.shape 5 jLK rsK).zb1.take 5)).getD r 0) B 32 tl.bzColumns)
    (hV2 : VirtRow entry tl.ix.BZ 2 (fun _ => 1) B 32 tl.bzColumns) :
    [row.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
        Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)
          (bzRun tl 0 (mulE g.leaves.eps g.leavesA)
            (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))),
      (Aff.slot g.sBit).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
        Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)
          (bzRun tl 1 (subE zeroE oneE) (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))),
      (Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding)))).value ρ
          (H.worldOf ρ (fun j => ν (.mask j)) entry) +
        Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (bzRun tl 2 oneE (pinW tl))] =
    [claimLeaves g.shape 5 jLK rsK ν (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb0 ν),
      claimBits g.shape 5 jLK rsK ν (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb1 ν),
      countK g.shape 5 (pinColK 5 ν)] :=
  (bits9_claim ρ tl g 5 jLK rsK F0 F F1 c c1 row p' hs h hI h0 hok hF).2.2.2.2 H hH ν entry _ _ _
    (pay_run tl g.shape hs hok hfull ν hz B hB _ (ends_zb0_len _ _ _ _) _ 0 hV0)
    (pay_run tl g.shape hs hok hfull ν hz B hB _ (ends_zb1_len _ _ _ _) _ 1 hV1)
    (pay_pin ρ tl g.shape hs hok hfull h5 ν hz B hB _ hV2)

end
end Fo
