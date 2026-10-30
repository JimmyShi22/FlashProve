-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsLaw.lean

The lookup's relation after the challenge, Cb.Lkp.MidP (Cb/Pv/Lookup/Alg/PadAlg.lean), at the joint
key vector and the joint table of a sub-proof (Ends.jointKey, Ends.jointTab,
OnBytes/Tie/Pv/Lookup/Ends/Joint.lean) and at bits that are the planes' matrix of
Johnson/HonestTrace/Counts.lean. It is stated once, for any shape h, any key vectors kv and any
padding places pad; the files on the kinds of sub-proof apply it.

Notation. NC, kT, cK, dT, rK are fields of h : Forest.Shape; d = kT + cK; v = dT + rK;
n_c = FoNums.nOf h c and k_c = FoNums.kOf h c; a place of call c is an index below 2^(n_c); lm: the
planes' matrix has 2^lm rows. See the head of Johnson/HonestTrace/Counts.lean.

MidP n D 5 32 key t pads M al has three clauses: every x = M u j with u < 2^D, j < 32 has
x (x - 1) = 0; the sum of 2^j M u j over u < 2^D, j < 32 is the natural number 2^n - padNum pads (a
subtraction that is cut off at 0; FoNums.ok h has padNum (FoNums.pads h) ≤ 2^v), cast into K; the
product of al - key b over b < 2^n is the padding's public factor padFac times the product over
j < 32 of (the product over u < 2^D of 1 + M u j (al - 1 - t u))^(2^j). Below it stands at n := v
and D := d.

Main theorems. "The four premises" are: FoNums.ok h; for every call c below h.NC every place below
2^(n_c) of kv c holds the value of a row below 2^(k_c) of tabOf K h c; every padding place of such a
call holds the value of the call's padding row; PubFits h pad.
* "midP_joint": under the four premises, for all θ and al, MidP holds at jointKey h kv θ,
  jointTab h θ, FoNums.pads h and the bits Cb.Lkp.hbitP at padJ and rowJ of hitsOf.
* "law_bits": under the four premises, if 5 ≤ lm ≤ kT + 5 and bits u j is the cell of plane, at
  hitsOf h (tabOf K h) kv pad, at FoNums.cellRC h lm (u / 2^cK, u % 2^cK, j) for all u < 2^d and
  j < 32, then for all θ and al MidP holds at jointKey h kv θ, jointTab h θ, FoNums.pads h and bits.
* "sum_plane_all": under FoNums.ok h and Fits h T Kv H, if 5 ≤ lm ≤ kT + 5: the cells of plane in
  the rows below 2^lm and the columns below NC 2^(kT + 5 - lm), weighted by 2^(r % 32), and
  h.padding add up to 2^v. A statement on natural numbers.
* "hbitP_plane": under FoNums.ok h, if 5 ≤ lm ≤ kT + 5, u < 2^d and j < 32, the bit hbitP at padJ
  and rowJ is the cell of plane at FoNums.cellRC h lm (u / 2^cK, u % 2^cK, j).
* "jointKey_sh", "jointTab_sh": under FoNums.ok h the joint vectors are Port.key and Port.tab
  (OnBytes/Tie/Pv/Lookup/Port/ShiftQPort.lean) at the tables tabOf K h, shifted by shKeyQ and shTabQ
  (Cb/Pv/Lookup/Shift/ShiftQ.lean).

Limits. h, kv and pad are arbitrary arguments. The four premises are assumed, not proved; whether
they can hold together is a matter of the file that applies the law. The second clause of MidP is an
equation in K: in a field of small characteristic it says less than "sum_plane_all". θ and al are
any elements: no probability occurs. K is a field with decidable equality because hitsOf compares
values.

Not claimed: that jointKey and jointTab are what a verifier checks; that MidP at these vectors makes
any claim of the protocol's lookup argument hold (its levels, leaves, masks and rounds do not occur
here); that a prover's committed cells are these bits; completeness of the protocol.

-/
import Johnson.HonestTrace.CountsTab
import Johnson.HonestTrace.CountsFits
import Johnson.HonestTrace.CountsJoint

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model
open Cb.Lkp Cb.LdLkp

section
variable {K : Type} [Field K]

/-- Under FoNums.ok h the joint key vector Ends.jointKey h kv θ is Port.key at the tables tabOf K h,
moved by the shift: call number times θ. -/
theorem jointKey_sh {h : Forest.Shape} (hok : FoNums.ok h = true) (kv : ℕ → ℕ → K) (θ : K) :
    Ends.jointKey h kv θ =
      shKeyQ (Port.fK h) (Port.key h (tabOf K h) kv) (fun c => (c : K)) θ := by
  funext X
  have h0 : 0 < h.calls.size := by
    have := calls_size hok
    omega
  exact Fo.jointKey_port (Cb.Fo.ok_portOK hok) (tabOf K h) kv θ (tabOf_eq K h h0 _) X

/-- Under FoNums.ok h the joint table Ends.jointTab h θ is Port.tab at the tables tabOf K h, moved
by the shift: call number times θ. -/
theorem jointTab_sh {h : Forest.Shape} (hok : FoNums.ok h = true) (θ : K) :
    Ends.jointTab h θ = shTabQ (Port.fT h) (Port.tab h (tabOf K h)) (fun c => (c : K)) θ := by
  funext u
  have hc : min (u % 2 ^ h.cK) (h.NC - 1) < h.calls.size := by
    have := calls_size hok
    omega
  show ((Ends.tauN h (min (u % 2 ^ h.cK) (h.NC - 1))
      (u / 2 ^ h.cK % 2 ^ Ends.kN h (min (u % 2 ^ h.cK) (h.NC - 1))) : ℕ) : K) + _ =
    tabOf K h (min (u % 2 ^ h.cK) (h.NC - 1))
      (u / 2 ^ h.cK % 2 ^ Port.kOf h (min (u % 2 ^ h.cK) (h.NC - 1))) + _
  rw [tabOf_eq K h hc]
  rfl

/-- Under FoNums.ok h, if 5 ≤ lm ≤ kT + 5, u < 2^d and j < 32: the bit hbitP h.v 32 at padJ h H and
rowJ h H, at (u, j), is the cell of plane h lm H at FoNums.cellRC h lm (u / 2^cK, u % 2^cK, j),
cast into K. -/
theorem hbitP_plane (h : Forest.Shape) (H : Hits) (hok : FoNums.ok h = true) {lm : ℕ}
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) {u j : ℕ} (hu : u < 2 ^ h.d) (hj : j < 32) :
    (hbitP h.v 32 (padJ h H) (rowJ h H) u j : K) =
      (plane h lm H (FoNums.cellRC h lm (u / 2 ^ h.cK, u % 2 ^ h.cK, j)).1
        (FoNums.cellRC h lm (u / 2 ^ h.cK, u % 2 ^ h.cK, j)).2 : K) := by
  have ht : u / 2 ^ h.cK < 2 ^ h.kT := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, Nat.add_comm]
    exact hu
  rw [hbitP_joint h H hok u j, plane_cellRC h lm H h5 hlm ht hj]
  split_ifs <;> simp

/-- Under FoNums.ok h and Fits h T Kv H, if 5 ≤ lm ≤ kT + 5: the cells of plane h lm H in the rows
below 2^lm and the columns below h.NC * 2^(kT + 5 - lm), each weighted by 2^(r % 32), and h.padding
add up to 2^v. -/
theorem sum_plane_all (h : Forest.Shape) (T Kv : ℕ → ℕ → K) (H : Hits)
    (hok : FoNums.ok h = true) (hF : Fits h T Kv H) {lm : ℕ} (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) :
    ∑ col ∈ range (h.NC * 2 ^ (h.kT + 5 - lm)), ∑ r ∈ range (2 ^ lm),
        2 ^ (r % 32) * plane h lm H r col + h.padding = 2 ^ h.v := by
  rw [sum_plane h lm H hok h5 hlm]
  exact sum_count h T Kv H hok hF

variable [DecidableEq K]

/-- Let FoNums.ok h hold; for every call c below h.NC let every place of kv c hold the value of a
row below 2^(k_c) of tabOf K h c, and every padding place the value of the call's padding row; let
PubFits h pad hold. Then for all θ and al MidP holds at jointKey h kv θ, jointTab h θ, FoNums.pads h
and the bits hbitP at padJ and rowJ of hitsOf h (tabOf K h) kv pad. -/
theorem midP_joint (h : Forest.Shape) (kv : ℕ → ℕ → K) (pad : ℕ → ℕ → Bool)
    (hok : FoNums.ok h = true)
    (hin : ∀ c < h.NC, InTable (FoNums.nOf h c) (FoNums.kOf h c) (kv c) (tabOf K h c))
    (hpad : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, pad c i = true →
      kv c i = tabOf K h c (FoNums.t0Of h c))
    (hpub : PubFits h pad) (θ al : K) :
    MidP h.v h.d 5 32 (Ends.jointKey h kv θ) (Ends.jointTab h θ) (FoNums.pads h)
      (hbitP h.v 32 (padJ h (hitsOf h (tabOf K h) kv pad))
        (rowJ h (hitsOf h (tabOf K h) kv pad))) al := by
  rw [jointKey_sh hok, jointTab_sh hok]
  exact midP_port h (tabOf K h) kv _ hok
    (fits_hitsOf h (tabOf K h) kv pad hok hin hpad hpub) θ al

/-- Under the premises of midP_joint, if 5 ≤ lm ≤ kT + 5 and, for all u < 2^d and j < 32, bits u j
is the cell of plane h lm (hitsOf h (tabOf K h) kv pad) at
FoNums.cellRC h lm (u / 2^cK, u % 2^cK, j), cast into K: then for all θ and al MidP holds at
jointKey h kv θ, jointTab h θ, FoNums.pads h and bits. -/
theorem law_bits (h : Forest.Shape) (kv : ℕ → ℕ → K) (pad : ℕ → ℕ → Bool)
    (hok : FoNums.ok h = true)
    (hin : ∀ c < h.NC, InTable (FoNums.nOf h c) (FoNums.kOf h c) (kv c) (tabOf K h c))
    (hpad : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, pad c i = true →
      kv c i = tabOf K h c (FoNums.t0Of h c))
    (hpub : PubFits h pad) {lm : ℕ} (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (bits : ℕ → ℕ → K)
    (hb : ∀ u < 2 ^ h.d, ∀ j < 32, bits u j =
      (plane h lm (hitsOf h (tabOf K h) kv pad)
        (FoNums.cellRC h lm (u / 2 ^ h.cK, u % 2 ^ h.cK, j)).1
        (FoNums.cellRC h lm (u / 2 ^ h.cK, u % 2 ^ h.cK, j)).2 : K)) (θ al : K) :
    MidP h.v h.d 5 32 (Ends.jointKey h kv θ) (Ends.jointTab h θ) (FoNums.pads h) bits al :=
  Cb.Lkp.midP_congr _ _ _ _ _ _ _ _ _ _ (by norm_num)
    (fun u hu j hj => (hb u hu j (by norm_num at hj; exact hj)).trans
      (hbitP_plane h _ hok h5 hlm hu (by norm_num at hj; exact hj)).symm)
    (midP_joint h kv pad hok hin hpad hpub θ al)

end

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.jointKey_sh
#print axioms OnBytes.HonestTrace.jointTab_sh
#print axioms OnBytes.HonestTrace.hbitP_plane
#print axioms OnBytes.HonestTrace.sum_plane_all
#print axioms OnBytes.HonestTrace.midP_joint
#print axioms OnBytes.HonestTrace.law_bits
