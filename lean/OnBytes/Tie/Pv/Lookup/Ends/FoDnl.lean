-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoDnl.lean.
The out-claim of a sub-proof's lookup from two parts: the claims that ride to the sub-proof's last
ledger, and the claim on the keys.

The list Fo.claimsOf has the rows on mask entries, three claims on the planes of the counts, and the
claim on the calls' key vectors (Fo.claimJoin). A group of layers adds the first two kinds as claims
of its one equation and makes no claim on the keys: what it holds of that claim goes into the form
from which its batched sumcheck starts (Layer.joinStart; Fo.joinStart_seam,
OnBytes/Tie/Pv/Lookup/Ends/FoStartSeam.lean). So at that caller the last member comes from another
place than the others. This file splits the list accordingly, at the letters' meant values.

Main names:
  `nuAt mk pl μ₀`: the lookup's places read through the layout in the entries μ₀.
  `DnL h lm jLK mk pl rs μ₀`: every row on mask entries holds, and the three claims on the planes
    hold, the planes' columns being the sums over the cells themselves.
  `JoinIs h L lm jLK mk pl rs st μ₀`: Fo.claimJoin is 0 at the extensions of the calls' key vectors
    at the calls' key points.
  `dnl_carry`: Fo.OutAt, DnL and JoinIs give Fo.CarryAt at these letters.
  `dnl_iff`: under Fo.OutAt and the bounds, DnL ∧ JoinIs says no more and no less than the
    out-claim.
  `dnl_out`: so they give the lookup's out-claim at x.
  `dnl_hG`: the same in the shape of the premise hG of a sub-proof's link: for claims Dn and Todo on
    the out-statement and the messages: if Dn gives, for some plain data within the bounds, OutAt
    (at the out-statement's own first part) and DnL, and Todo then gives JoinIs at the same data,
    then Dn ∧ Todo gives the out-claim. The "for some" stands in the premise.
Under: FoNums.ok h; 5 ≤ lm ≤ h.kT + 5.
Does not say: that any sub-proof's chain claims JoinIs at its start, nor that its last ledger gives
DnL.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoCarry

set_option autoImplicit false

namespace Fo.Dnl
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq Cb.Fo.Pin
open Cb.Fo.PlaneClaims OnBytes OnBytes.Model

section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- The lookup's places, read through the layout. -/
def nuAt (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (μ₀ : J₀ → E) : _root_.Fo.Pl → E :=
  fun p => zext μ₀ (placeOf mk pl p)

/-- The claims that ride: the rows on mask entries and the three claims on the planes. -/
structure DnL (h : FoNums.Sh) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (rs : Rounds E)
    (μ₀ : J₀ → E) : Prop where
  rows : ∀ y ∈ (endsOf h lm jLK rs).rows.map (rowRes (nuAt mk pl μ₀)), y = 0
  leaves : claimLeaves h lm jLK rs (nuAt mk pl μ₀)
    (colsK h lm (endsOf h lm jLK rs).zb0 (nuAt mk pl μ₀)) = 0
  bits : claimBits h lm jLK rs (nuAt mk pl μ₀)
    (colsK h lm (endsOf h lm jLK rs).zb1 (nuAt mk pl μ₀)) = 0
  count : countK h lm (pinColK lm (nuAt mk pl μ₀)) = 0

/-- The claim on the keys, at the extensions of the calls' key vectors. -/
def JoinIs (h : FoNums.Sh) (L : Lay E St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀)
    (rs : Rounds E) (st : St₀) (μ₀ : J₀ → E) : Prop :=
  claimJoin h lm jLK rs (nuAt mk pl μ₀)
    (fun c => extL (forK E L st (zext μ₀) c) ((endsOf h lm jLK rs).zk.getD c [])) = 0

variable {h : FoNums.Sh} {L : Lay E St₀ J₀} {lm jLK : ℕ} {mk : ℕ → J₀} {pl : ℕ → ℕ → J₀}
  {rs : Rounds E} {st : St₀} {x : TX (St₀ × E) E (Option J₀)} {μ₀ : J₀ → E}

omit [Fintype E] [Fintype J₀] in
/-- **The two parts give the clauses of Fo.CarryAt, at the letters' meant values.** -/
theorem dnl_carry (hx : OutAt h lm jLK (placeOf mk pl) rs st x) (D : DnL h lm jLK mk pl rs μ₀)
    (Jn : JoinIs h L lm jLK mk pl rs st μ₀) :
    CarryAt h L lm jLK mk pl rs st x μ₀
      (colsK h lm (endsOf h lm jLK rs).zb0 fun p => zext μ₀ (placeOf mk pl p))
      (colsK h lm (endsOf h lm jLK rs).zb1 fun p => zext μ₀ (placeOf mk pl p))
      (pinColK lm fun p => zext μ₀ (placeOf mk pl p))
      (fun c => extL (forK E L st (zext μ₀) c) ((endsOf h lm jLK rs).zk.getD c [])) := by
  refine ⟨hx, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun y hy => ?_⟩
  unfold claimsOf at hy
  rcases List.mem_append.1 hy with hy | hy
  · exact D.rows y hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact D.leaves
    · exact D.bits
    · exact D.count
    · exact Jn

/-- So they give the lookup's out-claim. -/
theorem dnl_out (H : FoNums.ok h = true) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5)
    (hx : OutAt h lm jLK (placeOf mk pl) rs st x) (D : DnL h lm jLK mk pl rs μ₀)
    (Jn : JoinIs h L lm jLK mk pl rs st μ₀) : (forA E h L).lk.out id id x (zext μ₀) :=
  carry_out H h5 hlm (dnl_carry hx D Jn)

/-- No more and no less than the out-claim. -/
theorem dnl_iff (H : FoNums.ok h = true) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5)
    (hx : OutAt h lm jLK (placeOf mk pl) rs st x) :
    (DnL h lm jLK mk pl rs μ₀ ∧ JoinIs h L lm jLK mk pl rs st μ₀) ↔
      (forA E h L).lk.out id id x (zext μ₀) := by
  refine ⟨fun k => dnl_out H h5 hlm hx k.1 k.2, fun ho => ?_⟩
  have C := ((carry_iff H h5 hlm hx).2 ho).claims
  unfold claimsOf at C
  refine ⟨⟨fun y hy => C y (List.mem_append_left _ hy), ?_, ?_, ?_⟩, ?_⟩
  · exact C _ (List.mem_append_right _ List.mem_cons_self)
  · exact C _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact C _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact C _ (List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

end

section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ M : Type} [Fintype J₀] [DecidableEq J₀]

/-- **In the shape of the premise hG of a sub-proof's link.** -/
theorem dnl_hG {h : FoNums.Sh} (H : FoNums.ok h = true) (L : Lay E St₀ J₀) (msg₀ : M → J₀ → E)
    (Dn Todo : TX (St₀ × E) E (Option J₀) → M → Prop)
    (hDn : ∀ x m, Dn x m → ∃ (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (rs : Rounds E),
      5 ≤ lm ∧ lm ≤ h.kT + 5 ∧ OutAt h lm jLK (placeOf mk pl) rs x.1.1 x ∧
        DnL h lm jLK mk pl rs (msg₀ m) ∧
        (Todo x m → JoinIs h L lm jLK mk pl rs x.1.1 (msg₀ m))) :
    ∀ x m, Dn x m ∧ Todo x m → (forA E h L).lk.out id id x (zext (msg₀ m)) := by
  rintro x m ⟨hd, ht⟩
  obtain ⟨lm, jLK, mk, pl, rs, h5, hlm, hx, D, hJ⟩ := hDn x m hd
  exact dnl_out H h5 hlm hx D (hJ ht)

end

end Fo.Dnl
