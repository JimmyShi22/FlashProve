-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoOutOf.lean.
The out-claim of the sub-proofs' lookup from the list of its claims, at an out-statement that is
given by its fields and not by a run.

A caller that composes the lookup with later blocks meets the out-statement x as a letter: what it
knows of x are its fields. This file says which fields are asked, that a run's out-statement has
them, and that at such an x the typed out-claim holds if and only if all values of Fo.claimsOf
are 0.

Main names:
  `OutAt h lm jLK ι rs st x`: x is the out-statement that the record of end values at the plain
    data rs describes: the state is st with the shift; the rows; the three fields of the masked
    claim on the keys. (The clauses of Fo.OutIs but the run's equation.)
  `outAt_run`: what the typed verifier puts out on a transcript τ has OutAt at τ read as plain data.
  `out_iff_claims`: at an x with OutAt: the out-claim ↔ all values of claimsOf are 0.
  `out_of_claims`: the direction from the claims to the out-claim.
Under: FoNums.ok h; 5 ≤ lm ≤ kT + 5; Fo.KFokAt at the reading at which the claim is said. In
outAt_run also the layout's two laws.
Does not say: that an out-statement met as a letter has OutAt: that is to ride in the caller's
relation or condition on statements.
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoClaims

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq Cb.Fo.Pin

section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- x is the out-statement that the record of end values at rs describes. -/
structure OutAt (h : FoNums.Sh) (lm jLK : ℕ) (ι : Pl → Option J₀) (rs : Rounds E) (st : St₀)
    (x : TX (St₀ × E) E (Option J₀)) : Prop where
  state : x.1 = (st, (endsOf h lm jLK rs).theta)
  rows : x.2.2 = (((endsOf h lm jLK rs).tieRows.reverse ++
    ((endsOf h lm jLK rs).keyRows.reverse ++ (((endsOf h lm jLK rs).tabRows.reverse ++
      [rowEnd (forN h lm jLK rs) (forTrace h lm jLK rs), (endsOf h lm jLK rs).bitU,
        rowBitE (forN h lm jLK rs) (forTrace h lm jLK rs)]) ++
      [rowNum (forN h lm jLK rs)]))).map (rowMap ι)).map toRow
  point : ∀ X < 2 ^ (FoNums.v' h + 1), Blocks.eqN (FoNums.v' h + 1) 0 x.2.1.pt X =
    TwV.eqN ((endsOf h lm jLK rs).zy.reverse ++ (endsOf h lm jLK rs).zx.reverse) X
  form : ∀ j, x.2.1.mf j = dense (mapL ι (endsOf h lm jLK rs).cEndF) j
  target : x.2.1.tg = (endsOf h lm jLK rs).alpha - (endsOf h lm jLK rs).cEndC

/-- A run's out-statement has these fields. -/
theorem outAt_run (h : FoNums.Sh) (H : FoNums.ok h = true) (L : Lay E St₀ J₀) (lm jLK : ℕ)
    (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (hmk : ∀ s, L.mkS s = mk (jLK + s))
    (hbc : ∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2)
    (Ex : ExtSpec) (a : St₀ × Ex.Str) (τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape)
    (b : TX (St₀ × E) E (Option J₀) × Ex.Str)
    (hb : (forB E h L V₀ V₀C (Ex := Ex)).R.red.out a τ = some b) :
    OutAt h lm jLK (placeOf mk pl) (forFl h L Ex τ) a.1 b.1 ∧ b.2 = a.2 := by
  obtain ⟨x, h1, h2, h3, h4, h5, h6⟩ := hcOut1E E St₀ J₀ h L lm jLK mk pl H hmk hbc Ex a τ
  obtain rfl : (x, a.2) = b := Option.some.inj (h1.symm.trans hb)
  exact ⟨⟨h2, h3, h4, h5, h6⟩, rfl⟩

/-- At such an out-statement: the out-claim holds if and only if every value of the list is 0. -/
theorem out_iff_claims (h : FoNums.Sh) (H : FoNums.ok h = true) (L : Lay E St₀ J₀) (lm jLK : ℕ)
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (rs : Rounds E) (st : St₀)
    (x : TX (St₀ × E) E (Option J₀)) (hx : OutAt h lm jLK (placeOf mk pl) rs st x)
    (KF : ℕ → AffK (Option J₀) E) (μ₀ : J₀ → E)
    (hKF : KFokAt h (forK E L st) (fun c => (endsOf h lm jLK rs).zk.getD c []) KF (zext μ₀)) :
    (forA E h L).lk.out id id x (zext μ₀) ↔
      ∀ y ∈ claimsOf h lm jLK rs (fun p => zext μ₀ (placeOf mk pl p))
        (colsK h lm (endsOf h lm jLK rs).zb0 fun p => zext μ₀ (placeOf mk pl p))
        (colsK h lm (endsOf h lm jLK rs).zb1 fun p => zext μ₀ (placeOf mk pl p))
        (pinColK lm fun p => zext μ₀ (placeOf mk pl p))
        (fun c => AffK.val (KF c) (zext μ₀)), y = 0 := by
  refine (forOut_ends h H L lm jLK h5 hlm (placeOf mk pl) rfl rs st x hx.state hx.rows hx.point
    hx.form hx.target KF (zext μ₀) hKF rfl).trans (claims_iff h lm jLK _ _ KF _ _ ?_).symm
  unfold AffK.val mapL
  simp only [List.map_map]
  rfl

/-- From the claims to the out-claim. -/
theorem out_of_claims (h : FoNums.Sh) (H : FoNums.ok h = true) (L : Lay E St₀ J₀) (lm jLK : ℕ)
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (rs : Rounds E) (st : St₀)
    (x : TX (St₀ × E) E (Option J₀)) (hx : OutAt h lm jLK (placeOf mk pl) rs st x)
    (KF : ℕ → AffK (Option J₀) E) (μ₀ : J₀ → E)
    (hKF : KFokAt h (forK E L st) (fun c => (endsOf h lm jLK rs).zk.getD c []) KF (zext μ₀))
    (h0 : ∀ y ∈ claimsOf h lm jLK rs (fun p => zext μ₀ (placeOf mk pl p))
        (colsK h lm (endsOf h lm jLK rs).zb0 fun p => zext μ₀ (placeOf mk pl p))
        (colsK h lm (endsOf h lm jLK rs).zb1 fun p => zext μ₀ (placeOf mk pl p))
        (pinColK lm fun p => zext μ₀ (placeOf mk pl p))
        (fun c => AffK.val (KF c) (zext μ₀)), y = 0) :
    (forA E h L).lk.out id id x (zext μ₀) :=
  (out_iff_claims h H L lm jLK h5 hlm mk pl rs st x hx KF μ₀ hKF).2 h0

end
end Fo
