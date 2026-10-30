-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoOutAll.lean.
The lookup of a sub-proof: what its typed verifier puts out, said whole in the terms of the
byte-level verifier's end values.

This is the statement on which a caller of the lookup stands. The typed verifier of a sub-proof's
lookup (forB, the short sumcheck filled in) never refuses, and its output claim holds if and only if
five claims hold, which are written after those that the byte-level verifier and its caller add for
a lookup, each from the record of end values (Fo.endsOf) at the transcript read as plain data:

  EndsHold h lm jLK rs cEnd KF ν μ:
    1. every claim on mask entries alone holds: the tie's, the key levels', the table's levels', the
      bits' sumcheck's (Forest.objects);
    2. the row of the leaves' sumcheck holds, with leavesA times the planes at zb0 (the first of
      Forest.planeClaims);
    3. the value shown by the bits' sumcheck, less its mask's share, is the planes at zb1 (the
      second);
    4. the counts sum to the number of keys that are not padding (the third);
    5. the form of the join is 0 (Forest.join), at the caller's forms KF of the calls' key vectors
      and at the form cEnd for the end of the key side.

States:
  forOut_ends: for an out-statement x that is described by the record (the clauses of Fo.OutIs): the
    lookup's output claim at x is EndsHold: and nothing else.
  HCends, hcEnds: a closed proposition and its proof: at every lawful shape, every layout whose mask
    places and cells are given by two maps, every statement and transcript: the verifier puts out
    some x, copies the
    oracles, and for every reading of the caller's entries its output claim at x is EndsHold.
  hcEnds_entries: the premises hold together: where each call's keys are entries, the forms that
    list them meet KFok, and only the test of the shape's numbers and the bounds on lm are left.
Premises: FoNums.ok h = true; 5 ≤ lm ≤ kT + 5; in forOut_ends: the renaming ι takes the place that
is no cell to the entry none, and μ reads that entry as 0; in hcEnds: the two equations that say
that the layout is made
from the maps mk, pl; KFokAt: AT THE READING AT WHICH THE CLAIM IS SAID the caller's forms have the
values of the calls' key vectors' extensions at the record's points. KFokAt is a claim on the
reading. Where a key is an entry that the form lists (the digits) it holds of every reading; where
the caller's forms name values that were sent, it is what the caller's later rounds are to show.
By: Fo.hcOut1E (the out-statement in the record's fields), Fo.forOut_iff (clauses 1 to 3),
Cb.Fo.Pin.rowNum_iff (clause 4), Fo.join_ends (clause 5).
Does not say: that the forms of the record (Heard.rows) and those which Forest.planeClaims and
Forest.join make have these values: that is claims_port
(OnBytes/Tie/Pv/Lookup/Forest/FoClaimsMeet.lean), at the values of the caller's forms. Nor that any
routine adds these forms to the sub-proof's equation.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoOutIff
import OnBytes.Tie.Pv.Lookup.Forest.FoPin
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinOut

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq
    Cb.Fo.Pin Finset

/-- The claims that the byte-level verifier and its caller add for one lookup, from the record of
end values. ν: the reading of the lookup's places; KF, μ: the caller's forms and the reading of the
caller's entries; cEnd: the form for the key side's end, on these entries. -/
def EndsHold {K P : Type} [CommRing K] (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K)
    (cEnd : AffK P K) (KF : ℕ → AffK P K)
    (ν : Pl → K) (μ : P → K) : Prop :=
  (∀ r ∈ (endsOf h lm jLK rs).rows, SRowHolds r ν) ∧
  (valS (hide (forN h lm jLK rs).ledE (dgE (forN h lm jLK rs)) (endsOf h lm jLK rs).lvXs) ν +
      (endsOf h lm jLK rs).lvEps * valS (endsOf h lm jLK rs).lvInc ν +
      (endsOf h lm jLK rs).lvEps * (leavesAK h (endsOf h lm jLK rs).theta (endsOf h lm jLK rs).alpha
          (endsOf h lm jLK rs).zb0 *
        planesK h lm (endsOf h lm jLK rs).zb0 (colsK h lm (endsOf h lm jLK rs).zb0 ν)) =
    (endsOf h lm jLK rs).lvFin - (endsOf h lm jLK rs).lvEps) ∧
  (((forTrace h lm jLK rs).bits.v 0 - (forTrace h lm jLK rs).bits.be *
      ν ((forN h lm jLK rs).ledB.sh 0)) -
      planesK h lm (endsOf h lm jLK rs).zb1 (colsK h lm (endsOf h lm jLK rs).zb1 ν) = 0) ∧
  countK h lm (pinColK lm ν) = 0 ∧
  AffK.val (joinK h (endsOf h lm jLK rs).theta (endsOf h lm jLK rs).alpha
      (eK h (endsOf h lm jLK rs).zy)
    (endsOf h lm jLK rs).zy KF cEnd) μ = 0

section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- The output claim at an out-statement that the record describes. -/
theorem forOut_ends (h : FoNums.Sh) (H : FoNums.ok h = true) (L : Lay E St₀ J₀) (lm jLK : ℕ)
    (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) (ι : Pl → Option J₀) (hι : ι .zero = none) (rs : Rounds E) (st : St₀)
    (x : TX (St₀ × E) E (Option J₀))
    (h1 : x.1 = (st, (endsOf h lm jLK rs).theta))
    (h3 : x.2.2 = (((endsOf h lm jLK rs).tieRows.reverse ++ ((endsOf h lm jLK rs).keyRows.reverse ++
        (((endsOf h lm jLK rs).tabRows.reverse ++
          [rowEnd (forN h lm jLK rs) (forTrace h lm jLK rs), (endsOf h lm jLK rs).bitU,
            rowBitE (forN h lm jLK rs) (forTrace h lm jLK rs)]) ++
          [rowNum (forN h lm jLK rs)]))).map (rowMap ι)).map toRow)
    (h4 : ∀ X < 2 ^ (FoNums.v' h + 1), Blocks.eqN (FoNums.v' h + 1) 0 x.2.1.pt X =
      TwV.eqN ((endsOf h lm jLK rs).zy.reverse ++ (endsOf h lm jLK rs).zx.reverse) X)
    (h5' : ∀ j, x.2.1.mf j = dense (mapL ι (endsOf h lm jLK rs).cEndF) j)
    (h6 : x.2.1.tg = (endsOf h lm jLK rs).alpha - (endsOf h lm jLK rs).cEndC)
    (KF : ℕ → AffK (Option J₀) E) (μ : Option J₀ → E)
    (hKF : KFokAt h (forK E L st) (fun c => (endsOf h lm jLK rs).zk.getD c []) KF μ)
    (hμ : μ none = 0) :
    (forA E h L).lk.out id id x μ ↔
      EndsHold h lm jLK rs (mapL ι (endsOf h lm jLK rs).cEndF, (endsOf h lm jLK rs).cEndC) KF
          (fun p => μ (ι p)) μ := by
  have h0 : (fun p => μ (ι p)) Pl.zero = 0 := by
    show μ (ι .zero) = 0
    rw [hι]
    exact hμ
  rw [forOut_iff h H L lm jLK h5 hlm ι hι rs x h3 μ hμ]
  have hP := rowNum_iff h H lm jLK h5 hlm (thetaOf h rs) (fun p => μ (ι p)) h0
  have hJ := join_ends h H L lm jLK ι rs st x h1 h4 h5' h6 KF μ hKF
  unfold EndsHold
  exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, hP.1 d, hJ.1 e⟩, fun ⟨a, b, c, d, e⟩ =>
      ⟨a, b, c, hP.2 d, hJ.2 e⟩⟩

end

/-- What the typed verifier of a sub-proof's lookup puts out, in the byte-level verifier's terms: a
closed proposition. -/
def HCends : Prop :=
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
              EndsHold h lm jLK (forFl h L Ex τ)
                (mapL (placeOf mk pl) (endsOf h lm jLK (forFl h L Ex τ)).cEndF,
                    (endsOf h lm jLK (forFl h L Ex τ)).cEndC) KF
                (fun p => zext μ₀ (placeOf mk pl p)) (zext μ₀))

theorem hcEnds : HCends := by
  intro E _ _ St₀ J₀ _ _ h L lm jLK mk pl H h5 hlm hmk hbc Ex a τ
  obtain ⟨x, h1, h2, h3, h4, h5', h6⟩ := hcOut1E E St₀ J₀ h L lm jLK mk pl H hmk hbc Ex a τ
  exact ⟨x, h1, fun KF μ₀ hKF =>
    forOut_ends h H L lm jLK h5 hlm (placeOf mk pl) rfl
        (forFl h L Ex τ) a.1 x h2 h3 h4 h5' h6 KF (zext μ₀) hKF rfl⟩

/-- The premises hold together: at the layout made from three maps (mask places, cells, and a place
for each call's each key) the caller's forms that list the keys meet KFok, and nothing is left but
the test of the
shape's numbers and the bounds on lm. -/
theorem hcEnds_entries (E : Type) [Field E] [Fintype E] (St₀ J₀ : Type) [Fintype J₀]
    [DecidableEq J₀] (h : FoNums.Sh)
    (lm jLK : ℕ) (mk : ℕ → J₀) (pl kp : ℕ → ℕ → J₀) (H : FoNums.ok h = true) (h5 : 5 ≤ lm)
        (hlm : lm ≤ h.kT + 5)
    (Ex : ExtSpec) (a : St₀ × Ex.Str)
    (τ : Tr (forB E h (⟨fun _ μ c i => μ (kp c i), fun t c j => pl (FoNums.cellRC h lm (t, c, j)).1
      (FoNums.cellRC h lm (t, c, j)).2, fun s => mk (jLK + s)⟩ : Lay E St₀ J₀) V₀ V₀C
          (Ex := Ex)).R.shape) :
    ∃ x : TX (St₀ × E) E (Option J₀),
      (forB E h (⟨fun _ μ c i => μ (kp c i), fun t c j => pl (FoNums.cellRC h lm (t, c, j)).1
        (FoNums.cellRC h lm (t, c, j)).2, fun s => mk (jLK + s)⟩ : Lay E St₀ J₀) V₀ V₀C
            (Ex := Ex)).R.red.out a τ = some (x, a.2) ∧
      ∀ μ₀ : J₀ → E,
        ((forA E h (⟨fun _ μ c i => μ (kp c i), fun t c j => pl (FoNums.cellRC h lm (t, c, j)).1
          (FoNums.cellRC h lm (t, c, j)).2, fun s => mk (jLK + s)⟩ : Lay E St₀ J₀)).lk.out id id x
              (zext μ₀) ↔
          EndsHold h lm jLK (forFl h _ Ex τ)
            (mapL (placeOf mk pl) (endsOf h lm jLK (forFl h _ Ex τ)).cEndF,
                (endsOf h lm jLK (forFl h _ Ex τ)).cEndC)
            (KFent (fun c i => some (kp c i)) fun c =>
                (endsOf h lm jLK (forFl h _ Ex τ)).zk.getD c [])
            (fun p => zext μ₀ (placeOf mk pl p)) (zext μ₀)) := by
  obtain ⟨x, h1, h2⟩ := hcEnds E St₀ J₀ h _ lm jLK mk pl H h5 hlm (fun _ => rfl)
      (fun _ _ _ _ => rfl) Ex a τ
  exact ⟨x, h1, fun μ₀ => h2 _ μ₀ (KFent_ok h (fun c i => some (kp c i)) _ (zext μ₀))⟩

end Fo
