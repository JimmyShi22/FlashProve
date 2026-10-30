-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3OutParts.lean: the kind "lookup" (K3): WHAT THE CLAIMS OF ITS RUNS "objects" AND
"planes" ARE WORTH, EACH UNDER ITS OWN PREMISES ALONE: claimsAre_of_runs
(Johnson/Top/H/K3OutWide.lean) cut where its own proof parts. Theorems with their proofs.

Why. claimsAre_of_runs asks all three runs and all four clauses of the calling kind's law K3HostLaw
at once. A calling kind need not have all: the layers (by reading; it is not shown here) have no key
forms and call no run "join": there the law on "join", its run and the clause on the keys have no
payer. Here these three are not asked.

Main names:
  `objectsAre_of_run`: the claims of "objects" are worth the rows' residues. Nothing is asked of the
    calling kind.
  `planesAre_of_run`: the claims of "planes" are worth the three claims on the planes at the
    committed cells' own combinations, under K3HostLaw's first three clauses, written out as
    premises b0, b1, pn, at the one world in which the claims are judged.
  `claimsAre_of_parts`: with a third equation, on whatever claim stands for the keys, the two give
    the middle K3ClaimsAre.

Limits. Ties: no error term. Nothing is proved of any caller. The third equation of
claimsAre_of_parts is owed by the calling kind in its own way, with its own error. Those of
Johnson/Top/H/K3OutWide.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OutWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

section
variable {S Cl K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (fork : S → Option Fork)
  (heard : S → Option Forest.Heard) (form : Cl → Aff) (lm : ℕ)

/-- **The claims of "objects".** -/
theorem objectsAre_of_run (objects : ℕ → S → Except String (List Cl × S))
    (hO : K3RunIsWorth fork heard form lm objects
      (fun _ _ g jLK rsK ν _ => (endsOf g.shape lm jLK rsK).rows.map (rowRes ν)))
    (g : Forest.Heard) (F' : Fork) (jLK : ℕ) (rsK : Rounds K)
    (hI : HeardIs ρ g F' (endsOf g.shape lm jLK rsK)) (hok : FoNums.ok g.shape = true)
    (sO : S) (clO : List Cl) (GO H : Fork) (rO : K3RanAt fork heard g F' objects sO clO GO)
    (lO : _root_.Fo.Later GO H) (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K) :
    clO.map (fun c => (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
      (endsOf g.shape lm jLK rsK).rows.map (rowRes ν) := by
  obtain ⟨FO, fO, laO, szO⟩ := rO.later
  obtain ⟨nO, sO', runO, gO⟩ := rO.ran
  obtain ⟨GO', bO, _, _, _, _, vO⟩ :=
    hO K ρ g jLK rsK F' FO nO sO sO' clO rO.heard fO hI laO hok szO runO
  obtain rfl : GO = GO' := Option.some.inj (gO.symm.trans bO)
  have wO := vO H lO ν entry
  beta_reduce at wO
  exact wO

/-- **The claims of "planes"**, under the first three clauses of the calling kind's law. -/
theorem planesAre_of_run (planes : ℕ → S → Except String (List Cl × S))
    (bit : S → ℕ → ℕ → Aff) (pin : S → ℕ → Aff)
    (hP : K3RunIsWorthAt fork heard form lm planes
      (fun s _ _ g jLK rsK ν val =>
        [claimLeaves g.shape lm jLK rsK ν fun col => val (bit s 0 col),
          claimBits g.shape lm jLK rsK ν fun col => val (bit s 1 col),
          Pin.countK g.shape lm fun col => val (pin s col)]))
    (g : Forest.Heard) (F' : Fork) (jLK : ℕ) (rsK : Rounds K)
    (hI : HeardIs ρ g F' (endsOf g.shape lm jLK rsK)) (hok : FoNums.ok g.shape = true)
    (sP : S) (clP : List Cl) (GP H : Fork) (rP : K3RanAt fork heard g F' planes sP clP GP)
    (lP : _root_.Fo.Later GP H) (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K)
    (b0 : ∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
      (bit sP 0 col).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        colsK g.shape lm (endsOf g.shape lm jLK rsK).zb0 ν col)
    (b1 : ∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
      (bit sP 1 col).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        colsK g.shape lm (endsOf g.shape lm jLK rsK).zb1 ν col)
    (pn : ∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
      (pin sP col).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = pinColK lm ν col) :
    clP.map (fun c => (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
      [claimLeaves g.shape lm jLK rsK ν (colsK g.shape lm (endsOf g.shape lm jLK rsK).zb0 ν),
        claimBits g.shape lm jLK rsK ν (colsK g.shape lm (endsOf g.shape lm jLK rsK).zb1 ν),
        countK g.shape lm (pinColK lm ν)] := by
  obtain ⟨FP, fP, laP, szP⟩ := rP.later
  obtain ⟨nP, sP', runP, gP⟩ := rP.ran
  obtain ⟨GP', bP, _, _, _, _, vP⟩ :=
    hP K ρ g jLK rsK F' FP nP sP sP' clP rP.heard fP hI laP hok szP runP
  obtain rfl : GP = GP' := Option.some.inj (gP.symm.trans bP)
  have wP := vP H lP ν entry
  beta_reduce at wP
  rw [wP, claimLeaves_congr _ _ _ _ _ _ _ fun col hc => b0 col hc,
    claimBits_congr _ _ _ _ _ _ _ fun col hc => b1 col hc,
    Cb.Fo.PlaneClaims.countK_congr _ _ _ _ fun col hc => pn col hc]

end

/-- With a third equation, on whatever claim stands for the keys, the two give the middle. -/
theorem claimsAre_of_parts {Cl K : Type} [CommRing K] {val : Cl → K} {h : FoNums.Sh}
    {lm jLK : ℕ} {rs : Rounds K} {ν : _root_.Fo.Pl → K} {kf : ℕ → K} {clO clP clJ : List Cl}
    (hO : clO.map val = (endsOf h lm jLK rs).rows.map (rowRes ν))
    (hP : clP.map val =
      [claimLeaves h lm jLK rs ν (colsK h lm (endsOf h lm jLK rs).zb0 ν),
        claimBits h lm jLK rs ν (colsK h lm (endsOf h lm jLK rs).zb1 ν),
        countK h lm (pinColK lm ν)])
    (hJ : clJ.map val = [claimJoin h lm jLK rs ν kf]) :
    K3ClaimsAre val h lm jLK rs ν kf clO clP clJ := ⟨hO, hP, hJ⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objectsAre_of_run
#print axioms VerifiableInference.OnPublicFiles.planesAre_of_run
