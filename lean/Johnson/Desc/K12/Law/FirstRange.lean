-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Law/FirstRange.lean: the one bound of the first half of GroupsAre (every position
that the first switch's second round drew lies in the stage's range) from the yes of the test
inRange of Johnson/Desc/K12/JoinGuarded.lean.

The term of inRange cut rs is written out here, so that this file does not import JoinGuarded.lean:
"inRange cut rs = true" is that term by unfolding. Statements and proofs.
Main names:
  `range_of_z`: that test's yes at two rounds: the second round's draws lie below 2 ^ its declared
    logN.
  `first_half_z`: first_half_paid (Johnson/Desc/K12/Law/FirstCutLaw.lean) with its last premise
    discharged by that yes at the first switch's cut and cutOk's clause cs.range, used here.
Limits: No soundness is claimed, and nothing is said on hiding.
Every theorem of this file is proved outright.

-/
import Johnson.Desc.K12.Law.FirstCutLaw

set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw

theorem range_of_z (dS dC : Fmt.DeclaredRound) (rS rC : Fmt.RoundView)
    (h : (([dS, dC].zip [rS, rC]).all fun x =>
      x.2.drawn.poss.all fun y => decide (y < 2 ^ x.1.entry.logN)) = true) :
    ∀ x ∈ rC.drawn.poss, x < 2 ^ dC.entry.logN := by
  simp only [List.zip_cons_cons, List.zip_nil_right, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem first_half_z {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (F : ℕ) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn)
    (hfit : roundsFit (proximityTestKind X p : Block T Cl).rounds rs = true)
    (hcols : ((cols.take ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
        (rs.map (·.drawn))).flatMap id).length).map (fun c => (c.1, c.2.1, c.2.2.length)) ==
      (groupsOf F (proximityTestKind X p : Block T Cl).rounds (rs.map (·.drawn))).flatMap id) = true)
    (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (row : GroupRow) (L : GroupLayout)
    (D : Plain) (hs : p.nums.stages = a :: rest) (hD : gpOf p t a L = some D)
    (hok : ok (gpL p a row D) = true) (hcut : cutOk p = true) (rS rC : Fmt.RoundView)
    (hrs : (rs.drop (1 + (1 + a.k))).take 2 = [rS, rC])
    (hz : (((cutS (laidS p) a.k).zip [rS, rC]).all fun x =>
      x.2.drawn.poss.all fun y => decide (y < 2 ^ x.1.entry.logN)) = true) :
    List.Forall₂ (fun z grp => grp.map (·.1) =
        (ownAt (logAt D.book z) (Positions.ofDraws a.C.a rC.drawn.poss)).toList) D.ts
      (grpS (laidS p) a.k (grpsS p (regroup ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
          (rs.map (·.drawn))).map (·.length))
        (cols.take ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
          (rs.map (·.drawn))).flatMap id).length)))) := by
  obtain ⟨dS, dC, c1, _, _, _, c5, _⟩ := cut_of_ok p a rest hs hcut
  rw [c1] at hz
  exact first_half_paid X p hp F rs cols hfit hcols t a rest row L D hs hD hok hcut rS rC hrs
    (by rw [← c5]; exact range_of_z dS dC rS rC hz)

end H2K.First
