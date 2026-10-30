-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Law/RangeOfFit.lean: every position that a round of a block drew lies in its
round's declared range, from the first test of `Block.step` alone. Statements and proofs.

The first test of `Block.step`, `roundsFit` (Johnson/Desc/Block.lean), asks at every round of the
block that each drawn position is below 2 ^ logN of the round's entry. `inRange`
(Johnson/Desc/K12/JoinGuarded.lean), which the parts of the proximity test ask in front of their own
decisions, asks the same of a part's cut. The frame deals each part a stretch of the block's rounds
with the same stretch of the rounds shown. So through `Block.step` that guard's test on the view
cannot refuse, and what the law reads off it can be read off `roundsFit`.
Main names:
  `inRange_of_fit`: `roundsFit ds rs = true` gives `inRange ds rs = true`.
  `fit_drop`: `roundsFit` holds of what lies behind the first i rounds.
  `inRange_take`: `inRange` holds of the first n rounds.
  `inRange_noDigest`: `inRange` answers the same when each round's sealed digest is removed.
  `inRange_stretch`: `roundsFit ds rs = true` gives `inRange` at every stretch: n rounds from number
    i on, as `decide` is shown them (without the digest).
  `cutS_rounds`: the first switch's cut is the stretch of two rounds from number 1 + (1 + k) on of
    the block's rounds.
  `first_half_fit`: `first_half_z` (Johnson/Desc/K12/Law/FirstRange.lean) without its premise on
    `inRange`: that premise is discharged by the theorem's own premise on `roundsFit`.
Limits: that each part's cut is such a stretch is shown here for the first switch alone
(`cutS_rounds`); for the other parts it is read off Johnson/Desc/K12/Frame.lean (take and drop in
`stagesFrom` and `andThen`), not proved. Nothing is said of the same guard's clause on the plan
(logN ≤ 32). No soundness is claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what `inRange_stretch` and
`first_half_fit` rest on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.FirstRange
import Johnson.Desc.K12.JoinGuarded

set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw

theorem inRange_of_fit : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds rs = true → inRange ds rs = true
  | [], _, _ => by simp [inRange]
  | _ :: _, [], _ => by simp [inRange]
  | d :: ds, r :: rs, h => by
    unfold roundsFit at h
    simp only [Bool.and_eq_true] at h
    have ih := inRange_of_fit ds rs h.2
    unfold inRange at ih ⊢
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
    exact ⟨h.1.1.1.2, ih⟩

theorem fit_drop : ∀ (i : ℕ) (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds rs = true → roundsFit (ds.drop i) (rs.drop i) = true
  | 0, _, _, h => by simpa using h
  | _ + 1, [], [], _ => by simp [roundsFit]
  | _ + 1, [], _ :: _, h => by simp [roundsFit] at h
  | _ + 1, _ :: _, [], h => by simp [roundsFit] at h
  | i + 1, d :: ds, r :: rs, h => by
    unfold roundsFit at h
    simp only [Bool.and_eq_true] at h
    simpa using fit_drop i ds rs h.2

theorem inRange_take : ∀ (n : ℕ) (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    inRange ds rs = true → inRange (ds.take n) (rs.take n) = true
  | 0, _, _, _ => by simp [inRange]
  | _ + 1, [], _, _ => by simp [inRange]
  | _ + 1, _ :: _, [], _ => by simp [inRange]
  | n + 1, d :: ds, r :: rs, h => by
    have ih := inRange_take n ds rs
    unfold inRange at h ih ⊢
    simp only [List.take_succ_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih h.2⟩

theorem inRange_noDigest : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    inRange ds (rs.map noDigest) = inRange ds rs
  | [], _ => by simp [inRange]
  | _ :: _, [] => by simp [inRange]
  | d :: ds, r :: rs => by
    have ih := inRange_noDigest ds rs
    unfold inRange at ih ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, ih]
    rfl

/-- **At every stretch of a block's rounds**, as `decide` is shown them. -/
theorem inRange_stretch (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView)
    (h : roundsFit ds rs = true) (i n : ℕ) :
    inRange ((ds.drop i).take n) (((rs.map noDigest).drop i).take n) = true := by
  rw [← List.map_drop, ← List.map_take, inRange_noDigest]
  exact inRange_take n _ _ (inRange_of_fit _ _ (fit_drop i ds rs h))

theorem cutS_rounds {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (k : ℕ) :
    cutS (laidS p) k = ((proximityTestKind X p : Block T Cl).rounds.drop (1 + (1 + k))).take 2 := by
  rw [H2K.Sw.k12_rounds X p hp]
  unfold cutS laidS
  rw [List.map_take, List.map_drop, List.map_drop, List.drop_drop]

/-- first_half_z without its premise on inRange. -/
theorem first_half_fit {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (F : ℕ) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn)
    (hfit : roundsFit (proximityTestKind X p : Block T Cl).rounds rs = true)
    (hcols : ((cols.take ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
        (rs.map (·.drawn))).flatMap id).length).map (fun c => (c.1, c.2.1, c.2.2.length)) ==
      (groupsOf F (proximityTestKind X p : Block T Cl).rounds (rs.map (·.drawn))).flatMap id) = true)
    (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (row : GroupRow) (L : GroupLayout)
    (D : Plain) (hs : p.nums.stages = a :: rest) (hD : gpOf p t a L = some D)
    (hok : ok (gpL p a row D) = true) (hcut : cutOk p = true) (rS rC : Fmt.RoundView)
    (hrs : (rs.drop (1 + (1 + a.k))).take 2 = [rS, rC]) :
    List.Forall₂ (fun z grp => grp.map (·.1) =
        (ownAt (logAt D.book z) (Positions.ofDraws a.C.a rC.drawn.poss)).toList) D.ts
      (grpS (laidS p) a.k (grpsS p (regroup ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
          (rs.map (·.drawn))).map (·.length))
        (cols.take ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
          (rs.map (·.drawn))).flatMap id).length)))) := by
  refine first_half_z X p hp F rs cols hfit hcols t a rest row L D hs hD hok hcut rS rC hrs ?_
  have h := inRange_take 2 _ _ (inRange_of_fit _ _ (fit_drop (1 + (1 + a.k)) _ _ hfit))
  rw [hrs, ← cutS_rounds X p hp] at h
  exact h

end H2K.First

#print axioms H2K.First.inRange_stretch
#print axioms H2K.First.first_half_fit
