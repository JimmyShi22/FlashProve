-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumPaid.lean: CONDITIONAL.

What is here. At the squares the premise "the maker returns", and at all three product levels of the
feed-forward layers' rounds the premise "the point has as many coordinates as the level has
variables" (SumLevels.lean), are paid from the shape of the challenges heard (`OwnFits`,
Johnson/Desc/K4/Honest/Law/PtsSizes.lean) and from equations between public numbers. Statements and
proofs.

K4 is the sub-protocol of the feed-forward layers' rounds.

  `preStack_le`, `preJoin2_le`, `preJoin2_le'`   lengths of stretches of the table
  `squares_point_size`, `jobSquares_returns`   the squares
  `downFrom_size`, `ztOf_size_of_le`, `gated_point_size`, `gated2_point_size`   the gated products'
     points

Limits. THE SECOND BEST OF TWO ROADS: SumAtRun.lean beside this file has, from the public test
`k4Fits`, that each maker returns at a run and that the run's cube fits; it asks that just as many
of K4's challenges have been heard as stand in front of the part, and that what the lookup has
sampled has the lengths of that at which the test was asked; it needs none of the equations below.
Premises: K4's own challenges have the shape of the verifier's table of rounds, and so many have
been heard as stand in front of the level (written as the length of a stretch of the table); THE
PLAN's NUMBERS OF VARIABLES ARE THE SUMS THAT THE LAYOUT MAKES THEM (three equations, and two
inequalities on the batched sumcheck's number of variables): public, and shown nowhere here: the
three equations are, to the letter, the library's `Mu` (`mu_of_pub`, `mu_of_public`,
Johnson/Road/K4/DsTailLens.lean); the two inequalities are had, in the letters of the library's
sizes and under `K4Plan`, a return of the batched sumcheck's maker, that job's having its call's
shape, and a call with an end value, by `lam_room_of_fit` (Law/W/LamRoomOfFit.lean): a road from a
run; neither is called here; the lookup's point has at least lt coordinates. AT THE GATED PRODUCTS
the maker of the two tables and the nine variables (SumLevels.lean) stay premises; that a gated
product's cube fits is not drawn here. Nothing from the public test `k4Fits`.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumLevels
import Johnson.Desc.K4.Honest.Law.PtsCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.Model (orderDefault)
open OnBytes.Model.Layer (downFrom normsStart)
open OnBytes.Desc.First.K4 (masked layerRds)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes.Desc.First.K4.Honest.PtsLaw

/-! ## 1 Lengths of stretches of the table -/

/-- The second token sumcheck's rounds stand in front of the batched sumcheck. -/
theorem preStack_le (Q : K4Pub) :
    (preTerms Q).length + 1 + Q.P.y.h.lt ≤ (preStack Q).length := by
  simp only [preStack, List.length_append, masked_rows, List.length_cons, List.length_nil]
  omega

/-- The batched sumcheck's rounds stand in front of the second round named "join". -/
theorem preJoin2_le (Q : K4Pub) :
    (preStack Q).length + 1 + Q.hp.lamS ≤ (preJoin2 Q).length := by
  simp only [preJoin2, List.length_append, masked_rows]
  omega

/-- So do the second token sumcheck's. -/
theorem preJoin2_le' (Q : K4Pub) :
    (preTerms Q).length + 1 + Q.P.y.h.lt ≤ (preJoin2 Q).length :=
  Nat.le_trans (preStack_le Q) (Nat.le_trans (by omega) (preJoin2_le Q))

/-! ## 2 The squares -/

/-- The squares' point has muV coordinates. -/
theorem squares_point_size (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (preJoin Q).length < (heard.drop Q.r0).length)
    (hmu : Q.P.rd.muV = Q.P.rd.lNI + Q.P.y.lPd + Q.P.y.h.lt) :
    (normsStart Q.P.y 0 (ptsOf Q w heard).gp (ptsOf Q w heard).rhoI (ptsOf Q w heard).PV).2.size =
      Q.P.rd.muV := by
  show ((ptsOf Q w heard).rhoI ++ Array.replicate Q.P.y.lPd _ ++ (ptsOf Q w heard).PV).size = _
  rw [Array.size_append, Array.size_append, Array.size_replicate, pts_rhoI Q w heard hf hn,
    PtsLaw.pts_PV Q w heard hf (by omega), hmu]

/-- **The squares' maker returns.** -/
theorem jobSquares_returns (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (preJoin Q).length < (heard.drop Q.r0).length)
    (hmu : Q.P.rd.muV = Q.P.rd.lNI + Q.P.y.lPd + Q.P.y.h.lt) :
    ∃ j, jobSquares Q w (ptsOf Q w heard) = some j := by
  have hfit : (sqJobOf Q.P.rd.muV
      (normsStart Q.P.y 0 (ptsOf Q w heard).gp (ptsOf Q w heard).rhoI (ptsOf Q w heard).PV).2
      (squaresTab Q w (ptsOf Q w heard).gp)).cube.fits = true := by
    refine fits_of _ ?_ ?_ ?_ ?_ ?_
    · show (orderDefault Q.P.rd.muV).length = Q.P.rd.muV
      simp [orderDefault]
    · intro v hv
      show v ∈ orderDefault Q.P.rd.muV
      simpa [orderDefault] using hv
    · intro t ht
      have ht' : t ∈ [squaresTab Q w (ptsOf Q w heard).gp] := ht
      rw [List.mem_singleton] at ht'
      rw [ht']
      show (squaresTab Q w (ptsOf Q w heard).gp).size = 2 ^ Q.P.rd.muV
      simp [squaresTab]
    · intro x hx
      have hx' : x ∈ [((oneE, 0, 0) : E × ℕ × ℕ)] := hx
      rw [List.mem_singleton] at hx'
      rw [hx']
      exact ⟨by show 0 < 1; norm_num, by show 0 < 1; norm_num⟩
    · intro r hr
      have h' : Way.point (normsStart Q.P.y 0 (ptsOf Q w heard).gp (ptsOf Q w heard).rhoI
          (ptsOf Q w heard).PV).2 = Way.point r := hr
      rw [← Way.point.inj h']
      exact squares_point_size Q w heard hf hn hmu
  rw [jobSquares_eq, if_pos hfit]
  exact ⟨_, rfl⟩

/-! ## 3 The gated products' points -/

/-- The first n coordinates, reversed: n of them where there are as many. -/
theorem downFrom_size (rs : Array E) (n : ℕ) (h : n ≤ rs.size) : (downFrom rs n).size = n := by
  simp only [downFrom, Array.size_reverse, Array.size_extract]
  omega

/-- The lookup's token point has lt coordinates, where the lookup's point has as many. -/
theorem ztOf_size_of_le (Q : K4Pub) (p : Pts) (h : Q.P.y.h.lt ≤ p.fo.zx.size) :
    (ztOf Q p).size = Q.P.y.h.lt := by
  have e : OnBytes.Model.lastOf p.fo.zx Q.P.y.h.lt =
      .ok (p.fo.zx.extract (p.fo.zx.size - Q.P.y.h.lt) p.fo.zx.size) := by
    unfold OnBytes.Model.lastOf OnBytes.Model.cutLast
    rw [if_neg (by omega)]
    rfl
  unfold ztOf
  rw [e]
  show (p.fo.zx.extract (p.fo.zx.size - Q.P.y.h.lt) p.fo.zx.size).size = _
  rw [Array.size_extract]
  omega

/-- **The first gated product's point has muH coordinates.** -/
theorem gated_point_size (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn)
    (hn : (preStack Q).length + 1 + Q.hp.lamS ≤ (heard.drop Q.r0).length)
    (hzx : Q.P.y.h.lt ≤ (ptsOf Q w heard).fo.zx.size)
    (hlam : Q.P.y.h.ll + Q.P.y.lPf ≤ Q.hp.lamS)
    (hmu : Q.P.rd.muH = Q.P.y.h.ll + Q.P.y.lPf + Q.P.y.h.lt) :
    (downFrom (ptsOf Q w heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q (ptsOf Q w heard)).size =
      Q.P.rd.muH := by
  rw [Array.size_append, downFrom_size _ _ (by rw [pts_rs Q w heard hn]; exact hlam),
    ztOf_size_of_le Q _ hzx, hmu]

/-- **The second gated product's point has muH2 coordinates.** -/
theorem gated2_point_size (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (preJoin2 Q).length < (heard.drop Q.r0).length) (hlam : Q.P.y.lfe ≤ Q.hp.lamS)
    (hmu : Q.P.rd.muH2 = Q.P.y.h.ll - 1 + Q.P.y.lfe + Q.P.y.h.lt) :
    ((ptsOf Q w heard).rhoM ++ downFrom (ptsOf Q w heard).rs Q.P.y.lfe ++
      (ptsOf Q w heard).rt).size = Q.P.rd.muH2 := by
  have h1 := preJoin2_le Q
  have h2 := preJoin2_le' Q
  rw [Array.size_append, Array.size_append, pts_rhoM Q w heard hf hn,
    downFrom_size _ _ (by rw [pts_rs Q w heard (by omega)]; exact hlam),
    pts_rt Q w heard (by omega), hmu]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.preStack_le
#print axioms ProofFile.Honest.K4.preJoin2_le
#print axioms ProofFile.Honest.K4.preJoin2_le'
#print axioms ProofFile.Honest.K4.squares_point_size
#print axioms ProofFile.Honest.K4.jobSquares_returns
#print axioms ProofFile.Honest.K4.downFrom_size
#print axioms ProofFile.Honest.K4.ztOf_size_of_le
#print axioms ProofFile.Honest.K4.gated_point_size
#print axioms ProofFile.Honest.K4.gated2_point_size
