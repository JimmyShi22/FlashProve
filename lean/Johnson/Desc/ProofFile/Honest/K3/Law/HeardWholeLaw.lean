-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/HeardWholeLaw.lean: where the verifier's hearing of a proof
file's lookup returns, eleven fields of the program's structure are those of `lookHeardAt`
(Honest/K3/HeardWhole.lean). So they depend on the challenges and the public shape alone, and on no
value that is sent in the lookup's rounds. Theorems.

Terms. Honest/K3/GLOSSARY.md ("hearing", "heard structure", "open part"). `OpenSame`
(HeardWhole.lean) says that two structures agree in the eleven fields.

What is shown.
  `heardWhole_of_hearV`: from `hearV` (Johnson/Desc/First/Look/Via/Rounds.lean) and `toHeard`
    (Johnson/Desc/First/Look/K3LookupGeneral.lean), the two steps of the hearing at a place.
  `heardWhole_of_hearVia`: from `hearVia` (Johnson/Desc/First/Look/Via/Via.lean), the hearing at a
    place itself.
  `heardWhole_sent`: two hearings whose rounds sampled the same challenges have the same eleven
    fields, whatever was sent.

Hypotheses that remain.
  `hv`: the hearing returns.
  `hg`: the structure is made (`toHeard` returns); in `heardWhole_of_hearVia`, instead, `hs`: the
    public parameters make the shape.
  `hd`: (in `heardWhole_sent`) the two lists of rounds sampled the same challenges. There `hv` and
    `hg` stand twice, once for each hearing: `hv₁`, `hg₁`, `hv₂`, `hg₂`.
  The list of challenges is any list that holds the samples of the lookup's own rounds from number
  base on: front ++ the rounds' samples ++ back, where base is the length of front.

How the proof goes. It rests on `pointsAgree_of_hearV` (Honest/K3/HeardLaw.lean): the points that
the hearing returns are those made of the challenges by number.

Users. Honest/K3/Law/Thread/DigitsHeardLink.lean and Honest/K3/Law/Thread/LayersTieHead.lean import
this file.

Limits. The eleven fields alone: shape, theta, alpha, leavesA, zx, zy, e, zb0, zb1, tT, zk. Nothing
is said on a, rows, leaves, sBit, cEnd and the three numbers of owed entries. `heardWhole_sent`
speaks where both hearings return.
Instances: Honest/K3/HeardWholeGuards.lean [not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.HeardWhole
import Johnson.Desc.ProofFile.Honest.K3.HeardLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E subE oneE)
open OnBytes.Model (Fork)
open OnBytes.Model.Forest (callWeight tableAt joinedTableAt)
open VerifiableInference.Desc.K3 (HeardV hearV toHeard toHeardG faceOf)

/-- **Conditional on the hearing returning and the structure being made: the structure's eleven
fields are those made of the challenges.** Instances: Honest/K3/HeardWholeGuards.lean
[not in this library] (by evaluation). -/
theorem heardWhole_of_hearV (h : OnBytes.Model.Forest.Shape) (F G : Fork) (rs : List Fmt.RoundView)
    (g : HeardV) (g' : OnBytes.Model.Forest.Heard) (front back : List Fmt.Drawn)
    (hv : hearV (faceOf h) F rs = some (g, G)) (hg : toHeard h (toHeardG g) = some g') :
    OpenSame g' (lookHeardAt h front.length (front ++ rs.map (·.drawn) ++ back)) := by
  have P := pointsAgree_of_hearV (faceOf h) h.v rfl F G rs g front back hv
  have hk : g.keys.map (·.1) =
      [(ptsOf (faceOf h) front.length (front ++ rs.map (·.drawn) ++ back)).keyPt 0 h.v] := P.keys
  obtain ⟨a, ha, hpt⟩ : ∃ a, g.keys = [a] ∧ a.1 =
      (ptsOf (faceOf h) front.length (front ++ rs.map (·.drawn) ++ back)).keyPt 0 h.v := by
    cases hq : g.keys with
    | nil => simp [hq] at hk
    | cons a l =>
      cases l with
      | nil => exact ⟨a, rfl, by simpa [hq] using hk⟩
      | cons b l' => simp [hq] at hk
  obtain ⟨pt, form⟩ := a
  simp only at hpt
  have ha' : (toHeardG g).keys = [(pt, form)] := ha
  unfold toHeard at hg
  rw [ha'] at hg
  simp only at hg
  split at hg
  · cases hg
    refine ⟨rfl, P.theta, P.alpha, ?_, ?_, ?_, ?_, P.zb0, P.zb1, ?_, ?_⟩
    · show subE (subE g.alpha oneE) (joinedTableAt h g.theta
        (h.calls.map fun k => tableAt k (g.zb0.extract (h.kT - k.k) h.kT))
        (g.zb0.extract h.kT (h.kT + h.cK))) = _
      rw [P.theta, P.alpha, P.zb0]
      rfl
    · show pt.extract 0 h.dT = _
      rw [hpt]
      rfl
    · show pt.extract h.dT pt.size = _
      rw [hpt]
      rfl
    · show (Array.range h.NC).map (callWeight h (pt.extract h.dT pt.size)) = _
      rw [hpt]
      rfl
    · show (h.calls.map fun k => tableAt k (g.zb0.extract (h.kT - k.k) h.kT)) = _
      rw [P.zb0]
      rfl
    · show ((Array.range h.NC).map fun c =>
        (pt.extract h.dT pt.size).extract (h.rK - h.iota.getD c 0) (pt.extract h.dT pt.size).size ++
          pt.extract 0 h.dT) = _
      rw [hpt]
      rfl
  · cases hg

/-- **The same from the hearing at a place itself.** Conditional on the parameters making the shape
and the hearing returning. Instances: as above. -/
theorem heardWhole_of_hearVia (p : VerifiableInference.Desc.First.Look.P)
    (h : OnBytes.Model.Forest.Shape) (hs : p.shape = some h) (F G : Fork) (rs : List Fmt.RoundView)
    (H : OnBytes.Model.Forest.Heard) (front back : List Fmt.Drawn)
    (hv : VerifiableInference.Desc.K3.Law.hearVia p F rs = some (H, G)) :
    OpenSame H (lookHeardAt h front.length (front ++ rs.map (·.drawn) ++ back)) := by
  unfold VerifiableInference.Desc.K3.Law.hearVia at hv
  rw [hs] at hv
  simp only at hv
  split at hv
  · obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.1 hv
    obtain ⟨gV, G'⟩ := x
    obtain ⟨H', hH, e⟩ := Option.map_eq_some_iff.1 h2
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, _⟩ := e
    subst e1
    exact heardWhole_of_hearV h F G' rs gV H' front back hx hH
  · exact nomatch hv

/-- **Conditional on two hearings returning, two structures being made, and the two lists of rounds
having sampled the same challenges: the two structures have the same eleven fields, whatever was
sent, and from whichever ledgers.** It speaks where both hearings return. By a reading of its text,
not shown here: the hearing rejects on shapes, counts, the sample of Y and the ledger's room, and on
no sent scalar's value. Instances: as above. -/
theorem heardWhole_sent (h : OnBytes.Model.Forest.Shape) (F₁ G₁ F₂ G₂ : Fork)
    (rs₁ rs₂ : List Fmt.RoundView) (g₁ g₂ : HeardV) (H₁ H₂ : OnBytes.Model.Forest.Heard)
    (hv₁ : hearV (faceOf h) F₁ rs₁ = some (g₁, G₁)) (hg₁ : toHeard h (toHeardG g₁) = some H₁)
    (hv₂ : hearV (faceOf h) F₂ rs₂ = some (g₂, G₂)) (hg₂ : toHeard h (toHeardG g₂) = some H₂)
    (hd : rs₁.map (·.drawn) = rs₂.map (·.drawn)) : OpenSame H₁ H₂ := by
  have A := heardWhole_of_hearV h F₁ G₁ rs₁ g₁ H₁ [] [] hv₁ hg₁
  have B := heardWhole_of_hearV h F₂ G₂ rs₂ g₂ H₂ [] [] hv₂ hg₂
  rw [hd] at A
  exact ⟨A.shape.trans B.shape.symm, A.theta.trans B.theta.symm, A.alpha.trans B.alpha.symm,
    A.leavesA.trans B.leavesA.symm, A.zx.trans B.zx.symm, A.zy.trans B.zy.symm,
    A.e.trans B.e.symm, A.zb0.trans B.zb0.symm, A.zb1.trans B.zb1.symm, A.tT.trans B.tT.symm,
    A.zk.trans B.zk.symm⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.heardWhole_of_hearV
#print axioms ProofFile.Honest.K3.Law.heardWhole_of_hearVia
#print axioms ProofFile.Honest.K3.Law.heardWhole_sent
