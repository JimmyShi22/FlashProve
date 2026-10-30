-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/MeetsBehind.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: THE FIRST HALVES OF WHAT THE CLAIMS SAY
(Johnson/Desc/K5/Honest/Law/SayOf.lean), AT A PLAN AND THE STATE BEHIND THE LAY OF THESE ROUNDS. One
statement with its proof: it lays Johnson/Desc/K5/Honest/Law/MeetsRuns.lean and Law/PtsFitOf.lean at
what the claims' reading returns there, by the tree's `inOf_behind`
(Johnson/Desc/First/Att/K05FormsMade.lean).

Main name:
  `meets_behind`     all six first halves

IT IS CONDITIONAL. The premises, and who is meant to show each:
  the claims' reading and the runs "first" and "second" return behind the lay; the claims' key
    points are those of what the lookup returned; six numbers of the shape are not 0: the caller's.
  `AttAt`: that every table of the list is true of the matrices in the world: whoever lays the
    world.
  `CellsAre`: whoever lays the matrices of the prover's input.
  `ChalLens` (Law/PtsFitOf.lean): whoever ties the hearing to the planner's numbers.
  hkey: the key points' lengths: the lookup's.
  "piece b is pair b" and the lists' lengths: public.
Limits. A plan in which the layers of the group have more than one shift is not reached. Nothing
here says that a premise holds at any place or run.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.MeetsRuns
import Johnson.Desc.K5.Honest.Law.PtsFitOf
import Johnson.Desc.First.Att.K05FormsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Slice (GE)
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf behind)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)
open K5Law (oldOf PosG)

/-- **All the first halves of what the claims say, at a plan A and the state behind the lay of an
attention segment's own rounds.** hd: what the verifier has heard; G: the ledger behind the hearing;
i, K: what the claims' reading returns there; g: what the lookup on the calls handed on, as the
state holds it (there is just one). CONDITIONAL on: that reading and the runs "first" and "second"
return; the claims' key points are gL's; six numbers of the shape are not 0 (public); `AttAt`;
`CellsAre`; `ChalLens`; hkey: the key point of each plane claim's call has at least the coordinates
of the claim's region; each plane claim's list and the three lists of the division have a piece for
each pair, in the pairs' order (public). -/
theorem meets_behind (A : Attention.Plan) {s : First.S} {att : First.AttOwn} {hd : P.Heard}
    {G : Fork} {i : P.Runs.In} {K : ℕ}
    (hin : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s att hd G) = some (i, K))
    {l₁ l₂ : List Aff} {j : JoinsP} (h1 : P.Runs.firstRun i K = some (l₁, j))
    (h2 : P.Runs.secondRun i K = some l₂) {gL : Forest.Heard} (hz : i.zk = gL.zk)
    (hpos : PosG (geoOf A.S)) {W : World GE} {M : Mats GE} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape}
    (At : AttAt Reading.gl W A.seam.tl K M (oldOf A.S gL i) lid cf fs) {w : K5In}
    (hc : CellsAre Reading.gl A.S M w) (Cl : ChalLens A.S hd)
    (hkey : ∀ g, att.g = some g → ∀ pc ∈ i.p.planes.toList,
      (if pc.isD = true then A.S.nD else A.S.nM) ≤ (g.zk.getD pc.call #[]).size)
    (prP : ∀ pc ∈ i.p.planes.toList, PairsAre (geoOf A.S) pc.pw ∧ pc.pw.size = A.S.NP)
    (prW : PairsAre (geoOf A.S) i.p.d.pwW) (prX : PairsAre (geoOf A.S) i.p.d.pwX)
    (prH : PairsAre (geoOf A.S) i.p.d.pwH) :
    MeetsPlanes W A.S gL i K w ∧
      (∀ k n tb, (k, n) ∈ i.p.scores.toList.zipIdx → i.t.score[n]? = some tb →
        MeetsUnit W A.S gL i K w k tb) ∧
      Meets5 W A.S gL i K w ∧ MeetsV W A.S gL i K w ∧ Meets7 W A.S gL i K w ∧
      Meets8 W A.S gL i K w := by
  obtain ⟨eg, _, _, g, l, lk, hg, _, hP, ht⟩ := P.inOf_behind hin
  have eg' : i.g = geoOf A.S := eg
  have hP' : P.pointsOf (geoOf A.S) g.zk hd l = some i.p := hP
  have ht' : P.tablesP (geoOf A.S) (K5Law.matsOf A.seam.tl.mats) A.nW lk i.p = some i.t := ht
  have F := ptsFit_of At.shape hP' ht' Cl (hkey g hg) prP prW prX prH
  exact meets_of_runs eg' hz (by rw [eg']; exact hP') (by rw [eg']; exact ht')
    (by rw [eg']; exact hpos) h1 h2 At hc F

end H2K5.Honest

#print axioms H2K5.Honest.meets_behind
