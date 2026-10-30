-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/EndsRun.lean: kind K5: from the kind's own runs to the library's maps:
at a record i of the kind's own over a Geo from a shape: where "first" and "second" return and every
form that they gather is worth 0 in W, the hidden values under all the end values' slots are the
library's maps on the cells (cellsK S M) at the verifier's own points.

Main names:
  `ends_of_runs`: EndsAt … scE .s8 ∧ EndsAt … vpm .s11 ∧ EndsAt … vpd .s12 ∧ the row maxima's rvM6 ∧
    the queries of .s16 ∧ rvKC ∧ rvIBP ∧ the bits' two.
  `UnitIs`, `unit_of_runs_fd`, `unit_of_runs_fm`: EndsAt … k.sc .s6d, .s6b at each visited
    softmax-table unit.
Premises, all at h := oldOf S gL i: the setting AttAt of Johnson/Road/Rows/AttRead.lean (the reading
takes numerals to numbers; the shape is the planner's; the matrices fit; every table of the kind's
own list is true of the matrices M in W: that is what the smallness test is meant to give; not shown
in this file or in what it imports); the public records ProductPub, BelowPub, OnPub, IndexPub,
BitsPub, ScorePub (lengths of points; the verifier's points are the library's, coordinate by
coordinate; "piece b is pair b"; each table lies in the list with its weights); i.g = geoOf S; i.zk
= gL.zk; A.NC = S.calls.size. That the public records hold of what pointsOf and tablesP make is not
shown in this file or in what it imports; their clauses on the tables are paid in
Johnson/Desc/First/Att/Claims/TablesAt.lean. The twins' added premises are paid here from the runs'
return (Johnson/Desc/First/Att/Claims/InRunAll.lean).
What these reach, and what not: as the head of Johnson/Desc/First/Att/Claims/EndsQ.lean says.
Used: what Johnson/Desc/First/Att/Claims/EndsAll.lean, Johnson/Desc/First/Att/Claims/InRunAll.lean
and Johnson/Desc/First/Att/Claims/Say58.lean name, and shapedG_of_hid.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.InRunAll

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)
open Inst.Model.AttSeg (Calls Pub Aext Bext rvM6 rvKC rvIBP)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K : ℕ} {M : Mats Kf}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {C : Calls} {p : Pub Kf}
  {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In} {l₁ l₂ : List Aff} {j : JoinsP}

theorem runs_at_old (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (h1 : P.Runs.firstRun i K = some (l₁, j))
    (h2 : P.Runs.secondRun i K = some l₂) :
    P.Runs.firstRun (inOld (oldOf S gL i)) K = some (l₁, j) ∧
      P.Runs.secondRun (inOld (oldOf S gL i)) K = some l₂ := by
  rw [← strip_is_old S gL i hg hz]
  exact ⟨h1, h2⟩

/-- **From the runs to the library's maps: behind the units.** -/
theorem ends_of_runs (A : Plan) (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (h2 : P.Runs.secondRun i K = some l₂)
    (hZ : AllZero ρ W (l₁ ++ l₂)) (At : AttAt ρ W tl K M (oldOf S gL i) lid cf fs)
    (pE : ProductPub ρ tl (oldOf S gL i) C p) (pV : BelowPub ρ tl (oldOf S gL i) C p)
    (pO : OnPub tl (oldOf S gL i)) (pI : IndexPub ρ tl (oldOf S gL i) p)
    (pB : BitsPub tl (oldOf S gL i)) :
    EndsAt ρ W (oldOf S gL i) M C p (oldOf S gL i).d.scE .s8 ∧
    EndsAt ρ W (oldOf S gL i) M C p (oldOf S gL i).d.vpm .s11 ∧
    EndsAt ρ W (oldOf S gL i) M C p (oldOf S gL i).d.vpd .s12 ∧
    (∀ b < S.NP, W.slot ((oldOf S gL i).x.sM6 + b) = rvM6 (L5.dimOf S) p (cellsK S M) b) ∧
    (∀ b < S.NP, W.slot ((oldOf S gL i).x.scF.sEnd + 2 * b) =
      Aext (L5.dimOf S) C p (cellsK S M) .s16 b (pt ρ (oldOf S gL i).x.scF.r)) ∧
    (∀ lam < S.Lam, W.slot ((oldOf S gL i).x.sKC + lam) =
      rvKC (L5.dimOf S) p (cellsK S M) (pt ρ (oldOf S gL i).x.scd.r) lam) ∧
    (∀ b < S.NP, ∀ k < S.cf.lt, W.slot ((oldOf S gL i).x.sIb S b k) =
      rvIBP (L5.dimOf S) (cellsK S M) (pt ρ (oldOf S gL i).x.scd.r) b k) ∧
    (∀ b < S.NP, W.slot ((oldOf S gL i).x.scH.sEnd + 2 * b) =
        Blocks.ext ((L5.dimOf S).lT + (L5.dimOf S).lg + 4)
          (bitCube 4 (L5.dimOf S) (cellsK S M) b) (pt ρ (oldOf S gL i).x.scH.r) ∧
      W.slot ((oldOf S gL i).x.scH.sEnd + (2 * b + 1)) =
        Blocks.ext ((L5.dimOf S).lT + (L5.dimOf S).lg + 4)
          (bitCube 4 (L5.dimOf S) (cellsK S M) b) (pt ρ (oldOf S gL i).x.scH.r) - 1) := by
  have Sy := (say_iff Kf ρ W A S gL i K l₁ l₂ j hg hz hN h1 h2).1 hZ
  obtain ⟨r1, r2⟩ := runs_at_old hg hz h1 h2
  have I := in_tail (oldOf S gL i) r1 r2 (shapedG_of_hid At.shape).G
  exact ⟨ends8_all At pE I Sy.s5, ends11_all At pE pV I Sy.s6, ends12_all At pE pV pO I Sy.s6,
    index_all At pI pB I Sy.s7 Sy.s8⟩

/-- What makes a softmax-table unit of the record a visited one with its tables and plane claim. -/
structure UnitIs (h : Attention.Heard) (k : Score) (tb : ScoreTables) : Prop where
  at' : ∃ c q n pc, (c, q) ∈ h.S.calls.toList.zipIdx ∧ (c.kind == Table.kfd) = true ∧
    (k, n) ∈ h.scores.toList.zipIdx ∧ (k.call == q) = true ∧ h.t.score[n]? = some tb ∧
    h.planes[k.claim]? = some pc

theorem unit_of_runs_fd (A : Plan) (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (h2 : P.Runs.secondRun i K = some l₂)
    (hZ : AllZero ρ W (l₁ ++ l₂)) (At : AttAt ρ W tl K M (oldOf S gL i) lid cf fs) {k : Score}
    {tb : ScoreTables} (U : UnitIs (oldOf S gL i) k tb) (P : ScorePub ρ tl (oldOf S gL i) C p .fd k tb) :
    EndsAt ρ W (oldOf S gL i) M C p k.sc .s6d := by
  have Sy := (say_iff Kf ρ W A S gL i K l₁ l₂ j hg hz hN h1 h2).1 hZ
  obtain ⟨r1, _⟩ := runs_at_old hg hz h1 h2
  obtain ⟨c, q, n, pc, hc, hk, hn, hq, ht, hp⟩ := U.at'
  exact unit_fd_all At P (in_unit (oldOf S gL i) r1 (shapedG_of_hid At.shape).G hc hk hn hq ht)
    (Sy.s4 (c, q) hc hk (k, n) hn hq tb pc ht hp)

theorem unit_of_runs_fm (A : Plan) (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (h2 : P.Runs.secondRun i K = some l₂)
    (hZ : AllZero ρ W (l₁ ++ l₂)) (At : AttAt ρ W tl K M (oldOf S gL i) lid cf fs) {k : Score}
    {tb : ScoreTables} (U : UnitIs (oldOf S gL i) k tb) (P : ScorePub ρ tl (oldOf S gL i) C p .fm k tb) :
    EndsAt ρ W (oldOf S gL i) M C p k.sc .s6b := by
  have Sy := (say_iff Kf ρ W A S gL i K l₁ l₂ j hg hz hN h1 h2).1 hZ
  obtain ⟨r1, _⟩ := runs_at_old hg hz h1 h2
  obtain ⟨c, q, n, pc, hc, hk, hn, hq, ht, hp⟩ := U.at'
  exact unit_fm_all At P (in_unit (oldOf S gL i) r1 (shapedG_of_hid At.shape).G hc hk hn hq ht)
    (Sy.s4 (c, q) hc hk (k, n) hn hq tb pc ht hp)

end K5Law
