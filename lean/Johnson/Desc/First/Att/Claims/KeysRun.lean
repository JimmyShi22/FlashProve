-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/KeysRun.lean: kind K5: from the kind's own runs to the rule values of
the key forms' named scalars: at a record i of the kind's own over a Geo from a shape: where "first"
and "second" return and every form that they gather is worth 0 in W, every named scalar that the key
forms read and that one claim ties to a table has its rule value on the cells (cellsK S M). It does
for these scalars what Johnson/Desc/First/Att/Claims/EndsRun.lean does for the end values.

Main names:
  `PlaneIs h pc`: pc is a plane claim of the record at a visited remainder-table call.
  `UnitIsAt h k tb pc`: k is a visited softmax-table unit of the record with the tables tb and the
    plane claim pc (UnitIs of EndsRun.lean with the plane claim named).
  `in_of_runs`: where "first" returns at inOld h and the four units are the record's own: LinIn.
  `lin_of_runs`: the statement above, at h := oldOf S gL i.
Premises, all at h := oldOf S gL i: AttAt (every table of the kind's own list is true of the
matrices M in W: the smallness test is there to show it); LinPub
(Johnson/Desc/First/Att/Claims/KeysWorth.lean: public facts); that the four units of u are the
record's own; i.g = geoOf S; i.zk = gL.zk; A.NC = S.calls.size. "The indices read lie in the table"
and "the heads' features are lawful" (LinIn) are premises no more: `in_of_runs` draws them out of
the return of "first" (Johnson/Desc/First/Att/Claims/KeysIn.lean).
Not among the scalars: the two scores, the accumulator, the denominator times the output.
Used: say_iff (Say58.lean), keys_lin (KeysWorth.lean), in_planeKR, in_unitLin, in_five
(KeysIn.lean), runs_at_old (EndsRun.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.KeysWorth
import Johnson.Desc.First.Att.Claims.EndsRun

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open Cb.Pv.Att.End (ReadK)
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)
open Inst.Model.AttSeg (Calls Pub rv KSc)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K : ℕ}
  {M : Mats Kf} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {C : Calls} {p : Pub Kf}
  {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In} {l₁ l₂ : List Aff} {j : JoinsP}

/-- A plane claim of the record at a visited remainder-table call. -/
def PlaneIs (h : Attention.Heard) (pc : PlaneClaim) : Prop :=
  ∃ c q, (c, q) ∈ h.S.calls.toList.zipIdx ∧ (c.kind == Table.kr) = true ∧ pc ∈ h.planes.toList ∧
    (pc.call == q) = true

/-- A visited softmax-table unit of the record, with its tables and its plane claim. -/
def UnitIsAt (h : Attention.Heard) (k : Score) (tb : ScoreTables) (pc : PlaneClaim) : Prop :=
  ∃ c q n, (c, q) ∈ h.S.calls.toList.zipIdx ∧ (c.kind == Table.kfd) = true ∧
    (k, n) ∈ h.scores.toList.zipIdx ∧ (k.call == q) = true ∧ h.t.score[n]? = some tb ∧
    h.planes[k.claim]? = some pc

/-- **Where "first" returns, the linear claims' indices lie in their tables.** -/
theorem in_of_runs (h : Attention.Heard) {x : List Aff × JoinsP}
    (h1 : P.Runs.firstRun (inOld h) K = some x) {u : Units} {cM cD : PlaneClaim}
    (iM : PlaneIs h u.pM) (iD : PlaneIs h u.pD) (jM : UnitIsAt h u.kM u.tM cM)
    (jD : UnitIsAt h u.kD u.tD cD) : LinIn h u cM cD := by
  obtain ⟨c1, q1, a1, a2, a3, a4⟩ := iM
  obtain ⟨c2, q2, b1, b2, b3, b4⟩ := iD
  obtain ⟨c3, q3, n3, d1, d2, d3, d4, d5, d6⟩ := jM
  obtain ⟨c4, q4, n4, e1, e2, e3, e4, e5, e6⟩ := jD
  obtain ⟨f1, f2, f3, f4⟩ := in_five h h1
  obtain ⟨g1, g2⟩ := in_unitLin h h1 d1 d2 d3 d4 d5 d6
  obtain ⟨g3, g4⟩ := in_unitLin h h1 e1 e2 e3 e4 e5 e6
  exact ⟨in_planeKR h h1 a1 a2 a3 a4, in_planeKR h h1 b1 b2 b3 b4, g1, g3, g2, g4, f1, f2, f3, f4⟩

/-- **From the runs to the rule values of the named scalars that one claim ties to a table.** -/
theorem lin_of_runs (A : Plan) (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (h2 : P.Runs.secondRun i K = some l₂)
    (hZ : AllZero ρ W (l₁ ++ l₂)) (At : AttAt ρ W tl K M (oldOf S gL i) lid cf fs) {u : Units}
    {cM cD : PlaneClaim} (P : LinPub ρ tl (oldOf S gL i) u cM cD C p)
    (iM : PlaneIs (oldOf S gL i) u.pM) (iD : PlaneIs (oldOf S gL i) u.pD)
    (jM : UnitIsAt (oldOf S gL i) u.kM u.tM cM) (jD : UnitIsAt (oldOf S gL i) u.kD u.tD cD) :
    ∀ k, ReadK (L5.dimOf S) k → Linear k →
      slotVal W (oldOf S gL i) u k = rv (L5.dimOf S) C p (cellsK S M) k := by
  have Sy := (say_iff Kf ρ W A S gL i K l₁ l₂ j hg hz hN h1 h2).1 hZ
  have I := in_of_runs (oldOf S gL i) (runs_at_old hg hz h1 h2).1 iM iD jM jD
  obtain ⟨c1, q1, a1, a2, a3, a4⟩ := iM
  obtain ⟨c2, q2, b1, b2, b3, b4⟩ := iD
  obtain ⟨c3, q3, n3, d1, d2, d3, d4, d5, d6⟩ := jM
  obtain ⟨c4, q4, n4, e1, e2, e3, e4, e5, e6⟩ := jD
  exact keys_lin At P I (Sy.s3 (c1, q1) a1 a2 u.pM a3 a4) (Sy.s3 (c2, q2) b1 b2 u.pD b3 b4)
    (Sy.s4 (c3, q3) d1 d2 (u.kM, n3) d3 d4 u.tM cM d5 d6)
    (Sy.s4 (c4, q4) e1 e2 (u.kD, n4) e3 e4 u.tD cD e5 e6) Sy.s5

end K5Law

#print axioms K5Law.in_of_runs
#print axioms K5Law.lin_of_runs
