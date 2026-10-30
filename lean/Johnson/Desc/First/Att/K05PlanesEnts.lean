-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05PlanesEnts.lean: kind K5: TWO PREMISES OF THE ROW K05_host_planes_door
(Johnson/Desc/First/Att/K05HostPlanesDoor.lean) PAID FROM THE LOOKUP ARGUMENT's FILES' LAWS ON ITS
RUN ON THE PLANES: hlate (LateLaid at the ledger behind the run) and hents (every entry of the
claims' forms names row 0 of the plan's array of the reads).

IS IT EMPTY HERE? NO MEMBER IS SHOWN. As reported of the two files called
(LateLaidAt.lean · PlanesRowsIn.lean): "not tried for emptiness at any real place".

Main names:
  `lateLaid_at`: LateLaid a.F (lateOf a.F G) G fs (Johnson/Desc/First/Att/K05WorthLate.lean), from
    Fo.Later a.F G and the test affInT at every form of fs, which is a clause of the table's own
    sentence formsTQ: lateLaid_affInT (Johnson/Top/H/Keep/LateLaidAt.lean),
    whose conclusion writes LateLaid's body out: one line, so that no second text drifts.
  `inOf_of_readers`: where the kind's two readers answer, the claims' seat's reading answers.
  `readers_rowsIn`: the readers' forms are RowsIn Q at Q t r := (t = A.iU3 ∧ r = 0) (readers_rows,
    Johnson/Desc/First/Att/K05ReadersRows.lean).
  `hents_of_run`: **hents**: from a yes of planesRun seat lm (readersOfO A) at sP with claims clP,
    "the leaves' start form is bare", sP.here = .att a₀ and U3At A (plannedK A) a₀.F:
    planes_rowsIn_bare (Johnson/Top/H/Keep/PlanesRowsIn.lean).
Limits. That the run stated under "planes" at the description's own link is planesRun seat lm
(readersOfO A) is shown nowhere here. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05ReadersRows
import Johnson.Desc.First.Att.K05WorthLate
import Johnson.Top.H.Keep.LateLaidAt
import Johnson.Top.H.Keep.PlanesRowsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (RowsIn Bare)
open VerifiableInference.Desc.K9 (lateOf affInT)
open VerifiableInference.Desc.Sound (lateLaid_affInT)
open VerifiableInference.Desc.K3 (planesRun)
open VerifiableInference.OnPublicFiles (planes_rowsIn_bare)

/-- **hlate, at the ledger behind the run.** -/
theorem lateLaid_at (own : List (ℕ × ℕ)) (free : Option ℕ) (a : VerifiableInference.Desc.K9.Part)
    (G : Fork) (hL : _root_.Fo.Later a.F G) (fs : List Aff)
    (h : ∀ f ∈ fs, affInT own free (lateOf a.F G) a f = true) :
    LateLaid a.F (lateOf a.F G) G fs :=
  lateLaid_affInT own free a G hL fs h

/-- Where the two readers answer, the seat's reading answers. -/
theorem inOf_of_readers {St : Type} {seat : SeatC St} {c : ParC} {s : St}
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (h : readersOfK seat c s = some r) :
    ∃ i K, inOf seat c s = some (i, K) := by
  unfold readersOfK at h
  obtain ⟨z, hz, _⟩ := Option.map_eq_some_iff.1 h
  exact ⟨z.1, z.2, hz⟩

/-- The readers' forms, in the word RowsIn (LedRowsOf.lean), in which PlanesRowsIn.lean speaks. -/
theorem readers_rowsIn (A : Attention.Plan) {sP : First.S} {a₀ : First.AttOwn}
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hs : sP.here = .att a₀)
    (hU : U3At A (plannedK A) a₀.F) (hr : readersOfO A sP = some r) :
    (∀ e col f, r.1 e col = some f → RowsIn (fun t r => t = A.iU3 ∧ r = 0) f) ∧
      ∀ col f, r.2 col = some f → RowsIn (fun t r => t = A.iU3 ∧ r = 0) f := by
  obtain ⟨i, K, hin⟩ := inOf_of_readers hr
  exact readers_rows A hs hU hr hin

/-- **hents.** -/
theorem hents_of_run {Cl : Type} (A : Attention.Plan)
    (seat : VerifiableInference.Desc.K3.Seat First.S Cl) (form : Cl → Aff)
    (hform : ∀ a, form (seat.claim a) = a) (lm : ℕ) {n : ℕ} {sP s' : First.S} {clP : List Cl}
    {g : Forest.Heard} {a₀ : First.AttOwn} (hg : seat.heard sP = some g)
    (hrun : planesRun seat lm (readersOfO A) n sP = .ok (clP, s')) (hb : Bare g.leaves.start)
    (hs : sP.here = .att a₀) (hU : U3At A (plannedK A) a₀.F) :
    ∀ f ∈ clP.map form, ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0 := by
  intro f hf y hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
  exact planes_rowsIn_bare (Q := fun t r => t = A.iU3 ∧ r = 0) seat form hform lm (readersOfO A) hg hrun
    hb (fun r hr => (readers_rowsIn A hs hU hr).1) (fun r hr => (readers_rowsIn A hs hU hr).2) c hc y hy

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.lateLaid_at
#print axioms VerifiableInference.Desc.First.Att.P.inOf_of_readers
#print axioms VerifiableInference.Desc.First.Att.P.readers_rowsIn
#print axioms VerifiableInference.Desc.First.Att.P.hents_of_run
