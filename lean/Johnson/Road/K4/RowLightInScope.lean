-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RowLightInScope.lean: THE LIGHT TEST ON THE PENDING ROW OF K4's SUB-PROTOCOL
(`rowLightB`, Johnson/Road/K4/PendLightDefs.lean) ACCEPTS AT ALL TWELVE GROUPS OF LAYERS AT ALL
PUBLIC FILES IN THE GOALS' SCOPE AT WHICH THE PUBLIC PART IS MADE: NO ENTRY TEST IS SPENT. A
STRENGTHENING OF `rowLight_of_head` (Johnson/Road/K4/RowLightOfHead.lean, WHICH DOES NOT TURN):
there the shape lin of the test on the committed table was the written one under row 9 of the
fourteen entry tests ("the first pin"), which comes off the head: MOVED INTO THE HEAD, NOT PAID.
HERE THAT ROW IS NOT SPENT. Statements with their proofs; nothing new is evaluated. HOW. The test
reads of lin its number of rows alone (`light_reads_rows`), and that number is
the committed table's layout's own, by the make of the built segments (`table_of_pub`: no
scope, no pin, no number), which in scope is the written shape's (`lay_in_scope`): all three
in Johnson/Desc/Sound/K11Tests/PendAllNoPin.lean. The rest is `rowLight_of_head`'s proof, line for
line: the view of the group's units (`unitsOf_view`), the laws that close it in scope, and
the kernel's fact `rowLight_written`. `rowLight_reads_rows`: the test at a group reads of lin its
  number of rows alone. **`rowLight_in_scope`**: the statement. PREMISES: the scope; the goals'
  reader's return; the plain road's public part at OnBytes.secondHashFunction. `rowLight_of_head_noPin`: so
  `rowLight_of_head`'s statement, to the letter, by a proof that spends of the head its fields
  scope, reads and laid.pub alone.
What is not claimed. That the public part is made at any files in scope. Nothing on frontB, the
other half of the row k4RowB. K04_law IS NOT PROVED. At OnBytes.secondHashFunction and the full size alone.
Nothing on soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Road.K4.RowLightOfHead
import Johnson.Desc.Sound.K11Tests.PendAllNoPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Pend
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Lay Pub Reads HPlan2 layout readsOf callsTS callsAC nclOf)
open OnBytes.Model.Verify (Public publicOf layerShape)
open OnBytes.Params (LinShape recordLines)
open OnBytes.Desc.First.K4.Total (unitsOf)
open Lk6.AtPlan (wsFull)
open VerifiableInference.PlanWritten (proofSizedFull)

/-- The test at a group reads of the shape its number of rows alone. -/
theorem rowLight_reads_rows (P : Pub) (g n : ℕ) {S S' : LinShape}
    (e : S.matrixRows = S'.matrixRows) : rowLightB P g n S = rowLightB P g n S' := by
  unfold rowLightB
  cases unitsOf P g with
  | none => rfl
  | some uis => exact LT28.K11Tests.light_reads_rows _ uis n e

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {Z : ProofFile.Pub}

/-- **THE LIGHT TEST ACCEPTS AT ALL TWELVE GROUPS, IN SCOPE: NO ENTRY TEST IS SPENT.** -/
theorem rowLight_in_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL = .ok Z) :
    ∀ g, g < 12 → ∀ hp, Z.p.X.G[g]? = some hp →
      rowLightB Z.p.X.layers g hp.NCL Z.first.lin = true := by
  intro g hg hp hG
  have hX : publicOf Pb.pol Pb.KL (some Pb.lay) = .ok Z.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public hZ
  obtain ⟨⟨hy, S, _, hrd, Zd, _, hN, _, Zw, hsL, _, _⟩, _⟩ :=
    Meaning.P34.pub34_all hS hR hX gl_numerals
  have hy' : layout (layerShape Z.p.X.P) Z.p.X.P.polCalls = .ok Z.p.X.layers.y := hy
  have hN' : LinesAre Z.p.X.layers.y := hN
  have hrd' : readsOf Z.p.X.layers.y = .ok Z.p.X.layers.rd := hrd
  have L := laySizes_of_layout hy'
  have ell : (layerShape Z.p.X.P).ll = 2 := by
    rw [← Zd.lL]
    rfl
  have eLam : Z.p.X.layers.y.Lam = 4 := by
    rw [L.Lam, ell]
    norm_num
  have eLamM : Z.p.X.layers.y.LamM = 2 := by
    rw [L.LamM, ell]
    norm_num
  have ep3 : Z.p.X.layers.y.h.p3 = true := by
    rw [L.shape]
    exact S.p3
  have eL : Z.p.X.layers.y.h.L = 48 := by
    rw [L.shape, ← hsL, Zw.L]
    rfl
  have hTS : callsTS Z.p.X.layers = some [0, 1, 2, 5] := ts_of_lines hy' S.p3 hN' hrd'
  have hW : wsLayOf wsFull true recordLines.blockLog = .ok Z.p.X.layers.wsLay :=
    LT28.K11Tests.wsLay_in_scope_O hS (ProofFile.Law.pub_public hZ)
  have hn : hp.NCL = nclOf Z.p.X.layers.y g :=
    (Riders.planG_slots _ g _ hp (Fo.Pub.public_G hX g hp hG)).2.1
  have hrows : Z.first.lin.matrixRows = proofSizedFull.batch.shape.matrixRows :=
    (LT28.K11Tests.table_of_pub hZ).1.trans (LT28.K11Tests.lay_in_scope hS hZ).1
  have hf := rowLight_written
  rw [hW] at hf
  have hg' := List.all_eq_true.1 hf _ (List.mem_map.2 ⟨g, List.mem_range.2 hg, rfl⟩)
  rw [rowLight_reads_rows _ _ _ hrows]
  unfold rowLightB
  rw [unitsOf_view _ _ hTS, callsAC_of_lines hN']
  simp only [segs_at hN']
  rw [eLam, eLamM, eL, ep3, hn]
  unfold nclOf
  rw [eLam, eLamM, ep3]
  exact hg'

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- `rowLight_of_head`'s statement, by a proof that spends no entry test. -/
theorem rowLight_of_head_noPin (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ∀ g, g < 12 → ∀ hp, Zp.p.X.G[g]? = some hp →
      rowLightB Zp.p.X.layers g hp.NCL Zp.first.lin = true :=
  rowLight_in_scope hA.scope hA.reads hA.laid.pub

end

end OnBytes.Road.K4.Pend

#print axioms OnBytes.Road.K4.Pend.rowLight_in_scope
#print axioms OnBytes.Road.K4.Pend.rowLight_of_head_noPin
#print axioms OnBytes.Road.K4.Pend.rowLight_reads_rows
