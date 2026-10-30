-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3Rows.lean: THE ENTRY TESTS' ROWS 11 TO 13 (`K3Asks.digEntry`,
`readsEntry`, `headEntry`: Johnson/Desc/First/Look/K3AsksDoor.lean) SAY YES AT THE FULL SIZE: the
premises k₁, k₂, k₃ of `Fourteen.laid_of_rows` (Johnson/AtFull/ProofRows/Join14.lean) FROM
EQUATIONS «what the public part holds, narrowed, is the written value» AND ONE FACT ON THE OUTPUT
HEAD's PUBLIC TABLES. Five theorems: joinings of Johnson/AtFull/ProofRows/K3Views.lean,
K3Full.lean, K3DigFull.lean and K3HeadRow.lean.
  `sent_full`: what the tests read beside the public parameters is the written value: from the
    first chain's codes, shape and layout and the built segments' views.
  `attLinks_full`: the attention segments' numbers, from p4 and NGr.
  `digEntry_full` (k₁), `readsEntry_full` (k₂), `headEntry_full` (k₃).
WHAT THEY READ OF THE PUBLIC PARAMETERS X := Zp.p.X: p4, NGr, P.frame, hS (eleven numbers), and
the values of `lookAt X i true` (25), `lookAt X i false` (the twelve attention segments and the
head's) and `tlAt X i` (25), each narrowed. No spelled-out X stands anywhere.
Limits. ALL ARE HYPOTHESES: the equations are owed by whoever holds the public parameters at the
full size; hOk (the kind's own test on a call says yes at the head's six calls: it reads three
tables of 65,536 rows whole) by the same or by a law on the tables' maker. WHAT RUNS HAVE SEEN AT
`VerifierAndGoals.storedPublicFiles` (evaluations, no theorem): the three rows by name: true, a bend each: false; every
written value held against the planner's own, field by field of the narrowed terms (every field
that a narrowing keeps, but f9, which hV lays empty on both sides): true at 25 of 25, 12 of 12 and
at the head, a bend each: false; hOk: true. No soundness is claimed.

-/
import Johnson.AtFull.ProofRows.K3DigFull
import Johnson.AtFull.ProofRows.K3HeadRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofRows.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K3Asks
open VerifiableInference.Desc.First.Look (Place P lookAt tlAt callOk)
open Johnson.AtFull.Made (viewFull)

/-- **What the tests read beside the public parameters is the written value.** -/
theorem sent_full {Zp : ProofFile.Pub} (p₁ : Zp.first.codes = Johnson.G.proofCodesWritten)
    (p₂ : Zp.first.shape = VerifiableInference.Desc.ReqLit.shapeFull)
    (p₃ : Zp.first.layout = Johnson.G.layoutFull)
    (hv : Zp.p.built.links.toList.map Johnson.AtFull.Made.viewOf = viewFull) :
    sentOf Zp = sentFull := by
  have e : Zp.p.built.links.map (·.arrayOf) = (viewFull.map (·.2.2.2)).toArray := by
    rw [← hv, List.map_map, ← Array.toList_map, Array.toArray_toList]
    rfl
  unfold sentOf sentFull
  rw [p₁, p₂, p₃, e]

/-- The attention segments' numbers. -/
theorem attLinks_full {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) :
    attLinks X = attFull := by
  unfold attLinks
  rw [h4, hN]
  decide

/-- **k₁.** -/
theorem digEntry_full {Zp : ProofFile.Pub} (h4 : Zp.p.X.p4 = true) (hN : Zp.p.X.NGr = 12)
    (hF : Zp.p.X.P.frame = Params.recordLines) (hD : sentOf Zp = sentFull)
    (hV : ∀ i < 25, ∃ x tl, lookAt Zp.p.X i true = some x ∧ tlAt Zp.p.X i = some tl ∧
      narrowP x = pFull i ∧ narrowT { tl with f9 := {} } = tFull i) : digEntry Zp = true := by
  unfold digEntry
  rw [hD]
  refine digRow_of (n := 25) (by unfold linksOf; rw [h4, hN]; rfl) fun i hi => ?_
  obtain ⟨x, tl, hx, ht, e1, e2⟩ := hV i hi
  refine ⟨x, tl, hx, ht, ?_⟩
  rw [hF]
  have h0 := dig_full i hi
  rw [← e1, ← e2, digOne_narrow] at h0
  exact h0

/-- **k₂.** -/
theorem readsEntry_full {Zp : ProofFile.Pub} (h4 : Zp.p.X.p4 = true) (hN : Zp.p.X.NGr = 12)
    (hD : sentOf Zp = sentFull)
    (hV : ∀ i ∈ attFull, ∃ x tl, lookAt Zp.p.X i false = some x ∧ tlAt Zp.p.X i = some tl ∧
      narrowC x = cFull i ∧ narrowM tl = mFull) : readsEntry Zp = true := by
  unfold readsEntry
  rw [hD]
  refine readsRow_of fun i hi => ?_
  rw [attLinks_full h4 hN] at hi
  obtain ⟨x, tl, hx, ht, e1, e2⟩ := hV i hi
  refine ⟨x, tl, hx, ht, ?_⟩
  have h0 := List.all_eq_true.1 reads_full i hi
  rw [← e1, ← e2, readsB_narrow] at h0
  exact h0

/-- **k₃.** -/
theorem headEntry_full {Zp : ProofFile.Pub} {x : Place} (h4 : Zp.p.X.p4 = true)
    (hN : Zp.p.X.NGr = 12) (hx : lookAt Zp.p.X 24 false = some x)
    (hOk : x.calls.all callOk = true) (hc : x.calls.map strip = callsHead) (hl : x.lid = 28)
    (hp : x.pub = pubHead) (hS : narrowH Zp.p.X.hS = hsFull) : headEntry Zp = true :=
  headRow_full h4 hN hx hOk hc hl hp hS

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.sent_full
#print axioms Johnson.AtFull.ProofRows.K3.attLinks_full
#print axioms Johnson.AtFull.ProofRows.K3.digEntry_full
#print axioms Johnson.AtFull.ProofRows.K3.readsEntry_full
#print axioms Johnson.AtFull.ProofRows.K3.headEntry_full
