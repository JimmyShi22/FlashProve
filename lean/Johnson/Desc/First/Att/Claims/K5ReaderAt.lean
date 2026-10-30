-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/K5ReaderAt.lean: kind K5: THE GENERIC READER's LISTS AT A RECORD ARE THE LISTS OF A LAW THAT HOLDS THE ROAD's AND THE RUNS' RETURNS AS PREMISES: at a record in an
attention segment that holds gL, h and the ledger G, from the premises in the form of the fields left · geo · zkI · points · tables · first · second of a law's record of returns, AND
u3 : i.iU3 = A.iU3, the reader ("the reader is the run itself") gives at (2, "first") just l₁ and at (2, "second") just l₂, each with no late slot.

u3 IS NO ORNAMENT: the runs write i.iU3 into every entry that their forms name (Att/RunsP.lean: uEnt h.iU3 …), and nothing else in these premises pins it: WITHOUT IT THE LAW's i NEED NOT BE THE
SEAT's RECORD, and the law's lists need not be the reader's.

The reader stands in another file (Claims/K5Reader.lean).
NOTHING COUNTED.
Main name: readers_at. inAt_is · firstAt_is · secondAt_is stand in Claims/InAtIs.lean.
Over Claims/InAtIs.lean, Claims/K5Reader.lean (reader_first | reader_second).
PREMISES BESIDE THE FIELDS: the array of the reads is in the ledger, at the law's width (hT · hK) · every entry of the lists meets ownRow at G (ho₁ · ho₂).
IS IT EMPTY HERE? Equations under returns that are shown of nothing here. "join" is not spoken of.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.InAtIs
import Johnson.Desc.First.Att.Claims.K5Reader

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.K9 (runOfForms RunOf readerOf ownRow)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Heard Left)

variable (A : Attention.Plan) {gL : Forest.Heard} {h : Heard} {G : Fork} {l : Left} {i : P.Runs.In} {Kc : ℕ} {T : HTree}

section
variable (left : P.LeftIs (P.geoOf A.S) gL.zk h G l) (geo : i.g = P.geoOf A.S) (zkI : i.zk = gL.zk) (u3 : i.iU3 = A.iU3)
  (points : P.pointsOf i.g gL.zk h l = some i.p)
  (tables : P.tablesP i.g (matsOf A.seam.tl.mats) A.nW (P.lookOfO (P.parCOf A).geo.lmb gL) i.p = some i.t)
  (hT : G.trees[A.iU3]? = some T) (hK : T.K = Kc)
include left geo zkI u3 points tables hT hK

/-- **The reader's lists are the law's.** -/
theorem readers_at {states : ℕ → List (RunOf First.S)} (hst : states 2 = (P.runsO A).map runOfForms) {s : First.S}
    {a₀ : First.AttOwn} (hs : s.here = .att a₀) (hg : a₀.g = some gL) (h5 : a₀.heard5 = some h) (hF : a₀.F = G)
    {l₁ l₂ : List Aff} {jn : P.Runs.JoinsP} (first : P.Runs.firstRun i Kc = some (l₁, jn))
    (second : P.Runs.secondRun i Kc = some l₂) (ho₁ : ∀ f ∈ l₁, f.ents.all (ownRow G) = true)
    (ho₂ : ∀ f ∈ l₂, f.ents.all (ownRow G) = true) :
    readerOf states 2 "first" s = some { forms := l₁, late := [] } ∧
      readerOf states 2 "second" s = some { forms := l₂, late := [] } := by
  subst hF
  refine ⟨reader_first A hst hs ?_ ho₁, reader_second A hst hs ?_ ho₂⟩
  · rw [hg, h5]
    exact firstAt_is A left geo zkI u3 points tables hT hK first
  · rw [hg, h5]
    exact secondAt_is A left geo zkI u3 points tables hT hK second

end

end K5Law

#print axioms K5Law.readers_at
