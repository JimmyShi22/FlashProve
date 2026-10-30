-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/AllFormsThereAt.lean: BESIDE Johnson/P5J/AllThereAt.lean: A SEVENTH SORT OF PUBLIC
ITEM ANSWERS THROUGH AN OPTION THAT THE LANDED TEST `dataThere` (Johnson/Desc/First/AllThere.lean)
DOES NOT WALK (a reader's find; that file's own head names it under "not covered"): formsIn AND
formsInT answer through the segment's readers, which the composed meaning makes by `K9.readersAt
𝔇.lk X (headLink X) m` (Johnson/Desc/Sound/MgAll.lean, `MgData.Rd`): where 𝔇.lk m is none the
readers answer none and the test says false at every state
(Johnson/Desc/First/Batch/ReadersAt.lean, FormsIn.lean). IT IS THERE: from the head, at every
asked item of these sorts. WHAT THIS DOES NOT SAY STANDS FIRST: AN EIGHTH OPTION LIES ONE STOREY
IN: the readers look a run up BY NAME in the link's own hearing blocks (`readerOf`,
Johnson/Desc/First/Batch/ReaderOf.lean): that each asked run is one that the link's blocks bear is
NOT shown here: evaluated alone.
  `formsSegB n`, `formsSeg_full`: BY THE KERNEL: every asked formsIn, formsInT and totalIn stands
    at a segment below 25. `forms_asked_some`: some asked item is of these sorts. `bend_formsSeg`:
    A NEGATIVE TEST: at 24 in place of 25 the test says false: the head's segment bears such
    items.
  `lk_there`: from the head: the link is there at every segment below 25 (another author's
    `sits_at`, Johnson/P5J/K09List.lean). `forms_link_there`: THE END: at every border, at every
    asked formsIn or formsInT: the link is there, and the readers are `readersOfLink` at it.
ON totalIn: it stands in the closed fact, not in the end: its test reads no reader: `totalIn
(N.group m) a.2` (Johnson/Desc/First/Batch/FormsPub.lean :46) reads the state's own open ledger
and the plan's numbers: no option off the public data [read; an outside reader reads it so too].
ON THE IDLE NAMES: an asked formsIn whose list of runs (`runsAt`) is empty is true for nothing: it
is not false: harmless here. A NINTH, OF ANOTHER SORT, NOT COVERED: a clause on public data alone
inside a test that is no option: the lookups' `k3OnOut` asks `h.calls.size == h.NC` of the place's
shape (Johnson/Desc/First/Look/K3Borders.lean): false at every state at a bad shape (a
reader's find).
Limits. The head h is a premise: a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction;
side library AtFullSide/Top/). At
OnBytes.secondHashFunction. The full size alone. No soundness is claimed.

-/
import Johnson.P5J.AllFilledAt
import Johnson.P5J.K09List

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Pub askedAt pubSets openSets pubOfItems start)

/-- An item of the runs' forms stands at a segment below n. -/
def formsSegB (n : ℕ) : Pub → Bool
  | .formsIn m _ _ => decide (m < n)
  | .formsInT m _ _ => decide (m < n)
  | .totalIn m => decide (m < n)
  | _ => true

/-- Is the item a formsIn or a formsInT? -/
def isFormsB : Pub → Bool
  | .formsIn _ _ _ => true
  | .formsInT _ _ _ => true
  | _ => false

theorem formsSeg_full :
    ((askedAt mgMore fullLinks At.ps).all fun Q => Q.all (formsSegB 25)) = true := by
  decide +kernel

/-- "Every" is not over nothing. -/
theorem forms_asked_some :
    ((askedAt mgMore fullLinks At.ps).any fun Q => Q.any isFormsB) = true := by
  decide +kernel

/-- **A negative test**: the head's segment bears such items. -/
theorem bend_formsSeg :
    ((askedAt mgMore fullLinks At.ps).all fun Q => Q.all (formsSegB 24)) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The link is there at every segment below 25.** -/
theorem lk_there (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {m : ℕ} (hm : m < 25) :
    ∃ L, h.𝔇.lk m = some L := by
  obtain ⟨L, p, Q, b₃, b₅, hs⟩ := sits_at h m hm
  exact ⟨L, hs.lk⟩

/-- **THE SEVENTH OPTION IS THERE AT EVERY ASKED ITEM THAT READS IT.** -/
theorem forms_link_there (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {k : ℕ} {q : Pub}
    (hq : q ∈ (pubSets mgMore fullLinks At.ps)[k]?.getD [] ++
      pubOfItems ((openSets fullLinks At.ps (start fullLinks))[k]?.getD []))
    {m pc : ℕ} {nm : String} (e : q = .formsIn m pc nm ∨ q = .formsInT m pc nm) :
    ∃ L, h.𝔇.lk m = some L ∧
      h.𝔇.pubD.Rd m = VerifiableInference.Desc.K9.readersOfLink
        (VerifiableInference.Desc.K9.holesAt (At.X Zp) (headLink (At.X Zp)) m L) L := by
  obtain ⟨Q, hQ, hm⟩ := asked_covers hq
  have h0 := List.all_eq_true.1 (List.all_eq_true.1 formsSeg_full Q (List.mem_of_getElem? hQ)) q hm
  have hlt : m < 25 := by
    rcases e with rfl | rfl
    · exact of_decide_eq_true h0
    · exact of_decide_eq_true h0
  obtain ⟨L, hL⟩ := lk_there h hlt
  exact ⟨L, hL, VerifiableInference.Desc.K9.readersAt_some _ _ _ m L hL⟩

end P5J

#print axioms P5J.formsSeg_full
#print axioms P5J.forms_asked_some
#print axioms P5J.bend_formsSeg
#print axioms P5J.lk_there
#print axioms P5J.forms_link_there
