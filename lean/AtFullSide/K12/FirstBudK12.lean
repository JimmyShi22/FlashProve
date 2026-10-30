-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the kind's share of the bound at the first chain, at the G of the return.
/-
AtFullSide/K12/FirstBudK12.lean: CONDITIONAL, WITH A KNOWN MEMBER.

Can the hypotheses be met together? YES, AT THE NAMED FILES (`VerifierAndGoals.NamedFiles`, Ladder.lean: by
its text the files are `VerifierAndGoals.storedPublicFiles` or `VerifierAndGoals.zGap`, two written values; so it is met at each by
rfl): `k12_bud₁_premises_met` (here): there the maker returns at the base filling, a head stands at
the return, and another house's value of the kinds' rows, `kOurs` (AtFullSide/M1/KOurs.lean), holds
the lot. THAT K IS NOT THE K OF THE STATEMENT ON ZERO KNOWLEDGE: it leaves nine lots bare. T: a
structure of data; no value is laid here. A SHARE CAN HOLD FOR NOTHING: where G's first chain holds
no list of the kind K12, or such a list has no side in the description, the ends are over nothing:
THAT THE ROW STANDS IN G WITH A SIDE IS NOT SAID HERE.

What is here. THE PREMISE bud₁ OF `k12_share_at_theGOfReturn` (AtFullSide/K12/ShareK12.lean; not
imported), TO THE LETTER OF ITS BINDER: at every list of the kind K12 in the first chain of G :=
`theGOfReturn` made h T K (E2E/TheG.lean), `BudOwed` (Johnson/M1/BudShareCore.lean): where the list
has a side in the description, the list's bud holds at each member of that side, at every due list
of challenges, of the challenges of that member's rounds and of what these ask of the trees. It is
the first clause of `KindBud` (Johnson/M1/BudGather.lean) at the kind. A SORTING OF HYPOTHESES: IT
PAYS NOTHING BEYOND WHAT THE LAWS CALLED PAY. No definition; three statements.

  `k12_bud₁_at_theG`   at G at the base, which stands at the head's description: `budOwed_at_L`
      (Johnson/M1/BudTestL.lean) at the job of the lot's row (`mem_rowsOfLot`, Sim2/KeystoneL.lean),
      the row from hK₀ (`k12_rows_at`, AtFullSide/M1/KindRowsTheG.lean).
  `k12_bud₁_at_theGOfReturn`   the same at the description that the return holds: `castSides_of`
      (E2E/TheSides.lean).
  `k12_bud₁_premises_met`   made · h · hK₀ hold together at the named files (`kOurs_named`,
      AtFullSide/M1/KOurs.lean).

THE PREMISES. THE MAKER AND THE HEAD: made (the second statement alone) · h. ON K: hK₀: the lot's
value `simulatorLot` (Sim2/SlotValueL.lean) at the matrices and Sz.ref is among K's lots. NO OTHER:
none on a run, on coins, on an input, on a relation or on a family of invariants. (K is itself a
structure that holds proofs, and the law on the rows spends two of them: that the lots' names are
apart and that each lot has the filling's sides. The gather binds the same K.) At all threads' parts
T: [by reading E2E/TheG.lean] T enters G through the parameters A and B of its lists alone, which
`BudOwed` does not read, so "at all T" is true and idle.

That the second end is the binder's text of AtFullSide/K12/ShareK12.lean is held by Lean where the
gather is called with it (AtFullSide/K12/MembershipsAtTheK.lean).

The label "NOT IN FRONT OF A LAW OVER COINS" (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's
head) is not borne: [by reading] no law called bears it, and no premise names a coin.

Every letter under "there are": in the third statement's end the return A is tied by the maker's
equation, the head h by its type at the files and A; K is no letter there: it is written out.

Limits. All limits of the files called; Johnson/M1/BudTestL.lean's own: "A run of one request". The
place of the test that closes the first chain alone; the kind's lists in the two later chains are
not spoken of. At the trace's size Sz.ref, at the plan's full size, and at the format's second hash function
alone. The bound is the lot's own `budBoth`: whether it is the bound that `Good` needs is for the
kind's pays, which is not here. The other shares at the first chain (On at a run; fits, exact and
fresh of `Good`) are not here. Nothing on completeness, soundness or hiding.
No property of the protocol is claimed.
-/
import Johnson.M1.BudTestL
import Johnson.Desc.ProofFile.Honest.K12.Sim2.KeystoneL
import AtFullSide.M1.KindRowsTheG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open VerifiableInference.Desc (KindName)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixInput baseFilling baseMaker theGAtBase)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.TheSides (KindRows castSides_of)
open AtPublicFiles.TheG (ThreadParts theGOfReturn)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- CONDITIONAL. **K12's SHARE OF bud₁ AT G AT THE BASE**: `BudOwed` at every list of the kind K12
in the first chain of G, at the head's description. From: the head at a return (h) · that the lot's
value is among K's lots (hK₀). No other premise. -/
theorem k12_bud₁_at_theG (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G)
    (hK₀ : simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots) :
    ∀ L ∈ (theGAtBase h T K).first, L.place.kind = KindName.K12 →
      Johnson.M1.BudOwed h.description L := by
  intro L hL hk
  obtain ⟨pl, -, -, hrow⟩ := mem_rowsOfLot matrixInput OnBytes.HonestTrace.Sz.ref A.Z A.G L.bare
    (AtFullSide.M1.k12_rows_at h T K hK₀ L hL hk)
  have eb : L.bud = budBoth (simulatorJobOfLot A.Z) := congrArg (fun q => q.bud) hrow
  exact budOwed_at_L h.head.toAtMg L
    (jobOfLot matrixInput OnBytes.HonestTrace.Sz.ref A.Z A.G pl)
    (numbersL_at_head h.head.toAtMg) rfl (simulatorJobOfLot A.Z) (numbersL_at_head h.head.toAtMg)
    rfl (congrArg (fun q => q.place) hrow) (congrArg (fun q => q.row) hrow)
    (fun n ds asks a => by rw [eb]; exact a)

/-- CONDITIONAL. **THE PREMISE bud₁ OF THE GATHER, TO THE LETTER OF ITS BINDER, AT THE G OF THE
RETURN.** From: that the maker returns A at the base filling (made) · the head at that return (h) ·
that the lot's value is among K's lots (hK₀). No other premise. -/
theorem k12_bud₁_at_theGOfReturn (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hK₀ : simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots) :
    ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = KindName.K12 →
      Johnson.M1.BudOwed A.F L :=
  castSides_of (atPure_at_laid h.head.laid made).2
    (Q := fun F₀ G => ∀ L ∈ G.first, L.place.kind = KindName.K12 → Johnson.M1.BudOwed F₀ L)
    (k12_bud₁_at_theG h T K hK₀)

/-- **THE THREE PREMISES HOLD TOGETHER AT THE NAMED FILES**: there the maker returns some A at the
base filling, a head stands at A, and the lot's value is among the lots of a value of
the kinds' rows, `kOurs`. That value leaves nine of the filling's lots bare: it is not the K of the
statement on zero knowledge. It does not say that a list of the kind stands in G. -/
theorem k12_bud₁_premises_met (files : VerifierAndGoals.PublicFiles) (named : VerifierAndGoals.NamedFiles files) :
    ∃ (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (h : HeadAtReturn files A),
      baseMaker files = .ok A ∧
        simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈
          (AtFullSide.M1.kOurs A h.head).lots := by
  obtain ⟨A, h, made, -⟩ := AtFullSide.M1.kOurs_named files named
  refine ⟨A, h, made, ?_⟩
  show _ ∈ AtFullSide.M1.mineOurs
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

end AtFullSide.K12

#print axioms AtFullSide.K12.k12_bud₁_at_theG
#print axioms AtFullSide.K12.k12_bud₁_at_theGOfReturn
#print axioms AtFullSide.K12.k12_bud₁_premises_met
