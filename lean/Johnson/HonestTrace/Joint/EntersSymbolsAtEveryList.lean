-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersSymbolsAtEveryList.lean

Nothing on hiding. No property of the protocol is claimed. Two theorems.

WHERE THE SENDERS' SENTENCE STANDS AT THE BOUND 0, NOTHING ELSE IS ASKED OF THE SCRIPT. "LaysFilling" at N := 0 speaks at every list of
challenges, the empty one too; "SeatEntriesArePackedAt" at every list is "ScriptSymsRawOn". So the premise "the seats' entries read no
challenge" (EntersSymbols.lean) falls away.

* "rawOn_of_laysFilling_at_every_list": EntersSymbolsFilling.lean's end at N := 0, with P a letter.
* "rawOn_at_the_inputs_trace_at_every_list": EntersSymbolsAtTheTrace.lean's end at N := 0: THREE named premises are left: lays,
  readersReadTheTrace, planesSizes.

Limits. NONE OF THE THREE IS PAID HERE; the head h, "isValid" and "traceIs" are premises too. The
senders' sentence at the bound 0 is shown of no Script here: both theorems may hold emptily. (In the
side library it is shown of the written first Script, at every bound, under premises:
AtFullSide/HonestTrace/EntersSymbolsAtTheWrittenScript.lean.) At "Sz.ref", the full size's numbers.
-/
import Johnson.HonestTrace.Joint.EntersSymbolsAtTheTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open VerifiableInference.Desc.Sound (MsgT)
open Meaning (sizesOf)
open P5J (CellsM AtMgA TS)
open OnBytes.Maker (WholeD)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K5 (LaysFilling)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {xp : VerifiableInference.Desc.First.Look.Place}
  {Bk : ProverCoinCounts} {W₀ Rc : Type}

/-- **ScriptSymsRawOn from the senders' sentence at the bound 0.** -/
theorem rawOn_of_laysFilling_at_every_list {T : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp)
    {valid : Local W₀ Rc ProofFile.Inst T → Prop} {readers : Local W₀ Rc ProofFile.Inst T → Readers}
    (lays : ∀ link < 25, ∃ seat heard, LaysFilling h Q valid 0 readers seat heard link)
    {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst T} (isValid : valid v) {τ : Tr}
    (cellsAreTheTraces : ∀ σ μ mu, σ.Below Sz.ref.nGr → Sz.ref.mu σ μ = some mu → ∀ row column,
      (readers v).cells.cell (σ.no Sz.ref.nGr) μ.label row column =
        ((τ (σ.no Sz.ref.nGr) mu row column : ℤ) : Cb.Gl.F))
    {P : ℕ → ℕ → Prop}
    (shapes : ∀ m < 25, ∀ a < (sizesOf (P5J.At.X Zp) m).NM, P m a →
      EntryHasTheFillingsShape (P5J.At.X Zp) m a) : ScriptSymsRawOn Zp Q k v τ P :=
  fun heard => seatEntriesArePacked_of_laysFilling h lays k isValid cellsAreTheTraces shapes
    (heard := heard) (Nat.zero_le _)

/-- **The end, at the bound 0.** -/
theorem rawOn_at_the_inputs_trace_at_every_list
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp)
    {valid : Local W₀ Rc ProofFile.Inst Cells → Prop} {readers : Local W₀ Rc ProofFile.Inst Cells → Readers}
    (lays : ∀ link < 25, ∃ seat heard, LaysFilling h Q valid 0 readers seat heard link)
    (planesSizes : ∀ link < 25, ∀ number segment,
      Sz.ref.matAt link number = some (segment, planeOf segment) →
      (sizesOf (P5J.At.X Zp) link).m number = (Sz.ref.shapeNo link number).1 ∧
        (sizesOf (P5J.At.X Zp) link).k number = (Sz.ref.shapeNo link number).2)
    {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst Cells} (isValid : valid v)
    (readersReadTheTrace : (readers v).cells = v.trace) {τ : Tr}
    (traceIs : v.trace = ⟨cellOf (P5J.At.X Zp) τ⟩) :
    ScriptSymsRawOn Zp Q k v τ fun _ _ => True :=
  rawOn_of_laysFilling_at_every_list h lays isValid
    (fun σ μ mu hσ hμ row column => by
      rw [readersReadTheTrace, traceIs]
      exact cellOf_at_the_fillings_names h.scope h.reads h.pubOne τ σ μ mu hσ hμ row column)
    (fun _ hm _ ha _ => entryHasTheFillingsShape_in_scope h.scope h.reads h.pubOne planesSizes hm ha)

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.rawOn_of_laysFilling_at_every_list
#print axioms OnBytes.HonestTrace.rawOn_at_the_inputs_trace_at_every_list
