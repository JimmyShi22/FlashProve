-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersSymbolsAtTheTrace.lean

Nothing on hiding. No property of the protocol is claimed. Two theorems.

THE END OF THE PIECE: "ScriptSymsRawOn" ON ALL ENTRIES, PLANES AND CELLS, at an input whose own trace is a trace τ read by "cellOf": the
clause "messages" of "ScriptReadsTheInput" (EntersItemsOverMatrices.lean; that file is not imported
here: the fit is not guarded by Lean here; Lean guards it in
AtFullSide/HonestTrace/EntersAtTheWrittenScript.lean) at τ := theTrace X i x. Under the head h,
FROM FOUR NAMED
PREMISES:
  lays          ON THE SCRIPT: the senders' sentence "LaysFilling" at every link below 25, each at
                seats of its own (the premise of packedTraceCellsAtTheHonestTrace (not guarded by
                Lean here: its file is not imported here))
  noChallenge   ON THE SCRIPT: the entries at the layout's seats read no challenge (EntersSymbols.lean)
  readers       the frame's reader of the cells reads the input's own trace
  planesSizes   ON PUBLIC DATA: the planes' matrices have the filling's sizes (the lookups' premise of that name)
None of the four is paid here.
-/
import Johnson.HonestTrace.Joint.EntersSymbolsShapes
import Johnson.HonestTrace.CellOfAt
import Johnson.Goal.HonestTrace.FullInScope

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
  {Q : Script Bk (Local W₀ Rc ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}

/-- In scope the reader by labels returns a trace's integers, at every matrix of the filling's sizes. -/
theorem cellOf_at_the_fillings_names {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (inScope : VerifierAndGoals.InScope Z = true)
    (filesRead : VerifierAndGoals.readFiles Z = .ok pp)
    (publicPart : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) (τ : Tr) (σ : Seg)
    (μ : MatName) (mu : ℕ) (hσ : σ.Below Sz.ref.nGr) (hμ : Sz.ref.mu σ μ = some mu)
    (row column : ℕ) :
    cellOf X τ (σ.no Sz.ref.nGr) μ.label row column =
      ((τ (σ.no Sz.ref.nGr) mu row column : ℤ) : Cb.Gl.F) := by
  obtain ⟨p0, p1, p2, p3⟩ := parts_in_scope inScope filesRead publicPart
  unfold Sz.mu at hμ
  rw [if_pos hσ] at hμ
  exact cellOf_label ⟨p0, p1, p2, p3⟩ τ hσ hμ row column

/-- **THE END.** -/
theorem rawOn_at_the_inputs_trace (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp)
    {valid : Local W₀ Rc ProofFile.Inst Cells → Prop} {N : ℕ}
    {readers : Local W₀ Rc ProofFile.Inst Cells → Readers}
    (lays : ∀ link < 25, ∃ seat heard, LaysFilling h Q valid N readers seat heard link)
    (planesSizes : ∀ link < 25, ∀ number segment,
      Sz.ref.matAt link number = some (segment, planeOf segment) →
      (sizesOf (P5J.At.X Zp) link).m number = (Sz.ref.shapeNo link number).1 ∧
        (sizesOf (P5J.At.X Zp) link).k number = (Sz.ref.shapeNo link number).2)
    {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst Cells} (isValid : valid v)
    (readersReadTheTrace : (readers v).cells = v.trace)
    (noChallenge : SeatEntriesReadNoChallenge Zp Q k v fun _ _ => True) {τ : Tr}
    (traceIs : v.trace = ⟨cellOf (P5J.At.X Zp) τ⟩) :
    ScriptSymsRawOn Zp Q k v τ fun _ _ => True :=
  rawOn_of_laysFilling h lays isValid
    (fun σ μ mu hσ hμ row column => by
      rw [readersReadTheTrace, traceIs]
      exact cellOf_at_the_fillings_names h.scope h.reads h.pubOne τ σ μ mu hσ hμ row column)
    (fun _ hm _ ha _ => entryHasTheFillingsShape_in_scope h.scope h.reads h.pubOne planesSizes hm ha)
    noChallenge

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.cellOf_at_the_fillings_names
#print axioms OnBytes.HonestTrace.rawOn_at_the_inputs_trace
