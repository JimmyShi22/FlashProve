-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03TermsCalls.lean: the kind "lookup" (K3): THE LEDGER's THREE TERMS AT THE CALLS (the
fields hid, small, reads of `AttOwedR`, `LayOwedR`: Johnson/Desc/Sound/MgAt/K3Owed.lean) AT THE
CLOSED CONSTANT, in the ledger's own texts, at num := `At.num Zp`, tls := `Meaning.tlAt (At.X Zp)`,
tok := fun w => `tokVOf` w.tok.

Main names:
  `k03_hid`, `k03_small`: by unfolding: the constant's H IS `hidAtSeat` at the model's owner's sizes
    and at the seats by the label (Johnson/P5J/LettersAt.lean).
  `k03_reads`: under TWO PREMISES: the scope's public core, and `PadsFree` at the seats by the label
    (no place that the 24 pairs' seats name is a pad's: Johnson/P5J/WordsAtQ.lean: it has no test
    with code): one call of `readsOne_readAt` (WordsAtQ.lean), after the lookups' authors'
    `reads_of_plan` (Johnson/Desc/Sound/MgAt/K3CallsTermsAt.lean).

Limits: `PadsFree` and the public core are premises. Nothing on soundness by itself; nothing on
hiding.


-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.Sound.MgAt.K3CallsTermsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model OnBytes.Road
open Inst.Model Inst.Model.All
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (szOf)
open _root_.Meaning (BaseSegF fLay hidAtF ReadsOne sizesOf fit_sizesOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

theorem k03_hid (h : AtMgA o Z D r Zp Np cF x) :
    ∀ w, (h.toAtMg.𝔇 h.𝔇).H.hid w =
      hidAtF (At.X Zp) (fun j => szOf (_root_.Meaning.tlAt (At.X Zp) j))
        (_root_.Meaning.seatBy (fLay (h.toAtMg.𝔇 h.𝔇).sent.layout (At.num Zp)) (At.X Zp)
          fun j => szOf (_root_.Meaning.tlAt (At.X Zp) j))
        (tokVOf w.tok)
        (fun j => readAt (h.toAtMg.𝔇 h.𝔇).cs (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms
          (h.toAtMg.𝔇 h.𝔇).N j w) :=
  fun _ => rfl

theorem k03_small (h : AtMgA o Z D r Zp Np cF x) :
    ∀ j w, (h.toAtMg.𝔇 h.𝔇).H.base j w →
      BaseSegF (fun j => szOf (_root_.Meaning.tlAt (At.X Zp) j))
        (_root_.Meaning.seatBy (fLay (h.toAtMg.𝔇 h.𝔇).sent.layout (At.num Zp)) (At.X Zp)
          fun j => szOf (_root_.Meaning.tlAt (At.X Zp) j))
        (fun j => readAt (h.toAtMg.𝔇 h.𝔇).cs (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms
          (h.toAtMg.𝔇 h.𝔇).N j w) j :=
  fun _ _ hb => hb

theorem k03_reads (h : AtMgA o Z D r Zp Np cF x) (C : Hd.PublicCore (At.X Zp).P)
    (hP : PadsFree (h.toAtMg.𝔇 h.𝔇).cs (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms
      (h.toAtMg.𝔇 h.𝔇).N (sizesOf (At.X Zp))
      (_root_.Meaning.seatBy (fLay (h.toAtMg.𝔇 h.𝔇).sent.layout (At.num Zp)) (At.X Zp)
        (sizesOf (At.X Zp))) (At.X Zp)) :
    ∀ w : Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT,
      ReadsOne (At.X Zp) (fun j => szOf (_root_.Meaning.tlAt (At.X Zp) j))
        (_root_.Meaning.seatBy (fLay (h.toAtMg.𝔇 h.𝔇).sent.layout (At.num Zp)) (At.X Zp)
          fun j => szOf (_root_.Meaning.tlAt (At.X Zp) j))
        (fun j => readAt (h.toAtMg.𝔇 h.𝔇).cs (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms
          (h.toAtMg.𝔇 h.𝔇).N j w) := fun w =>
  readsOne_readAt
    (fit_sizesOf h.toAtMg.pubOne C (fLay (h.toAtMg.𝔇 h.𝔇).sent.layout (At.num Zp))).1
    (fit_sizesOf h.toAtMg.pubOne C (fLay (h.toAtMg.𝔇 h.𝔇).sent.layout (At.num Zp))).2
    h.toAtMg.plan.hN h.toAtMg.plan.hG hP w

end P5J

#print axioms P5J.k03_hid
#print axioms P5J.k03_small
#print axioms P5J.k03_reads
