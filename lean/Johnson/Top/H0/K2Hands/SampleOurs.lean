-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/SampleOurs.lean: five more parts of the first chain keep an invariant on the
messages' stored sample rows (SampleChain.lean's RowsInv Q, at every Q): the smallness test's
hearing block (K8), the merging of the head's claims (K11), a link's laying, the frame's step
"opened" in its three forms, and a link's clearing. A law file; no running text imports it. Each
is one call of a law that is typed in another file, named below.

  sameRows_of_eq, keepsInv_of_st   a block that leaves the statement (Block.Leaves fun s => s.st,
                      Johnson/Desc/Sound/FoldHeard.lean) keeps the invariant.
  keepsInv_hear       K8's decision: by hear_leaves_statement (K8/LawLeaves.lean).
  keepsInv_whole, keepsRuns_whole   the kind K8, whole: its decision is that one; its three runs of
                      claims and two runs behind the batching leave the statement: by
                      whole_claims_rest, whole_after_rest (K8/LawRuns.lean).
  keepsInv_merge      K11's decision: by leavesSeven (MergeLaw/Law.lean).
  layFront_inv        a link's laying: the state stays (Walk.Law.layFront_ok).
  openAtt_inv, openLay_inv, openLayZero_inv   "opened": the statement stays (Walk.Tied's
                      OpenedLeaves, third clause).
  clearWith_smp, clearWith_inv   a link's clearing, at the function of the pending row that the
                      description hands it: where the link leaves no row the statement stays; where
                      it leaves one, one message's ledger is written and nothing else
                      (Walk.Law.clearWith_ok, pendingRowO_spec).
Limits. The blocks as supplied (under another name, guarded, joined) follow by
ChainKeeps.lean's keepsD_under | _guarded | _andThen: not typed. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.RowsGround
import Johnson.Desc.First.K8.LawLeaves
import Johnson.Desc.First.K8.LawRuns
import Johnson.Top.H0.MergeLaw.Law
import Johnson.Top.H0.Walk.FrameLaw
import Johnson.Top.H0.Walk.FrameTiedRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Keeps1
open Johnson.Desc.First.Walk (LinkPub layFront clearWith)
open VerifiableInference.Desc.First.Pend (pendingRowO)

variable {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop} {Cl : Type}

theorem sameRows_of_eq {A B : Statement} (h : B = A) : SameRows A B := h ▸ SameRows.refl A

theorem keepsInv_of_st {b : Block S Cl} (h : b.Leaves fun s : S => s.st) : KeepsInv Q b :=
  keepsInv_of_rows fun s s' rs gs hy => sameRows_of_eq (h s rs gs s' hy)

theorem keepsInv_hear (p : K8.Par) : KeepsInv Q (K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p) :=
  keepsInv_of_st (K8.hear_leaves_statement p)

theorem keepsInv_whole (p : K8.ParW) : KeepsInv Q (K8.whole p) :=
  keepsD_under (b := K8.approximateRangeProofDrawKind (Cl := VerifiableInference.Desc.Claim) K8.atS p.toPar) rfl
    (keepsInv_hear p.toPar)

theorem keepsRuns_whole (p : K8.ParW) : KeepsRuns (Inv Q) (K8.whole p) :=
  ⟨fun r hr n s y h hs =>
      rowsInv_rows (sameRows_of_eq (congrArg (·.1) (K8.whole_claims_rest p r hr n s y h))) hs,
    fun r hr s s' h hs =>
      rowsInv_rows (sameRows_of_eq (congrArg (·.1) (K8.whole_after_rest p r hr s s' h))) hs⟩

theorem keepsInv_merge (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    KeepsInv Q (Johnson.Desc.First.ForkMerge.headClaimMergeKind P) :=
  keepsInv_of_rows fun s s' rs gs hy => sameRows_of_eq (MergeLaw.leavesSeven P s rs gs s' hy).1

theorem layFront_inv {l : Nat} {s t : S} (h : layFront l s = .ok t) (hs : Inv Q s) : Inv Q t := by
  rw [(Johnson.Desc.First.Walk.Law.layFront_ok h).1]
  exact hs

theorem openAtt_inv {P : Johnson.Desc.First.Walk.AttPar} {s t : S}
    (h : Johnson.Desc.First.Walk.openAtt P s = .ok t) (hs : Inv Q s) : Inv Q t :=
  rowsInv_rows
    (sameRows_of_eq (Johnson.Desc.First.Walk.Tied.openedAttGives P s t h).2.2.1.2.2.1) hs

theorem openLay_inv {P : Johnson.Desc.First.Walk.LayPar} {s t : S}
    (h : Johnson.Desc.First.Walk.openLay P s = .ok t) (hs : Inv Q s) : Inv Q t :=
  rowsInv_rows
    (sameRows_of_eq (Johnson.Desc.First.Walk.Tied.openedLayGives P s t h).2.2.1.2.2.1) hs

theorem openLayZero_inv {P : Johnson.Desc.First.Walk.LayPar} {fvs : List Bool} {kCol : Nat}
    {s t : S} (h : Johnson.Desc.First.Walk.openLayZero P fvs kCol s = .ok t) (hs : Inv Q s) :
    Inv Q t :=
  rowsInv_rows
    (sameRows_of_eq (Johnson.Desc.First.Walk.Tied.openedZeroGives P fvs kCol s t h).2.2.1.2.2.1) hs

theorem clearWith_smp {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t) :
    SameRows s.st t.st := by
  obtain ⟨C, F, -, -, -, -, -, -, -, -, -, h0, h1⟩ := Johnson.Desc.First.Walk.Law.clearWith_ok h
  cases hv : X.fv with
  | false => exact sameRows_of_eq (h0 hv).2
  | true =>
    obtain ⟨w, r, os, -, hr, -, e⟩ := h1 hv
    obtain ⟨l, c, l', -, -, -, rfl⟩ := Johnson.Desc.First.Walk.Law.pendingRowO_spec hr
    rw [e]
    exact sameRows_modOracle s.st _ _ fun _ => ⟨rfl, rfl⟩

theorem clearWith_inv {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hs : Inv Q s) : Inv Q t := rowsInv_rows (clearWith_smp h) hs

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.keepsInv_hear
#print axioms VerifiableInference.Desc.First.K2.keepsInv_merge
#print axioms VerifiableInference.Desc.First.K2.keepsRuns_whole
#print axioms VerifiableInference.Desc.First.K2.clearWith_inv
#print axioms VerifiableInference.Desc.First.K2.openLayZero_inv
