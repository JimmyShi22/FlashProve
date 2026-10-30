-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/SampleChainS.lean: SampleChain.lean's general laws at the invariant that the
code switch's law spends: SampleGoodS (Johnson/Top/H/SwitchSeedFits.lean):
every stored sample row is the program's Send.form at a seed with enough coordinates and a factor
that is not zero and is in canonical form. A law file; no running text imports it.

  sampleGoodS_iff     SampleGoodS is RowsInv QGoodS, by definition.
  sampleGoodS_yes     a yes of the kind K2's own decision keeps it, state to state, where round 1's
                      drawn elements are in canonical form: by that file's sampleGoodS_kept.
  keepsS_k2           so the kind's block has KeepsInv QGoodS.
  goodS_start         it holds at the chain's first state.
  goodS_in_chain      where the chain's parts keep it (ChainKeeps) and the view has passed the
                      fold's test on its words: SampleGoodS at the verifier's state in front of any
                      block of the chain's flat list.
Limits: those of SampleChain.lean: that the description's first chain has ChainKeeps is not shown;
of its parts K2's kind alone is paid here. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.K2Hands.SampleChain
import Johnson.Top.H.SwitchSeedFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks viewWordsBelowPrime)
open VerifiableInference.Desc.Keeps1

theorem sampleGoodS_iff (St : Statement) : SampleGoodS St ↔ RowsInv QGoodS St := Iff.rfl

/-- **A yes of the kind's own decision keeps the invariant, state to state.** -/
theorem sampleGoodS_yes (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (s' : S) (hok : OkDrawn r₁) (h : decideWith _root_.Tw.K2.sendByL8 p s [r₁, r₂] gs = .ok s')
    (hg : SampleGoodS s.st) : SampleGoodS s'.st := by
  obtain ⟨x, y, S3, Y, rows, G, c, A⟩ := yes_whole p s r₁ r₂ gs s' h
  obtain ⟨e1, e2⟩ := front_tables A.front
  exact sampleGoodS_kept A hok (rowsInv_congr (Q := QGoodS) e1 e2 hg)

variable {Cl : Type}

theorem keepsS_k2 (p : P2) : KeepsInv QGoodS (codeSwitchKind p : Block S Cl) :=
  keepsInv_k2 p fun s r₁ r₂ gs s' hok h hg => sampleGoodS_yes p s r₁ r₂ gs s' hok h hg

theorem goodS_start {P : Par} {codes : Codes} {shape : Params.ReqShape}
    {layout : Params.ReqLayout} {T V : Nat} {req : Array UInt32} {s : S}
    (h : S.startReqP P codes shape layout T V req = some s) : SampleGoodS s.st :=
  rowsInv_startReqP (Q := QGoodS) h

/-- **In front of any block of the chain's flat list.** -/
theorem goodS_in_chain {ft : Nat} {c : Chain S Cl} (hc : ChainKeeps OkDrawn (Inv QGoodS) c)
    {pre l : List (Block S Cl)} {B : Block S Cl} (hcut : c.blocksInOrder = pre ++ B :: l) {s m : S}
    {v : Fmt.View} (hv : viewWordsBelowPrime v = true) {rs' : List Fmt.RoundView} {cols' : List Col}
    (h : foldBlocks ft pre s v.rounds v.opened = .ok (m, rs', cols')) (hs : SampleGoodS s.st) :
    SampleGoodS m.st := inv_in_chain (Q := QGoodS) hc hcut (okDrawn_of_view hv) h hs

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.goodS_in_chain
#print axioms VerifiableInference.Desc.First.K2.keepsS_k2
