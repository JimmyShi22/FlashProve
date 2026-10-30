--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/K2Hands/SamplePre.lean: SampleChain.lean's and SampleChainS.lean's ends, asking the
keeping OF THE BLOCKS IN FRONT ALONE. A law file; no running text imports it.

On another house's reading: the invariant on the messages' stored sample rows is spent in front of a
code switch, so only what stands in front of that switch in the chain's flat list must keep it: the
last proximity test, the members' steps and the chain's end stand behind every code switch of the
first chain and owe nothing.

  inv_at_pre     where every block of the list pre keeps RowsInv Q: at the verifier's state behind
                 the fold over pre.
  goodS_at_pre   the like at SampleGoodS, where the view has passed the fold's test on its words.
Limits: those of SampleChain.lean. That a given block stands behind every code switch is not shown
here. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.SampleChainS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn foldBlocks viewWordsBelowPrime)
open VerifiableInference.Desc.Keeps1

variable {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop} {Cl : Type}

theorem inv_at_pre {ft : Nat} {pre : List (Block S Cl)} (hb : ∀ b ∈ pre, KeepsInv Q b) {s m : S}
    {rs rs' : List Fmt.RoundView} {cols cols' : List Col} (hr : ∀ r ∈ rs, OkDrawn r)
    (h : foldBlocks ft pre s rs cols = .ok (m, rs', cols')) (hs : RowsInv Q s.st) :
    RowsInv Q m.st :=
  fold_keeps (R := OkDrawn) (P := Inv Q) okDrawn_noDigest ft pre s m rs rs' cols cols' hb hr h hs

theorem goodS_at_pre {ft : Nat} {pre : List (Block S Cl)} (hb : ∀ b ∈ pre, KeepsInv QGoodS b)
    {s m : S} {v : Fmt.View} (hv : viewWordsBelowPrime v = true) {rs' : List Fmt.RoundView} {cols' : List Col}
    (h : foldBlocks ft pre s v.rounds v.opened = .ok (m, rs', cols')) (hs : SampleGoodS s.st) :
    SampleGoodS m.st := inv_at_pre (Q := QGoodS) hb (okDrawn_of_view hv) h hs

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.goodS_at_pre
