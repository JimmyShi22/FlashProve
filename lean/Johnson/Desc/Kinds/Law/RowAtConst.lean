-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowAtConst.lean.
WHAT IT DOES NOT SHOW. No soundness. NO LAW OF ANY SUB-PROTOCOL. FIVE THIN CALLS OF THE TABLE's
FILES' OWN THEOREMS, AT THEIR OWN HEAD AND ROW: nothing is proved here that does not lie there at
other letters. ALL UNDER q₁, q₂, q₃: the three lists of L are the IOP's own: at another L nothing is
said. No example.
WORDS. "The row": P5J/RowsAtMg.lean: AtMg.row: the first chain's pieces at the seated term. "Held"
(Desc/Sound: held): a sub-protocol as a piece holds it: under the strict reading, lifted over the
public part.
LETTERS. No "there is". k: any number of a piece; kind-free.
OBJECT. The pieces of the first chain at the table's files' head AtMg.
USER. The conditions of the two kinds K6 and K7 at the closed constant (K07AtMg.lean: K7At's lift,
more, blocks, and the lists at which book and told stand; Law/K6LawAtMgAll.lean: more, cap, blocks).
WHAT IT IS. WHAT A KIND's CONDITION ASKS OF "THE PIECE AT k OF THE ROW", KIND-FREE, FROM THE HEAD
ALONE.
first_is: the seated term's first chain is the head's letter cF (by definition).
atRow_more: the maker's piece and its cap (Desc/Sound/PieceSeated.lean: seated_more), for k + 1 <
the list's length. atRow_lift: what the piece holds (Desc/Sound/AtDriver.lean: OfDesc.pieceAt).
atRow_blocks: the sub-protocols' tests, at the held list (Desc/Sound/PieceLaid.lean: planOk_parts,
from the head's own laid.planOk; blocksOk_held). atRow_told: the held list tells what the chain's
own list tells (toldOf_held).
NEAREST RELATIVES: Desc/Sound/PieceLaid.lean: laid_pieces: the like at "there is F", not at the
head's term and row · Desc/Sound/PieceMore.lean: row_more: ANOTHER THEOREM OF THAT NAME (on a tiled
row): hence the names atRow_...

-/
import Johnson.P5J.RowsAtMg
import Johnson.Desc.Sound.PieceLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_zero rchAt_hand block_at piece_step)
open _root_.Iop (Err)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- The seated term's first chain is the head's letter. -/
theorem first_is : (P5J.F0T o Zp Np cF).first = cF := rfl

/-- **The maker's piece, and its cap, at the row.** -/
theorem atRow_more (h : P5J.AtMg o Z D r Zp Np cF)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T o Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T o Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T o Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T o Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (k : Nat) (q)
    (hq : (h.row L)[k]? = some q) (hk : k + 1 < cF.blocksInOrder.length) :
    PieceMore (numAt (D.at frS.P.T.a).t₁ (D.at frS.P.T.a).t₂ 0) 0 (cF.blocksInOrder.map held) k q ∧
      q.err = Err.cap 128 (uLT (ckP .two) q.ds) :=
  (seated_more (P5J.F0T o Zp Np cF) "proof file" (D.at frS.P.T.a)
    (by rw [P5J.LaidAt.atDepth h.scope h.laid]; exact h.laid.data)
    (sealLast_of_planOk (P5J.F0T o Zp Np cF) h.laid.planOk) (ckP .two) L.c₁ L.k₁ L.c₂ L.k₂ L.c₃ L.k₃
    q₁ q₂ q₃ L.e₁ L.e₂ L.e₃ L.dW L.wEnd).1 k q hq hk

/-- **What the piece at k holds.** -/
theorem atRow_lift (h : P5J.AtMg o Z D r Zp Np cF)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T o Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T o Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T o Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T o Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (k : Nat) (q)
    (B : Block P5J.TS ProofFile.Cl) (hq : (h.row L)[k]? = some q) (hB : cF.blocksInOrder[k]? = some B) :
    q.b = (Sound.below B).lift Prod.snd fun t s => (t.1, s) :=
  OfDesc.pieceAt (h.ofDesc L q₁ q₂ q₃) hq hB

/-- **The sub-protocols' tests pass, at the held list.** -/
theorem atRow_blocks (h : P5J.AtMg o Z D r Zp Np cF) :
    blocksOk (cF.blocksInOrder.map (held (P := ProofFile.InstPub))) = true := by
  rw [blocksOk_held]
  exact (planOk_parts (P5J.F0T o Zp Np cF) h.laid.planOk).1

/-- The held list tells what the chain's own list tells. -/
theorem atRow_told : toldOf (cF.blocksInOrder.map (held (P := ProofFile.InstPub))) = toldOf cF.blocksInOrder :=
  toldOf_held cF.blocksInOrder

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.first_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.atRow_more
#print axioms VerifiableInference.Desc.Kinds.Head.Law.atRow_lift
#print axioms VerifiableInference.Desc.Kinds.Head.Law.atRow_blocks
#print axioms VerifiableInference.Desc.Kinds.Head.Law.atRow_told
