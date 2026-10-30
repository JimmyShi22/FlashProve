-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstStart.lean: THE PROMISE's BOOK-KEEPING AT BORDER 0 HOLDS OF THE
SHARED CHAIN's FIRST STATE, AT THE SHARED TABLE's CONSTANT (Johnson/Desc/K14/Law/SharedConst.lean).
Sh.pm's shape at 0 is three tests: "the key has the planned sizes and o_u is not yet noted" (pmZ) ·
the layout's test (layX) · Sh.X. Each holds of K14.first: the first by
promise_at_start (Johnson/Desc/K14/Law/KeyFitsAtStart.lean) at every instance of the seat; the other
two by make.

  Sh.shape_zero   what Sh.pm's shape at 0 is, as a term.
  Sh.shape_start  it accepts K14.first A.Q.codes key, where pmZ's test does.
  Sh.shape_start_at   at the seat's parameters, at every instance's key: no premise but AtFull of
                  the made value.
  Sh.on_start     **the chain's first state stands in the promise at border 0**: the promise there
                  is two clauses; the book-keeping by Sh.shape_start; "the committed table decodes"
                  and the slot's own condition are owed from the joint with the first chain.
What is not claimed. No soundness; no level. The other clauses of the promise at the start (the
    table's promise, no collision, what is shown) are not here.

-/
import Johnson.Desc.K14.Law.SharedConstWalk
import Johnson.Desc.K14.Law.SharedConstAt
import Johnson.Desc.K14.Law.KeyFitsAtStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

namespace Sh

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

theorem shape_zero (s : St) : (pm A O).shape 0 s =
    ((pmZ A.Q.par idleP).shape 0 s && (layX A.Q 0 s && X A 0 s)) := rfl

theorem shape_start (key : TableKey)
    (hk : (pmZ A.Q.par idleP).shape 0 (first A.Q.codes key) = true) :
    (pm A O).shape 0 (first A.Q.codes key) = true := by
  rw [shape_zero, hk, X_first A key]
  have hl : layX A.Q 0 (first A.Q.codes key) = true := by
    unfold layX
    exact decide_eq_true rfl
  rw [hl]
  rfl

/-- **THE CHAIN's FIRST STATE STANDS IN THE PROMISE AT BORDER 0.** At border 0 the promise has two
clauses (no message of the chain is pinned yet): the committed table decodes, and the book-keeping.
hT: the first, at the chain's first state: from the first chain's last promise. hO: the slot's own
condition: from the joint. -/
theorem on_start {Cl : Type} {Fr : Frame} (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
    MsgT)) (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
    (a : (P₁ × St) × Fr.E.Str) (key : TableKey) (ha : a.1.2 = first A.Q.codes key)
    (hk : (pmZ A.Q.par idleP).shape 0 (first A.Q.codes key) = true)
    (hT : decodesOf (decT₂ A O) ((actQ (nums A O) f l 0).2 a).1
      (strsOfAct Fr ((actQ (nums A O) f l 0).2 a)))
    (hO : own A O a.1.1 (strsOf Fr a.2)) :
    onQ₂ (nums A O) (pm A O) (own A O) true f l 0 a := by
  refine ⟨fun c hc => ?_, hO⟩
  have e : promsAt true 0 = [.tablePromise, .shape 0] := rfl
  rw [e] at hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact hT
  · obtain rfl := List.mem_singleton.1 hc
    have h := shape_start A O key hk
    rw [← ha] at h
    exact h

/-- **At the seat.** -/
theorem shape_start_at (Z : ProofFile.Pub) (N : H2U.Places4) (G : FileDescription Xi)
    (O : ShOpen P₀ P₁ Cells Tok (planAt Z N G).Q) (z : LPFD.Full.XF × RecFull)
    (h : H2K.Sizes.AtFull Z.p.chains.made) :
    (pm (planAt Z N G) O).shape 0
      (first (planAt Z N G).Q.codes (LPFD.Full.instanceAsPlainRecord z).pub.key) = true :=
  shape_start (planAt Z N G) O _ (promise_at_start z h _ idleP)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.shape_zero
#print axioms Desc.K14.Law.Sh.shape_start
#print axioms Desc.K14.Law.Sh.shape_start_at
#print axioms Desc.K14.Law.Sh.on_start
