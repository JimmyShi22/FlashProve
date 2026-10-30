-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/StartAt.lean: the first states of the proof file's IOP as written in
Lean. Theorems only; no file of that IOP imports this one.
Why. The table of promises between sub-protocols starts at a first state in the sense of `IsStart`
(Johnson/Desc/First/BordersStart.lean). The rule that lays the meaning
(Johnson/Goal/Meaning/SpentAtPlain.lean) asks the first promise at the first chain's first state
(`TieOwes.on`). Its premise `oneKey` asks more than stands here: `shared_start_key` is a step toward
it, not its sentence.
  `startS_isStart`   the first chain's first state `startS Z p` is a first state in that sense, at
                     the first chain's codes and the words of the request file. It is `isStart_if`
                     of that file at our text
  `startS_reply`     so no reply is held there
  `shared_start_key`   the second chain's first state reads the table's key alone, not the request
  `fileDescBy_start₂`  the field `start₂` is `A.start`, by `rfl`

-/
import Johnson.Desc.ProofFile.Law.PureMade
import Johnson.Desc.First.BordersStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.First

/-- **The first chain's first state is a first state** in the sense of `IsStart`. -/
theorem startS_isStart {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pureRoad.pub o pol lay KL = .ok Z) (p : InstPub) :
    IsStart Z.first.codes (Verify.words32 p.request) (startS Z p) :=
  isStart_if (Pp := parP Z.first) (shape := Z.first.shape) (layout := Z.first.layout)
    (pubBy_start (show pubBy (ProofFile.PlainG.madeOf o) plainStarts pol lay KL = .ok Z from h))
    Z.p.X.T Z.p.X.P.h.V (Verify.words32 p.request)

theorem startS_reply {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pureRoad.pub o pol lay KL = .ok Z) (p : InstPub) : (startS Z p).out.reply = none :=
  isStart_reply (startS_isStart h p)

/-- The second chain's first state reads the table's key alone. -/
theorem shared_start_key {Z : Pub} {A : SharedSeat} (hA : onlineSharedChain Z = some A)
    (p p' : InstPub) (h : p.key = p'.key) : A.start p = A.start p' := by
  unfold onlineSharedChain laterShared Desc.K14.sharedSeatAt at hA
  split at hA
  · cases hA
    show Desc.K14.first _ p.key = Desc.K14.first _ p'.key
    rw [h]
  · cases hA

theorem fileDescBy_start₂ {σ : Type} (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (A : SharedSeat)
    (B : SecondSeat) (get : σ → S) (start : InstPub → σ) (c : Chain σ Cl) :
    (fileDescBy o mk Z A B get start c).start₂ = A.start := rfl

end ProofFile.Law

#print axioms ProofFile.Law.startS_isStart
#print axioms ProofFile.Law.startS_reply
#print axioms ProofFile.Law.shared_start_key
