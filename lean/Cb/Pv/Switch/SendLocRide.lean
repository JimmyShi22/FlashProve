-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Switch/SendLocRide.lean: the code switch between two groups of a request's chain
(Cb/Pv/Switch/SendLoc.lean) whose first prover message also bears a rider: the fresh mask of the new
group's own fold, an oracle without a sample. One kind of block of two rounds.

In the programs the first message of the switch holds the word into which the old group's folded
word is encoded anew, the kept messages anew, the new link's first oracle messages, and the fresh
mask of the new group's fold (OnBytes/Iop/Req.lean, `ReqFrame.first`, `ReqFrame.finish`). All but
the mask are sampled in that sending; the mask has no sample and is no member of the group
(OnBytes/Iop/Fold.lean,
`foldMaskNotice`, `foldMaskOk`). Here the mask is a rider (Cb/Pv/Switch/RideIn.lean): it is sent in
a round of its own before the sending, the sending and the locations run beside it, and a plan
merges the four rounds into two (Cb/Pv/Switch/Recut.lean):
  (mask . one value) (words . seeds) (answers . one value) (nothing . positions)
  becomes ((mask, words) . seeds) ((answers, nothing) . positions).
Nothing of the library's two moves is stated anew. Definitions and proofs.

Main names:
  `Size`: a size of Cb/Pv/Switch/SendLoc.lean and the rider's code Cw.
  `long4 s`: the four rounds. `plan s`: the plan. `R`, `eps`, `ext`: the reduction, TWO rounds; its
    errors; the extractor.
  `inJ`, `outJ`: the joint before: that of Cb/Pv/Switch/SendLoc.lean; the joint behind: that file's,
    read on the first component (`IOR.Rels.keepE`, Ior/Frame.lean): it asks nothing of the rider.
  `HAt s`, `OK s`, `hAt`: the statement at a size; the condition, that of Cb/Pv/Switch/SendLoc.lean;
    the statement holds under it. `good`: the four clauses together (`IOR.GoodK₀`,
    Cb/Thin/Kinds/Rules.lean).
  `point`, `isLocal`, `onOut`; `never_rejects`, `rounds`, `errs`, `vals`: the errors and the numbers
    of values of the verifier's messages are those of Cb/Pv/Switch/SendLoc.lean: the rider adds
    nothing.
  `out_eq`, `imp_eq`: the verifier and the new oracles in closed form.
  `imp_rider`: the second component of the new implicit instance is the word that was sent as the
rider.
Limits: as in Cb/Pv/Switch/SendLoc.lean. One rider. In the merged first message the rider is
the first component; in the programs' message the mask stands last: order and leaves are the
layout's matter, of which nothing is said here. That the fold which follows takes the rider as its
mask is not said here.
-/
import Cb.Pv.Switch.SendLoc
import Cb.Pv.Switch.RideIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.SendLocRide
open Iop Prob IOR Cb

/-- What the block is made of: the switch, and the rider's code. -/
structure Size (E : Type) [Field E] [Fintype E] : Type 1 where
  /-- the switch without the rider -/
  sw : SendLoc.Size E
  /-- the rider's long positions and its code -/
  Pw : Type
  Cw : LdCode E Pw

variable {E : Type} [Field E] [Fintype E] (s : Size E)

/-- The four rounds: the rider's; then the sending and the locations beside the rider. -/
noncomputable def long4 : IOR (SendLoc.stage s.sw).X (SendLoc.stage s.sw).Ex (SendLoc.loc
  s.sw).tgt.X
    ((SendLoc.loc s.sw).tgt.Ex.prod s.Cw.nat) :=
  rideIn s.Cw (SendLoc.long s.sw).R

/-- The plan: the rider's round is merged with the round of the words; the round of the answers
with the round of the positions. -/
noncomputable def plan : XPlan (long4 s).shape :=
  .msg _ _ () (.keep _ (.msg _ _ () (.keep _ .nil)))

theorem plan_ok : (plan s).OK := ⟨fun _ => rfl, fun _ => rfl, trivial⟩

/-- The reduction: two rounds. -/
noncomputable def R : IOR (SendLoc.stage s.sw).X (SendLoc.stage s.sw).Ex (SendLoc.loc s.sw).tgt.X
    ((SendLoc.loc s.sw).tgt.Ex.prod s.Cw.nat) :=
  (long4 s).recut (plan s)

/-- The errors. -/
noncomputable def eps : Err (R s).shape :=
  Err.recut (plan s)
    (Err.app (s := (rider s.Cw (SendLoc.stage s.sw).X (SendLoc.stage s.sw).Ex).shape) (0, ())
      (SendLoc.long s.sw).P.err)

/-- The extractor: that of the switch without the rider, on the transcript read back. -/
noncomputable def ext : (SendLoc.stage s.sw).X × (SendLoc.stage s.sw).Ex.Str → Tr (R s).shape →
    (SendLoc.loc s.sw).tgt.W → (SendLoc.stage s.sw).W :=
  fun a τ w =>
    IOR.extSeq (rider s.Cw _ _) ((SendLoc.long s.sw).R.keepE s.Cw.nat) (fun _ _ w => w)
      (fun a τ w => (SendLoc.long s.sw).ext (a.1, a.2.1) τ w) s.sw.w₀ a (Tr.old (plan s) τ) w

/-- The joint before the block. -/
def inJ : Rels s.sw.Kc (SendLoc.stage s.sw).X (SendLoc.stage s.sw).Ex (SendLoc.stage s.sw).W :=
  SendLoc.inJ s.sw

/-- The joint behind the block: that of the switch; nothing is asked of the rider. -/
def outJ : Rels s.sw.Kc (SendLoc.loc s.sw).tgt.X ((SendLoc.loc s.sw).tgt.Ex.prod s.Cw.nat)
    (SendLoc.loc s.sw).tgt.W :=
  (SendLoc.outJ s.sw).keepE s.Cw.nat

/-- The statement that the block at the size s is knowledge sound. -/
def HAt : Prop := (R s).red.Know (inJ s).on (inJ s).relR (outJ s).relR (ext s) (eps s)

/-- The condition: that of the switch without the rider. -/
def OK : Prop := SendLoc.OK s.sw

/-- The four clauses together. -/
theorem good (h : OK s) : IOR.GoodK₀ (R s) (inJ s) (outJ s) (ext s) (eps s) :=
  goodK₀_recut (long4 s) (plan s) (plan_ok s) () _ _ _ _
    (rideIn_good s.Cw (SendLoc.long s.sw).R (SendLoc.inJ s.sw) (SendLoc.outJ s.sw)
      (SendLoc.long s.sw).ext (SendLoc.long s.sw).P.err s.sw.w₀
      ((goodK_iff (SendLoc.long s.sw)).1 (SendLoc.long_goodK s.sw h)))

/-- The statement holds under the condition. -/
theorem hAt (h : OK s) : HAt s := (good s h).know

/-! ### beside the statement -/

theorem point (h : OK s) : Nonempty (R s).shape.IsPoint := (good s h).point

theorem isLocal (h : OK s) : (R s).IsLocal := (good s h).isLocal

theorem onOut (h : OK s) : ∀ a τ b, (inJ s).on a → (R s).red.out a τ = some b → (outJ s).on b :=
  (good s h).onOut

/-- The verifier never rejects. -/
theorem never_rejects (x : (SendLoc.stage s.sw).X) (y : (SendLoc.stage s.sw).Ex.Str)
    (τ : Tr (R s).shape) : ((R s).out x y τ).isSome := rfl

theorem rounds : (R s).shape.length = 2 := rfl

/-- The errors are those of the switch without the rider. -/
theorem errs :
    Err.toList (eps s) =
      [ldSendFamErr s.sw.d.N s.sw.d.Sd s.sw.d.L, (Fintype.card s.sw.P - s.sw.e - 1) ^ s.sw.t] := by
  show [0 * Fintype.card s.sw.d.Sd.D + Fintype.card Unit * ldSendFamErr s.sw.d.N s.sw.d.Sd s.sw.d.L,
    0 * Fintype.card (Fin s.sw.t → s.sw.P) +
      Fintype.card Unit * (Fintype.card s.sw.P - s.sw.e - 1) ^ s.sw.t] = _
  simp

theorem vals :
    Shape.chalList (R s).shape = [Fintype.card s.sw.d.Sd.D, Fintype.card (Fin s.sw.t → s.sw.P)] :=
  rfl

/-- The rider behind the block is the word that was sent: the oracle part of the first component of
the first message. -/
theorem imp_rider (y : (SendLoc.stage s.sw).Ex.Str) (τ : Tr (R s).shape) :
    ((R s).imp y τ).2 = (Round.msgFst τ.1).1 := rfl

/-- THE VERIFIER IN CLOSED FORM. x: the statement before: ((claim on the open word, the held
messages' samples), the rest) and the samples of the messages that are open. y: the oracles before:
(the open word, the further oracles) and the open messages' words. The transcript: a first message,
the joint seed, a second message, the positions. What is put out: the claim and the held samples as
they were; beside them THE POSITIONS AND THE LONG SYMBOLS OF THE OPEN WORD AT THE POSITIONS; the
rest as it was; the old samples, and for each new member ITS SEED OUT OF THE JOINT SEED WITH ITS
ANSWERS. -/
theorem out_eq (x : (SendLoc.stage s.sw).X) (y : (SendLoc.stage s.sw).Ex.Str) (τ : Tr (R s).shape) :
    (R s).out x y τ =
      some (((x.1.1, (τ.2.2.2.1, fun i => s.sw.C.T y.1.1 (τ.2.2.2.1 i))), x.1.2),
        s.sw.S₀.join s.sw.d.N (T := OMsg.Smp) x.2
          fun a => (s.sw.d.Sd.sd a τ.2.1, (Round.msgFst τ.2.2.1).2 a)) := rfl

/-- THE NEW ORACLES IN CLOSED FORM: the further oracles as they were (the open word is gone); the
open messages' words, and the new members' words out of the second component of the first message;
and the rider, out of its first component. -/
theorem imp_eq (y : (SendLoc.stage s.sw).Ex.Str) (τ : Tr (R s).shape) :
    (R s).imp y τ =
      ((y.1.2, s.sw.S₀.join s.sw.d.N (T := OMsg.Str) y.2 (Round.msgSnd τ.1).1),
        (Round.msgFst τ.1).1) := rfl

end Cb.Pv.SendLocRide

#print axioms Cb.Pv.SendLocRide.good
#print axioms Cb.Pv.SendLocRide.errs
