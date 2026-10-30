-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Switch/FoldSeam.lean: the seam from the fold of a group of a request's chain to the code
switch into the next group, and the switch's size at the library's own record of a closing.

A group of a request's chain is closed by a batching round and a fold; then comes the code switch
(Cb/Pv/Switch/SendLoc.lean, SendLocRide.lean). The fold ends at a joint of the form "the claim on
the folded word, beside the joint over the messages that are kept". The switch begins at a joint
over the kept messages THAT ARE NOT HELD in the folded word; the held ones are read in the folded
word's slots from there on, and their samples stand in the explicit part. The library has the data
of both sides and the step between them:
`LdFoldD` with `pX`, `pE`, `pB` (Cb/Req1/LdSegKit.lean), the step's law `LdFoldD.stepK`
(Cb/Thin/Kinds/Fold.lean), and `LdCloseD D`, the record of the sending and the locations behind a
fold D (Cb/Req1/LdSegFit.lean). This file reads them at the kinds of Cb/Pv/Switch/. Nothing of the
library is stated anew. Definitions and proofs.

Main names (D : `LdFoldD E Kc`; Q : `LdCloseD D`; w₀: a witness of the stage behind the fold):
  `size D Q w₀`: the size of the switch. `stage_size`, `loc_size`: its stage before is `D.tgt`, its
    record of the locations is `Q.loc`, by definition. `sizeR D Q w₀ Cw`: the same with a rider's
    code.
  `ok_size`: the switch's condition `SendLoc.OK` at that size follows from `Q.snd.HypK` (the codes'
    laws, fair seeds, bounded lists, samples that evade) and `D.held.Laws D.e` (the laws of the
    slots). The two clauses on the base joint hold by definition (`ldSegFit_near`).
  `left D`: the joint behind the fold, `D.mid`, WITH `D.Tw` BESIDE ITS CONDITION: the slots of the
    folded word are the words of the held messages.
  `seam`, `seamR`: the step (`D.pX`, `D.pE`, `D.pB`) from `left D` to the switch's joint before WITH
    ITS OWN CONDITION (`SendLoc.inJP`, `SendLocRide.inJP`, Cb/Pv/Switch/SendLocInto.lean): local;
    the condition is carried; a witness behind the step gives one before it. No premise.
      f: (xo, (st, smp)) goes to (((xo, the held messages' samples), st), the samples of the kept
         messages that are not held).
      g: (the folded word, (e, words)) goes to ((the folded word, e), the words of those not held).
      back: (wit, (wf, wp)) goes to (wf, (for a held message the slots of wf, else wit; wp)).
  `knowInto_and`: a reduction that is knowledge sound into a condition, and whose every output has
    Q, is knowledge sound into "the condition and Q". `into_left`: so a block that ends at `D.mid`
    and whose every output has `D.Tw` ends at `left D`.
Limits: THAT EVERY OUTPUT OF THE BLOCK BEFORE HAS `D.Tw` IS A PREMISE OF `into_left`: it is a fact
on that block's verifier and new oracles (the library asks it of its own: `LdFoldD.HypK.word`),
shown here of no block. Which kept messages are held, and where their slots are (`cl`, `sW`, `sJ`,
`sQ`), are data of D. Nothing says that a group of the programs is a value of D and Q. Nothing on an
honest prover.
-/
import Cb.Pv.Switch.SendLocInto
import Cb.Thin.Kinds.Fold
import Cb.Req1.LdSegFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.FoldSeam
open Iop Prob IOR Cb

variable {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc) (Q : LdCloseD D) (w₀ : D.tgt.W)

/-- The size of the switch behind the fold D, at the library's record Q of the closing. -/
@[reducible] def size : SendLoc.Size E where
  Kc := Kc
  S₀ := D.S₂
  P := D.Pf
  neP := Q.neP
  C := D.Cf
  e := D.e
  t := Q.t
  hd := D.held
  Xc := E × D.Stf
  St₀ := D.St₀
  Wp₀ := D.Cf.N.Wit × D.Wp
  E₀ := D.E₀
  Φ := D.slf.Holds
  A₀ := D.tgt.A
  d := Q.snd
  cut := Q.loc.cut
  A₁ := Q.A₁
  w₀ := w₀

/-- The same with a rider's code. -/
@[reducible] def sizeR {Pw : Type} (Cw : LdCode E Pw) : SendLocRide.Size E := ⟨size D Q w₀, Pw, Cw⟩

theorem stage_size : SendLoc.stage (size D Q w₀) = D.tgt := rfl

theorem loc_size : SendLoc.loc (size D Q w₀) = Q.loc := rfl

/-- The switch's condition at that size. -/
theorem ok_size (h : Q.snd.HypK) (hl : D.held.Laws D.e) : SendLoc.OK (size D Q w₀) :=
  ⟨h, ⟨(ldSegFit_near E Kc D Q).relR, (ldSegFit_near E Kc D Q).on, hl⟩⟩

/-- The joint behind the fold, with "the slots of the folded word are the words of the held
messages" beside its condition. -/
def left : Rels Kc D.mid.X D.mid.E D.mid.W :=
  D.mid.rels.and (fun _ _ _ => True) (fun _ _ => True) D.Tw

/-- THE SEAM: from the joint behind the fold to the switch's joint before, with its own condition.
-/
theorem seam :
    IOR.StepK (fun x => some (D.pX x)) D.pE (fun _ w => D.pB w) (left D)
      (SendLoc.inJP (size D Q w₀)) :=
  D.stepK

/-- The same for the switch whose first message bears a rider. -/
theorem seamR {Pw : Type} (Cw : LdCode E Pw) :
    IOR.StepK (fun x => some (D.pX x)) D.pE (fun _ w => D.pB w) (left D)
      (SendLocRide.inJP (sizeR D Q w₀ Cw)) :=
  D.stepK

/-- Knowledge soundness into a condition, and a property of every output: into both. -/
theorem knowInto_and {A B WA WB : Type} (K : Reduction A B) (on : A → Prop) (on' Qo : B → Prop)
    (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape)
    (h : K.KnowInto on on' RA RB ext ε) (hQ : ∀ a τ b, K.out a τ = some b → Qo b) :
    K.KnowInto on (fun b => on' b ∧ Qo b) RA (fun b w => RB b w ∧ True) ext ε := fun a ha =>
  Doomed.mono _ _
    (fun τ hτ b w hb hw =>
      hτ b w hb (hw.elim (fun k => Or.inl k.1) fun n => Or.inr fun k => n ⟨k, hQ a τ b hb⟩))
    (h a ha)

/-- A block that ends at the joint behind the fold, and whose every output has `D.Tw`, ends at
`left D`. -/
theorem into_left {A WA : Type} (K : Reduction A (D.mid.X × D.mid.E.Str)) (on : A → Prop)
    (RA : A → WA → Prop) (ext : A → Tr K.shape → D.mid.W → WA) (ε : Err K.shape)
    (h : K.KnowInto on D.mid.rels.on RA D.mid.rels.relR ext ε)
    (word : ∀ a τ b, K.out a τ = some b → D.Tw b) :
    K.KnowInto on (left D).on RA (left D).relR ext ε :=
  knowInto_and K on _ D.Tw RA _ ext ε h word

end Cb.Pv.FoldSeam

#print axioms Cb.Pv.FoldSeam.ok_size
#print axioms Cb.Pv.FoldSeam.seamR
#print axioms Cb.Pv.FoldSeam.into_left
