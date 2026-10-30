-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/ChainRun.lean: the verifier of a chain (Cb/Pv/Att/Chain.lean) on a transcript that is
given stage by stage.

Whoever ties a chain to a routine that hears its rounds one stage after the other has a transcript
for each stage. This file joins them and says what the chain's verifier puts out on the joined
transcript, without a split.

Main names:
  c.Trs: a transcript for each stage of c: for a sumcheck a transcript of its rounds, for a draw the
    element drawn, for sent scalars the scalars and the element drawn.
  c.join Ex ts: the transcript of c.R Ex that is made of them, by Tr.app.
  c.run x ts: the last statement, stage by stage: a sumcheck puts the further scalars and shortV
    (Cb/G6/Value.lean) at its claim behind the statement; a draw the element; sent scalars the
    scalars and the element.
  Ch.val_join: c.val Ex (Cb/Pv/Att/ChainVal.lean) on the joined transcript is c.run.
  Ch.out_join: so, if every pick is lawful, the reduction of c.R Ex puts out c.run x ts on the
    joined transcript.

Limits: nothing on soundness, knowledge soundness or hiding. That every transcript of c.R Ex is a
joined one is not shown here; a tie from a routine that hears stage by stage needs joined
transcripts alone.
-/
import Cb.Pv.Att.ChainVal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole TWhole.G9 Johnson.L5.Layers Cb.Pv.Lay

variable {E : Type} [Field E] [Fintype E] {M : Type}

namespace Ch

/-- A transcript for each stage. -/
def Trs : {X : Type} → Ch E M X → Type
  | _, .done _ => Unit
  | _, .ride Y n _ _ _ _ _ next => Tr (shapeRN Y n) × next.Trs
  | _, .draw D _ _ next => D.D × next.Trs
  | _, .send n D _ _ _ next => ((Fin n → E) × D.D) × next.Trs

/-- The transcript of the whole chain. -/
noncomputable def join (Ex : ExtSpec) : {X : Type} → (c : Ch E M X) → c.Trs → Tr (c.R Ex).shape
  | _, .done _, _ => ()
  | _, .ride Y n _ _ _ _ _ next, ts => Tr.app (s := shapeRN Y n) ts.1 (next.join Ex ts.2)
  | _, .draw D _ _ next, ts =>
    Tr.app (s := [drawRound D.D]) ((((), ()), ts.1, ()) : Tr [drawRound D.D]) (next.join Ex ts.2)
  | _, .send n D _ _ _ next, ts =>
    Tr.app (s := [sendRound E (Fin n) D.D])
      ((((), ts.1.1), ts.1.2, ()) : Tr [sendRound E (Fin n) D.D]) (next.join Ex ts.2)

/-- The last statement, stage by stage. -/
noncomputable def run : {X : Type} → (c : Ch E M X) → X → c.Trs → c.End
  | _, .done _, x, _ => x
  | _, .ride Y n F cl _ _ _ next, x, ts =>
    next.run ((x, riders Y n ts.1), shortV Y F (cl x (riders Y n ts.1)) (unrideN Y n ts.1)) ts.2
  | _, .draw _ _ _ next, x, ts => next.run (x, ts.1) ts.2
  | _, .send _ _ _ _ _ next, x, ts => next.run ((x, ts.1.1), ts.1.2) ts.2

/-- The chain's function on a joined transcript. -/
theorem val_join (Ex : ExtSpec) : ∀ {X : Type} (c : Ch E M X) (x : X) (y : Ex.Str) (ts : c.Trs),
    c.val Ex (x, y) (c.join Ex ts) = (c.run x ts, y)
  | _, .done _, _, _, _ => rfl
  | _, .ride Y n F cl _ _ _ next, x, y, ts =>
    (seqV_app (shapeRN Y n) (next.R Ex).shape (rideV Ex Y n F cl) (next.val Ex) (x, y) ts.1
      (next.join Ex ts.2)).trans (val_join Ex next _ y ts.2)
  | _, .draw D _ _ next, x, y, ts =>
    (seqV_app [drawRound D.D] (next.R Ex).shape (drawV D.D (fun x β => (x, β)) Ex) (next.val Ex)
      (x, y) _ (next.join Ex ts.2)).trans (val_join Ex next _ y ts.2)
  | _, .send n D _ _ _ next, x, y, ts =>
    (seqV_app [sendRound E (Fin n) D.D] (next.R Ex).shape (sendV Ex n D.D) (next.val Ex) (x, y) _
      (next.join Ex ts.2)).trans (val_join Ex next _ y ts.2)

/-- What the chain's verifier puts out on a joined transcript. -/
theorem out_join (Ex : ExtSpec) {X : Type} (c : Ch E M X) (h : c.FixOK) (x : X) (y : Ex.Str)
    (ts : c.Trs) : (c.R Ex).red.out (x, y) (c.join Ex ts) = some (c.run x ts, y) := by
  rw [tot Ex c h (x, y) (c.join Ex ts), val_join]

end Ch
end Cb.Pv.Att

#print axioms Cb.Pv.Att.Ch.val_join
#print axioms Cb.Pv.Att.Ch.out_join
