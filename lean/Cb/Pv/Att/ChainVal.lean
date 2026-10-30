-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/ChainVal.lean: at lawful picks the verifier of a chain (Cb/Pv/Att/Chain.lean) rejects
nothing; what it puts out, as one function of the statement and the transcript.

Main names:
  rideV, ride_tot: the sumcheck with further scalars (rideNR, Cb/Pv/Att/Ride.lean): at a lawful pick
    its reduction rejects nothing and its output is the statement, the further scalars and shortV
    (Cb/G6/Value.lean) at the claim that they give. The form is Tot (Cb/G9/Tot.lean).
  sendV, send_tot: the round with scalars and a draw (Cb/Pv/Lay/Draws.lean). done_tot: no stage.
  c.FixOK: every sumcheck of the chain has a lawful pick (HFixs.OK).
  c.val Ex: the chain's function, by recursion on the chain.
  Ch.tot: under c.FixOK the reduction of c.R Ex rejects nothing and its output is c.val Ex, for all
    statements and transcripts.
  Tot.unique: a reduction that rejects nothing has one such function. So a function with code that
    is proved, stage by stage, to be the output of the same reduction is c.val Ex (Ch.val_eq).

To run: c.val Ex has no code: it splits transcripts by Tr.fst and Tr.snd and calls shortV. For a
chain that is written out, the same function is built with code from the cuts of Cb/G9/Split.lean
and shortL of Cb/G9/Light.lean, by the rule Tot.ior_seqC. Cb/Pv/Att/TestChainVal.lean does so for a
draw, a round with scalars and a plain sumcheck with a further scalar, and runs it over Cb.Gl.E.

Limits: nothing on soundness, knowledge soundness or hiding. At a pick that is not lawful a
sumcheck's verifier may reject, and nothing is said. Since the chain's verifier rejects nothing, all
that the chain's knowledge soundness gives lies in c.Last, which whoever follows must test.
-/
import Cb.Pv.Att.Chain
import Cb.G9.Split

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole TWhole.G9 Johnson.L5.Layers Cb.Pv.Lay

/-- A reduction that rejects nothing has one output function. -/
theorem _root_.TWhole.G9.Tot.unique {A B : Type} {K : Reduction A B} {v v' : A → Tr K.shape → B}
    (h : Tot K v) (h' : Tot K v') : v = v' :=
  funext fun a => funext fun τ => Option.some.inj ((h a τ).symm.trans (h' a τ))

variable {E : Type} [Field E] [Fintype E] {M : Type}

section Stages
variable {X : Type} (Ex : ExtSpec)

/-- What the sumcheck with further scalars puts out. -/
noncomputable def rideV (Y : PscPar E) (n : ℕ) (F : ∀ st, HFixs (Y.vars st))
    (cl : X → (Fin n → E) → E × Y.St) (a : X × Ex.Str) (τ : Tr (shapeRN Y n)) :
    ((X × (Fin n → E)) × Y.Out) × Ex.Str :=
  (((a.1, riders Y n τ), shortV Y F (cl a.1 (riders Y n τ)) (unrideN Y n τ)), a.2)

theorem ride_tot (Y : PscPar E) (n : ℕ) (F : ∀ st, HFixs (Y.vars st))
    (cl : X → (Fin n → E) → E × Y.St) (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) :
    Tot (rideNR Y n F cl Ex).red (rideV Ex Y n F cl) := fun a τ => by
  show (((shortR Y F Ex).out (cl a.1 (riders Y n τ)) a.2 (unrideN Y n τ)).map
    fun o => ((a.1, riders Y n τ), o)).map (fun xo => (xo, a.2)) = _
  rw [short_out Y F Ex hF]
  rfl

/-- What the round with scalars and a draw puts out. -/
def sendV (n : ℕ) (D : Type) [Fintype D] [Nonempty D] (a : X × Ex.Str)
    (τ : Tr [sendRound E (Fin n) D]) : ((X × (Fin n → E)) × D) × Ex.Str :=
  (((a.1, sent τ), drawnS τ), a.2)

omit [Fintype E] in
theorem send_tot (n : ℕ) (D : Type) [Fintype D] [Nonempty D] :
    Tot (send E (Fin n) D X Ex).red (sendV Ex n D) := fun _ _ => rfl

theorem done_tot : Tot (IOR.pure (some : X → Option X) (ExtMap.id Ex)).red (fun a _ => a) :=
  fun _ _ => rfl

end Stages

namespace Ch

/-- Every sumcheck of the chain has a lawful pick. -/
def FixOK : {X : Type} → Ch E M X → Prop
  | _, .done _ => True
  | _, .ride Y _ F _ _ _ _ next => (∀ st, HFixs.OK (Y.vars st) (F st)) ∧ next.FixOK
  | _, .draw _ _ _ next => next.FixOK
  | _, .send _ _ _ _ _ next => next.FixOK

/-- What the chain's verifier puts out. -/
noncomputable def val (Ex : ExtSpec) : {X : Type} → (c : Ch E M X) → X × Ex.Str →
    Tr (c.R Ex).shape → c.End × Ex.Str
  | _, .done _ => fun a _ => a
  | _, .ride Y n F cl _ _ _ next =>
    seqV (shapeRN Y n) (next.R Ex).shape (rideV Ex Y n F cl) (next.val Ex)
  | _, .draw D _ _ next =>
    seqV [drawRound D.D] (next.R Ex).shape (drawV D.D (fun x β => (x, β)) Ex) (next.val Ex)
  | _, .send n D _ _ _ next =>
    seqV [sendRound E (Fin n) D.D] (next.R Ex).shape (sendV Ex n D.D) (next.val Ex)

/-- The chain's verifier rejects nothing, and what it puts out. -/
theorem tot (Ex : ExtSpec) : ∀ {X : Type} (c : Ch E M X), c.FixOK → Tot (c.R Ex).red (c.val Ex)
  | _, .done _, _ => done_tot Ex
  | _, .ride Y n F cl _ _ _ next, h => Tot.ior_seq (ride_tot Ex Y n F cl h.1) (tot Ex next h.2)
  | _, .draw D _ _ next, h => Tot.ior_seq (Tot.draw D.D (fun x β => (x, β)) Ex) (tot Ex next h)
  | _, .send n D _ _ _ next, h => Tot.ior_seq (send_tot Ex n D.D) (tot Ex next h)

/-- Any function that is proved to be the output of the chain's reduction is c.val Ex. -/
theorem val_eq (Ex : ExtSpec) {X : Type} (c : Ch E M X) (h : c.FixOK)
    (v : X × Ex.Str → Tr (c.R Ex).shape → c.End × Ex.Str) (hv : Tot (c.R Ex).red v) :
    c.val Ex = v := Tot.unique (tot Ex c h) hv

end Ch
end Cb.Pv.Att

#print axioms TWhole.G9.Tot.unique
#print axioms Cb.Pv.Att.ride_tot
#print axioms Cb.Pv.Att.send_tot
#print axioms Cb.Pv.Att.done_tot
#print axioms Cb.Pv.Att.Ch.tot
#print axioms Cb.Pv.Att.Ch.val_eq
