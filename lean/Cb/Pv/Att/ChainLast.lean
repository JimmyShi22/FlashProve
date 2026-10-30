-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/ChainLast.lean: what a chain (Cb/Pv/Att/Chain.lean) claims at its end, on a transcript
that is given stage by stage, written out as one claim for each stage.

c.Last Dn is a claim on the last statement. On the last statement of a run that is given stage by
stage (c.run x ts, Cb/Pv/Att/ChainRun.lean) it is a conjunction: each stage's own claims at the
statement that this stage has found.

Main names:
  c.Owed x ts m: by recursion on the chain. At a sumcheck with the further scalars r and the output
    o: L x r m, Ow ((x, r), o) m and what the rest owes at ((x, r), o). At a draw β: what the rest
    owes at (x, β). At sent scalars s and a draw β: L x s m and what the rest owes at ((x, s), β).
  Ch.last_run: c.Last Dn (c.run x ts) m holds exactly if Dn x m and c.Owed x ts m hold.
  Ch.back_run: the first statement inside c.run x ts is x.
  Ch.trsComap, Ch.owed_comap: a chain read through a map f of statements has the same stages'
    transcripts, and owes at x what the chain owes at f x.

Limits: definitions unfolded; nothing on soundness, knowledge soundness or hiding.
-/
import Cb.Pv.Att.ChainRun
import Cb.Pv.Att.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole TWhole.G9 Johnson.L5.Layers Cb.Pv.Lay

variable {E : Type} [Field E] [Fintype E] {M : Type}

namespace Ch

/-- What the stages claim, each at the statement that it has found. -/
def Owed : {X : Type} → (c : Ch E M X) → X → c.Trs → M → Prop
  | _, .done _, _, _, _ => True
  | _, .ride Y n F cl _ L Ow next, x, ts, m =>
    L x (riders Y n ts.1) m ∧
      Ow ((x, riders Y n ts.1), shortV Y F (cl x (riders Y n ts.1)) (unrideN Y n ts.1)) m ∧
      next.Owed ((x, riders Y n ts.1), shortV Y F (cl x (riders Y n ts.1)) (unrideN Y n ts.1))
        ts.2 m
  | _, .draw _ _ _ next, x, ts, m => next.Owed (x, ts.1) ts.2 m
  | _, .send _ _ _ _ L next, x, ts, m => L x ts.1.1 m ∧ next.Owed ((x, ts.1.1), ts.1.2) ts.2 m

/-- The claim at the end of a run, stage by stage. -/
theorem last_run : ∀ {X : Type} (c : Ch E M X) (Dn : X → M → Prop) (x : X) (ts : c.Trs) (m : M),
    c.Last Dn (c.run x ts) m ↔ Dn x m ∧ c.Owed x ts m
  | _, .done _, _, _, _, _ => (and_iff_left trivial).symm
  | _, .ride _ _ _ _ _ _ _ next, _, _, ts, m =>
    (last_run next _ _ ts.2 m).trans (by simp only [Owed, and_assoc])
  | _, .draw _ _ _ next, _, _, ts, m => last_run next _ _ ts.2 m
  | _, .send _ _ _ _ _ next, _, _, ts, m =>
    (last_run next _ _ ts.2 m).trans (by simp only [Owed, and_assoc])

/-- The first statement inside the last one. -/
theorem back_run : ∀ {X : Type} (c : Ch E M X) (x : X) (ts : c.Trs), c.back (c.run x ts) = x
  | _, .done _, _, _ => rfl
  | _, .ride _ _ _ _ _ _ _ next, _, ts => congrArg (fun b => b.1.1) (back_run next _ ts.2)
  | _, .draw _ _ _ next, _, ts => congrArg (fun b => b.1) (back_run next _ ts.2)
  | _, .send _ _ _ _ _ next, _, ts => congrArg (fun b => b.1.1) (back_run next _ ts.2)

/-- The stages' transcripts of a chain, for the chain read through a map of statements. -/
def trsComap : {X : Type} → (c : Ch E M X) → {X' : Type} → (f : X' → X) → c.Trs → (c.comap f).Trs
  | _, .done _, _, _, _ => ()
  | _, .ride _ _ _ _ _ _ _ next, _, _, ts => (ts.1, next.trsComap _ ts.2)
  | _, .draw _ _ _ next, _, _, ts => (ts.1, next.trsComap _ ts.2)
  | _, .send _ _ _ _ _ next, _, _, ts => (ts.1, next.trsComap _ ts.2)

theorem owed_comap : ∀ {X : Type} (c : Ch E M X) {X' : Type} (f : X' → X) (x : X') (ts : c.Trs)
    (m : M), (c.comap f).Owed x (c.trsComap f ts) m ↔ c.Owed (f x) ts m
  | _, .done _, _, _, _, _, _ => Iff.rfl
  | _, .ride _ _ _ _ _ _ _ next, _, _, _, ts, m =>
    and_congr Iff.rfl (and_congr Iff.rfl (owed_comap next _ _ ts.2 m))
  | _, .draw _ _ _ next, _, _, _, ts, m => owed_comap next _ _ ts.2 m
  | _, .send _ _ _ _ _ next, _, _, _, ts, m => and_congr Iff.rfl (owed_comap next _ _ ts.2 m)

end Ch
end Cb.Pv.Att

#print axioms Cb.Pv.Att.Ch.last_run
#print axioms Cb.Pv.Att.Ch.back_run
#print axioms Cb.Pv.Att.Ch.owed_comap
