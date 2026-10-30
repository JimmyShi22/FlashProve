-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyExitStep.lean: the rounds in which the verifier only draws, as steps.

OnBytes/Slice/KeyStep.lean has a calculus of steps: a step is a list of written rounds with error
counts, a test and a next state, and its soundness statement (Step.Sem) says that a false claim
before the step stays false after it, but for the counted verifier messages. This file states two
one-round blocks in that form:
 a round in which a value is drawn, from a count of bad values (sem_draw): the claim after the round
 is "the claim before it holds, or the drawn value is bad";
 the round in which all rows of a proximity test become one (BatSemAt.sem).
It also names the states of the three rounds of the test for a linear claim on a stored table
(KLin.A to KLin.A5) and their bad values (KLin.B1, B3, B5).

The states of the three rounds are nested pairs: the table, the claim and the vector w'; then the
shared point; then u'; then the locations; then ω'; then zeta. The vectors join the state between
the rounds, by steps that this file does not fix.

Main definitions: drawStep, batStep, KLin.A to KLin.A5 (states), KLin.B1, B3, B5 (bad values).

Main theorems: passT_one, sem_draw, BatSemAt.sem.


Not claimed. What OnBytes/Slice/KeyExit.lean and OnBytes/Slice/KeyLinVec.lean do not claim.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyStep
import OnBytes.Slice.KeyExit
import OnBytes.Slice.KeyLinVec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- The tests of work of one written round pass if and only if the round's own does. -/
theorem passT_one (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) :
    passT [d] (m, c, ()) ↔ GChal.pass (b := d.entry.work) c = true := by
  show (GChal.pass (b := d.entry.work) c && true) = true ↔ _
  rw [Bool.and_true]

/-! ## A drawn value -/

/-- The step of one round in which a value is drawn: nothing is tested, and the value, read by g,
joins the state. The error count is e times the number in the law of the format's sampler. -/
def drawStep {X D : Type} (d : PQ.RD) (e : ℕ) (g : Vals .two (Fmt.dsOf d.entry d.kind) → D) :
    Step X (X × D) :=
  Step.one d (e * (bsRound .two d.entry d.kind).w) (fun _ _ _ => True)
    fun x _ c => (x, g (valsOf d c))

/-- A drawn value, from a count. If at each state at which the claim Φ is false at most e values
are bad, then after the round "Φ holds or the value is bad" is false, but for the counted verifier
messages. -/
theorem sem_draw {X D : Type} [Fintype D] (d : PQ.RD)
    (g : Vals .two (Fmt.dsOf d.entry d.kind) → D) (hg : Function.Injective g)
    (hlog : d.entry.logN ≤ 64) (e : ℕ) (Φ : X → Prop) (Bad : X → D → Prop)
    (hc : ∀ x, ¬ Φ x → cnt (Bad x) ≤ e) :
    (drawStep (X := X) d e g).Sem Φ fun p => Φ p.1 ∨ Bad p.1 p.2 := fun x hx =>
  draw_cnt d g hg hlog [] () e (fun _ => Bad x) (fun _ => hc x hx) _
    (fun m c _ hp h => by
      rw [(passT_one d m c).1 h] at hp
      cases hp)
    fun _ _ hB _ _ h => h.elim hx hB

/-! ## All rows become one -/

/-- The step of the round in which n rows on the tables of the stage s become one. A state before
it: targets, vectors and the word. A state after it: the combined row and the word. -/
def batStep (s : Sg) (n : ℕ) (dA : PQ.RD) (εa : ℕ) :
    Step (((Fin n → GE) × (Fin n → s.cIn.J → GE)) × s.cIn.Word)
      ((GE × (s.cIn.J → GE)) × s.cIn.Word) :=
  Step.one dA εa (fun _ _ _ => True)
    fun x _ c => (sumRow s x.1.1 x.1.2 (gOne _ (valsOf dA c)), x.2)

/-- The batching as a step: from "some message is near the word and meets all rows" to "the
combined row has a witness in the stage's relaxed relation". -/
theorem BatSemAt.sem {s : Sg} {e n : ℕ} {dA : PQ.RD} {εa : ℕ} (h : BatSemAt s e n dA εa) :
    (batStep s n dA εa).Sem
      (fun x => ∃ w, ConL s.cIn.N e
        (Slf.All fun _ : Fin n => (Slf.idf (E := GE) (J := s.cIn.J))) x w)
      fun x' => ∃ w, s.RIn e x' w := fun x hx =>
  h [] () x.2 x.1.1 x.1.2 (fun w hw => hx ⟨w, hw⟩) _
    (fun m c _ hp h' => by
      rw [(passT_one dA m c).1 h'] at hp
      cases hp)
    fun _ _ hB _ _ hw => hw.elim hB

/-! ## The test for a linear claim on a stored table -/

namespace KLin
variable (K : KLin)

/-- The state before the shared point's round: the table, the claim, the vector w'. -/
abbrev A : Type := (K.S.Pos → Run.PQ.SgX) × K.Cl × (K.D.Col → GE)
/-- The state after the shared point's round. -/
abbrev A1 : Type := K.A × K.D.Pt
/-- The state before the locations' round: u' has joined. -/
abbrev A2 : Type := K.A1 × (K.S.Co → GE)
/-- The state after the locations' round. -/
abbrev A3 : Type := K.A2 × (Fin K.t → K.S.Pos)
/-- The state before zeta's round: ω' has joined. -/
abbrev A4 : Type := K.A3 × (Fin K.nY → GE)
/-- The state after zeta's round. -/
abbrev A5 : Type := K.A4 × (Fin K.l → GE)

/-- The bad shared points at a state. -/
def B1 (a : K.A) : K.D.Pt → Prop := K.BadPt a.1 a.2.1.g a.2.2
/-- The bad lists of locations at a state. -/
def B3 (p : K.A2) : (Fin K.t → K.S.Pos) → Prop := K.BadLoc p.1.1.1 p.1.2.1 p.2
/-- The bad values of zeta at a state. -/
def B5 (p : K.A4) : (Fin K.l → GE) → Prop := K.BadZeta p.1.1.1.2.2 p.1.1.2 p.2
variable {K}

end KLin

end OnBytes.Slice
