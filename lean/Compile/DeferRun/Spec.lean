-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DeferRun/Spec.lean: mode I of a token program that reveals nothing is a plain run with a
log. DEFINITIONS AND STATEMENTS; the proofs are in Compile/DeferRun/Proof.lean. General in the
family of oracles.

General statements. This file states no goal of the release.

A token program (Step, Rom/Defer.lean) has two runs. In mode I a marked evaluation gets a fresh
uniform answer and does not touch the table; a later release writes it there, where the table has no
entry. `erase` (Compile/Star.lean) forgets the tokens and leaves an ordinary oracle algorithm.
Compile/Step1_life2_Erase.lean shows that mode R is the lazy run of the erasure. Here is the twin
for mode I: as long as the program reveals nothing, mode I is the run of the erasure in which
deferred queries get fresh answers that go into a log (OComp.runDefer, Rom/Handle/Defs.lean), and
the evaluations that the state keeps are the log's entries, one by one and in their order.

To say which queries of the erasure are deferred, a test mk on (oracle, point) is given, and the
program must fit it:

  Marks mk c vs   From the store vs, on every path: c reveals nothing, each marked evaluation of c
                  is at a point with mk, each plain one at a point without.
  qa              An evaluation, as the state keeps it, as an entry of a log: oracle, point, answer.
  keep            What is kept of a run in mode I: the result, the store, the table, and the
                  evaluations as a log.

  Spec.modeI_defer    mode I of c, of which `keep` is kept, = runDefer mk of erase c.
  Spec.modeI_seq      The same for two programs one after the other, EACH WITH ITS OWN TEST. So one
                      oracle may be plain in the first part and deferred in the second at points
                      that no single test tells apart.
  Spec.modeI_frame    What such a run leaves alone: the shown tokens; the evaluations that stood
                      before, which stay at the head of the list; and each new one is unreleased.
  Spec.release_lay    What a release does to the table in mode I: it writes, where there is no
                      entry (Table.lay), the entries of the evaluations that are unreleased and
                      charged to a shown token, in their order.

With the last two, a program of the form "evaluate; then one reveal" is, in mode I, a plain run with
a log, followed by the writing of the chosen entries.

At the file's end: a small program that fits a test, and one that does not, so that `Marks` is seen
to be met and to be failed.

Limits. `keep` drops what the state holds beside that: to which token an evaluation is charged,
which other tokens it holds, its tail, whether it is released; the counts; the flag for a broken
rule. So these statements say nothing on which entries a later reveal releases, but for
Spec.release_lay, which names them by tokens.
Follows the pattern of Compile/Step1_life2_Erase.lean.
Terms: lean/GLOSSARY.md.

-/
import Compile.Star
import Rom.Handle.Defs

set_option autoImplicit false

noncomputable section

namespace Compile
namespace DeferRun
open Rom Prob

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- An evaluation, as the state keeps it, as an entry of a log. -/
def qa (e : Ev S) : QA S := ⟨e.o, e.pt, e.ans⟩

/-- **The program fits the test mk**, from the store vs, on every path: it reveals nothing; its
marked evaluations are at points with mk, its plain ones at points without. -/
def Marks (mk : Mark S) : Step S sp α → List Bits → Prop
  | .pure _, _ => True
  | .sample _ k, vs => ∀ r, Marks mk (k r) vs
  | .plain o q k, vs => mk o q = false ∧ ∀ r, Marks mk (k r) vs
  | .fresh ℓ k, vs => ∀ u : Fin ℓ → Bool, Marks mk (k vs.length) (vs ++ [List.ofFn u])
  | .marked o t us pt _ k, vs =>
      mk o (pt (vs.getD t []) (us.map fun u => vs.getD u [])) = true ∧
        ∀ r, Marks mk (k (sp.split o r).1 vs.length) (vs ++ [List.ofFn (sp.split o r).2])
  | .reveal _ _, _ => False

/-- What is kept of a run in mode I: the result and the store; the table; the evaluations as a log.
-/
def keep (x : α × DSt S) : (α × List Bits) × Table S × Trace S :=
  ((x.1, x.2.vals), x.2.table, x.2.evs.map qa)

/-- **Mode I of a program that fits mk is the run of its erasure with a log.** -/
def Spec.modeI_defer : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α : Type) (mk : Mark S) (c : Step S sp α) (D : DSt S),
    Marks mk c D.vals →
    (c.run true D).map keep = (erase c D.vals).runDefer mk D.table (D.evs.map qa)

/-- **Two programs one after the other, each with its own test.** -/
def Spec.modeI_seq : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α β : Type) (mk₁ mk₂ : Mark S) (c₁ : Step S sp α)
      (c₂ : α → Step S sp β) (D : DSt S),
    Marks mk₁ c₁ D.vals →
    (∀ x ∈ (c₁.run true D).support, Marks mk₂ (c₂ x.1) x.2.vals) →
    ((c₁.bind c₂).run true D).map keep =
      ((erase c₁ D.vals).runDefer mk₁ D.table (D.evs.map qa)).bind fun y =>
        (erase (c₂ y.1.1) y.1.2).runDefer mk₂ y.2.1 y.2.2

/-- What a run in mode I of a program that fits mk leaves alone. -/
def Spec.modeI_frame : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α : Type) (mk : Mark S) (c : Step S sp α) (D : DSt S),
    Marks mk c D.vals →
    ∀ x ∈ (c.run true D).support, x.2.shown = D.shown ∧
      ∃ new, x.2.evs = D.evs ++ new ∧ ∀ e ∈ new, e.released = false

/-- What a release does to the table in mode I. -/
def Spec.release_lay : Prop :=
  ∀ (S : OSpec) (shown : List Tok) (evs : List (Ev S)) (T : Table S),
    (releaseAll true shown evs T).2 =
      T.lay ((evs.filter fun e => !e.released && shown.contains e.charged).map qa)

/-! ## A program that fits a test, and one that does not -/

/-- Over the one oracle of `rom lam`: nothing of an answer is visible. -/
def toySplit (lam : ℕ) : Split (rom lam) where
  Vis := fun _ => Unit
  tl := fun _ => lam
  split := fun _ => (Equiv.punitProd _).symm

/-- A fresh token of ℓ bits, one plain evaluation at the empty string, one marked evaluation at "1"
followed by the token. -/
def toy (lam ℓ : ℕ) : Step (rom lam) (toySplit lam) Unit :=
  .fresh ℓ fun t => .plain () [] fun _ =>
    .marked () t [] (fun v _ => true :: v) (fun _ _ _ h => (List.cons.inj h).2) fun _ _ => .pure ()

/-- The test: the point begins with "1". -/
def toyMark (lam : ℕ) : Mark (rom lam) := fun _ q => q.head?.getD false

theorem toy_marks (lam ℓ : ℕ) (vs : List Bits) : Marks (toyMark lam) (toy lam ℓ) vs :=
  fun _ => ⟨rfl, fun _ => ⟨rfl, fun _ => trivial⟩⟩

/-- Under the test that defers nothing the program does not fit. -/
theorem toy_not_marks (lam ℓ : ℕ) (vs : List Bits) :
    ¬ Marks (fun _ _ => false) (toy lam ℓ) vs :=
  fun h => Bool.false_ne_true ((h fun _ => false).2 (fun _ => false)).1

end DeferRun
end Compile
