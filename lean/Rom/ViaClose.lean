-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/ViaClose.lean: two lemmas on the translation of the points of the oracles (Rom/SpecVia.lean).

  `OComp.via_bind`, `Adv.prog_via`  A translation commutes with bind and with the program that an
                                    adversary and a step make (`Adv.prog`).

This file does not prove that closeness of two provers is kept if the points are permuted;
ProverClose is not in this library.

Notation:
  `QMap` (Rom/SpecVia.lean): a translation of queries: for the point (o, q) the point (o', q') that
      is queried in its place, and how an answer of o' is read as an answer of o
  `OComp.via φ c` (Rom/SpecVia.lean): the algorithm that queries φ p where c queries p
  `Adv.via φ A` (Rom/SpecVia.lean): the adversary that queries φ p where A queries p; its calls are
      unchanged
  `Adv.prog step A t` (Rom/Forget.lean): an adversary and the replies of a challenger, as one oracle
      algorithm; it returns the output and the final private state;
      `step : τ → Out → OComp S (In × τ)`, `t : τ`, τ a type
-/
import Rom.Via
import Rom.SpecCarryP

open scoped ENNReal
open Prob ZKCP
namespace Rom

variable {S : OSpec} {Out In α β : Type}

theorem OComp.via_bind (φ : QMap S) :
    ∀ (c : OComp S α) (g : α → OComp S β), (c.bind g).via φ = (c.via φ).bind fun a => (g a).via φ
  | .pure _, _ => rfl
  | .query o q k, g =>
    congrArg (OComp.query (φ o q).1 (φ o q).2.1)
      (funext fun r => OComp.via_bind φ (k ((φ o q).2.2 r)) g)
  | .sample n k, g => congrArg (OComp.sample n) (funext fun r => OComp.via_bind φ (k r) g)

/-- The program of a translated adversary with translated steps is the translated program. -/
theorem Adv.prog_via {τ : Type} (φ : QMap S) (step : τ → Out → OComp S (In × τ)) :
    ∀ (A : Adv S Out In α) (t : τ),
      (A.via φ).prog (fun s m => (step s m).via φ) t = (A.prog step t).via φ
  | .halt _, _ => rfl
  | .sample n k, t => congrArg (OComp.sample n) (funext fun r => Adv.prog_via φ step (k r) t)
  | .query o q k, t =>
    congrArg (OComp.query (φ o q).1 (φ o q).2.1)
      (funext fun r => Adv.prog_via φ step (k ((φ o q).2.2 r)) t)
  | .call m k, t => by
      show ((step t m).via φ).bind
          (fun p => ((k p.1).via φ).prog (fun s m => (step s m).via φ) p.2) =
        ((step t m).bind fun p => (k p.1).prog step p.2).via φ
      rw [OComp.via_bind]
      exact congrArg ((step t m).via φ).bind (funext fun p => Adv.prog_via φ step (k p.1) p.2)


variable {I X W IVK ISK Pf : Type}


end Rom
