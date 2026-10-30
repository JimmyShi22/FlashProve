-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/Ker.lean: MAPS FROM A STATE TO A LAW ON (VALUE, NEXT STATE), IN SEQUENCE, AND
DRAWS THAT ARE CARRIED INWARD. Definitions and a small calculus, general in all types.

General definitions and lemmas. This file states no goal of the release.

WHAT IT IS FOR. It was made for Johnson/TokenSide2/LateDraws.lean. There a committer that draws all
its coins first is shown to have the law of the same committer with each secret coin drawn just
before the part that reads it. The parts are no algorithms under one rule for answering queries (the
rule changes from part to part, and entries are written into the table between the parts), so the
calculus for algorithms (Eqv, Johnson/TokenSide2/Same.lean) does not serve, and the same is said
here one level up, of maps on tables. Johnson/LateWorld/TabList.lean and
Johnson/LateWorld/Normal.lean import it too. All lemmas are equations of such maps. Those on pure,
bind, draw and late hold by the laws of PMF.bind (bind_bind, pure_bind, bind_comm); ofLazy_bind and
ofDefer_bind rest on the laws of runs in Rom/Handle/Laws.lean that are named below.

A part of an experiment that reads and writes a table is a map from a table to a law on (what the
part gives, the table after it). Such maps are composed in sequence. A draw that stands in front of
some parts which do not read it can be made behind them: the law is the same.

  Ker σ α            the type of these maps.
  Ker.pure, .bind    a value; two parts in sequence.
  Ker.draw μ f       draw c from μ, go on with f c. The state is not touched.
  Ker.late μ f       THE SAME MAP AS Ker.draw μ f, under a second name: a draw that is to be carried
                     inward. The lemmas below carry a "late" past a part that does not read it
                     (late_comm) and past a "draw" (late_draw), and never move a "draw". Used as
                     rewriting rules from left to right they end, with each "late" just in front of
                     the first part that reads it.
  Ker.ofLazy, .ofDefer   an oracle algorithm under lazy sampling; with marked queries deferred and
                     the log dropped at the end (OComp.runDefer, Rom/Handle/Defs.lean). Both turn a
                     sequence of algorithms into a sequence of maps (ofLazy_bind, ofDefer_bind): for
                     the second, because entries that stand in the log at the start change nothing
                     else (OComp.interp_defer_shift, Rom/Handle/Laws.lean).
Terms: lean/GLOSSARY.md.

-/
import Rom.Handle.Laws

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob

/-- A map from a state to a law on (value, next state). -/
abbrev Ker (σ α : Type) : Type := σ → PMF (α × σ)

namespace Ker
variable {σ α β γ δ : Type}

def pure (a : α) : Ker σ α := fun s => PMF.pure (a, s)

def bind (m : Ker σ α) (f : α → Ker σ β) : Ker σ β := fun s => (m s).bind fun p => f p.1 p.2

/-- Draw c from μ, go on with f c. -/
def draw (μ : PMF γ) (f : γ → Ker σ α) : Ker σ α := fun s => μ.bind fun c => f c s

/-- The same, under the name of a draw that is to be carried inward. -/
def late (μ : PMF γ) (f : γ → Ker σ α) : Ker σ α := fun s => μ.bind fun c => f c s

theorem late_eq_draw (μ : PMF γ) (f : γ → Ker σ α) : late μ f = draw μ f := rfl

theorem pure_bind (a : α) (f : α → Ker σ β) : (pure a).bind f = f a :=
  funext fun _ => PMF.pure_bind _ _

theorem bind_assoc (m : Ker σ α) (f : α → Ker σ β) (g : β → Ker σ γ) :
    (m.bind f).bind g = m.bind fun a => (f a).bind g :=
  funext fun _ => PMF.bind_bind _ _ _

theorem draw_bind (μ : PMF γ) (f : γ → Ker σ α) (g : α → Ker σ β) :
    (draw μ f).bind g = draw μ fun c => (f c).bind g :=
  funext fun _ => PMF.bind_bind _ _ _

theorem late_bind (μ : PMF γ) (f : γ → Ker σ α) (g : α → Ker σ β) :
    (late μ f).bind g = late μ fun c => (f c).bind g :=
  funext fun _ => PMF.bind_bind _ _ _

/-- A draw in front of a part that does not read it, or behind it. -/
theorem late_comm (μ : PMF γ) (m : Ker σ α) (f : γ → α → Ker σ β) :
    (late μ fun c => m.bind (f c)) = m.bind fun a => late μ fun c => f c a :=
  funext fun _ => PMF.bind_comm _ _ _

/-- Two draws, in either order. -/
theorem late_draw (μ : PMF γ) (ν : PMF δ) (f : γ → δ → Ker σ α) :
    (late μ fun c => draw ν fun d => f c d) = draw ν fun d => late μ fun c => f c d :=
  funext fun _ => PMF.bind_comm _ _ _

theorem draw_of_bind (μ : PMF γ) (k : γ → PMF δ) (f : δ → Ker σ α) :
    draw (μ.bind k) f = draw μ fun c => draw (k c) f :=
  funext fun _ => PMF.bind_bind _ _ _

theorem draw_of_pure (c : γ) (f : γ → Ker σ α) : draw (PMF.pure c) f = f c :=
  funext fun _ => PMF.pure_bind _ _

/-! ## Oracle algorithms as such maps -/

variable {S : OSpec}

/-- An oracle algorithm under lazy sampling. -/
def ofLazy (c : OComp S α) : Ker (Table S) α := fun T => c.runLazy T

theorem ofLazy_pure (a : α) : ofLazy (OComp.pure a : OComp S α) = pure a := rfl

theorem ofLazy_sample (n : ℕ) (k : Fin (n + 1) → OComp S α) :
    ofLazy (OComp.sample n k) = draw (unif (Fin (n + 1))) fun r => ofLazy (k r) := rfl

theorem ofLazy_bind (c : OComp S α) (g : α → OComp S β) :
    ofLazy (c.bind g) = (ofLazy c).bind fun a => ofLazy (g a) :=
  funext fun T => by
    show (c.bind g).runLazy T = (c.runLazy T).bind fun p => (g p.1).runLazy p.2
    rw [← OComp.interp_lazy, OComp.interp_bind, OComp.interp_lazy]
    exact congrArg _ (funext fun p => OComp.interp_lazy _ _)

/-- An oracle algorithm with the marked queries deferred, from the empty log; the log is dropped. -/
def ofDefer (mk : Mark S) (c : OComp S α) : Ker (Table S) α := fun T =>
  (c.runDefer mk T []).map fun o => (o.1, o.2.1)

theorem ofDefer_pure (mk : Mark S) (a : α) : ofDefer mk (OComp.pure a : OComp S α) = pure a :=
  funext fun _ => PMF.pure_map _ _

theorem ofDefer_bind (mk : Mark S) (c : OComp S α) (g : α → OComp S β) :
    ofDefer mk (c.bind g) = (ofDefer mk c).bind fun a => ofDefer mk (g a) :=
  funext fun T => by
    show ((c.bind g).interp (Handler.defer mk Handler.lazy) (T, [])).map _ =
      ((c.interp (Handler.defer mk Handler.lazy) (T, [])).map fun o => (o.1, o.2.1)).bind fun p =>
        ((g p.1).interp (Handler.defer mk Handler.lazy) (p.2, [])).map fun o => (o.1, o.2.1)
    rw [OComp.interp_bind, PMF.map_bind, PMF.bind_map]
    refine congrArg _ (funext fun p => ?_)
    have e := OComp.interp_defer_shift mk Handler.lazy (g p.1) p.2.1 p.2.2 []
    rw [List.append_nil] at e
    show ((g p.1).interp (Handler.defer mk Handler.lazy) (p.2.1, p.2.2)).map _ = _
    rw [e, PMF.map_comp]
    rfl

end Ker

end Rom

#print axioms Rom.Ker.late_comm
#print axioms Rom.Ker.late_draw
#print axioms Rom.Ker.ofLazy_bind
#print axioms Rom.Ker.ofDefer_bind
