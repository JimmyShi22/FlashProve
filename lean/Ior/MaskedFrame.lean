-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/MaskedFrame.lean: the item "masked messages" (`Honest.MM`, Ior/Masked.lean) goes through the
constructions without new rounds.

The constructions of Ior/Frame.lean but `IOR.pure` add no rounds to R: a further explicit part or
further oracles are handed on (`keepX`, `keepE`, `keep`), the witness has a further part (`carry`),
a step without rounds is put before or after (`pre`, `post`). All have the shape of R itself, an
interactive oracle reduction (IOR, Ior/Ior.lean).
A block is an IOR with its honest side H (`IOR.Honest`, Ior/Honest.lean), taken as a part of a
chain.
`MaskData R Wi` is a structure: a type `Kc` with `kc : Wi → Kc`; a type `Xp` with `pub : Xi → Xp`;
a finite, non-empty type `Mk` with `put : Mk → Kc → Kc`; a predicate `Cl` on `Xp` and `Kc`; `msg`,
from `Kc`, `Xp` and the verifier's randomness ρ to plain parts; and `sim`, from `Xp` and ρ to
distributions on plain parts.
`H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always empty; the honest
prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under `D.put`; and
where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the distribution `D.sim xp ρ`.
In every statement of this file `MM` stands as a premise and as the conclusion.
`GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every
(x, y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. `GoodM` stands in no statement of
this file.
A block that works on messages alone is written once, on a small statement, and then set into a
large one by these constructions.
Here: if the small block has the item (Ior/Masked.lean: `H.MM D`), the large one has it, with the
same own masks, the same closed form and the same simulator; only the two readings change: what is
read of the explicit part (`pub`) and of the witness (`kc`) is what the small block read, of the
part on which it works.
Definitions, statements and proofs. No protocol, no code occurs here.
`H.MM D`, `MaskData`, `GoodM`: see their rows in the head of Ior/Masked.lean and, for the first
two, the fields' docstrings there.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names:
  `Spec.mm_keepX`, `Spec.mm_keepE`, `Spec.mm_keep`, `Spec.mm_carry`, `Spec.mm_post`: the item is
    kept.
  `Spec.mm_pre`: a step before the block: m is what the honest prover does to (explicit part,
    witness). Asked: what the block reads after the step is a function of separate readings before
    it:
      pub (m (x, w)).1 = px x and kc (m (x, w)).2 = kw w.

So a further explicit part (answers that earlier rounds have given) is not read by the simulator of
the large block either: by type, and by `MaskData.keepX`: `pub := fun a => D.pub a.1`,
`sim := D.sim`.

Limits: this file says nothing on the other fields of the bundle `GoodM`: `base` (all of `GoodT`
but zero knowledge) goes through these constructions by rules of its own
(Ior/KnowCollRulesFrame.lean); for `claim` that file has no rule.
Terms: lean/GLOSSARY.md.
-/
import Ior.Masked
import Ior.Frame

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR
variable {Xi Xi' Xo Xo' : Type}
  {Ei Ei' Eo Eo' : ExtSpec} {Wi Wi' Wo Wo' : Type} {R : IOR Xi Ei Xo Eo}

namespace MaskData

/-- the parameters with other readings of explicit part and witness, for an IOR of the same
shape -/
def keepX (D : MaskData R Wi) (Z : Type) : MaskData (R.keepX Z) Wi :=
  { Kc := D.Kc, kc := D.kc, Xp := D.Xp, pub := fun a => D.pub a.1, Mk := D.Mk, put := D.put,
    Cl := D.Cl, msg := D.msg, sim := D.sim }

def keepE (D : MaskData R Wi) (F : ExtSpec) : MaskData (R.keepE F) Wi :=
  { Kc := D.Kc, kc := D.kc, Xp := D.Xp, pub := D.pub, Mk := D.Mk, put := D.put, Cl := D.Cl,
    msg := D.msg, sim := D.sim }

@[reducible] def keep (D : MaskData R Wi) (Z : Type) (F : ExtSpec) : MaskData (R.keep Z F) Wi :=
  (D.keepX Z).keepE F

def carry (D : MaskData R Wi) (Wz : Type) : MaskData R (Wi × Wz) :=
  { Kc := D.Kc, kc := fun w => D.kc w.1, Xp := D.Xp, pub := D.pub, Mk := D.Mk, put := D.put,
    Cl := D.Cl, msg := D.msg, sim := D.sim }

def pre (D : MaskData R Wi) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei)
    (px : Xi' → D.Xp) (kw : Wi' → D.Kc) : MaskData (R.pre f g) Wi' :=
  { Kc := D.Kc, kc := kw, Xp := D.Xp, pub := px, Mk := D.Mk, put := D.put, Cl := D.Cl,
    msg := D.msg, sim := D.sim }

def post (D : MaskData R Wi) (f : Xo → Option Xo') (g : ExtMap Eo Eo') : MaskData (R.post f g) Wi :=
  { Kc := D.Kc, kc := D.kc, Xp := D.Xp, pub := D.pub, Mk := D.Mk, put := D.put, Cl := D.Cl,
    msg := D.msg, sim := D.sim }

end MaskData
end IOR

namespace Spec
open IOR

def mm_keepX : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (D : MaskData R Wi) (Z : Type),
    H.MM D → (H.keepX Z).MM (D.keepX Z)

def mm_keepE : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (D : MaskData R Wi) (F : ExtSpec),
    H.MM D → (H.keepE F).MM (D.keepE F)

/-- States: a further explicit part and further oracles are handed on: the item is kept, with the
same simulator. -/
def mm_keep : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (D : MaskData R Wi) (Z : Type) (F : ExtSpec),
    H.MM D → (H.keep Z F).MM (D.keep Z F)

def mm_carry : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (D : MaskData R Wi) (Wz : Type),
    H.MM D → (H.carry Wz).MM (D.carry Wz)

/-- A step without rounds before the block. -/
def mm_pre : Prop :=
  ∀ (Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo : Type)
      (H : R.Honest Wi Wo) (D : MaskData R Wi) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei)
      (m : Xi' × Wi' → Xi × Wi) (px : Xi' → D.Xp) (kw : Wi' → D.Kc),
    (∀ x w, D.pub (m (x, w)).1 = px x) → (∀ x w, D.kc (m (x, w)).2 = kw w) →
    H.MM D → (H.pre f g m).MM (D.pre f g px kw)

def mm_post : Prop :=
  ∀ (Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wo' : Type)
      (H : R.Honest Wi Wo) (D : MaskData R Wi) (f : Xo → Option Xo')
      (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo'),
    H.MM D → (H.post f g m).MM (D.post f g)

end Spec

open IOR

theorem mm_keepX : Spec.mm_keepX := fun _ _ _ _ _ _ _ H D _ h =>
  { noOrc := h.noOrc
    free := fun w a => h.free w a.1
    run := fun w a c ρ => by
      show ((Strat.map _ (H.strat w a.1 c)).run ρ).1.plains = D.msg (D.kc w) (D.pub a.1) ρ
      rw [Strat.run_map]
      exact h.run w a.1 c ρ
    stable := h.stable
    law := h.law }

theorem mm_keepE : Spec.mm_keepE := fun _ _ _ _ _ _ _ _ _ _ h =>
  { noOrc := h.noOrc, free := h.free, run := h.run, stable := h.stable, law := h.law }

theorem mm_keep : Spec.mm_keep := fun Xi Xo Ei Eo R Wi Wo H D Z F h =>
  mm_keepE _ _ _ _ _ _ _ _ _ F (mm_keepX Xi Xo Ei Eo R Wi Wo H D Z h)

theorem mm_carry : Spec.mm_carry := fun _ _ _ _ _ _ _ H D _ h =>
  { noOrc := h.noOrc
    free := fun w x => h.free w.1 x
    run := fun w x c ρ => by
      show ((Strat.map _ (H.strat w.1 x c)).run ρ).1.plains = D.msg (D.kc w.1) (D.pub x) ρ
      rw [Strat.run_map]
      exact h.run w.1 x c ρ
    stable := h.stable
    law := h.law }

theorem mm_pre : Spec.mm_pre := fun _ _ _ _ _ _ _ _ _ _ H D _ _ m px kw hx hw h =>
  { noOrc := h.noOrc
    free := fun w x => h.free (m (x, w)).2 (m (x, w)).1
    run := fun w x c ρ => by
      show ((H.strat (m (x, w)).2 (m (x, w)).1 c).run ρ).1.plains = D.msg (kw w) (px x) ρ
      rw [h.run, hx, hw]
    stable := h.stable
    law := h.law }

theorem mm_post : Spec.mm_post := fun _ _ _ _ _ _ _ _ _ _ H D _ _ m h =>
  { noOrc := h.noOrc
    free := h.free
    run := fun w x c ρ => by
      show ((Strat.map m (H.strat w x c)).run ρ).1.plains = D.msg (D.kc w) (D.pub x) ρ
      rw [Strat.run_map]
      exact h.run w x c ρ
    stable := h.stable
    law := h.law }

end Iop
