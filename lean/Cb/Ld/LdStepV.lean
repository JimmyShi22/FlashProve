-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdStepV.lean: batch proofs: a step in which no message is sent, run for N instances.

Definitions, statements (each a `Prop` in `Iop.Spec`) and proofs. Generic: no protocol, no code
occurs here.

Why: a test over a configuration starts with a step without rounds that brings the statement into
the form in which the test is built. In a batch that step is also where what the shared part holds
changes its type: from the object's private input for the shared oracle to what the test's shared
part works with.
The shared part is one for all slots of the batch; what it holds goes from `W0` to `W0'` by the
argument `s` of `IOR.stepV`.
`IOR.stepV` is used in `LdOL.lvE` (Cb/Obj/LdObjectOnBTerm.lean), the step before the test for linear
constraints on the encoded index at N instances. There the object is `O`, `W0` is `O.Cf.conf.PIdx`
and `s` is `O.shIn`.

Main names:
  `IOR.stepV f g m s`: the honest side of the step `IOR.pure f g` in a batch (`HonestV`,
    Ior/LinkV.lean): nobody speaks, there are no coins, nothing is withheld; a slot goes on with m
    (explicit part, witness), the shared part with s (what it holds).
  `Spec.stepV_wh`: nothing is withheld.
  `Spec.stepV_piece`: it is a piece of a chain of batch links (`PieceV`, Ior/LinkVBears.lean), at
    the budget that asks nothing, if: the step is local; on the link's relation the verifier's step
    is the honest prover's and leads into the next relation; what follows needs of the old oracles
    no more than the demand allows.
  `Spec.idx_pre`: a link that does not read an oracle and hands it on (`KeepsAt`,
    Cb/Ld/LdLinBData.lean) and whose annotation is coherent, then a link with `a'.Idx e' t`, has
    `Idx e t`: coherent annotation, nothing of the oracle survives, the positions read in it are a
    function of the shared verifier messages, at most t.

Notation: `f`, `g`: the step's maps, on explicit parts (`Xi → Option Xo`) and on oracles
(`ExtMap Ei Eo`); `N`: the number of slots; `Ri`: the link's relation; `Ro`: the next relation;
`qi`, `qo`: predicates on families of sets of positions, one set for each slot (`QFam`,
Ior/LinkVBears.lean); `a`, `a'`: links with what a batch needs (`LinkA`, Cb/Ld/LdLinChainB.lean);
`e`, `e'`: families of positions, of A's and of B's oracles (`ι → A.E.Pos`, `ι → B.E.Pos`); `d`: a
witness of A (`A.W`), an argument of `LinkA.seq`.

Limits: this file says nothing on soundness. A step is a link with the empty shape:
Ior/BatchSeq.lean's knowB_local takes it.

Terms: lean/GLOSSARY.md: step without rounds, link (the sense of Ior/), slot (of a batch), honest
side, annotation, configuration, batch, demand.
-/
import Cb.Ld.LdLinBData
import Cb.Ld.LdLinChainV

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo W0 W0' : Type}

/-- The honest side of a step without rounds, in a batch. -/
def stepV (f : Xi → Option Xo) (g : ExtMap Ei Eo) (m : Xi × Wi → Xo × Wo) (s : W0 → W0') :
    (IOR.pure f g).HonestV (PUnit.unit : RoundSplits (IOR.pure f g).shape) W0 Wi W0' Wo where
  Coin0 := Unit
  Coin := Unit
  strat0 := fun w0 _ => s w0
  strat := fun _ _ x w _ => m (x, w)
  Bad := ∅
  stop0 := fun _ => false

end IOR

namespace Spec
open IOR

def stepV_wh : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo W0 W0' : Type) (f : Xi → Option Xo) (g : ExtMap Ei Eo)
      (m : Xi × Wi → Xo × Wo) (s : W0 → W0'),
    (stepV f g m s).withheld = ∅

/-- Under the hypotheses below: a step without rounds is a piece of a chain of batch links. -/
def stepV_piece : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo W0 W0' : Type) (f : Xi → Option Xo) (g : ExtMap Ei Eo)
      (m : Xi × Wi → Xo × Wo) (s : W0 → W0') (N : ℕ) (Ri : Xi → Ei.Str → W0 × Wi → Prop)
      (Ro : Xo → Eo.Str → W0' × Wo → Prop) (qi : QFam Ei N) (qo : QFam Eo N),
    (IOR.pure f g).IsLocal →
    (∀ x y w,
      Ri x y w → f x = some (m (x, w.2)).1 ∧ Ro (m (x, w.2)).1 (g.map y) (s w.1, (m (x, w.2)).2)) →
    (∀ J Us Vs, qo J Us → (∀ j p, p ∈ Vs j ↔ ∃ u ∈ Us j, p ∈ g.src u) → qi J Vs) →
    PieceV (IOR.pure f g) PUnit.unit (stepV f g m s) N Ri Ro (fun _ _ _ => True) qi qo

/-- A link that hands the oracle on, then a link that reads it at few shared positions and drops it.
-/
def idx_pre : Prop :=
  ∀ (K ι : Type) (A B C : Joint K) (a : LinkA K A B) (a' : LinkA K B C) (d : A.W) (e : ι → A.E.Pos)
      (e' : ι → B.E.Pos) (t : ℕ),
    a.l.R.KeepsAt e e' → a.ann.Coherent → a'.Idx e' t → (a.seq a' d).Idx e t

end Spec

open IOR

theorem stepV_wh : Spec.stepV_wh := fun _ _ _ _ _ _ _ _ _ _ _ _ =>
  Set.eq_empty_of_forall_notMem fun _ h => h.elim (fun h => h) fun h => Bool.noConfusion h

theorem ldk_mem_need_step {Xi Xo : Type} {Ei Eo : ExtSpec} (f : Xi → Option Xo) (g : ExtMap Ei Eo)
    (ρ : Rho (IOR.pure f g).shape) (U : Finset Eo.Pos) (p : Ei.Pos) :
    p ∈ (IOR.pure f g).need ρ U ↔ ∃ u ∈ U, p ∈ g.src u := by
  classical
  rw [mem_need, mem_given]
  constructor
  · rintro ((h | ⟨r, _, h⟩) | h)
    · exact absurd h (Finset.notMem_empty _)
    · exact absurd h (Finset.notMem_empty _)
    · exact h
  · exact Or.inr

theorem stepV_piece : Spec.stepV_piece := by
  classical
  intro Xi Xo Ei Eo Wi Wo W0 W0' f g m s N Ri Ro qi qo hl hacc hq
  have hw : ∀ ρ, ρ ∉ (stepV (W0 := W0) (W0' := W0') f g m s).withheld := fun ρ h => by
    rw [stepV_wh] at h
    exact h
  refine ⟨hl,
    fun x y w c ρ hR _ => hacc x y w hR,
    ⟨fun J _ _ Ts _ => PMF.pure fun j => some ((IOR.pure f g).view (Ts j) ()),
      fun w0 J as _ ρ Ts _ => ?_⟩,
    fun J ρ Us hU => ⟨trivial, hq J Us _ hU fun j p => ldk_mem_need_step f g _ _ p⟩⟩
  have e : (fun (c : Unit × (Fin N → Unit)) => fun j : J =>
      if ρ.slot j.1 ∈ (stepV (W0 := W0) (W0' := W0') f g m s).withheld then none
      else
        some ((IOR.pure f g).view (Ts j)
            (((stepV (W0 := W0) (W0' := W0') f g m s).one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run
              (ρ.slot j.1)).1)) =
      fun _ =>
        fun j : J =>
          some ((IOR.pure f g).view (Ts j) ()) := funext fun c => funext fun j => if_neg (hw _)
  exact (congrArg (fun G => (unif (Unit × (Fin N → Unit))).map G) e).trans (PMF.map_const _ _)

theorem idx_pre : Spec.idx_pre := by
  intro K ι A B C a a' d e e' t hk hc h
  have hr : ∀ (ρ : Rho (a.l.R.shape ++ a'.l.R.shape)) j,
      e j ∈ (a.seq a' d).l.R.extReads ρ ↔
      e' j ∈ a'.l.R.extReads (Rho.snd (s := a.l.R.shape) ρ) := by
    intro ρ j
    show e j ∈ (a.l.R.seq a'.l.R).extReads ρ ↔ _
    rw [mem_seq_extReads]
    constructor
    · rintro (h1 | ⟨q, hq, hs⟩)
      · exact absurd h1 (hk.quiet _ j)
      · rw [(hk.src _ q j).1 hs] at hq
        exact hq
    · exact fun h1 => Or.inr ⟨_, h1, (hk.src _ _ j).2 rfl⟩
  refine ⟨RoundSplits.app_coherent hc h.coh, fun ρ q j hj => ?_, fun ρ ρ' j hρ => ?_, fun ρ S hS => ?_⟩
  · obtain ⟨q', hq', hs⟩ := (mem_seq_srcE a.l.R a'.l.R ρ q (e j)).1 hj
    rw [(hk.src _ q' j).1 hs] at hq'
    exact h.drop _ q j hq'
  · rw [hr, hr]
    refine h.shared _ _ j ?_
    rw [← RhoSh.sndA_sh a.ann a'.ann ρ, ← RhoSh.sndA_sh a.ann a'.ann ρ']
    exact congrArg _ hρ
  · exact h.few (Rho.snd (s := a.l.R.shape) ρ) S fun j hj => (hr ρ j).1 (hS j hj)

end Iop
