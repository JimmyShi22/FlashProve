-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailRngOnSeams.lean: the seams beside the draw of the matrix of a smallness test with
a condition on statements that is carried past the draw.

Johnson/Top/H/TailRngOn.lean has the kind `KTailRngOn`. Here are the two seams beside it, between
joints with their conditions, against the kind of sending that ends at such a joint (`kSendInto`,
Johnson/Top/H/SendInto.lean). Definitions, statements and proofs.

Main names:
  `tailIntoRngOn`, `tailIntoRngOn_ok`: the seam from a sending into the draw; beside `hrel` it asks
    that the condition in front of the sending gives `on` (`hon`).
  `tailBehindOn`, `tailFromRngOn`, `tailFromRngOn_ok`: the caller of the sending behind the draw,
    which starts at the joint at which the draw ends, with the condition; the seam: no premise.
  `tailHostOn`, `tailHostOn_into_ok`: at the letters of a sub-proof's frame
    (Johnson/Top/H/TailHostBase.lean) with `on` := the condition of the joint in front of the
    sending: `hon` holds by definition.

Limits: those of Johnson/Top/H/TailSeams.lean and TailHostBase.lean.
`tailHostOn_into_ok` takes a map `it` from the entries of the reads to the places of the tables. At
sizes without a table there is no such place, so the map exists only where there is no entry. The
sizes of the verifier's plan's own record, whose list of tables and list of first columns are empty,
are such sizes: the seam is meant at the sizes of a record in which the tables' shapes and the first
columns are laid.
The joint `Br` is a letter: at a `Br` whose condition no statement of a run meets, what is shown
here holds and says nothing.
No type bars a use in which the digits are counted among the messages that are fixed before the
draw: such a use is hollow.
-/
import Johnson.Top.H.TailRngOn
import Johnson.Top.H.TailHostBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop Cb IOR TWhole VerifiableInference.OnPublicFiles Cb.Sub Cb.Pv.Tail Cb.Pv.Att

/-- The seam from a sending into the draw. -/
@[reducible] noncomputable def tailIntoRngOn (d : SentCaller) (on : d.X × d.Ex.Str → Prop)
    {Kc W₀ : Type} (A₀ : Rels Kc d.X d.Ex (d.S.Msg × W₀)) (bk : d.snd.N.Msg → d.Wp → W₀) :
    StepD ((kSendInto [d.before A₀ bk]).dst (d.before A₀ bk)) (KTailRngOn.src ⟨d.caller, on⟩) :=
  seamSentP d.S d.snd.N A₀ bk (TailCallerOn.A ⟨d.caller, on⟩)

theorem tailIntoRngOn_ok (d : SentCaller) (on : d.X × d.Ex.Str → Prop) {Kc W₀ : Type}
    (A₀ : Rels Kc d.X d.Ex (d.S.Msg × W₀)) (bk : d.snd.N.Msg → d.Wp → W₀)
    (hon : ∀ a, A₀.on a → on a)
    (hrel : ∀ a w, A₀.on a → (Cb.Pv.Tail.A d.caller.letters).relR a w →
      (d.S.grow d.snd.N A₀ bk).relR a w) : (tailIntoRngOn d on A₀ bk).OK :=
  seamSentP_ok d.S d.snd.N A₀ bk _ (fun a ha => ⟨trivial, hon a ha⟩) hrel

/-- The caller of the sending behind the draw: it starts at the joint at which the draw ends. -/
@[reducible] def tailBehindOn (d : TailCallerOn) (snd : Cb.Pv.Send.Size Cb.Gl.E) (W' : Type)
    (back : snd.N.Msg → W' → d.c.Sg.Wit × d.c.Wp) : SendCaller Cb.Gl.E :=
  ⟨snd, Unit, (d.c.X × Dr d.c.s) × d.c.Sg.Smp, d.c.Sg.Wit × d.c.Wp, W', d.c.Ex.prod d.c.Sg.ext,
    d.c.Sg.over d.B, back⟩

/-- The seam from the draw to that sending: nothing is mapped. -/
@[reducible] noncomputable def tailFromRngOn (d : TailCallerOn) (snd : Cb.Pv.Send.Size Cb.Gl.E)
    (W' : Type) (back : snd.N.Msg → W' → d.c.Sg.Wit × d.c.Wp) :
    StepD (KTailRngOn.dst d)
      ((kSendInto [tailBehindOn d snd W' back]).src (tailBehindOn d snd W' back)) :=
  ⟨some, ExtMap.id _, fun _ w => w⟩

theorem tailFromRngOn_ok (d : TailCallerOn) (snd : Cb.Pv.Send.Size Cb.Gl.E) (W' : Type)
    (back : snd.N.Msg → W' → d.c.Sg.Wit × d.c.Wp) : (tailFromRngOn d snd W' back).OK where
  isLocal := fun _ _ q h => h q (Finset.mem_singleton_self q)
  onOut := fun b x' hb hx => by
    obtain rfl : b.1 = x' := Option.some.inj hx
    exact hb
  know := fun b x' w _ hx hw => by
    obtain rfl : b.1 = x' := Option.some.inj hx
    exact hw

section
variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] {s : Size} {K Xe Wp Wp₁ : Type} {Ex : ExtSpec}
  (S₁ : Sig Cb.Gl.E) (snd : Cb.Pv.Send.Size Cb.Gl.E) (bk₁ : snd.N.Msg → Wp₁ → Wp)
  (Br B' : Rels K Xe Ex (S₁.Msg × Wp)) (msg₁ : S₁.Msg → J₁ → Cb.Gl.E)
  (ent : snd.N.Msg → J₂ → Cb.Gl.E)
  (w : Xe → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → Cb.Gl.E)
  (sym : S₁.Msg → Syms Cb.Gl.E s)
  (tab : snd.N.Msg → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → Cb.Gl.E)
  (dig : Wp₁ → Dig Cb.Gl.E s)

/-- The caller at a frame's letters, with the condition of the joint in front of the sending: that
of B', and the ledger has at most n claims. -/
@[reducible] def tailHostOn (a : Xe → J₂ → Aff Cb.Gl.E J₁) (n : ℕ) : TailCallerOn :=
  ⟨(tailSentOf S₁ snd bk₁ Br msg₁ ent w sym tab dig).caller, (virtJ B' a msg₁ n).on⟩

/-- The seam into the draw at these letters: the condition passes by definition. -/
theorem tailHostOn_into_ok (hB : ∀ b v, Base (sym v.1) → Br.relR b v → B'.relR b v) (p : ℕ)
    [CharP Cb.Gl.E p] (hu : s.Uniq p) (a : Xe → J₂ → Aff Cb.Gl.E J₁) (ic : JCell s → J₁)
    (it : J₂ → JTab s) (hc : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (ha : ∀ (x : (tailHost S₁ snd bk₁ Br msg₁ ent w sym tab dig).let.X) j v,
      (a x.1 j).val v =
        (affRead (tailHost S₁ snd bk₁ Br msg₁ ent w sym tab dig).let x (it j)).val
          fun i => v (ic i))
    (ht : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2) (n : ℕ) :
    (tailIntoRngOn (tailSentOf S₁ snd bk₁ Br msg₁ ent w sym tab dig) (virtJ B' a msg₁ n).on
      (virtJ B' a msg₁ n) bk₁).OK :=
  tailIntoRngOn_ok _ _ _ _ (fun _ h => h)
    (tailHost_hrel_base S₁ snd bk₁ Br B' msg₁ ent w sym tab dig hB p hu a ic it hc ha ht n)

end

end KObj

#print axioms KObj.tailIntoRngOn_ok
#print axioms KObj.tailFromRngOn_ok
#print axioms KObj.tailHostOn_into_ok
