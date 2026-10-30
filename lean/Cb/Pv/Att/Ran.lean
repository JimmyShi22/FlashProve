-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/Ran.lean: the joint behind a block, on the statements that a run of the block puts out;
and that every statement which a chain (Cb/Pv/Att/Chain.lean) puts out is the last statement of a
run that is given stage by stage.

Definitions, statements and proofs. A sumcheck's output holds a public state of its own, at which
its claims are read. On the output of a run that state is the claim's. A premise on "every last
statement" would speak also of statements in which that state is another. So whoever follows a block
may want to know that the statement in front of him was put out by a run. That costs nothing: in
`KnowAt` (Cb/G6/Cut.lean) the clause on knowledge soundness does not read the condition of the joint
behind the block.

Main names:
  `ranJ R A B`: the joint B, with the condition: B's, and the statement is put out by R at some
    statement with A's condition and some transcript.
  `knowAt_ran`: `KnowAt R A B ext ε` gives `KnowAt R A (ranJ R A B) ext ε`.
  `RunOf R A b`: b is put out by R at some statement with A's condition and some transcript.
    `knowAt_into`: from B to another joint B' behind the block, with the run in hand in both
    premises. `withRun R A pr A0`: a joint A0 read through pr, with the run in the condition.
  `c.cut Ex τ`: a transcript of `c.R Ex`, cut into a transcript for each stage (`c.Trs`,
    Cb/Pv/Att/ChainRun.lean).
  `Ch.val_cut`: `c.val Ex` (Cb/Pv/Att/ChainVal.lean) on τ is `c.run` on the cut transcript.
  `Ch.out_run`: if every pick is lawful (`c.FixOK`), whatever `c.R Ex` puts out at (x, y) on τ is
    (`c.run x (c.cut Ex τ)`, y).
  `Ch.ran_on`: so the condition of `ranJ` behind a chain gives x and ts with: the statement is
    `c.run x ts`, and A0's condition holds at x.

Limits: nothing new on soundness. Nothing on an honest prover or on zero knowledge.
-/
import Cb.Pv.Att.ChainLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole TWhole.G9 Johnson.L5.Layers Cb.Pv.Lay

/-- The joint B, on the statements that a run of R puts out. -/
def ranJ {K X X' W W' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo) (A : Rels K X Ei W)
    (B : Rels K X' Eo W') : Rels K X' Eo W' :=
  ⟨B.rel, B.relR, fun b => B.on b ∧ ∃ a τ, A.on a ∧ R.red.out a τ = some b, B.core⟩

/-- The run goes into the condition of the joint behind the block. -/
theorem knowAt_ran {K M X X' Wp Wp' : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo}
    {A : Rels K X Ei (M × Wp)} {B : Rels K X' Eo (M × Wp')}
    {ext : M → X × Ei.Str → Tr R.shape → Wp' → Wp} {ε : Err R.shape} (h : KnowAt R A B ext ε) :
    KnowAt R A (ranJ R A B) ext ε :=
  ⟨h.point, h.isLocal, fun a τ b ha hb => ⟨h.onOut a τ b ha hb, a, τ, ha, hb⟩, h.know⟩

/-- The statement b is put out by a run of R at a statement with A's condition. -/
def RunOf {K X X' W : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo) (A : Rels K X Ei W)
    (b : X' × Eo.Str) : Prop := ∃ a τ, A.on a ∧ R.red.out a τ = some b

/-- To another joint behind the block, with the run in hand in both premises. -/
theorem knowAt_into {K M X X' Wp Wp' : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo}
    {A : Rels K X Ei (M × Wp)} {B B' : Rels K X' Eo (M × Wp')}
    {ext : M → X × Ei.Str → Tr R.shape → Wp' → Wp} {ε : Err R.shape} (g : KnowAt R A B ext ε)
    (hon : ∀ b, B.on b → RunOf R A b → B'.on b)
    (hrel : ∀ b w, B.on b → RunOf R A b → B'.relR b w → B.relR b w) : KnowAt R A B' ext ε where
  point := g.point
  isLocal := g.isLocal
  onOut := fun a τ b ha hb => hon b (g.onOut a τ b ha hb) ⟨a, τ, ha, hb⟩
  know := fun m a ha =>
    Doomed.mono _ _ (fun τ hτ b w hb hw =>
      hτ b w hb (hrel b (m, w) (g.onOut a τ b ha hb) ⟨a, τ, ha, hb⟩ hw)) (g.know m a ha)

/-- A joint A0 read through pr, with the run in the condition. -/
def withRun {K X X' X0 W W' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo) (A : Rels K X Ei W)
    (pr : X' → X0) (A0 : Rels K X0 Eo W') : Rels K X' Eo W' :=
  ⟨fun x y w => A0.rel (pr x) y w, fun b w => A0.relR (pr b.1, b.2) w,
    fun b => A0.on (pr b.1, b.2) ∧ RunOf R A b, A0.core⟩

variable {E : Type} [Field E] [Fintype E] {M : Type}

namespace Ch

/-- A transcript of the whole chain, cut into a transcript for each stage. -/
noncomputable def cut (Ex : ExtSpec) : {X : Type} → (c : Ch E M X) → Tr (c.R Ex).shape → c.Trs
  | _, .done _, _ => ()
  | _, .ride Y n _ _ _ _ _ next, τ =>
    (Tr.fst (s := shapeRN Y n) τ, next.cut Ex (Tr.snd (s := shapeRN Y n) τ))
  | _, .draw D _ _ next, τ =>
    (IOR.drawn (Tr.fst (s := [drawRound D.D]) τ), next.cut Ex (Tr.snd (s := [drawRound D.D]) τ))
  | _, .send n D _ _ _ next, τ =>
    ((sent (Tr.fst (s := [sendRound E (Fin n) D.D]) τ),
        drawnS (Tr.fst (s := [sendRound E (Fin n) D.D]) τ)),
      next.cut Ex (Tr.snd (s := [sendRound E (Fin n) D.D]) τ))

/-- The chain's function on a transcript is the run on the cut transcript. -/
theorem val_cut (Ex : ExtSpec) : ∀ {X : Type} (c : Ch E M X) (x : X) (y : Ex.Str)
    (τ : Tr (c.R Ex).shape), c.val Ex (x, y) τ = (c.run x (c.cut Ex τ), y)
  | _, .done _, _, _, _ => rfl
  | _, .ride Y n _ _ _ _ _ next, _, y, τ => val_cut Ex next _ y (Tr.snd (s := shapeRN Y n) τ)
  | _, .draw D _ _ next, _, y, τ => val_cut Ex next _ y (Tr.snd (s := [drawRound D.D]) τ)
  | _, .send n D _ _ _ next, _, y, τ =>
    val_cut Ex next _ y (Tr.snd (s := [sendRound E (Fin n) D.D]) τ)

/-- Whatever the chain's verifier puts out is the last statement of a run. -/
theorem out_run (Ex : ExtSpec) {X : Type} (c : Ch E M X) (h : c.FixOK) (x : X) (y : Ex.Str)
    (τ : Tr (c.R Ex).shape) (b : c.End × Ex.Str) (hb : (c.R Ex).red.out (x, y) τ = some b) :
    b = (c.run x (c.cut Ex τ), y) := by
  rw [tot Ex c h (x, y) τ] at hb
  exact (Option.some.inj hb).symm.trans (val_cut Ex c x y τ)

/-- What the condition of `ranJ` behind a chain gives. -/
theorem ran_on (Ex : ExtSpec) {X Kc X0 Wp : Type} (c : Ch E M X) (h : c.FixOK)
    (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0) (G : X → M → Prop)
    (B : Rels Kc c.End Ex (M × Wp)) (e : c.End) (y : Ex.Str)
    (he : (ranJ (c.R Ex) (jt A0 pr G) B).on (e, y)) :
    ∃ x ts, e = c.run x ts ∧ A0.on (pr x, y) := by
  obtain ⟨_, a, τ, ha, hb⟩ := he
  have e1 := out_run Ex c h a.1 a.2 τ (e, y) hb
  have e2 : y = a.2 := congrArg Prod.snd e1
  exact ⟨a.1, c.cut Ex τ, congrArg Prod.fst e1, e2 ▸ ha⟩

end Ch
end Cb.Pv.Att
