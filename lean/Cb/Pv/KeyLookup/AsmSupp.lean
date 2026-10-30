-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/AsmSupp.lean: whatever the assembled lookup's verifier puts out, its rows and its
claims' mask forms are 0 outside a set G of
entries, if each stretch keeps that property of the state.

It imports Cb/Pv/KeyLookup/Asm.lean and the library (`SuppIn`, `RowsSupp`: Cb/Ld/LdLkpSupp.lean;
`IOR.seq_out`); no file of the port.

Why «whatever the verifier puts out». The state at the joints is a flat record whose forms are free
fields: of an arbitrary state nothing can be
said. So the property is an invariant along the outputs of the reductions, not a statement on all
states.

  `Inv R P Q`     whenever the verifier of R outputs x' from x, and P x, then Q x'. Rules:
                  `Inv.seq`, `Inv.post`.
  `A.SuppX G x`   every form in the state x (of all, run, roots, planes, top, cls, and of each row)
                  is 0 outside G.
  `B.Supp G`      what is asked of the letters: head puts out states with `SuppX G`; each other
                  block keeps it.
  `lam1_supp`     B.Supp G, and every cell of a live plane lies in G ⇒ for all st y τ o:
                  B.lam1.R.out st y τ = some o →
                  RowsSupp G o.2.2 ∧ ∀ i, SuppIn G (o.2.1 i).mf.
Nothing on an honest side; nothing on which places a stretch names: that is each stretch's own lemma
(«every place that the stretch names lies in G ⇒ its block keeps SuppX G»).

-/
import Cb.Pv.KeyLookup.Asm
import Cb.Ld.LdLkpSupp
import Cb.Ld.LdWfPre

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn Finset

/-- An invariant along the verifier's outputs. -/
def Inv {X₁ X₂ : Type} {E₁ E₂ : ExtSpec} (R : IOR X₁ E₁ X₂ E₂) (P : X₁ → Prop) (Q : X₂ → Prop) :
    Prop :=
  ∀ x y τ x', R.out x y τ = some x' → P x → Q x'

theorem Inv.seq {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃}
    {P : X₁ → Prop} {Q : X₂ → Prop} {T : X₃ → Prop} (h₁ : Inv R₁ P Q) (h₂ : Inv R₂ Q T) :
    Inv (R₁.seq R₂) P T := by
  intro x y τ x' h hP
  obtain ⟨x₂, hx, hx'⟩ := Option.bind_eq_some_iff.1 ((seq_out R₁ R₂ x y τ).symm.trans h)
  exact h₂ _ _ _ _ hx' (h₁ _ _ _ _ hx hP)

theorem Inv.post {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {R : IOR X₁ E₁ X₂ E₂} {P : X₁ → Prop}
    {Q : X₂ → Prop} {T : X₃ → Prop} (h : Inv R P Q) (f : X₂ → Option X₃) (g : ExtMap E₂ E₃)
    (hf : ∀ x x', f x = some x' → Q x → T x') : Inv (R.post f g) P T := by
  intro x y τ x' hx hP
  obtain ⟨x₂, h1, h2⟩ := Option.bind_eq_some_iff.1 (show (R.out x y τ).bind f = some x' from hx)
  exact hf _ _ h2 (h _ _ _ _ h1 hP)

theorem Inv.pre {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {R : IOR X₂ E₂ X₃ E₃} {P : X₁ → Prop}
    {Q : X₂ → Prop} {T : X₃ → Prop} (h : Inv R Q T) (f : X₁ → Option X₂) (g : ExtMap E₁ E₂)
    (hf : ∀ x x', f x = some x' → P x → Q x') : Inv (R.pre f g) P T := by
  intro x y τ x' hx hP
  obtain ⟨x₂, h1, h2⟩ :=
    Option.bind_eq_some_iff.1 (show (f x).bind (fun x₁ => R.out x₁ (g.map y) τ) = some x' from hx)
  exact h _ _ _ _ h2 (hf _ _ h1 hP)

variable {E : Type} [Field E] [Fintype E]

/-- Every form in the state is 0 outside G. -/
structure Dat.SuppX (A : Dat E) (G : A.J → Prop) (x : A.XS) : Prop where
  all    : SuppIn G x.all.mf
  run    : SuppIn G x.run.mf
  roots  : ∀ i, SuppIn G (x.roots i).mf
  planes : ∀ j, SuppIn G (x.planes j).mf
  top    : SuppIn G x.top.mf
  cls    : ∀ i, SuppIn G (x.cls i).mf
  rows   : RowsSupp G x.rows

/-- The state right after the first draw has no form but 0. -/
theorem Dat.suppX_ini (A : Dat E) (G : A.J → Prop) (st : A.St) (al : E) : A.SuppX G (A.ini st al) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ =>
      rfl,
    fun _ h => absurd h (List.not_mem_nil)⟩

/-- The row on the counts is 0 outside G if every cell of a live plane lies in G. -/
theorem Dat.supp_numRow (A : Dat E) (G : A.J → Prop) (hc : ∀ u j, j < A.pl → G (A.bAt u j)) :
    SuppIn G A.numRow.cf := by
  intro i hi
  show (∑ u ∈ range (2 ^ A.d), ∑ j ∈ range A.pl, if A.bAt u j = i then (2 : E) ^ j else 0) = 0
  refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun j hj => if_neg fun e => hi ?_
  rw [← e]
  exact hc u j (Finset.mem_range.1 hj)

namespace Bks
variable {A : Dat E} {Ex : ExtSpec} (B : Bks A Ex)

/-- What is asked of the letters. -/
structure Supp (G : A.J → Prop) : Prop where
  head  : Inv B.head.R (fun _ => True) (A.SuppX G)
  parts : Inv B.parts.R (A.SuppX G) (A.SuppX G)
  join  : Inv B.join.R (A.SuppX G) (A.SuppX G)
  keys  : Inv B.keys.R (A.SuppX G) (A.SuppX G)
  table : Inv B.table.R (A.SuppX G) (A.SuppX G)
  clo   : Inv B.clo.R (A.SuppX G) (A.SuppX G)
  zero  : Inv B.zero.R (A.SuppX G) (A.SuppX G)
  bits  : Inv B.bits.R (A.SuppX G) (A.SuppX G)

theorem chn_supp (G : A.J → Prop) (h : B.Supp G) : Inv B.chn.R (fun _ => True) (A.SuppX G) :=
  (((((((h.head.seq h.parts).seq h.join).seq h.keys).seq h.table).seq h.clo).seq h.zero).seq h.bits)

/-- Whatever the lookup's verifier puts out is 0 outside G. -/
theorem lam1_supp (G : A.J → Prop) (h : B.Supp G) (hc : ∀ u j, j < A.pl → G (A.bAt u j)) :
    ∀ st y τ o, B.lam1.R.out st y τ = some o →
      RowsSupp G o.2.2 ∧ ∀ i, SuppIn G (o.2.1 i).mf := by
  intro st y τ o ho
  refine ((B.chn_supp G h).post (fun x => some (A.rd x)) (ExtMap.id Ex)
    (T := fun o : A.Out => RowsSupp G o.2.2 ∧ ∀ i, SuppIn G (o.2.1 i).mf) ?_) st y τ o ho trivial
  intro x o' e hx
  obtain rfl := Option.some.inj e
  refine ⟨fun r hr => ?_, fun i => hx.cls i⟩
  rcases List.mem_append.1 hr with hr | hr
  · exact hx.rows r hr
  · rw [List.mem_singleton.1 hr]
    exact A.supp_numRow G hc

end Bks
end Lk6

#print axioms Lk6.Bks.lam1_supp
