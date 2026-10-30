-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartGlueSame.lean: gluing keeps "all coefficient tables are the same at two instances"
(`SegSpec.SameAt`, Cb/Part/LdPartDef.lean; `SegSpec.glued`, Cb/Req/ReqGlue.lean).

Book-keeping for the arithmetisation: gluing merges several families of conditions into one family
on at least as many variables. The statement (`Cb.Spec.ldPartGlueSame`) and proofs. A generic
auxiliary lemma: for the field `reply` of `LdPartD.Props`, at a partition that is given in glued
form. The glued form of a segment has one family of identities and one family of keys for each
table. A coefficient table is `Term.coef` (Cb/Req/ReqSpec.lean): a function of the instance and the
vertex.

Main names:
  `Spec.ldPartGlueSame`: S.SameAt x x' ⇒ S.glued.SameAt x x'.

Why: the four steps of gluing (more variables; a public factor; a public table; side by
side) change a coefficient table by reading it at other vertices or by a factor that does not read
the instance; the tables that gluing adds do not read the instance.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartDef
import Cb.Req.ReqGlue

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset

def Spec.ldPartGlueSame : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (S : SegSpec X F E) (x x' : X),
    S.SameAt x x' → S.glued.SameAt x x'

section
variable {X E : Type} {x x' : X}

theorem Atom.to_sameAt (a : Atom X E) (N v : ℕ) (h : a.SameAt x x') : (a.to N v).SameAt x x' := by
  cases a with
  | base _ => exact trivial
  | sum w P =>
    intro t ht
    obtain ⟨t0, h0, rfl⟩ := List.mem_map.1 (show t ∈ P.terms.map (Term.low P.v) from ht)
    exact fun b => h t0 h0 _

theorem Fam.to_sameAt (f : Fam X E) (N : ℕ) (h : f.SameAt x x') : (f.to N).SameAt x x' := by
  refine ⟨fun t ht => ?_, fun j hj => Atom.to_sameAt _ N f.v (h.2 j hj)⟩
  obtain ⟨t0, h0, rfl⟩ := List.mem_map.1 (show t ∈ f.terms.map (Term.low f.v) from ht)
  exact fun b => h.1 t0 h0 _

theorem Fam.mask_sameAt [Mul E] (c : X → ℕ → E) (hc : ∀ b, c x b = c x' b)
    (f : Fam X E) (h : f.SameAt x x') : (f.mask c).SameAt x x' := by
  refine ⟨fun t ht => ?_, h.2⟩
  obtain ⟨t0, h0, rfl⟩ := List.mem_map.1
    (show t ∈ f.terms.map (fun t => (⟨fun x b => c x b * t.coef x b, t.atoms⟩ : Term X E)) from ht)
  intro b
  show c x b * t0.coef x b = c x' b * t0.coef x' b
  rw [hc b, h.1 t0 h0 b]

theorem Fam.pub_sameAt [Zero E] (v : ℕ) (c : X → ℕ → E) (hc : ∀ b, c x b = c x' b) :
    (Fam.pub v c).SameAt x x' := by
  refine ⟨fun t ht => ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  rw [List.mem_singleton.1 (show t ∈ [(⟨c, []⟩ : Term X E)] from ht)]
  exact hc

theorem Fam.add_sameAt (f g : Fam X E) (hf : f.SameAt x x') (hg : g.SameAt x x') :
    (Fam.add f g).SameAt x x' := by
  refine ⟨fun t ht => ?_, fun j hj => ?_⟩
  · rcases List.mem_append.1
      (show t ∈ f.terms ++ g.terms.map (fun t => (⟨t.coef, t.atoms.map (· + f.na)⟩ : Term X E))
        from ht) with h1 | h1
    · exact hf.1 t h1
    · obtain ⟨t0, h0, rfl⟩ := List.mem_map.1 h1
      exact hg.1 t0 h0
  · show (if j < f.na then f.atom j else g.atom (j - f.na)).SameAt x x'
    have hj' : j < f.na + g.na := hj
    split
    · rename_i h1
      exact hf.2 j h1
    · exact hg.2 _ (by omega)

theorem glueFrom_sameAt [Zero E] [One E] [Mul E] (N V : ℕ) :
    ∀ (i : ℕ) (L : List (Fam X E)), (∀ f ∈ L, f.SameAt x x') → (glueFrom N V i L).SameAt x x'
  | _, [], _ => Fam.pub_sameAt N _ fun _ => rfl
  | i, f :: L, h =>
    Fam.add_sameAt _ _
      (Fam.mask_sameAt (x := x) (x' := x') _ (fun _ => rfl) _
        (Fam.to_sameAt f N (h f List.mem_cons_self)))
      (glueFrom_sameAt N V (i + 1) L fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem Fam.glue_sameAt [Zero E] [One E] [Mul E] (pad : E)
    (L : List (Fam X E)) (h : ∀ f ∈ L, f.SameAt x x') : (Fam.glue pad L).SameAt x x' :=
  Fam.add_sameAt _ _ (Fam.pub_sameAt _ _ fun _ => rfl) (glueFrom_sameAt _ _ 0 L h)

end

theorem ldPartGlueSame : Spec.ldPartGlueSame := by
  classical
  intro X F E _ _ _ S x x' h
  refine ⟨fun f hf => ?_, fun k hk => ?_⟩
  · rw [List.mem_singleton.1 (show f ∈ [Fam.glue 0 S.idn] from hf)]
    exact Fam.glue_sameAt 0 S.idn h.1
  · obtain ⟨T, _, rfl⟩ := List.mem_map.1
      (show k ∈ (S.keys.map (·.2)).dedup.map (fun T =>
          (Fam.glue (algebraMap F E (T.t 0)) ((S.keys.filter fun k => decide (k.2 = T)).map (·.1)),
            T)) from hk)
    refine Fam.glue_sameAt _ _ fun f hf => ?_
    obtain ⟨k0, h0, rfl⟩ := List.mem_map.1 hf
    exact h.2 k0 (List.mem_filter.1 h0).1

end Cb
