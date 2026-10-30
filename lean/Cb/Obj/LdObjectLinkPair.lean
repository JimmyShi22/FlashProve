-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinkPair.lean: the test that two encodings hold the same index: under `Cf.OK L`,
every reduction for it with the properties `K.TailOKAt on0 on1`, with a step without rounds in front
of it, has what the holographic IOP requires, for any pair of conditions on the two encodings under
which knowledge soundness is claimed, if the IOP's own condition implies the pair (in the form
`K.FitsK on0 on1`, which asks more than that: "Main names").

Definitions, statements (in `Cb.Spec`) and proofs.
For "link", "joint" and "tail" see the head of Cb/Obj/LdObjectLink.lean.
Cb/Obj/LdObjectLink.lean joins a tail from the link's first joint to the object's two lists for the
link (`Hiop.LinkListR`, `Hiop.LinkKnowR`) at one pair of conditions: neither index has a collision
at its record's seed. The object's own condition says more of the first index: it decodes to an
index (`onEq`, Hiop/RecConf.lean). Here the join is generic in the pair (on0, on1). The terms
(`K.Tail`, `K.enter`, `K.link`, `K.hLink`, `K.nums`, `K.fi`) do not depend on the conditions and are
reused as they are.

Main names:
  `K.FitsK on0 on1`: the object's condition gives the pair: an index that decodes with its record,
    without a collision, has on0; an index without a collision has on1.
  `K.TailOKAt on0 on1 T`: T is a tail from `K.P.j0 on0 on1`, within t₀ and t₁ positions.
  `Spec.ldOlA_object`: the main statement (hypotheses and conclusion: its doc comment).

The proofs follow Cb/Obj/LdObjectLinkProofs.lean; of the four bridging facts (`Spec.ldOlA_bridge`)
only the second reads the pair (by `K.FitsK`).
At the pair (`K.free`, `K.free`) all is that of Cb/Obj/LdObjectLink.lean, by definition, but for the
premise `K.FitsK K.free K.free` of `Spec.ldOlA_bridge` and `Spec.ldOlA_object`, which holds
trivially. The link on chains with its closing at a pair: Cb/Obj/LdObjectLinkPairFull.lean. Why the
pair matters (the second regime for the first index, `K.dec0`): Cb/Obj/LdObjectLinkAt.lean, "Why".

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinkProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdCf.LinkPar
variable {F E : Type} [Field F] [Field E] [Algebra F E] {Cf : LdCf F E} (K : Cf.LinkPar)

/-- the index decodes with its record -/
def dec0 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop := fun f rec =>
  K.P.D.X.dec f rec ≠ none

variable (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop)

/-- The object's condition gives the pair. -/
def FitsK : Prop :=
  (∀ f rec, K.P.D.X.dec f rec ≠ none → ¬ K.P.D.X.Coll f rec.1 → on0 f rec) ∧
  ∀ f rec, ¬ K.P.D.X.Coll f rec.1 → on1 f rec

/-- The first joint of the link, read on two words of one alphabet. -/
def jInAt : IOR.Rels Unit K.P.X0 (twoExternalStrings Cf.C₀.n Cf.Sg) K.P.W0 where
  rel  := fun x y w => (K.P.j0 on0 on1).rel x y w
  relR := fun a w => (K.P.j0 on0 on1).relR a w
  on   := fun a => (K.P.j0 on0 on1).on a
  core := fun _ => ()

def TailOKAt (T : K.Tail) : Prop := IOR.TailTr T.Q T.H (K.P.j0 on0 on1) trivRels T.ext T.N K.P.q0

end LdCf.LinkPar

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldOlA_enter : Prop :=
  ∀ (Cf : LdCf F E) (K : Cf.LinkPar)
      (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop),
    PieceTr K.enter K.hEnter (K.jInAt on0 on1) (K.P.j0 on0 on1) (fun _ _ w => w)
      (Nums.pure Unit some K.two) K.P.q0 K.P.q0

def ldOlA_tail : Prop :=
  ∀ (Cf : LdCf F E) (K : Cf.LinkPar)
      (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop) (T : K.Tail) (d : K.P.W0),
    K.TailOKAt on0 on1 T →
    TailTr (K.link0 T) (K.hLink0 T) (K.jInAt on0 on1) trivRels (K.extT T d) (K.numsT T) K.P.q0

open Classical in
/-- The four bridging facts, from `Cf.OK L` and `K.FitsK on0 on1`. -/
def ldOlA_bridge : Prop :=
  ∀ (Cf : LdCf F E) (K : Cf.LinkPar)
      (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop) (L : ℕ),
    Cf.OK L → K.FitsK on0 on1 →
    (∀ x y w, Cf.conf.Req x y w → (K.jInAt on0 on1).rel x y (K.fi w)) ∧
    (∀ a, Cf.conf.onEq a → (K.jInAt on0 on1).on a) ∧
    (∀ a w, Cf.conf.onEq a → (K.jInAt on0 on1).relR a w → Cf.conf.ReqR a ()) ∧
    ∀ U : Finset (twoExternalStrings Cf.conf.n Cf.conf.Sg).Pos, K.P.q0 U →
      (U.filter fun p => p.isLeft).card ≤ K.t₀ ∧ (U.filter fun p => p.isRight).card ≤ K.t₁

/-- Every tail from the first joint, at a pair of conditions that the object's gives, is a link of
the object: under `Cf.OK L`, `K.FitsK on0 on1` and `K.TailOKAt on0 on1 T`, `K.link T` (the step,
then the tail T) has `LinkListR` and `LinkKnowR`. -/
def ldOlA_object : Prop :=
  ∀ (Cf : LdCf F E) (K : Cf.LinkPar)
      (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop) (T : K.Tail) (L : ℕ),
    Cf.OK L → K.FitsK on0 on1 → K.TailOKAt on0 on1 T →
    LinkListR (C := Cf.conf) (K.link T) (K.hLink T) (K.nums T) ∧
    LinkKnowR (C := Cf.conf) (K.link T) (K.nums T).err

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] [Fintype E] in
theorem ldOlA_enter : Spec.ldOlA_enter F E := by
  classical
  intro Cf K on0 on1
  refine pieceTr_pure Unit _ _ _ _ _ _ (K.jInAt on0 on1) (K.P.j0 on0 on1) some K.two (fun a => a)
    (fun _ w => w) K.P.q0 K.P.q0 ?_ ?_
  · refine { isLocal := ?_, acc := fun _ _ _ h => ⟨rfl, h⟩, onOut := ?_,
             keeps := fun _ _ => rfl, know := ?_ }
    · intro y y' q h
      have h1 := h q (Finset.mem_singleton_self q)
      rcases q with q | q
      · exact congrArg Sum.inl h1
      · exact congrArg Sum.inr h1
    · intro x y x' hon hx
      obtain rfl := Option.some.inj hx
      exact hon
    · intro x y x' w' _ hx hR
      obtain rfl := Option.some.inj hx
      exact hR
  · intro U hU
    convert hU using 1
    ext p
    rw [ldLk_mem_biUnion]
    constructor
    · rintro ⟨a, ha, hp⟩
      rw [Finset.mem_singleton.1 hp]
      exact ha
    · exact fun h => ⟨p, h, Finset.mem_singleton_self p⟩

omit [Fintype F] [Fintype E] in
theorem ldOlA_tail : Spec.ldOlA_tail F E := fun Cf K on0 on1 _ d h =>
  tailTr_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _ _ _ (ldOlA_enter F E Cf K on0 on1) h

omit [Fintype E] in
theorem ldOlA_bridge : Spec.ldOlA_bridge F E := by
  classical
  intro Cf K on0 on1 L hOK hF
  obtain ⟨ha, -, hc, hd⟩ := ldOl_bridge F E Cf K L hOK
  refine ⟨ha, fun a hon => ⟨hF.1 _ _ ?_ (Cf.free_of_isSome hon.1), hF.2 _ _ hon.2⟩, hc, hd⟩
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hon.1
  obtain ⟨-, U, hU, -⟩ := (ldCf_D F E Cf a.2.1 a.1.1 i).mp hi
  intro hn
  exact absurd (hU.symm.trans hn) (by simp)

omit [Fintype E] in
theorem ldOlA_object : Spec.ldOlA_object F E := by
  intro Cf K on0 on1 T L hOK hF hT
  obtain ⟨ha, hb, hc, hd⟩ := ldOlA_bridge F E Cf K on0 on1 L hOK hF
  exact ldObj_link Cf.conf K.P.W0 (K.link T) (K.hLink0 T) (K.jInAt on0 on1)
    (K.extT T (fun _ _ => 0, fun _ _ => 0)) (K.numsT T) K.P.q0 K.t₀ K.t₁ K.fi
    (ldOlA_tail F E Cf K on0 on1 T _ hT) ha hb hc hd

end
end Cb
