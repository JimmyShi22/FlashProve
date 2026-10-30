-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollGood.lean: the bundle of an IOR's properties with an extractor that may read the whole
statement and the whole transcript (`GoodT`), its rule for chains, and conditions on statements
that may fail with a bad event.

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean):
knowledge soundness with an extractor that may read the transcript.
Definitions, statements and proofs. No protocol, no code occurs here.
A statement has an explicit part, which the verifier holds, and an implicit part: oracles that it
reads by queries.

Why `GoodT`: in the bundle `Good R H A B ext P` of Ior/Chain.lean the extractor reads the implicit
part of the input statement, the oracles sent, a witness of the output statement; by type no
verifier message, no plain part, no explicit part.
Beyond unique decoding that is not enough. With a relaxation that says "some codeword within the
radius meets the claim", let the input word have two candidates within the radius, one linear claim
that the first meets and the second does not, and a second claim the other way round. A prover can
send the same oracles in both runs, with different plain parts, and be accepted on more lists of
positions than the error allows to a prover that has lost. An extractor that sees only the word and
the oracles gives one answer for both runs, and it is wrong in one. [Here an argument in words. As a
theorem, for the base case with lists: Cb/Ld/LdBaseTest.lean (`blind_fails`, `instance2_blind`),
which stands above this folder.] The extractors of the paper that this protocol builds on
(lean/CREDITS.md) go BACKWARDS, from a witness of the output statement to one of the input
statement, and some of them read verifier messages (a fold's coefficient), plain parts (a message
sent in the clear) and the explicit part. `Reduction.Know` (Ior/Know.lean) allows all that.

Main names:
  `GoodT R H A B ext P`: `Good`, field for field, but for the type of ext. Same `Rels`, same `Nums`
    (Ior/Chain.lean).
  `Spec.goodT_of_good`: a `Good` IOR is `GoodT`, with its extractor read on the transcript's
    oracles.
  `Spec.good_of_goodT`: a `GoodT` IOR whose extractor reads the implicit part, the oracles and a
    witness of the output statement only is `Good`.
  `Spec.goodT_seq`, `Spec.goodT_seq_ext`: the rule for chains: errors in a row, probabilities
    added, the composed budget, the composed extractor (in `Spec.goodT_seq`: `IOR.extSeq` of
    Ior/SeqProofs.lean; d is its value where the first verifier rejects; in `Spec.goodT_seq_ext`:
    see its docstring). No premise of its own is asked of the middle implicit instance (no
    `R₁.ImpBy io`, which `Spec.good_seq`, Ior/Chain.lean, asks), which may read verifier messages.
  `Spec.goodT_ext_congr`: an extractor is read only on the statements with `A.on`, where the
    verifier outputs a statement with a witness in `B.relR`.
  `Spec.goodT_of_det`: where the relaxed relation determines its witness.

Why `A.cf` (Ior/KnowColl.lean says for what: "collision-free"): the field `onOut` asks that every
output of a statement with `A.on` meets the condition of the next joint. A condition that fails
with a bad event is therefore moved from `on` into the relaxed relation, by a wrapper on joints;
the relations themselves are not touched (in this sense: `A.cf` has `rel := A.rel` and
`relR := Reduction.orOff A.on A.relR`: see `Rels.cf`). A chain of joints `A.cf`, `B.cf`, `C.cf` ..
composes by `goodT_seq` as it stands.

Limits: this file says nothing on the compiler: its door (CompileK/Main.lean) takes a witness map
that reads the instance and the oracles of a session; a door for a witness map that reads more is
another lot (CompileK/WideMain.lean). It says nothing on running times. The rules for batches
(Ior/Batch.lean: `SndBK`; Ior/BatchSeq.lean) are not repeated here; the `KnowB` of
Ior/BatchSeq.lean has wide extractors, of the type of `GoodT`'s.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowColl

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- R, with the honest side H, leads from A to B; the extractor may read the whole input statement
and the whole transcript. -/
structure GoodT (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R) : Prop where
  point   : Nonempty R.shape.IsPoint
  isLocal : R.IsLocal
  acc     : H.Acc A.rel B.rel
  onOut   : ∀ a τ b, A.on a → R.red.out a τ = some b → B.on b
  keeps   : ∀ w x c ρ, B.core ((H.strat w x c).run ρ).2.2 = A.core w
  prBad   : prRho H.Bad ≤ P.pBad
  cover   : ∀ w x, H.Hid w x ⊆ P.cov (A.core w)
  prCov   : ∀ k, prRho (P.cov k) ≤ P.pHid
  know    : R.red.Know A.on A.relR B.relR ext P.err
  exact   : H.Exact A.rel P.bud

/-- A joint whose condition may fail: the joint A with `on` := all statements and `relR` :=
`A.relR` enlarged by the statements outside `A.on` (`Reduction.orOff`). -/
def Rels.cf {X : Type} {E : ExtSpec} {W : Type} (A : Rels K X E W) : Rels K X E W where
  rel  := A.rel
  relR := Reduction.orOff A.on A.relR
  on   := fun _ => True
  core := A.core

end IOR

namespace Spec
open IOR

def goodT_of_good : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R),
    Good R H A B ext P → GoodT R H A B (fun a τ w => ext a.2 τ.read w) P

def good_of_goodT : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R),
    GoodT R H A B (fun a τ w => ext a.2 τ.read w) P → Good R H A B ext P

/-- The rule for chains, general form: any extractor that agrees with "the second's, then the
first's" wherever the first verifier outputs a statement. (not all hypotheses are named here: see
the statement below) -/
def goodT_seq_ext : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (ext : X₁ × E₁.Str → Tr (R₁.shape ++ R₂.shape) → W₃ → W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂),
    GoodT R₁ H₁ A B e₁ P₁ → GoodT R₂ H₂ B C e₂ P₂ →
    (∀ a (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) b w,
      R₁.red.out a τ₁ = some b → ext a (Tr.app τ₁ τ₂) w = e₁ a τ₁ (e₂ b τ₂ w)) →
    GoodT (R₁.seq R₂) (H₁.seq H₂) A C ext (P₁.seq P₂)

/-- States the rule for chains: from A to B, then from B to C, is from A to C. -/
def goodT_seq : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂) (d : W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂),
    GoodT R₁ H₁ A B e₁ P₁ → GoodT R₂ H₂ B C e₂ P₂ →
    GoodT (R₁.seq R₂) (H₁.seq H₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂)

/-- Consequence: a smaller honest input relation, a larger honest output relation; a stronger
condition at A, a weaker one at B; a larger relaxed input relation, a smaller relaxed output
relation; the same cores; weaker numbers (`Nums.Le`). -/
def goodT_conseq : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A A' : Rels K Xi Ei Wi) (B B' : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P P' : Nums K R),
    GoodT R H A B ext P → (∀ x y w, A'.rel x y w → A.rel x y w) →
    (∀ x y w, B.rel x y w → B'.rel x y w) → (∀ a, A'.on a → A.on a) → (∀ b, B.on b → B'.on b) →
    (∀ a w, A'.on a → A.relR a w → A'.relR a w) → (∀ b w, B'.relR b w → B.relR b w) →
    (∀ w, A'.core w = A.core w) → (∀ w, B'.core w = B.core w) → P.Le P' → GoodT R H A' B' ext P'

def goodT_ext_congr : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext ext' : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    (∀ a τ b w, A.on a → R.red.out a τ = some b → B.relR b w → ext' a τ w = ext a τ w) →
    GoodT R H A B ext P → GoodT R H A B ext' P

/-- States: if, on the statements of the joint A, the relaxed relation determines its witness
(A.relR a w implies w = d a), the extractor may be replaced by the decoder d of the statement. -/
def goodT_of_det : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (d : Xi × Ei.Str → Wi),
    (∀ a w, A.on a → A.relR a w → w = d a) →
    GoodT R H A B ext P → GoodT R H A B (fun a _ _ => d a) P

/-- States: a `GoodT` IOR from A to B is `GoodT` from `A.cf` to `B.cf` (it carries the condition,
by `onOut`). -/
def goodT_cf : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodT R H A B ext P → GoodT R H A.cf B.cf ext P

/-- States: `GoodT` from A to `B.cf` is equivalent to `GoodT` from `A.cf` to `B.cf`. This is how a
block that is proved "on `A.on`, into `B.on`" (its field `know` is `Reduction.KnowInto`) enters a
chain. -/
def goodT_cf_in : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodT R H A B.cf ext P ↔ GoodT R H A.cf B.cf ext P

/-- States, for the end of a chain: `GoodT` from `A.cf` to B gives `GoodT` from A to B, if every
output of a statement with `A.on` meets `B.on`. -/
def goodT_cf_out : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    (∀ a τ b, A.on a → R.red.out a τ = some b → B.on b) →
    GoodT R H A.cf B ext P → GoodT R H A B ext P

end Spec

open IOR ChainKit

theorem goodT_of_good : Spec.goodT_of_good := fun _ _ _ _ _ _ _ _ _ _ _ _ _ g =>
  ⟨g.point, g.isLocal, g.acc, g.onOut, g.keeps, g.prBad, g.cover, g.prCov, g.know, g.exact⟩

theorem good_of_goodT : Spec.good_of_goodT := fun _ _ _ _ _ _ _ _ _ _ _ _ _ g =>
  ⟨g.point, g.isLocal, g.acc, g.onOut, g.keeps, g.prBad, g.cover, g.prCov, g.know, g.exact⟩

theorem goodT_seq_ext : Spec.goodT_seq_ext := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ ext P₁ P₂ g₁ g₂ he
  exact
    { point := g₁.point.elim fun p₁ => g₂.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩
      isLocal := g₁.isLocal.seq g₂.isLocal
      acc := g₁.acc.seq g₂.acc
      onOut := by
        intro a τ c ha hc
        obtain ⟨b, hb, hc'⟩ := Option.bind_eq_some_iff.1 ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hc)
        exact g₂.onOut b _ c (g₁.onOut a _ b ha hb) hc'
      keeps := by
        intro w x c ρ
        rw [Honest.run_seq]
        exact (g₂.keeps _ _ _ _).trans (g₁.keeps _ _ _ _)
      prBad := le_trans (prRho_cyl_union_le H₁.Bad H₂.Bad) (add_le_add g₁.prBad g₂.prBad)
      cover := by
        rintro w x ρ (hρ | ⟨_, c, hc⟩)
        · exact Or.inl (g₁.cover w x hρ)
        · have h := g₂.cover _ _ hc
          rw [g₁.keeps] at h
          exact Or.inr h
      prCov := fun k =>
        le_trans (prRho_cyl_union_le (P₁.cov k) (P₂.cov k)) (add_le_add (g₁.prCov k) (g₂.prCov k))
      know := by
        intro a ha
        refine Doomed.mono _ _ ?_ (Reduction.Know.seq_ext g₁.know g₂.know g₁.onOut ext he a ha)
        intro τ h b w hb hw
        exact h b w ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hb) hw
      exact := exact_seq X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A.rel B.rel P₁.bud P₂.bud g₁.isLocal
        g₁.acc g₁.exact g₂.exact }

theorem goodT_seq : Spec.goodT_seq := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ g₁ g₂
  refine goodT_seq_ext K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂
    (IOR.extSeq R₁ R₂ e₁ e₂ d) P₁ P₂ g₁ g₂ ?_
  intro a τ₁ τ₂ b w hb
  obtain ⟨xo, hx, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact IOR.extSeq_app R₁ R₂ e₁ e₂ d a τ₁ τ₂ xo w hx

theorem goodT_conseq : Spec.goodT_conseq := by
  intro K Xi Xo Ei Eo R Wi Wo H A A' B B' ext P P' g hA hB hoA hoB hrA hrB hcA hcB hP
  exact
    { point := g.point
      isLocal := g.isLocal
      acc := fun x y w c ρ hR hρ =>
        ⟨(g.acc x y w c ρ (hA x y w hR) hρ).1, hB _ _ _ (g.acc x y w c ρ (hA x y w hR) hρ).2⟩
      onOut := fun a τ b ha hb => hoB b (g.onOut a τ b (hoA a ha) hb)
      keeps := fun w x c ρ => by rw [hcA, hcB]; exact g.keeps w x c ρ
      prBad := le_trans g.prBad hP.pBad
      cover := fun w x => by rw [hP.cov, hcA]; exact g.cover w x
      prCov := fun k => by rw [hP.cov]; exact le_trans (g.prCov k) hP.pHid
      know := (g.know.conseq hoA hrA hrB).mono_err hP.err
      exact := g.exact.elim fun S hS =>
        ⟨S, fun x y w hw ρ hρ T hT => hS x y w (hA x y w hw) ρ hρ T (hP.bud ρ T hT)⟩ }

theorem goodT_ext_congr : Spec.goodT_ext_congr := fun _ _ _ _ _ R _ _ _ A B ext ext' P he g =>
  { g with know := know_ext_congr _ _ _ _ R.red A.on A.relR B.relR ext ext' P.err he g.know }

theorem goodT_of_det : Spec.goodT_of_det := fun _ _ _ _ _ R _ _ _ A B ext P d hd g =>
  { g with know := know_of_det _ _ _ _ R.red A.on A.relR B.relR ext P.err d hd g.know }

theorem goodT_cf_in : Spec.goodT_cf_in := fun _ _ _ _ _ R _ _ _ A B ext P =>
  ⟨fun g =>
      { g with
        onOut := fun _ _ _ _ _ => trivial,
        know := (know_iff_orOff _ _ _ _ R.red A.on A.relR B.cf.relR ext P.err).1 g.know },
    fun g =>
      { g with
        onOut := fun _ _ _ _ _ => trivial,
        know := (know_iff_orOff _ _ _ _ R.red A.on A.relR B.cf.relR ext P.err).2 g.know }⟩

theorem goodT_cf : Spec.goodT_cf := fun K Xi Xo Ei Eo R Wi Wo H A B ext P g =>
  (goodT_cf_in K Xi Xo Ei Eo R Wi Wo H A B ext P).1
    { g with
      onOut := fun _ _ _ _ _ => trivial,
      know := knowInto_of_carry _ _ _ _ R.red A.on B.on A.relR B.relR ext P.err
          (fun a τ b hb ha => g.onOut a τ b ha hb) g.know }

theorem goodT_cf_out : Spec.goodT_cf_out := fun _ _ _ _ _ R _ _ _ A B ext P ho g =>
  { g with
    onOut := ho, know := (know_iff_orOff _ _ _ _ R.red A.on A.relR B.relR ext P.err).2 g.know }

end Iop
