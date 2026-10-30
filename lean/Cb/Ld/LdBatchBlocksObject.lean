-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatchBlocksObject.lean: round-by-round knowledge soundness of a proximity test with linear
claims, run on a batch of at most N instances that share one encoded index and its record: stated
under the hypotheses that are listed under Limits.

Definitions, statements and proofs (an assembly). Conditional: the plan is a hypothesis (see
Limits). The plan without a splitting meets it under the hypotheses of `Spec.ldPlanLin_kb`
(Cb/Ld/LdBatchPlanLin.lean). Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

In standard terms:
  `LinBKnowR S Q N d0 ε` (Hiop/RecSubs.lean), the object's item on knowledge soundness, says, for
    each record, with that record in all slots: the batch protocol Q is round-by-round knowledge
    sound with the list of errors ε, on the collision-free statements whose encoded index decodes
    with the record. The extractor is fixed: it decodes the statement. The object: `LdObj`,
    Cb/Obj/LdObject.lean.
  `KnowB` (Ior/BatchSeq.lean; in words in the head of Cb/Ld/LdBatchBlocks.lean) is the form of that
    property for one reduction and the admissible vectors of at most N statements.
  A plan for a batch, `QA : LdTcA ..` (Cb/Ld/LdBatchBlocksPlan.lean), is a closing, a chain of
    annotated links, and the proof that its links are the closing's. `KB N k k'`
    (Cb/Ld/LdLinChainB.lean) says, link by link, along some keys at the joints between k and k':
    `KnowB` for the vectors on which the key, a function of the statement, is constant; and the link
    takes such vectors to such vectors.
  `O : LdOL F E` (Cb/Obj/LdObjectLin.lean) is the test's data; `O.enter`
    (Cb/Obj/LdObjectLinFull.lean) the step without rounds from the object's types to the test over a
    signature.

Main names:
  `O.fullB`: the batch protocol on the object's types: the test for linear constraints, with its
    closing as a term, over the one configuration. `O.errFB`, `O.extFB`: its errors and its
    extractor.
  `Spec.ldOLB_knowB`: `KnowB` of `O.fullB` from the object's first joint `O.P.j0 on0`, for the
    vectors with one (encoded index, record), under the hypotheses of its statement.
  `Spec.ldOLB_item`: the item. `Spec.ldOLB_item_far`: the item in the second regime.

Limits: what is still asked, in the statements' own text:
  the fields F and E are finite, and the code has a position (`Nonempty (Fin O.Cf.C₀.n)`): instance
    arguments;
  distance and radii (`HasDist O.Cf.C₀.G O.Cf.C₀.d`; `O.Cf.eM < O.Cf.C₀.d`; in the second regime
    `O.e' + O.Cf.eM < O.Cf.C₀.d`);
  `O.Fits on0` and `O.toC.P.FoldErr on0 εf` (not in the second regime);
  the layout's places are distinct (`Function.Injective O.py`);
  what the three sendings ask (`Sn.OK`);
  the plan for a batch: its closing is knowledge sound from what the core makes the slots share
    (`KB` of `O.toC.cZA QA fq` from `O.toC.P.key6`).
The rules of Cb/Ld/LdBatchBlocksPlan.lean (`Spec.ldLinB_cZ_kb`, `Spec.ldPlanB_nil`,
`Spec.ldPlanB_cons_local`, `Spec.ldPlanB_cons_shared`) give it under their own hypotheses.
No plan is chosen. This file says nothing on a splitting, and nothing on the honest side of a batch
(`LinBListR`). It does not say that the hypotheses can be met together.


It does not say how the errors of
local and of shared rounds are to be read: see the head of Cb/Ld/LdBatchBlocksPlan.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBatchBlocksPlan
import Cb.Obj.LdObjectLinFullProofs
import Cb.Obj.LdObjectLinB
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdOL
variable {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E) [Fintype F]
  [Fintype E] [Nonempty (Fin O.Cf.C₀.n)]
variable (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
  (εf N : ℕ) (QA : LdTcA O.toC.S O.toC.E₀ O.toC.Wpa) (fq : O.toC.St6 → QA.Q.St) (d : O.toC.P.W0)

/-- the test on chains for a batch, as one annotated link -/
def lkCA : LinkA Unit (O.toC.P.J0 on0) LdLinP.JT :=
  O.toC.P.linCA on0 Sn εf N (O.toC.cZA QA fq) d

/-- The test for at most N instances, over the configuration: the step, then the test; its
annotation is the test's. -/
def fullB : BIOP (O.left.Xl × O.Cf.conf.Rec) O.left.El :=
  ⟨O.enter.seq (O.lkCA on0 Sn εf N QA fq d).l.R,
    RoundSplits.app (s := O.enter.shape) PUnit.unit (O.lkCA on0 Sn εf N QA fq d).ann⟩

def errFB : Err (O.fullB on0 Sn εf N QA fq d).ior.shape :=
  Err.app (s := O.enter.shape) () (O.lkCA on0 Sn εf N QA fq d).err

def extFB (d₀ : O.P.W0) :
    O.P.X0 × O.P.E0.Str → Tr (O.fullB on0 Sn εf N QA fq d).ior.shape → Unit → O.P.W0 :=
  IOR.extSeq O.enter (O.lkCA on0 Sn εf N QA fq d).l.R (fun _ _ w => (w.1, w.2.1))
    (O.lkCA on0 Sn εf N QA fq d).l.ext d₀

end LdOL

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- States, for a code with a position (`Nonempty (Fin O.Cf.C₀.n)`), that the term
`(O.fullB ..).ior` is the one-instance test's: the step, then core and closing as one link, with the
plan's own links. -/
def ldOLB_same : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
      (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd) (εf N : ℕ)
      (QA : LdTcA O.toC.S O.toC.E₀ O.toC.Wpa) (fq : O.toC.St6 → QA.Q.St) (d : O.toC.P.W0),
    (O.fullB on0 Sn εf N QA fq d).ior = O.enter.seq (O.toC.P.linC on0 Sn εf (O.toC.cZ QA.Q fq) d).R

def ldOLB_knowB : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
      (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
      (εf N : ℕ) (QA : LdTcA O.toC.S O.toC.E₀ O.toC.Wpa) (fq : O.toC.St6 → QA.Q.St)
      (d : O.toC.P.W0) (d₀ : O.P.W0),
    O.toC.P.FoldErr on0 εf → Function.Injective O.py → Sn.OK →
    (O.toC.cZA QA fq).KB N O.toC.P.key6 ldKeyT →
    (O.fullB on0 Sn εf N QA fq d).ior.KnowB (O.fullB on0 Sn εf N QA fq d).ann N
      (SameKey fun a => (a.2.1, a.1.2)) (O.P.j0 on0).on (O.P.j0 on0).relR (fun _ (_ : Unit) => True)
      (O.extFB on0 Sn εf N QA fq d d₀) (O.errFB on0 Sn εf N QA fq d)

/-- States the item of the object, `LinBKnowR` of `O.fullB` with the errors `O.errFB`, for any
condition on0 on the index that holds wherever the item speaks (`O.Fits on0`,
Cb/Obj/LdObjectLinB.lean) and any bound εf for the fold's bad points under it
(`O.toC.P.FoldErr on0 εf`), under the further hypotheses below. -/
def ldOLB_item : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
      (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
      (εf N : ℕ) (QA : LdTcA O.toC.S O.toC.E₀ O.toC.Wpa) (fq : O.toC.St6 → QA.Q.St)
      (d : O.toC.P.W0) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d → O.Fits on0 → O.toC.P.FoldErr on0 εf →
    Function.Injective O.py → Sn.OK → (O.toC.cZA QA fq).KB N O.toC.P.key6 ldKeyT →
    LinBKnowR O.left (O.fullB on0 Sn εf N QA fq d) N d0 (O.errFB on0 Sn εf N QA fq d)

/-- The second regime: states the item at on0 := the index decodes with its record (`O.onDec`);
e' + eM below the distance; εf = 0; under the further hypotheses below. The first regime is `O.on0`
(Cb/Obj/LdObjectLin.lean): no collision of the index at the record's seed. Both conditions have
`O.Fits` (`Spec.ldOB_fits`, Cb/Obj/LdObjectLinB.lean). -/
def ldOLB_item_far : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (Sn : O.toC.P.Snd) (N : ℕ)
      (QA : LdTcA O.toC.S O.toC.E₀ O.toC.Wpa) (fq : O.toC.St6 → QA.Q.St)
      (d : O.toC.P.W0) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.e' + O.Cf.eM < O.Cf.C₀.d → Function.Injective O.py → Sn.OK →
    (O.toC.cZA QA fq).KB N O.toC.P.key6 ldKeyT →
    LinBKnowR O.left (O.fullB O.onDec Sn 0 N QA fq d) N d0 (O.errFB O.onDec Sn 0 N QA fq d)

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOLB_same : Spec.ldOLB_same F E := by
  intro O _ on0 Sn εf N QA fq d
  have h : (O.lkCA on0 Sn εf N QA fq d).l = O.toC.P.linC on0 Sn εf (O.toC.cZ QA.Q fq) d :=
    (ldLinCB_same O.toC.P on0 εf N Sn (O.toC.cZA QA fq) d).trans
      (congrArg (fun c => O.toC.P.linC on0 Sn εf c d) (ldLinB_cZ_same _ _ _ _ _ O.toC QA fq))
  show O.enter.seq (O.lkCA on0 Sn εf N QA fq d).l.R = _
  rw [h]

theorem ldOLB_knowB : Spec.ldOLB_knowB F E := by
  intro O _ on0 Sn εf N QA fq d d₀ hF hpy hS hKB
  have h2 := (ldLinB_close _ _ _ _ _ O.toC on0 εf N Sn d QA fq hF hpy hS hKB).1
  have h1 := knowB_conseq _ _ _ _ _ _ _ _ N _
    (SameKey fun a : O.P.X0 × O.P.E0.Str => (a.2.1, a.1.2)) _ _ _ _ _ _ _ _
    (knowB_pure O.P.X0 O.toC.P.X0 O.P.E0 O.toC.P.E0 O.P.W0 O.toC.P.W0 some O.enG N (O.P.j0 on0).on
      (O.P.j0 on0).relR (O.toC.P.j0 on0).relR (fun _ w => (w.1, w.2.1))
      (fun x y x' w _ hx h => by
        obtain rfl := Option.some.inj hx
        exact h))
    (fun _ _ => trivial) (fun _ h => h) (fun _ _ _ h => h) (fun _ _ h => h)
  exact knowB_seq _ _ _ _ _ _ _ _ _ O.enter (O.lkCA on0 Sn εf N QA fq d).l.R
    _ _ N _ _ _ _ _ _ _ _ _ _ _ d₀ h1 h2
    (fun a τ b h hb => by
      obtain rfl := Option.some.inj hb
      exact ⟨h.1, h.2, trivial⟩)
    (fun a ha τ => sameKey_any _ _ _ _ _ _ O.enter _ N (fun a => (a.2.1, a.1.2)) O.toC.P.k0 id (fun a τ b hb => by
      obtain rfl := Option.some.inj hb
      rfl) a ha τ)

theorem ldOLB_item :
    Spec.ldOLB_item F E := fun O _ on0 Sn εf N QA fq d d0 hd he hFit hF hpy hS hKB =>
  ldOB_know F E O on0 (O.fullB on0 Sn εf N QA fq d) N
    (O.extFB on0 Sn εf N QA fq d (fun _ _ => 0, fun _ => (fun _ => 0, fun _ => 0)))
    (O.errFB on0 Sn εf N QA fq d) d0 hd he hFit
    (ldOLB_knowB F E O on0 Sn εf N QA fq d _ hF hpy hS hKB)

theorem ldOLB_item_far : Spec.ldOLB_item_far F E := fun O _ Sn N QA fq d d0 hd he hpy hS hKB =>
  ldOLB_item F E O O.onDec Sn 0 N QA fq d d0 hd (lt_of_le_of_lt (Nat.le_add_left _ _) he)
    (ldOB_fits F E O).1 (ldOB_foldErr F E O hd he) hpy hS hKB

end
end Cb
