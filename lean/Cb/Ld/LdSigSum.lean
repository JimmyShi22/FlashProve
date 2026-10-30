-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSigSum.lean: book-keeping for composing reductions: the oracle messages that a statement has
already and a family that is newly sent are put under one index set.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdSigSumProofs.lean. Signatures, joints and "collision-free" are those of Cb/Ld/LdSig.lean.
A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core.

Why: Cb/Ld/LdSendFam.lean sends a family N from any joint A, and ends at the joint over N alone,
with A's statement nested inside. Where A is itself a joint over a signature S, a protocol needs one
signature again: S and N side by side, so that the next block (a reduction on claims about all
messages, a batching on a group with old and new members) finds one family.

Main names:
  `S.sum N`: the signature with the names S.O ⊕ N.O.
  `S.grow N A bk`: the base joint over `S.sum N` whose witnesses are the pairs (messages, w'). It
    claims the base joint A (over S) of the pair (old messages, bk (new messages) w'): a part of A's
    further witness is in the new messages.
  `S.mergeX`, `S.mergeE`, `S.mergeW`, `S.splitW`: the renaming.
  `ldSendSig S N Sd`: the sending of N (Cb/Ld/LdSendFam.lean), then the renaming: no further round.
  `Spec.sigSum_cf`, `Spec.sigSum_decs`: collision-free, and the decoder, part by part.
  `Spec.sigSum_step`: the renaming is a step without rounds (`Step`, Ior/Frame.lean) from the nested
    joint to the joint over `S.sum N`, both with the condition moved into the relaxed relation
    (`Rels.cf`, Ior/KnowCollGood.lean).
  `Spec.ldSendSig_goodT`, `Spec.ldSendSig_good`, `Spec.ldSendSig_chain` (`Good`, Ior/Chain.lean;
    `GoodT`, Ior/KnowCollGood.lean): from `S.over A` into `(S.sum N).over (S.grow N A bk)`,
    collision-free: the errors, budget and hypotheses of Cb/Ld/LdSendFam.lean; the extractor keeps
    the old pairs and applies bk to the new messages.
    (`Spec.ldSendSig_chain`: from `(S.over A).cf`.)

Limits: this file says nothing new on errors or zero knowledge: all is passed on. `S.add o` of
Cb/Ld/LdSig.lean is not identified with `S.sum (Sig.one o)`: use the latter with this file.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendFam
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

namespace Sig
variable {E : Type} (S N : Sig E)

/-- Two signatures side by side. -/
@[reducible] def sum : Sig E := { O := S.O ⊕ N.O, om := Sum.elim S.om N.om }

/-- A family over the two parts; its parts. -/
def join {T : OMsg E → Type} (s : ∀ a, T (S.om a)) (n : ∀ a, T (N.om a)) : ∀ a, T ((S.sum N).om a)
  | .inl a => s a
  | .inr a => n a
def left {T : OMsg E → Type} (t : ∀ a, T ((S.sum N).om a)) : ∀ a, T (S.om a) := fun a => t (.inl a)
def right {T : OMsg E → Type} (t : ∀ a, T ((S.sum N).om a)) : ∀ a, T (N.om a) := fun a => t (.inr a)

variable {Kc St Wp Wp' : Type} {E₀ : ExtSpec}

/-- The base joint A over S, a part of whose further witness is in the messages of N. -/
def grow (A : IOR.Rels Kc St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp) :
    IOR.Rels Kc St E₀ ((S.sum N).Msg × Wp') where
  rel  := fun st y w =>
    A.rel st y (S.left N (T := OMsg.Msg) w.1, bk (S.right N (T := OMsg.Msg) w.1) w.2)
  relR := fun a w => A.relR a (S.left N (T := OMsg.Msg) w.1, bk (S.right N (T := OMsg.Msg) w.1) w.2)
  on   := A.on
  core := fun w => A.core (S.left N (T := OMsg.Msg) w.1, bk (S.right N (T := OMsg.Msg) w.1) w.2)

/-- the extractor of the sending, on nested witnesses -/
def backN (bk : N.Msg → Wp' → Wp) : N.Msg → S.Wit × Wp' → S.Wit × Wp := fun m w => (w.1, bk m w.2)

/-- The renaming: explicit parts, oracles, witnesses. -/
def mergeX (St : Type) : (St × S.Smp) × N.Smp → Option (St × (S.sum N).Smp) := fun x =>
  some (x.1.1, S.join N (T := OMsg.Smp) x.1.2 x.2)

def mergeE (E₀ : ExtSpec) : ExtMap ((E₀.prod S.ext).prod N.ext) (E₀.prod (S.sum N).ext) where
  map := fun y => (y.1.1, S.join N (T := OMsg.Str) y.1.2 y.2)
  src := fun q => match q with
    | .inl p => {Sum.inl (Sum.inl p)}
    | .inr ⟨.inl a, x⟩ => {Sum.inl (Sum.inr ⟨a, x⟩)}
    | .inr ⟨.inr a, x⟩ => {Sum.inr ⟨a, x⟩}

def mergeW (St Wp' : Type) :
    ((St × S.Smp) × N.Smp) × (N.Wit × (S.Wit × Wp')) →
    (St × (S.sum N).Smp) × ((S.sum N).Wit × Wp') := fun a =>
  ((a.1.1.1, S.join N (T := OMsg.Smp) a.1.1.2 a.1.2),
    (S.join N (T := OMsg.Wit) a.2.2.1 a.2.1, a.2.2.2))

def splitW (Wp' : Type) : (S.sum N).Wit × Wp' → N.Wit × (S.Wit × Wp') := fun w =>
  (S.right N (T := OMsg.Wit) w.1, (S.left N (T := OMsg.Wit) w.1, w.2))

end Sig

section
variable {E : Type} [Field E] (S N : Sig E) (Sd : N.Seeds) (St : Type) (E₀ : ExtSpec)

/-- The sending of a family to a statement over S. -/
def ldSendSig :
    IOR (St × S.Smp) (E₀.prod S.ext) (St × (S.sum N).Smp) (E₀.prod (S.sum N).ext) :=
  (ldSendFam N Sd (St × S.Smp) (E₀.prod S.ext)).post (S.mergeX N St) (S.mergeE N E₀)

variable {S N} {Wp Wp' : Type}

def ldSendSigHon (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) :
    (ldSendSig S N Sd St E₀).Honest (S.Wit × Wp) ((S.sum N).Wit × Wp') :=
  (ldSendFamHon Sd (St × S.Smp) (E₀.prod S.ext) D).post
    (S.mergeX N St) (S.mergeE N E₀) (S.mergeW N St Wp')

variable (S N)

def ldSendSigNums (Kc : Type) (L t : N.O → ℕ) :
    IOR.Nums Kc (ldSendSig S N Sd St E₀) :=
  (ldSendFamNums N Sd (St × S.Smp) (E₀.prod S.ext) Kc L t).post (S.mergeX N St) (S.mergeE N E₀)

end

namespace Spec
open IOR

section
variable (E : Type) [Field E]

def sigSum_cf : Prop :=
  ∀ (S N : Sig E) (σ : (S.sum N).Smp) (y : (S.sum N).ext.Str),
    (S.sum N).CF σ y ↔
    S.CF (S.left N (T := OMsg.Smp) σ) (S.left N (T := OMsg.Str) y) ∧
    N.CF (S.right N (T := OMsg.Smp) σ) (S.right N (T := OMsg.Str) y)

def sigSum_decs : Prop :=
  ∀ (S N : Sig E) (σ : (S.sum N).Smp) (y : (S.sum N).ext.Str),
    (∀ a, (S.sum N).decs σ y (.inl a) =
      S.decs (S.left N (T := OMsg.Smp) σ) (S.left N (T := OMsg.Str) y) a) ∧
    ∀ a, (S.sum N).decs σ y (.inr a) =
      N.decs (S.right N (T := OMsg.Smp) σ) (S.right N (T := OMsg.Str) y) a

/-- The renaming is a step without rounds. -/
def sigSum_step : Prop :=
  ∀ (S N : Sig E) (Kc St Wp Wp' : Type) (E₀ : ExtSpec)
      (A : Rels Kc St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp),
    Step (S.mergeX N St) (S.mergeE N E₀) (S.mergeW N St Wp') (fun _ w => S.splitW N Wp' w)
      (N.over (N.pull (S.over A) (S.backN N bk))).cf ((S.sum N).over (S.grow N A bk)).cf

/-- Under the hypotheses below: the sending of a family leads from the joint over S into the joint
over S and the family, collision-free. -/
def ldSendSig_good : Prop :=
  ∀ (S N : Sig E) (Sd : N.Seeds) (Kc St Wp Wp' : Type) (E₀ : ExtSpec)
      (A : Rels Kc St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp)
      (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) (L t : N.O → ℕ),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws (S.backN N bk) → D.Blind Sd → D.Nn.Hides (N.budT t) →
    Good (ldSendSig S N Sd St E₀) (ldSendSigHon Sd St E₀ D) (S.over A)
      ((S.sum N).over (S.grow N A bk)).cf
      (fun _ _ w => (S.left N (T := OMsg.Wit) w.1, bk (N.msgs (S.right N (T := OMsg.Wit) w.1)) w.2))
      (ldSendSigNums S N Sd St E₀ Kc L t)

def ldSendSig_goodT : Prop :=
  ∀ (S N : Sig E) (Sd : N.Seeds) (Kc St Wp Wp' : Type) (E₀ : ExtSpec)
      (A : Rels Kc St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp)
      (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) (L t : N.O → ℕ),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws (S.backN N bk) → D.Blind Sd → D.Nn.Hides (N.budT t) →
    GoodT (ldSendSig S N Sd St E₀) (ldSendSigHon Sd St E₀ D) (S.over A)
      ((S.sum N).over (S.grow N A bk)).cf
      (fun _ _ w => (S.left N (T := OMsg.Wit) w.1, bk (N.msgs (S.right N (T := OMsg.Wit) w.1)) w.2))
      (ldSendSigNums S N Sd St E₀ Kc L t)

/-- As it enters a chain: from (S.over A).cf. -/
def ldSendSig_chain : Prop :=
  ∀ (S N : Sig E) (Sd : N.Seeds) (Kc St Wp Wp' : Type) (E₀ : ExtSpec)
      (A : Rels Kc St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp)
      (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) (L t : N.O → ℕ),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws (S.backN N bk) → D.Blind Sd → D.Nn.Hides (N.budT t) →
    GoodT (ldSendSig S N Sd St E₀) (ldSendSigHon Sd St E₀ D) (S.over A).cf
      ((S.sum N).over (S.grow N A bk)).cf
      (fun _ _ w => (S.left N (T := OMsg.Wit) w.1, bk (N.msgs (S.right N (T := OMsg.Wit) w.1)) w.2))
      (ldSendSigNums S N Sd St E₀ Kc L t)

end
end Spec
end Cb
