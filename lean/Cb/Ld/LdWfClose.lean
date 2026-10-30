-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfClose.lean: book-keeping between two forms of a preamble's properties, from the bundle of
its chain (over oracle messages with samples) to its parameter list.

A preamble is built as a chain of reductions, and its properties are proved step by step.
Hiop/RecSubs.lean asks for them in another form, in two parts (next paragraph). This file has the
chain's last step, which has no rounds: it re-brackets the explicit part and cuts the honest
prover's witness down (4. below). It also has the rule that, under the hypotheses told under
"Limits:", turns the chain's properties into that form.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdWfCloseProofs.lean.
One rule for both preambles (weights-formedness, a request). No protocol occurs here. The bundle is
`GoodT` (Ior/KnowCollGood.lean).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Hiop/RecSubs.lean defines two things that are required of a preamble: its list without knowledge
soundness (`PreListR`) and its item on knowledge soundness (`PreKnowR`: on the statements named,
into the collision-free statements of the constraint relation). Both are about "what a preamble
leaves" (Hiop/RecConf.lean: `ConfigurationWithOutOfDomainSample.Left`). A preamble is built as a chain of blocks whose joints are
`(S.over B).cf` (Cb/Ld/LdSig.lean; Ior/KnowCollGood.lean): S the signature of the oracle messages
sent so far, B a base joint in which the encoded index is a further oracle, its record a part of the
explicit part. This file joins the two forms.

Main names (2., 3.: sections of definitions below; then the statements):
 2. `sigLeft C S Cl holds`: what a preamble leaves, for a signature (its fields: see `sigLeft`
    below); "is the encoding of" (`aEnc`) is `S.Enc` (a relation: words are sent in a format).
 3. `idxRels C P PR`: the base joint of a preamble: explicit part (st, record), further oracle: the
    encoded index, witness (messages, prover encoded index). Exact: the index is the encoding of the
    prover encoded index, with this record, and P holds of its message. Relaxed: the statement
    decodes the index with its record, and PR holds of what it decodes to; the prover encoded index
    in the witness is not read. Condition: the index has no collision at the record's seed.
  `Spec.ldClose_know`: from knowledge soundness of the chain, "on A.on into the statements of S.over
    B" (in the statement: `on`, `RA`; `Spec.ldClose` takes them at `A.on`, `A.relR`), to `PreKnowR`.
    (not all hypotheses are named here: see its statement)
    The new extractor: put the message m beside fixed randomness and a fixed further witness, apply
    the chain's extractor, read off what the relaxed input relation reads (fr). Same errors.
  `Spec.ldClose_list`: from the bundle `GoodT` of the chain and its formats to `PreListR`.
    (not all hypotheses are named here: see its statement)
    Same numbers.
  `Spec.ldClose`: the two together.

Limits: no preamble is given. This file says nothing on running times.
Beside the bundle the following is asked, in the order of the statement of `Spec.ldClose`:
  of the chain's formats: it is a prefix (`IdxPrefix`); the record is handed on (`Passes`); the
    honest prover hands the prover encoded index on (`Hands`);
  of the last base joint B: its exact relation gives "the index is the encoding of the prover
    encoded index that the further witness holds (pi), and the claims hold"; the claims on the
    decoded index give its relaxed relation at the fixed further witness z0: so `B.relR` may not
    read a further witness in earnest; the condition of B (`B.on`) gives "no collision of the
    index";
  of the first joint A: on the statements that meet `A.on`, what its relaxed relation says of a
    witness w, the relaxed input relation RiR of the list says of fr w.
Bundles have one type of witnesses for a relation and its relaxation; the lists have two: a relaxed
witness holds no prover encoded index.
`IdxPrefix` says: the verifier does not read the index; nothing is tied to it; it is copied; a
symbol of the copy comes from that symbol alone (`srcIdx`); no other new symbol comes from the index
(`srcAux`); nothing else is asked of the other oracles. Cb/Ld/LdWfPre.lean has the rules that carry
the formats through a chain.
B is any base joint; `idxRels` is the case in view.
Declared. The answers of the samples stand in "holds" of `sigLeft`, since `ConfigurationWithOutOfDomainSample.Left` has no other
place for them; in the relaxed relation that clause is implied by the decoder (`adec`: `S.decAll`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSig
import Hiop.RecSubs
import Hiop.ChainList
import Cb.Ld.LdWfPre
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

/-! ## 1. Tuples -/

namespace Sig
variable {E : Type} (S : Sig E)

/-- The encoding randomness of all oracle messages. -/
abbrev Rnd : Type := ∀ a, (S.om a).Rnd
def rnds (w : S.Wit) : S.Rnd := fun a => (w a).2
def pair (m : S.Msg) (r : S.Rnd) : S.Wit := fun a => (m a, r a)

variable [Field E]

open Classical in
/-- The tuple of the messages to which all oracle messages decode with their samples; none if one of
them does not decode. -/
def decAll (σ : S.Smp) (y : S.ext.Str) : Option S.Msg :=
  if h : ∀ a, (S.decs σ y a).isSome then some fun a => (S.decs σ y a).get (h a) else none

end Sig

section
variable {E : Type} [Field E]

/-! ## 2. What a preamble leaves, for a signature -/

/-- What a preamble leaves: the oracle messages of S, with their samples in the claims. -/
@[reducible] def sigLeft
    (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (Cl : Type) (holds : Cl → C.Rec → C.Msg → S.Msg → Prop) : C.Left where
  Ej    := S.ext
  Xl    := Cl × S.Smp
  AMsg  := S.Msg
  ARnd  := S.Rnd
  aEnc  := fun y m r => S.Enc y (S.pair m r)
  adec  := fun xl y => S.decAll xl.2 y
  afree := fun xl y => S.CF xl.2 y
  holds := fun xl rec U m => S.Ans xl.2 m ∧ holds xl.1 rec U m

/-! ## 3. The base joint of a preamble -/

/-- The base joint of a preamble: the encoded index is a further oracle, its record is in the
explicit part, and in the relaxed relation the statement decodes the index. -/
def idxRels (C : ConfigurationWithOutOfDomainSample) {St M : Type} (P PR : St → C.Rec → C.Msg → M → Prop) :
    IOR.Rels Unit (St × C.Rec) C.E0 (M × C.PIdx) where
  rel  := fun x y w => C.Enc x.2 y w.2 ∧ P x.1 x.2 w.2.1.1 w.1
  relR := fun a w => ∃ U, C.dcd a.2 a.1.2 = some U ∧ PR a.1.1 a.1.2 U w.1
  on   := fun a => ¬ C.coll a.2 a.1.2.1
  core := fun _ => ()

/-! ## 4. The last step -/

variable {C : ConfigurationWithOutOfDomainSample} (S : Sig E) {Cl Xi Wi Wp : Type}

/-- The explicit part is re-bracketed. -/
def closeX (x : (Cl × C.Rec) × S.Smp) : (Cl × S.Smp) × C.Rec := ((x.1.1, x.2), x.1.2)
/-- The honest prover's last witness; pi: the prover encoded index that the further witness holds.
-/
def closeW (pi : Wp → C.PIdx) (w : S.Wit × Wp) : C.PIdx × (S.Msg × S.Rnd) :=
  (pi w.2, (S.msgs w.1, S.rnds w.1))

variable {S}

/-- The chain, closed. -/
def closeF (F : IOR Xi C.E0 ((Cl × C.Rec) × S.Smp) (C.E0.prod S.ext)) :
    IOR Xi C.E0 ((Cl × S.Smp) × C.Rec) (C.E0.prod S.ext) :=
  F.post (fun x => some (closeX S x)) (ExtMap.id _)

def closeH {F : IOR Xi C.E0 ((Cl × C.Rec) × S.Smp) (C.E0.prod S.ext)}
    (pi : Wp → C.PIdx) (H : F.Honest Wi (S.Wit × Wp)) :
    (closeF F).Honest Wi (C.PIdx × (S.Msg × S.Rnd)) :=
  H.post _ _ fun a => (closeX S a.1, closeW S pi a.2)

/-- The numbers of the closed chain: those of the chain, without its cover `cov`. -/
def closeN {Kc : Type} {F : IOR Xi C.E0 ((Cl × C.Rec) × S.Smp) (C.E0.prod S.ext)}
    (P : IOR.Nums Kc F) : PreNums (closeF F) :=
  ⟨P.err, P.pBad, P.pHid, P.bud⟩

end

/-! ## The statements -/

namespace Spec
open IOR
section
variable (E : Type) [Field E]

def ldClose_decAll : Prop :=
  ∀ (S : Sig E) (σ : S.Smp) (y : S.ext.Str) (m : S.Msg),
    S.decAll σ y = some m ↔ ∀ a, S.decs σ y a = some (m a)

/-- The constraint relation of `sigLeft` is the exact relation of the joint over `idxRels`, up to
the re-bracketing (`closeX`, `closeW`). -/
def ldClose_rlin : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (Cl : Type) (holds : Cl → C.Rec → C.Msg → S.Msg → Prop)
      (x : (Cl × C.Rec) × S.Smp) (y : (C.E0.prod S.ext).Str) (w : S.Wit × C.PIdx),
    (sigLeft C S Cl holds).Rlin (closeX S x) y (closeW S id w) ↔
    (S.over (idxRels C holds holds)).rel x y w

/-- The relaxation of the constraint relation of `sigLeft` is the relaxed relation of the joint over
`idxRels`, up to the re-bracketing (`closeX`, `S.msgs`). -/
def ldClose_rlinR : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (Cl : Type) (holds : Cl → C.Rec → C.Msg → S.Msg → Prop)
      (x : (Cl × C.Rec) × S.Smp) (y : (C.E0.prod S.ext).Str) (w : S.Wit × C.PIdx),
    (sigLeft C S Cl holds).RlinR (closeX S x, y) (S.msgs w.1) ↔
    (S.over (idxRels C holds holds)).relR (x, y) w

/-- The collision-free statements of `sigLeft` are the statements that meet the condition (`on`) of
the joint over `idxRels`, up to the re-bracketing (`closeX`). -/
def ldClose_cond : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (Cl : Type) (holds : Cl → C.Rec → C.Msg → S.Msg → Prop)
      (x : (Cl × C.Rec) × S.Smp) (y : (C.E0.prod S.ext).Str),
    (sigLeft C S Cl holds).cond (closeX S x, y) ↔ (S.over (idxRels C holds holds)).on (x, y)

/-- Under the hypotheses below, knowledge soundness of the chain gives the item of the list. -/
def ldClose_know : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (Kc Xi Wi Wr Cl Wp : Type) (holds : Cl → C.Rec → C.Msg → S.Msg → Prop)
      (F : IOR Xi C.E0 ((Cl × C.Rec) × S.Smp) (C.E0.prod S.ext)) (on : Xi × C.E0.Str → Prop)
      (RA : Xi × C.E0.Str → Wi → Prop) (B : Rels Kc (Cl × C.Rec) C.E0 (S.Msg × Wp))
      (ext : Xi × C.E0.Str → Tr F.shape → S.Wit × Wp → Wi) (ε : Err F.shape)
      (RiR : Xi × C.E0.Str → Wr → Prop) (fr : Wi → Wr) (z0 : Wp) (r0 : S.Rnd),
    F.red.KnowInto on (S.over B).on RA (S.over B).relR ext ε →
    (∀ a m U, C.dcd a.2 a.1.2 = some U → holds a.1.1 a.1.2 U m → B.relR a (m, z0)) →
    (∀ a, B.on a → ¬ C.coll a.2 a.1.2.1) → (∀ a w, on a → RA a w → RiR a (fr w)) →
    PreKnowR (sigLeft C S Cl holds) (closeF F) on RiR
      (fun a τ m => fr (ext a τ (S.pair m r0, z0))) ε

/-- Under the hypotheses below, the bundle of the chain gives the list. -/
def ldClose_list : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (Kc Xi Wi Cl Wp : Type) (holds : Cl → C.Rec → C.Msg → S.Msg → Prop)
      (F : IOR Xi C.E0 ((Cl × C.Rec) × S.Smp) (C.E0.prod S.ext)) (H : F.Honest Wi (S.Wit × Wp))
      (A : Rels Kc Xi C.E0 Wi) (B : Rels Kc (Cl × C.Rec) C.E0 (S.Msg × Wp))
      (ext : Xi × C.E0.Str → Tr F.shape → S.Wit × Wp → Wi) (P : Nums Kc F) (rc : Xi → C.Rec)
      (px : Wi → C.PIdx) (pi : Wp → C.PIdx),
    GoodT F H A (S.over B).cf ext P → F.IdxPrefix → F.Passes rc (fun b => b.1.2) →
    H.Hands A.rel px (fun w => pi w.2) →
    (∀ x y w, B.rel x y w → C.Enc x.2 y (pi w.2) ∧ holds x.1 x.2 (pi w.2).1.1 w.1) →
    PreListR (sigLeft C S Cl holds) (closeF F) (closeH pi H) rc px A.rel (closeN P)

/-- The closing rule: `ldClose_list` and `ldClose_know` together. -/
def ldClose : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (Kc Xi Wi Wr Cl Wp : Type) (holds : Cl → C.Rec → C.Msg → S.Msg → Prop)
      (F : IOR Xi C.E0 ((Cl × C.Rec) × S.Smp) (C.E0.prod S.ext)) (H : F.Honest Wi (S.Wit × Wp))
      (A : Rels Kc Xi C.E0 Wi) (B : Rels Kc (Cl × C.Rec) C.E0 (S.Msg × Wp))
      (ext : Xi × C.E0.Str → Tr F.shape → S.Wit × Wp → Wi) (P : Nums Kc F) (rc : Xi → C.Rec)
      (px : Wi → C.PIdx) (pi : Wp → C.PIdx) (RiR : Xi × C.E0.Str → Wr → Prop) (fr : Wi → Wr)
      (z0 : Wp) (r0 : S.Rnd),
    GoodT F H A (S.over B).cf ext P → F.IdxPrefix → F.Passes rc (fun b => b.1.2) →
    H.Hands A.rel px (fun w => pi w.2) →
    (∀ x y w, B.rel x y w → C.Enc x.2 y (pi w.2) ∧ holds x.1 x.2 (pi w.2).1.1 w.1) →
    (∀ a m U, C.dcd a.2 a.1.2 = some U → holds a.1.1 a.1.2 U m → B.relR a (m, z0)) →
    (∀ a, B.on a → ¬ C.coll a.2 a.1.2.1) → (∀ a w, A.on a → A.relR a w → RiR a (fr w)) →
    PreListR (sigLeft C S Cl holds) (closeF F) (closeH pi H) rc px A.rel (closeN P) ∧
    PreKnowR (sigLeft C S Cl holds) (closeF F) A.on RiR
      (fun a τ m => fr (ext a τ (S.pair m r0, z0))) P.err

end
end Spec
end Cb
