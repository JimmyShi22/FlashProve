-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReq.lean: what is asked of a candidate for the preamble of a request (`O.ReqT`,
`T.OK core`) over the configuration `O.Cf.conf`, and that its parameter list follows from
`T.OK core`.

A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves.
Definitions, statements (`Cb.Spec.ldOR_object`, `Cb.Spec.ldOR_fit`) and proofs.
The request relation `C.Rreq` (`C : ConfigurationWithOutOfDomainSample`, Hiop/RecConf.lean) says: the oracle is the encoding of
the prover encoded index, and the record of the statement is its record, with the answers of its
message; its message holds an index i, and `Ryes i x cells`. Its relaxation `C.RreqR` says: the
index decoder returns an i with `Rno i x cells`. `PreKnowR` is round-by-round knowledge soundness of
a preamble; `PreListR` has all other items of its parameter list.
Hiop/RecSubs.lean asks of the preamble of a request: a reduction from ((instance, record), the
encoded index) to the constraint relation of "what the preamble leaves", an honest side on (prover
encoded index, cells), the list `PreListR`, the item `PreKnowR` with an extractor `cellsOf` that
goes backwards, and (Hiop/RecBuild.lean) the line "the preamble's budget bears what the test that
follows reads". `Spec.ldClose` (Cb/Ld/LdWfClose.lean) leads from the bundle of a chain and its
formats to the list and the item, for any two end joints with four facts on them (told below, at
`O.EndOK`). Here the first end joint of a request is fixed, and two forms of the last are given,
over any configuration with a record. Then all is read over `O.Cf.conf`, with the data O of
Cb/Obj/LdObjectLin.lean, so that what the request leaves is what the batch test starts from: the
same `O.left`.

Main names:
  `ldReqRels C core`: the first joint. Explicit part (instance, record); oracle: the encoded index;
    witness (prover encoded index, cells). Exact: `C.Rreq`; relaxed: `C.RreqR` of the cells alone
    (the prover encoded index is not read); condition: the index decoder answers.
  `idxRelsK C P PR core`: a last base joint: `idxRels` of Cb/Ld/LdWfClose.lean, with a core that is
    a parameter.
  `idxRelsG C G P PR core`: the same with a ghost G beside the prover encoded index: a part of the
    witness that no relation reads.
  `O.EndOK pi B`: what ties any last base joint B to `O.holds`: it gives three of the four facts
    (the second is asked at every further witness). The fourth holds of `ldReqRels` by definition.
    `Spec.ldClose` asks the four of the two end joints (here with "holds" := `O.holds`, `RiR` :=
    `C.RreqR`): that B's exact relation gives `C.Enc` of the prover encoded index and `O.holds`
    (`relB`); that B's relaxed relation holds (at `z0`) where `C.dcd` returns a message of which
    `O.holds` (`relRB`); that B's condition excludes a collision, `C.coll` (`onB`); and that the
    first joint's relaxed relation, under its condition, gives `C.RreqR`.
  `O.ReqT Kc`: any term: a reduction F with honest side, extractor and numbers, to the oracle
    messages `O.S` over any last base joint `T.B`.
  `T.OK core`: all that `Spec.ldOR_object` uses of the term: its bundle `GoodT` between the two end
    joints, `O.EndOK T.pi T.B`, and its formats (`passes`: the record is handed on; `hands`: the
    honest prover hands its prover encoded index on; `prefx`: `IdxPrefix`, Cb/Ld/LdWfPre.lean, among
    its fields: the index is not read, nothing is tied to it, and it is copied).
    Cb/Obj/LdObjectReqSeg.lean (`Spec.ldOS_okAt`) gives these, under its hypotheses, for a request
    built of segments (Cb/Req1/LdReq.lean, Cb/Req1/LdReqStart.lean, Cb/Req1/LdReqFormat.lean).
  `Spec.ldOR_object`: if `T.OK core`, then `PreListR O.left T.req T.hReq` (record) (prover encoded
    index) `C.Rreq T.nums` and `PreKnowR O.left T.req` (the index decoder answers)
    `C.RreqR (T.cellsOf z0 r0) T.nums.err`.
  `Spec.ldOR_fit`: under the hypotheses of its statement, the line on budgets, from "the term bears
    what follows" at the bound qi of the test that follows (closed under subsets).

Why the ghost: every link of a chain keeps the core, at all witnesses. A chain with a range check
has a core that determines the integer cells of every segment; what a request leaves (its last
oracle messages, the prover encoded index) does not hold them. Without room for the core in the last
witness no request with a range check could have its bundle. The ghost is dropped when the list is
made.

Limits: no term is given. Nothing on the model's relation pair. Nothing on running times.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinProofs
import Cb.Req1.LdSegKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The first joint of a request. -/
def ldReqRels (C : ConfigurationWithOutOfDomainSample) {Kc : Type} (core : C.PIdx × C.Cells → Kc) :
    Rels Kc (C.X × C.Rec) C.E0 (C.PIdx × C.Cells) where
  rel  := C.Rreq
  relR := fun a w => C.RreqR a w.2
  on   := fun a => (C.D a.2 a.1.2).isSome
  core := core

/-- The base joint of a preamble, with any core. -/
def idxRelsK (C : ConfigurationWithOutOfDomainSample) {St M Kc : Type}
    (P PR : St → C.Rec → C.Msg → M → Prop) (core : M × C.PIdx → Kc) :
    Rels Kc (St × C.Rec) C.E0 (M × C.PIdx) where
  rel  := fun x y w => C.Enc x.2 y w.2 ∧ P x.1 x.2 w.2.1.1 w.1
  relR := fun a w => ∃ U, C.dcd a.2 a.1.2 = some U ∧ PR a.1.1 a.1.2 U w.1
  on   := fun a => ¬ C.coll a.2 a.1.2.1
  core := core

/-- The same with a ghost G beside the prover encoded index: a part of the witness that no relation
reads, in which the core can stand. -/
def idxRelsG (C : ConfigurationWithOutOfDomainSample) {St M Kc : Type} (G : Type)
    (P PR : St → C.Rec → C.Msg → M → Prop) (core : M × (C.PIdx × G) → Kc) :
    Rels Kc (St × C.Rec) C.E0 (M × (C.PIdx × G)) where
  rel  := fun x y w => C.Enc x.2 y w.2.1 ∧ P x.1 x.2 w.2.1.1.1 w.1
  relR := fun a w => ∃ U, C.dcd a.2 a.1.2 = some U ∧ PR a.1.1 a.1.2 U w.1
  on   := fun a => ¬ C.coll a.2 a.1.2.1
  core := core

namespace LdOL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E) {Kc : Type}

def jReq (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc) :
    Rels Kc (O.Cf.conf.X × O.Cf.conf.Rec) O.Cf.conf.E0 (O.Cf.conf.PIdx × O.Cf.conf.Cells) :=
  ldReqRels O.Cf.conf core
def bEnd (core : O.S.Msg × O.Cf.conf.PIdx → Kc) :
    Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × O.Cf.conf.PIdx) :=
  idxRelsK O.Cf.conf O.holds O.holds core

/-- The last stage of a request. -/
@[reducible] def zReq (core : O.S.Msg × O.Cf.conf.PIdx → Kc) : LdStage E Kc :=
  ⟨O.S, O.Cl × O.Cf.conf.Rec, O.Cf.conf.E0, O.Cf.conf.PIdx, O.bEnd core⟩

/-- The last base joint with a ghost; `zReqG`: the last stage with it. -/
def bEndG (G : Type) (core : O.S.Msg × (O.Cf.conf.PIdx × G) → Kc) :
    Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × (O.Cf.conf.PIdx × G)) :=
  idxRelsG O.Cf.conf G O.holds O.holds core
@[reducible] def zReqG (G : Type) (core : O.S.Msg × (O.Cf.conf.PIdx × G) → Kc) :
    LdStage E Kc :=
  ⟨O.S, O.Cl × O.Cf.conf.Rec, O.Cf.conf.E0, O.Cf.conf.PIdx × G, O.bEndG G core⟩

/-- What ties a last base joint B to `O.holds`; pi: where the prover encoded index is in the further
witness. -/
structure EndOK {Wp : Type} (pi : Wp → O.Cf.conf.PIdx)
    (B : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)) : Prop where
  relB   : ∀ x y w, B.rel x y w → O.Cf.conf.Enc x.2 y (pi w.2) ∧ O.holds x.1 x.2 (pi w.2).1.1 w.1
  relRB  : ∀ a m U z, O.Cf.conf.dcd a.2 a.1.2 = some U → O.holds a.1.1 a.1.2 U m → B.relR a (m, z)
  onB    : ∀ a, B.on a → ¬ O.Cf.conf.coll a.2 a.1.2.1

variable (Kc) in
/-- Any term: the data. -/
structure ReqT where
  /-- the further witness at the end, where the prover encoded index is in it; the last base joint
  -/
  Wp  : Type
  pi  : Wp → O.Cf.conf.PIdx
  B   : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)
  F   : IOR (O.Cf.conf.X × O.Cf.conf.Rec) O.Cf.conf.E0
    ((O.Cl × O.Cf.conf.Rec) × O.S.Smp) (O.Cf.conf.E0.prod O.S.ext)
  H   : F.Honest (O.Cf.conf.PIdx × O.Cf.conf.Cells) (O.S.Wit × Wp)
  ext : (O.Cf.conf.X × O.Cf.conf.Rec) × O.Cf.conf.E0.Str →
    Tr F.shape → O.S.Wit × Wp → O.Cf.conf.PIdx × O.Cf.conf.Cells
  P   : Nums Kc F

namespace ReqT
variable {O} (T : O.ReqT Kc)

/-- What is used of the term. -/
structure OK (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc) : Prop where
  good   : GoodT T.F T.H (O.jReq core) (O.S.over T.B).cf T.ext T.P
  prefx  : T.F.IdxPrefix
  passes : T.F.Passes Prod.snd fun b => b.1.2
  hands  : T.H.Hands O.Cf.conf.Rreq Prod.fst fun w => T.pi w.2
  last   : O.EndOK T.pi T.B

/-- The preamble of a request, in the list's types. -/
def req :
    IOR (O.Cf.conf.X × O.Cf.conf.Rec) O.Cf.conf.E0 (O.left.Xl × O.Cf.conf.Rec) O.left.El :=
  closeF T.F
def hReq :
    T.req.Honest (O.Cf.conf.PIdx × O.Cf.conf.Cells) (O.Cf.conf.PIdx × O.left.WAux) :=
  closeH T.pi T.H
def nums : PreNums T.req := closeN T.P
def cellsOf (z0 : T.Wp) (r0 : O.S.Rnd) :
    (O.Cf.conf.X × O.Cf.conf.Rec) × O.Cf.conf.E0.Str →
    Tr T.req.shape → O.left.AMsg → O.Cf.conf.Cells :=
  fun a τ m => (T.ext a τ (O.S.pair m r0, z0)).2

end ReqT
end LdOL

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E]

/-- States: every term `T` with `T.OK core` is a preamble of a request of the object. -/
def ldOR_object : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (T : O.ReqT Kc) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc)
      (z0 : T.Wp) (r0 : O.S.Rnd),
    T.OK core →
    PreListR O.left T.req T.hReq Prod.snd Prod.fst O.Cf.conf.Rreq T.nums ∧
    PreKnowR O.left T.req (fun a => (O.Cf.conf.D a.2 a.1.2).isSome) O.Cf.conf.RreqR
      (T.cellsOf z0 r0) T.nums.err

open Classical in
/-- Under the hypotheses below, the preamble's budget bears what the test that follows reads of the
oracles left. -/
def ldOR_fit : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (T : O.ReqT Kc)
      (Q : IOR (O.left.Xl × O.Cf.conf.Rec) O.left.El Unit extNone)
      (qa : Finset O.Cf.conf.E0.Pos → Prop) (qi : Finset O.left.El.Pos → Prop),
    T.F.Bears T.P.bud qa qi → (∀ U V, V ⊆ U → qi U → qi V) →
    (∀ ρ, qi (Q.given ρ ∅) ∧ Q.extReads ρ ⊆ Q.given ρ ∅) →
    ∀ ρ₁ ρ₂, T.nums.bud ρ₁ ((Q.extReads ρ₂).biUnion (T.req.srcO ρ₁))

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E]

theorem ldOR_object : Spec.ldOR_object F E := fun O Kc T core z0 r0 h =>
  ldClose E O.Cf.conf O.S Kc _ _ O.Cf.conf.Cells O.Cl T.Wp O.holds T.F T.H (O.jReq core) T.B T.ext
    T.P Prod.snd Prod.fst T.pi O.Cf.conf.RreqR Prod.snd z0 r0 h.good h.prefx h.passes h.hands
    h.last.relB (fun a m U hU hh => h.last.relRB a m U z0 hU hh) h.last.onB (fun _ _ _ hR => hR)

/-- The two standard last base joints are tied to `O.holds` (with `LdOL.endOKG`). -/
theorem LdOL.endOK {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)
    {Kc : Type} (core' : O.S.Msg × O.Cf.conf.PIdx → Kc) : O.EndOK id (O.bEnd core') :=
  ⟨fun _ _ _ hB => hB, fun _ _ U _ hU hh => ⟨U, hU, hh⟩, fun _ hon => hon⟩

theorem LdOL.endOKG {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)
    {Kc : Type} (G : Type) (core' : O.S.Msg × (O.Cf.conf.PIdx × G) → Kc) :
    O.EndOK Prod.fst (O.bEndG G core') :=
  ⟨fun _ _ _ hB => hB, fun _ _ U _ hU hh => ⟨U, hU, hh⟩, fun _ hon => hon⟩

open Classical in
theorem ldOR_fit : Spec.ldOR_fit F E := by
  intro O Kc T Q qa qi hB hsub hQ ρ₁ ρ₂
  have h := (hB ρ₁ _ (hsub _ _ (hQ ρ₂).2 (hQ ρ₂).1)).1
  have e : (Q.extReads ρ₂).biUnion (T.req.srcO ρ₁) = (Q.extReads ρ₂).biUnion (T.F.srcO ρ₁) :=
    Finset.biUnion_congr rfl fun q _ => post_id_srcO T.F _ ρ₁ q
  show T.P.bud ρ₁ _
  rw [e]
  exact h

end
end Cb
