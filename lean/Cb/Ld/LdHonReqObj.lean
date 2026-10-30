-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHonReqObj.lean: the object's list for the preamble of a request, without its item on
knowledge soundness, and the line "the preamble's budget bears what the test reads", follow from the
honest form of the request's four properties; the line also from two conditions on the test.

A record, statements (in `Cb.Spec`) and proofs: assemblies on Cb/Gen/FullErrReq.lean,
Cb/Obj/LdObjectReq.lean. Any request, any object `T : LdObjT` (Cb/Obj/LdObjectTerms.lean). Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
The list is `PreListR` (Hiop/RecSubs.lean): the parameter list of a preamble: all items but
knowledge soundness. `r.hon` (Cb/Gen/FullErrReq.lean) is the request r with the errors of every
fold's link (`IOR.Link`) overwritten by the full list.

Main names:
  `P.GoodH`, for `P : LdReqPack F E` (Cb/Obj/LdObjectDataRef.lean): `P.Good` with `P.r.hon.Hyp` in
    the place of `P.r.Hyp`: rHyp: all moves' hypotheses, but of a fold's link the bundle is asked
    at the full list of errors (of its four clauses the first alone is touched: the words that the
    fold puts out, the honest prover's pairs and the slots' laws are asked as they stand); rZk,
    rFmt, rEnd: `P.Good`'s own, at `P.r` itself.
  `Spec.ldHonR_good`: `P.Good` → `P.GoodH` (the honest form asks less).
  `Spec.ldHonR_list`: a term `T : O.ReqT Kc` with `GoodT` at `T.P.full`, the three formats and
    `O.EndOK T.pi T.B`, with `T.Wp` and `O.S.Rnd` nonempty, has `PreListR` at its own numbers
    `T.nums`: the thirteen items read pBad, pHid and the budget alone.
  `Spec.ldHonR_term`: `EndOK`, `r.hon.Hyp`, `r.ZkS` (`LdReq.ZkS`, Cb/Req1/LdReqS.lean), the format,
    `Wp` and `O.S.Rnd` nonempty ⇒ `PreListR` of the term `O.termAt r pi w₀`, at its own numbers.
  `Spec.ldHonR_fit`: `Cb.Spec.ldOS_fitAt` with `r.hon.Hyp` for `r.Hyp`, under the hypotheses of its
    statement.
  `Spec.ldHonR_req`, for `T : LdObjT F E`: `T.pack.GoodH` ⇒ the clause "req" of
    `T.obj.subs.HypH T.obj.nums` (Hiop/RecBuild.lean).
  `Spec.ldHonR_fitOn`: `T.pack.GoodH`, and of the test at N instances: its bound is closed under
    subsets, its verifier reads within it ⇒ the clause "fitOn".

The two clauses are said of the object's own request, honest prover and numbers. The clause req
holds (fields of `PreListR`): point structure, locality, the honest prover is accepted on inputs in
the relation, where the verifier's randomness is not withheld (`PreListR.acc`: `Honest.Acc`,
Ior/Honest.lean), the chances of the two withheld sets, exact honest-verifier zero knowledge at the
budget (`PreListR.exact`: `Honest.Exact`, Ior/Honest.lean), the formats. The record that
`Spec.ldHonR_req` concludes has the field `exact` (`PreListR`, Hiop/RecSubs.lean): a conclusion.
`H.ExactWith Ri bud S`: for every (x, y, w) in Ri, every ρ outside `H.Hid w x` and every T with
`bud ρ T`, the distribution `H.output w x ρ T` equals `S x ρ T a`, where a gives the symbols of y at
the positions `R.given ρ T` and `none` at the others. `Exact` says that some S does.

Limits: this file says nothing on knowledge soundness (`PreKnowR`). It does not say that a pack has
`GoodH`. It says nothing on
the other five clauses of `HypH`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.FullErrReq
import Cb.Obj.LdObjectDataRef
import Cb.Obj.LdObjectTerms

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- The four properties, in the honest form. -/
structure LdReqPack.GoodH {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (P : LdReqPack F E) : Prop where
  rHyp : P.r.hon.Hyp
  rZk  : P.r.ZkS
  rFmt : P.r.Fmt (P.on.ol.fmtA P.cr P.qφ) (P.on.ol.fmtZAt P.Bz P.piz P.qi)
  rEnd : P.on.ol.EndOK P.piz P.Bz

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldHonR_good : Prop := ∀ P : LdReqPack F E, P.Good → P.GoodH

def ldHonR_list : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (T : O.ReqT Kc) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc)
      (_ : T.Wp) (_ : O.S.Rnd),
    GoodT T.F T.H (O.jReq core) (O.S.over T.B).cf T.ext T.P.full → T.F.IdxPrefix →
    (T.F.Passes Prod.snd fun b => b.1.2) → (T.H.Hands O.Cf.conf.Rreq Prod.fst fun w => T.pi w.2) →
    O.EndOK T.pi T.B → PreListR O.left T.req T.hReq Prod.snd Prod.fst O.Cf.conf.Rreq T.nums

def ldHonR_term : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc) (Wp : Type)
      (B : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)) (pi : Wp → O.Cf.conf.PIdx)
      (r : O.ReqAt core Wp B) (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells)
      (qφ : Finset (LdStage.start E Kc (O.jReq core)).J.E.Pos → Prop)
      (qi : Finset (O.zAt Wp B).J.E.Pos → Prop) (_ : Wp) (_ : O.S.Rnd),
    O.EndOK pi B → r.hon.Hyp → r.ZkS → r.chain.Fmt (O.fmtA core qφ) (O.fmtZAt B pi qi) →
    PreListR O.left (O.termAt r pi w₀).req (O.termAt r pi w₀).hReq
      Prod.snd Prod.fst O.Cf.conf.Rreq (O.termAt r pi w₀).nums

open Classical in
def ldHonR_fit : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc) (Wp : Type)
      (B : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)) (pi : Wp → O.Cf.conf.PIdx)
      (r : O.ReqAt core Wp B) (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells)
      (qφ : Finset (LdStage.start E Kc (O.jReq core)).J.E.Pos → Prop)
      (qi : Finset O.left.El.Pos → Prop)
      (Q : IOR (O.left.Xl × O.Cf.conf.Rec) O.left.El Unit extNone),
    r.hon.Hyp → r.chain.Fmt (O.fmtA core qφ) (O.fmtZAt B pi qi) → (∀ U V, V ⊆ U → qi U → qi V) →
    (∀ ρ, qi (Q.given ρ ∅) ∧ Q.extReads ρ ⊆ Q.given ρ ∅) →
    ∀ ρ₁ ρ₂,
      (O.termAt r pi w₀).nums.bud ρ₁ ((Q.extReads ρ₂).biUnion ((O.termAt r pi w₀).req.srcO ρ₁))

/-- The clause "req" of the object's honest half. -/
def ldHonR_req : Prop :=
  ∀ T : LdObjT F E, T.toLdObjD.pack.GoodH →
    PreListR T.obj.subs.on T.obj.subs.req T.obj.subs.hReq Prod.snd Prod.fst
      T.obj.Cf.conf.Rreq T.obj.nums.req

open Classical in
/-- The clause "fitOn". -/
def ldHonR_fitOn : Prop :=
  ∀ T : LdObjT F E, T.toLdObjD.pack.GoodH → (∀ U V, V ⊆ U → T.linB.qi U → T.linB.qi V) →
    (∀ ρ, T.linB.qi (T.linB.R.given ρ ∅) ∧ T.linB.R.extReads ρ ⊆ T.linB.R.given ρ ∅) →
    ∀ ρ₁ ρ₂,
      T.obj.nums.req.bud ρ₁ ((T.obj.subs.linOn.ior.extReads ρ₂).biUnion (T.obj.subs.req.srcO ρ₁))

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldHonR_good : Spec.ldHonR_good F E := fun P h => ⟨fullReq_hyp E P.Kr _ _ P.r h.rHyp, h.rZk, h.rFmt, h.rEnd⟩

omit [Fintype E] in
theorem ldHonR_list : Spec.ldHonR_list F E := fun O Kc T core z0 r0 hg h1 h2 h3 h4 =>
  have h := (ldOR_object F E O Kc { T with P := T.P.full } core z0 r0 ⟨hg, h1, h2, h3, h4⟩).1
  ⟨h.point, h.isLocal, h.acc, h.prBad, h.prHid, h.exact, h.noReads, h.noTie, h.passes, h.hands,
    h.copy, h.srcIdx, h.srcAux⟩

theorem ldHonR_term : Spec.ldHonR_term F E := by
  intro O Kc core Wp B pi r w₀ qφ qi z0 r0 hE hH hZ hF
  obtain ⟨h1, h2, h3, -⟩ := fullReq_startFmt E Kc _ _ O.Cf.conf.Rec O.Cf.conf.PIdx O.Cf.conf.E0
    (O.jReq core) O.S _ _ B r w₀ (O.fmtA core qφ) (O.fmtZAt B pi qi) (fun _ => True) hH hF rfl
    rfl (fun _ _ => trivial)
  exact ldHonR_list F E O Kc (O.termAt r pi w₀) core z0 r0
    (fullReq_start E Kc _ _ O.Cf.conf.E0 (O.jReq core) (O.zAt Wp B) r w₀ hH hZ) h1 h2 h3 hE

open Classical in
theorem ldHonR_fit : Spec.ldHonR_fit F E := by
  intro O Kc core Wp B pi r w₀ qφ qi Q hH hF hsub hQ
  obtain ⟨-, -, -, h4⟩ := fullReq_startFmt E Kc _ _ O.Cf.conf.Rec O.Cf.conf.PIdx O.Cf.conf.E0
    (O.jReq core) O.S _ _ B r w₀ (O.fmtA core qφ) (O.fmtZAt B pi qi) (fun _ => True) hH hF rfl
    rfl (fun _ _ => trivial)
  exact ldOR_fit F E O Kc (O.termAt r pi w₀) Q (fun _ => True) qi h4 hsub hQ

theorem ldHonR_req : Spec.ldHonR_req F E := fun T h =>
  ldHonR_term F E T.on.ol T.Kr T.cr T.Wz T.Bz T.piz T.r T.w₀ T.qφ T.linB.qi T.z0 T.r0 h.rEnd h.rHyp
    h.rZk (ldFmt_req E T.Kr _ _ _ _ _ T.r _ _ h.rFmt)

open Classical in
theorem ldHonR_fitOn : Spec.ldHonR_fitOn F E := fun T h hm hr =>
  ldHonR_fit F E T.on.ol T.Kr T.cr T.Wz T.Bz T.piz T.r T.w₀ T.qφ T.linB.qi T.linB.R h.rHyp
    (ldFmt_req E T.Kr _ _ _ _ _ T.r _ _ h.rFmt) hm hr

end
end Cb
