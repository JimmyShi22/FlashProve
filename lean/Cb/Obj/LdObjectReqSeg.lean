-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqSeg.lean: a preamble of a request built of segments (`LdReq`, Cb/Req1/LdReq.lean)
is, under the hypotheses named under Limits, a preamble of a request of the object (a term `O.ReqT`,
`O : LdOL`, with `T.OK core`, Cb/Obj/LdObjectReq.lean).

A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves. The object (`LdObj`, Cb/Obj/LdObject.lean) is one record
with a configuration and, over it, the sub-protocols of the proof system, as five terms. A request's
preamble is the fourth.
Definitions, statements (`Cb.Spec.ldOS_ok` and its like) and proofs. Three files are put together.
Cb/Req1/LdReq.lean: a request is one first sending, further sendings and steps, any number of
segments, a last part (`LdReq a z`). Cb/Req1/LdReqStart.lean: such a request from a joint without
oracle messages, as one reduction `r.F`, with theorems on its bundle and formats.
Cb/Obj/LdObjectReq.lean: every term `T` over `O.Cf.conf` with `T.OK core` meets the object's list
(`PreListR`, `PreKnowR`, Hiop/RecSubs.lean; what they say: the head of Cb/Obj/LdObjectReq.lean).

Main names:
  `O.Req core core'`: the requests from the first joint `O.jReq core` (exact: `O.Cf.conf.Rreq`;
    condition: the index decoder answers) to the last stage `O.zReq core'` (the oracle messages
    `O.S`; base joint: the statement decodes the index, and `O.holds`).
  `O.fmtA core q`, `O.fmtZ core' q`: the formats at the two ends; q: the demands on positions. (A
    format, `JFmt`, Cb/Req1/LdReqFormat.lean, says where the index is among a joint's oracles;
    `Chain.Fmt` says, among other clauses, that each link leaves that oracle alone, and what it
    hands on.)
  `O.termOf r w₀`: the request as a term of Cb/Obj/LdObjectReq.lean (`O.ReqT`).
  `O.zAt Wp B`, `O.ReqAt core Wp B`, `O.fmtZAt B pi q`, `O.termAt r pi w₀`; `Spec.ldOS_okAt`,
    `Spec.ldOS_fitAt`: the general form: the last stage has any further witness Wp and any last base
    joint B that is tied to `O.holds` (`O.EndOK pi B`). The names above are its case Wp := the
    prover encoded index. A request with a range check needs the general form, with a ghost beside
    the prover encoded index (`O.zReqG G core'` = `O.zAt _ (O.bEndG G core')`, pi := the first
    part): Cb/Obj/LdObjectReq.lean says why.
  `Spec.ldOS_ok`: from `r.Hyp`, `r.Zk` and one fact on formats,
    `r.chain.Fmt (O.fmtA core qφ) (O.fmtZ core' qi)`: `(O.termOf r w₀).OK core`.
  `Spec.ldOS_object`: from the same three: `PreListR` and `PreKnowR` of the object, over `O.left`.
  `Spec.ldOS_fit`: under the hypotheses of its statement, the line "the preamble's budget bears what
    the test that follows reads", at the test's bound qi (closed under subsets).

Limits: still hypotheses: `r.Hyp` (the hypotheses of all moves), `r.Zk` (among what it asks: masks
are fresh where they are used; at a move "sub": `Chain.OkGiven`, Cb/Req1/LdSegFresh.lean; move by
move: `LdMv.Zk`, Cb/Req1/LdReq.lean), `r.chain.Fmt` (formats, link by link:
Cb/Req1/LdReqFormat.lean); in the general form also `O.EndOK pi B`. No request is given.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReq
import Cb.Req1.LdReqStart
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdOL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  (O : LdOL F E) {Kc : Type}

/-- The requests over the configuration. -/
abbrev Req (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc) (core' : O.S.Msg × O.Cf.conf.PIdx → Kc) :
    Type 1 :=
  LdReq (LdStage.start E Kc (O.jReq core)) (O.zReq core')

/-- The formats at the two ends. -/
def fmtA (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc)
    (q : Finset (LdStage.start E Kc (O.jReq core)).J.E.Pos → Prop) :
    JFmt Kc O.Cf.conf.E0 O.Cf.conf.Rec O.Cf.conf.PIdx (LdStage.start E Kc (O.jReq core)).J :=
  ⟨IxAt.left O.Cf.conf.E0 (Sig.nil E).ext, fun x => x.1.2, fun w => w.2.1, q⟩
def fmtZ (core' : O.S.Msg × O.Cf.conf.PIdx → Kc) (q : Finset (O.zReq core').J.E.Pos → Prop) :
    JFmt Kc O.Cf.conf.E0 O.Cf.conf.Rec O.Cf.conf.PIdx (O.zReq core').J :=
  ⟨IxAt.left O.Cf.conf.E0 O.S.ext, fun b => b.1.2, fun w => w.2, q⟩

/-- The last stage with any further witness and any last base joint; then the requests that end
there, the format there, and such a request as a term. -/
@[reducible] def zAt
    (Wp : Type) (B : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)) : LdStage E Kc :=
  ⟨O.S, O.Cl × O.Cf.conf.Rec, O.Cf.conf.E0, Wp, B⟩
abbrev ReqAt (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc) (Wp : Type)
    (B : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)) : Type 1 :=
  LdReq (LdStage.start E Kc (O.jReq core)) (O.zAt Wp B)
def fmtZAt {Wp : Type}
    (B : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)) (pi : Wp → O.Cf.conf.PIdx)
    (q : Finset (O.zAt Wp B).J.E.Pos → Prop) :
    JFmt Kc O.Cf.conf.E0 O.Cf.conf.Rec O.Cf.conf.PIdx (O.zAt Wp B).J :=
  ⟨IxAt.left O.Cf.conf.E0 O.S.ext, fun b => b.1.2, fun w => pi w.2, q⟩
def termAt {core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc} {Wp : Type}
    {B : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)} (r : O.ReqAt core Wp B)
    (pi : Wp → O.Cf.conf.PIdx) (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells) : O.ReqT Kc :=
  ⟨Wp, pi, B, r.F w₀, r.FH w₀, r.Fext w₀, r.FP w₀⟩

/-- The request as a term: the case without a ghost. -/
def termOf {core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc}
    {core' : O.S.Msg × O.Cf.conf.PIdx → Kc} (r : O.Req core core')
    (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells) : O.ReqT Kc :=
  O.termAt (B := O.bEnd core') r id w₀

end LdOL

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The general form: any further witness, any last base joint that is tied to `O.holds`. -/
def ldOS_okAt : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc) (Wp : Type)
      (B : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)) (pi : Wp → O.Cf.conf.PIdx)
      (r : O.ReqAt core Wp B) (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells)
      (qφ : Finset (LdStage.start E Kc (O.jReq core)).J.E.Pos → Prop)
      (qi : Finset (O.zAt Wp B).J.E.Pos → Prop),
    O.EndOK pi B → r.Hyp → r.Zk →
    r.chain.Fmt (O.fmtA core qφ) (O.fmtZAt B pi qi) → (O.termAt r pi w₀).OK core

open Classical in
def ldOS_fitAt : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc) (Wp : Type)
      (B : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)) (pi : Wp → O.Cf.conf.PIdx)
      (r : O.ReqAt core Wp B) (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells)
      (qφ : Finset (LdStage.start E Kc (O.jReq core)).J.E.Pos → Prop)
      (qi : Finset O.left.El.Pos → Prop)
      (Q : IOR (O.left.Xl × O.Cf.conf.Rec) O.left.El Unit extNone),
    r.Hyp → r.chain.Fmt (O.fmtA core qφ) (O.fmtZAt B pi qi) → (∀ U V, V ⊆ U → qi U → qi V) →
    (∀ ρ, qi (Q.given ρ ∅) ∧ Q.extReads ρ ⊆ Q.given ρ ∅) →
    ∀ ρ₁ ρ₂,
      (O.termAt r pi w₀).nums.bud ρ₁ ((Q.extReads ρ₂).biUnion ((O.termAt r pi w₀).req.srcO ρ₁))

def ldOS_ok : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc)
      (core' : O.S.Msg × O.Cf.conf.PIdx → Kc) (r : O.Req core core')
      (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells)
      (qφ : Finset (LdStage.start E Kc (O.jReq core)).J.E.Pos → Prop)
      (qi : Finset (O.zReq core').J.E.Pos → Prop),
    r.Hyp → r.Zk → r.chain.Fmt (O.fmtA core qφ) (O.fmtZ core' qi) → (O.termOf r w₀).OK core

/-- Under the hypotheses below, a request built of segments meets the object's list. -/
def ldOS_object : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc)
      (core' : O.S.Msg × O.Cf.conf.PIdx → Kc) (r : O.Req core core')
      (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells)
      (qφ : Finset (LdStage.start E Kc (O.jReq core)).J.E.Pos → Prop)
      (qi : Finset (O.zReq core').J.E.Pos → Prop) (z0 : O.Cf.conf.PIdx) (r0 : O.S.Rnd),
    r.Hyp → r.Zk → r.chain.Fmt (O.fmtA core qφ) (O.fmtZ core' qi) →
    PreListR O.left (O.termOf r w₀).req (O.termOf r w₀).hReq
      Prod.snd Prod.fst O.Cf.conf.Rreq (O.termOf r w₀).nums ∧
    PreKnowR O.left (O.termOf r w₀).req (fun a => (O.Cf.conf.D a.2 a.1.2).isSome) O.Cf.conf.RreqR
      ((O.termOf r w₀).cellsOf z0 r0) (O.termOf r w₀).nums.err

open Classical in
def ldOS_fit : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc)
      (core' : O.S.Msg × O.Cf.conf.PIdx → Kc) (r : O.Req core core')
      (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells)
      (qφ : Finset (LdStage.start E Kc (O.jReq core)).J.E.Pos → Prop)
      (qi : Finset O.left.El.Pos → Prop)
      (Q : IOR (O.left.Xl × O.Cf.conf.Rec) O.left.El Unit extNone),
    r.Hyp → r.chain.Fmt (O.fmtA core qφ) (O.fmtZ core' qi) → (∀ U V, V ⊆ U → qi U → qi V) →
    (∀ ρ, qi (Q.given ρ ∅) ∧ Q.extReads ρ ⊆ Q.given ρ ∅) →
    ∀ ρ₁ ρ₂, (O.termOf r w₀).nums.bud ρ₁ ((Q.extReads ρ₂).biUnion ((O.termOf r w₀).req.srcO ρ₁))

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOS_okAt : Spec.ldOS_okAt F E := by
  intro O Kc core Wp B pi r w₀ qφ qi hE hH hZ hF
  obtain ⟨h1, h2, h3, -⟩ := ldReqStart_fmt E Kc _ _ O.Cf.conf.Rec O.Cf.conf.PIdx O.Cf.conf.E0
    (O.jReq core) O.S _ _ B r w₀ (O.fmtA core qφ) (O.fmtZAt B pi qi) (fun _ => True) hH hF rfl
    rfl (fun _ _ => trivial)
  exact ⟨ldReqStart_goodT E Kc _ _ O.Cf.conf.E0 (O.jReq core) (O.zAt Wp B) r w₀ hH hZ, h1, h2, h3,
    hE⟩

open Classical in
theorem ldOS_fitAt : Spec.ldOS_fitAt F E := by
  intro O Kc core Wp B pi r w₀ qφ qi Q hH hF hsub hQ
  obtain ⟨-, -, -, h4⟩ := ldReqStart_fmt E Kc _ _ O.Cf.conf.Rec O.Cf.conf.PIdx O.Cf.conf.E0
    (O.jReq core) O.S _ _ B r w₀ (O.fmtA core qφ) (O.fmtZAt B pi qi) (fun _ => True) hH hF rfl
    rfl (fun _ _ => trivial)
  exact ldOR_fit F E O Kc (O.termAt r pi w₀) Q (fun _ => True) qi h4 hsub hQ

theorem ldOS_ok : Spec.ldOS_ok F E := fun O Kc core core' r w₀ qφ qi hH hZ hF =>
  ldOS_okAt F E O Kc core _ (O.bEnd core') id r w₀ qφ qi (O.endOK core') hH hZ hF

theorem ldOS_object : Spec.ldOS_object F E := fun O Kc core core' r w₀ qφ qi z0 r0 hH hZ hF =>
  ldOR_object F E O Kc (O.termOf r w₀) core z0 r0 (ldOS_ok F E O Kc core core' r w₀ qφ qi hH hZ hF)

open Classical in
theorem ldOS_fit : Spec.ldOS_fit F E := by
  intro O Kc core core' r w₀ qφ qi Q hH hF hsub hQ
  obtain ⟨-, -, -, h4⟩ := ldReqStart_fmt E Kc _ _ O.Cf.conf.Rec O.Cf.conf.PIdx O.Cf.conf.E0
    (O.jReq core) O.S _ _ (O.bEnd core') r w₀ (O.fmtA core qφ) (O.fmtZ core' qi) (fun _ => True)
    hH hF rfl rfl (fun _ _ => trivial)
  exact ldOR_fit F E O Kc (O.termOf r w₀) Q (fun _ => True) qi h4 hsub hQ

end
end Cb
