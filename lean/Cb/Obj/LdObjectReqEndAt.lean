-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqEndAt.lean: a request that ends with the final batching meets the object's list
(`PreListR`, `PreKnowR`), under the hypotheses of `Spec.ldOREAt_object`, at the datum that is read
off that batching.

A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves. Its last moves, the final batching, make the claims on the
encoded index that are still pending into one.
One definition, statements and proofs. Cb/Obj/LdObjectReqEnd.lean reads the test's datum `R.O` off
the last claim of a request's final batching, and ends at its own last stage `R.z` (further witness:
prover encoded index, ghost). Cb/Obj/LdObjectReq.lean and Cb/Obj/LdObjectReqSeg.lean give, under
their hypotheses, the object's list (`PreListR`, `PreKnowR`, Hiop/RecSubs.lean; what they say: the
head of Cb/Obj/LdObjectReq.lean) for any request that ends at a stage tied to `O.holds`. Here the
two meet.

Main names:
  `Spec.ldOREAt_z`: `R.z` is the object's last stage with a ghost, `R.O.zReqG R.G R.coreZ`: by
    definition.
  `Spec.ldOREAt_end`: `R.bEnd` is tied to `R.O.holds` (`O.EndOK Prod.fst ..`).
  `R.reqOf ..`: the request with given first sendings, segments with a closing, and last part (any
    list "tail" that ends at `R.X.src`: the last segment's body), then `R.lastP`.
  `Spec.ldOREAt_hyp`, `Spec.ldOREAt_zk`: its `r.Hyp` and `r.Zk` from those of its parts and the
    conditions of Cb/Obj/LdObjectReqEnd.lean.
  `Spec.ldOREAt_object`: the list: for every request r from the first joint `R.O.jReq core` to
    `R.z`: `r.Hyp`, `r.Zk` and the format give `PreListR R.O.left ..` and `PreKnowR R.O.left ..`.

Limits: this file says nothing on the format of `R.lastP` (Cb/Obj/LdObjectReqEndFmt.lean). This file
gives no instance that meets its hypotheses.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReqEndProofs
import Cb.Obj.LdObjectReqSeg
import Cb.Req1.LdReqLast
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

namespace LdORE
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E]
  [Algebra F E] (R : LdORE F E Kc)

/-- The request that ends with the final batching. -/
def reqOf {a : LdStage E Kc} (first : LdSendD a) (a₁ : LdStage E Kc)
    (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
    (segs : LdSegs a₁ b) (tail : LdProg b R.X.src) : LdReq a R.z :=
  LdReq.withLast first a₁ more hm b segs (tail.app R.lastP)

end LdORE

namespace Spec
section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldOREAt_z : Prop := ∀ (R : LdORE F E Kc), R.z = R.O.zReqG R.G R.coreZ

def ldOREAt_end : Prop := ∀ (R : LdORE F E Kc), R.O.EndOK Prod.fst R.bEnd

def ldOREAt_hyp : Prop :=
  ∀ (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (segs : LdSegs a₁ b) (tail : LdProg b R.X.src),
    first.Hyp → more.Hyp → segs.Hyp → tail.Hyp → 2 ≤ R.n → R.Z.OK → R.Tie →
    (R.reqOf first a₁ more hm b segs tail).Hyp

/-- What honest-verifier zero knowledge asks of it, beside its hypotheses; `base₀`: the facts that
are fresh before the first segment. -/
def ldOREAt_zk : Prop :=
  ∀ (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (segs : LdSegs a₁ b) (tail : LdProg b R.X.src),
    tail.Hyp → 2 ≤ R.n → R.Z.OK → R.Tie → R.X.Own →
    segs.Zk (R.reqOf first a₁ more hm b segs tail).base₀ →
    tail.Zk (segs.After (R.reqOf first a₁ more hm b segs tail).base₀) →
    R.X.stepIn.After (tail.After (segs.After (R.reqOf first a₁ more hm b segs tail).base₀))
      R.X.mask.fact →
    (R.reqOf first a₁ more hm b segs tail).Zk

/-- The object's list (`PreListR`, `PreKnowR`). -/
def ldOREAt_object : Prop :=
  ∀ (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (r : LdReq (LdStage.start E Kc (R.O.jReq core)) R.z) (w₀ : R.Cf.conf.PIdx × R.Cf.conf.Cells)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (qi : Finset R.z.J.E.Pos → Prop) (z0 : R.Cf.conf.PIdx × R.G) (r0 : R.S.Rnd),
    r.Hyp → r.Zk → r.chain.Fmt (R.O.fmtA core qφ) (R.O.fmtZAt R.bEnd Prod.fst qi) →
    PreListR R.O.left (R.O.termAt (B := R.bEnd) r Prod.fst w₀).req
      (R.O.termAt (B := R.bEnd) r Prod.fst w₀).hReq Prod.snd Prod.fst R.Cf.conf.Rreq
      (R.O.termAt (B := R.bEnd) r Prod.fst w₀).nums ∧
    PreKnowR R.O.left (R.O.termAt (B := R.bEnd) r Prod.fst w₀).req
      (fun a => (R.Cf.conf.D a.2 a.1.2).isSome) R.Cf.conf.RreqR
      ((R.O.termAt (B := R.bEnd) r Prod.fst w₀).cellsOf z0 r0)
      (R.O.termAt (B := R.bEnd) r Prod.fst w₀).nums.err

end
end Spec

section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOREAt_z : Spec.ldOREAt_z F E Kc := fun _ => rfl

theorem ldOREAt_end : Spec.ldOREAt_end F E Kc := fun _ =>
  ⟨fun _ _ _ h => h, fun _ _ U _ hU hh => ⟨U, hU, hh⟩, fun _ h => h⟩

theorem ldOREAt_hyp : Spec.ldOREAt_hyp F E Kc := fun R _ _ _ _ _ _ _ tail h1 h2 h3 h4 hn hZ hT =>
  ⟨h1, h2, h3,
    ldReqLast_hyp E Kc _ _ _
      ((ldProg_app_hyp E Kc _ _ _ tail R.lastP).2 ⟨h4, ldORE_hyp F E Kc R hn hZ hT⟩)⟩

theorem ldOREAt_zk : Spec.ldOREAt_zk F E Kc := fun R _ _ _ _ _ _ _ tail h4 hn hZ hT hO z1 z2 z3 =>
  ⟨z1, ldReqLast_zk E Kc _ _ _ _
      ((ldProg_app_hyp E Kc _ _ _ tail R.lastP).2 ⟨h4, ldORE_hyp F E Kc R hn hZ hT⟩)
      ((ldProg_app_zk E Kc _ _ _ tail R.lastP _).2 ⟨z2, ldORE_zk F E Kc R _ hn hZ hO z3⟩)⟩

theorem ldOREAt_object : Spec.ldOREAt_object F E Kc := fun R core r w₀ qφ qi z0 r0 hH hZ hF =>
  ldOR_object F E R.O Kc (R.O.termAt (B := R.bEnd) r Prod.fst w₀) core z0 r0
    (ldOS_okAt F E R.O Kc core _ R.bEnd Prod.fst r w₀ qφ qi (ldOREAt_end F E Kc R) hH hZ hF)

end
end Cb
