-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRef.lean: the reference request as a term: first sendings; any number of reference
segments, each with its closing; the last segment, which has none; the final batching.

The term is the chain of interactive oracle reductions that treats one request: its preamble.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs.
A request `r : LdReq a z` (Cb/Req1/LdReq.lean) runs from a stage a to a stage z (`LdStage`,
Cb/Req1/LdSegKit.lean): a first sending, further moves, a list of segments, a last part. Moves
(`LdMv`), lists of moves (`LdProg`) and segments (`LdSeg`) are in Cb/Req1/LdSeg.lean; `Hyp` is what
is asked of each.

Why a step without rounds between two segments: a segment ends at "what its locations leave, beside
what else is claimed"; the next one begins at "each function's keys are in its table, beside what
rides". That the first says the second is the model's matter (which claims a segment has). It is a
step without rounds at the head of the next segment's body; its hypothesis (`IOR.StepT`) is asked.
Why one configuration, one matrix of the index: all segments of a request are over the same
`I : LdRefIx E` (configuration; rows, column variables and entries of the matrix of the index): a
parameter of the segments' data; for a request with the end R it is `R.ix`: the configuration and
the matrix of the final batching.

Main names:
  `LdRefS E Kc I a`: one reference segment that begins at the stage a: the data A, K of
    Cb/Req1/LdSegRefAll.lean, the link bridge-to-fold `l` (a parameter), the one sending and the
    locations Qc, and the entry step (four maps).
  `S.d`, `S.entry`, `S.seg : LdSeg a S.d`. `S.OK pp`: the entry step's hypothesis, and the
    hypotheses of `Spec.ldSegRefAll_one`.
  `LdRefL E Kc I a b`: a list of such segments, each beginning where the one before ends;
    `L.segs : LdSegs a b`; `L.OK pp`.
  `LdRefT R b`: the last segment, for the end R (`LdORE`) of the request, beginning at b: A; what
    its tensor batching leaves (St₁, fz, Az); the entry step; the exit step into `R.X.src` ("rows on
    all entries, beside the pending tensor rows"). `T.tail : LdProg b R.X.src`; `T.OK pp`.
  `ldReqRef R first a₁ more hm b L T : LdReq a R.z`: the request.
  In `Spec.ldReqRef_hyp` pp is the characteristic of E (`[CharP E pp]`).
  `Spec.ldReqRef_hyp`: `r.Hyp` from: the first sending's seven hypotheses; `more.Hyp`; `L.OK pp`;
    `T.OK pp`; 2 ≤ degree, the evader's law and `R.Tie` of the final batching.
  So `Spec.ldReq_goodB` (Cb/Req1/LdReq.lean) applies: the request as a chain has all of the bundle
  but zero knowledge (`IOR.GoodB`, Ior/Masked.lean).

Limits: of the whole, this file says nothing on zero knowledge, the format, the bound on the errors
(they follow part by part, under the hypotheses of the statements there:
Cb/Req1/LdSegFrontRefZk.lean, Cb/Req1/LdSegWholeZk.lean, Cb/Req1/LdSegWholeAfter.lean,
Cb/Obj/LdObjectReqEndAt.lean; Cb/Req1/LdSegFrontFmt.lean, Cb/Req1/LdSegWholeFmt.lean,
Cb/Obj/LdObjectReqEndFmt.lean; Cb/Req1/LdReqBelow.lean): put together in Cb/Req1/LdReqRefFinal.lean.
It says nothing on segments with two groups (this protocol's technical report (lean/CREDITS.md) has
one group a segment). This file gives no instance that meets its hypotheses, so as far as this file
shows its theorems may hold of nothing.
The order of the parts restates the technical report in our own words
(lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefAllProofs
import Cb.Obj.LdObjectReqEndAt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- The request's configuration and matrix of the index: what all its segments share. -/
@[reducible] def LdORE.ix
    {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc) :
    LdRefIx E :=
  ⟨R.Cf.conf, R.Rw, R.k, R.mat⟩

/-- A segment with one more step at the head of its body. -/
def LdSeg.pre {E Kc : Type} [Field E] [Fintype E] {a a₀ d : LdStage E Kc}
    (s : LdSeg a₀ d) (en : LdMv a a₀) (he : en.tag = .step) : LdSeg a d :=
  { s with
    body := ((LdProg.nil a).snoc en).app s.body
    bodyT := (ldProg_app_all E Kc _ _ _ _ _ _).2
      ⟨(LdProg.all_snoc _ _ _).2 ⟨LdProg.all_nilK _ _, Or.inr (Or.inr he)⟩, s.bodyT⟩ }

theorem LdSeg.pre_hyp {E Kc : Type} [Field E] [Fintype E] {a a₀ d : LdStage E Kc} (s : LdSeg a₀ d)
    (en : LdMv a a₀) (he : en.tag = .step) (h₀ : en.Hyp) (h : s.Hyp) : (s.pre en he).Hyp :=
  ⟨(ldProg_app_hyp E Kc _ _ _ _ _).2 ⟨(LdProg.hyp_snoc _ _).2 ⟨LdProg.hyp_nilK _, h₀⟩, h.1⟩,
    h.2, h.3, h.4, h.5⟩

/-- One reference segment that begins at the stage a: the data. -/
structure LdRefS (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a : LdStage E Kc) :
    Type 1 where
  A  : LdRefD E Kc I
  K  : LdRefC1 A
  l  : Link Kc K.R.c1.fold.src.J K.R.c1.fold.mid
  Qc : LdCloseD K.R.c1.fold
  /-- The entry step. -/
  f    : a.X → Option A.V.Fp.s0.X
  g    : ExtMap a.Ex A.V.Fp.s0.Ex
  m    : a.X × a.W → A.V.Fp.s0.X × A.V.Fp.s0.W
  back : a.X × a.Ex.Str → A.V.Fp.s0.W → a.W

namespace LdRefS
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E}
  {a : LdStage E Kc} (S : LdRefS E Kc I a)

/-- Where it ends. -/
def d : LdStage E Kc := S.Qc.loc.tgt

def entry : LdMv a S.A.V.Fp.s0 := .step a S.A.V.Fp.s0 S.f S.g S.m S.back

/-- The segment: the reference segment, with the entry step at the head of its body. -/
def seg : LdSeg a S.d := (S.K.seg S.l S.Qc).pre S.entry rfl

/-- What is asked of it. -/
structure OK (pp : ℕ) : Prop where
  entry : S.entry.Hyp
  body  : S.A.OK pp
  ends  : S.A.X.Ends S.K.St₁ S.K.fz S.K.Az
  ev    : S.K.Z.OK
  named : ∀ n, S.A.Gr.Named n → S.K.grp.mem n.1
  fold  : S.K.R.c1.fold.Hyp S.l
  snd   : S.Qc.snd.Hyp

end LdRefS

/-- A list of reference segments. -/
inductive LdRefL (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a : LdStage E Kc) :
    LdStage E Kc → Type 1
  | nil : LdRefL E Kc I a a
  | snoc {b : LdStage E Kc} (L : LdRefL E Kc I a b) (S : LdRefS E Kc I b) : LdRefL E Kc I a S.d

namespace LdRefL
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}

def segs : {b : LdStage E Kc} → LdRefL E Kc I a b → LdSegs a b
  | _, .nil => .nil a
  | _, .snoc L S => .snoc L.segs S.seg

def OK (pp : ℕ) : {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.OK pp ∧ S.OK pp

end LdRefL

/-- The last segment: the data. -/
structure LdRefT {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (R : LdORE F E Kc) (b : LdStage E Kc) : Type 1 where
  A   : LdRefD E Kc R.ix
  St₁ : Type
  fz  : A.X.bt.par.Mid → St₁
  Az  : Rels Kc St₁ R.Cf.conf.E0 (A.Xa.Q.T.Msg × (R.Cf.conf.PIdx × (A.W₁ × A.Gh)))
  /-- The entry step. -/
  f    : b.X → Option A.V.Fp.s0.X
  g    : ExtMap b.Ex A.V.Fp.s0.Ex
  m    : b.X × b.W → A.V.Fp.s0.X × A.V.Fp.s0.W
  back : b.X × b.Ex.Str → A.V.Fp.s0.W → b.W
  /-- The exit step. -/
  f'    : (A.X.tgt St₁ Az).X → Option R.X.src.X
  g'    : ExtMap (A.X.tgt St₁ Az).Ex R.X.src.Ex
  m'    : (A.X.tgt St₁ Az).X × (A.X.tgt St₁ Az).W → R.X.src.X × R.X.src.W
  back' : (A.X.tgt St₁ Az).X × (A.X.tgt St₁ Az).Ex.Str → R.X.src.W → (A.X.tgt St₁ Az).W

namespace LdRefT
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {R : LdORE F E Kc} {b : LdStage E Kc} (T : LdRefT R b)

def entry : LdMv b T.A.V.Fp.s0 := .step b T.A.V.Fp.s0 T.f T.g T.m T.back
def exit : LdMv (T.A.X.tgt T.St₁ T.Az) R.X.src :=
  .step _ R.X.src T.f' T.g' T.m' T.back'

/-- The last segment: entry step; body; exit step. -/
def tail : LdProg b R.X.src :=
  (((LdProg.nil b).snoc T.entry).app (T.A.body T.St₁ T.fz T.Az)).snoc T.exit

structure OK (pp : ℕ) : Prop where
  entry : T.entry.Hyp
  body  : T.A.OK pp
  ends  : T.A.X.Ends T.St₁ T.fz T.Az
  exit  : T.exit.Hyp

end LdRefT

/-- The reference request: the first sending and `more`; the segments of L; the last segment T, then
`R.lastP`. -/
def ldReqRef {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (R : LdORE F E Kc) {a : LdStage E Kc} (first : LdSendD a) (a₁ : LdStage E Kc)
    (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) : LdReq a R.z :=
  R.reqOf first a₁ more hm b L.segs T.tail

namespace Spec

def ldReqRef_seg : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E)
      (a : LdStage E Kc) (S : LdRefS E Kc I a),
    S.OK pp → S.seg.Hyp

def ldReqRef_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E)
      (a b : LdStage E Kc) (L : LdRefL E Kc I a b),
    L.OK pp → L.segs.Hyp

def ldReqRef_tail : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (b : LdStage E Kc) (T : LdRefT R b),
    T.OK pp → T.tail.Hyp

/-- The reference request's hypotheses. -/
def ldReqRef_hyp : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b),
    first.Hyp → more.Hyp → L.OK pp → T.OK pp → 2 ≤ R.n → R.Z.OK →
    R.Tie → (ldReqRef R first a₁ more hm b L T).Hyp

end Spec

theorem ldReqRef_seg : Spec.ldReqRef_seg := fun E Kc _ _ pp _ _ _ S h =>
  LdSeg.pre_hyp (S.K.seg S.l S.Qc) S.entry rfl h.entry
    (ldSegRefAll_one E Kc pp _ S.A S.K S.l S.Qc h.body h.ends h.ev h.named h.fold h.snd)

theorem ldReqRef_segs : Spec.ldReqRef_segs := by
  intro E Kc _ _ pp _ I a b L
  induction L with
  | nil => intro _; rw [LdRefL.segs, LdSegs.Hyp]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.OK] at h
      rw [LdRefL.segs, LdSegs.Hyp]
      exact ⟨ih h.1, ldReqRef_seg E Kc pp _ _ S h.2⟩

theorem ldReqRef_tail : Spec.ldReqRef_tail := fun _ E Kc _ _ _ _ _ pp _ _ _ T h =>
  (LdProg.hyp_snoc _ _).2
    ⟨(ldProg_app_hyp E Kc _ _ _ _ _).2
        ⟨(LdProg.hyp_snoc _ _).2 ⟨LdProg.hyp_nilK _, h.entry⟩,
          ldSegRefAll_body E Kc pp _ T.A T.St₁ T.fz T.Az h.body h.ends⟩,
      h.exit⟩

theorem ldReqRef_hyp :
    Spec.ldReqRef_hyp := fun F E Kc _ _ _ _ _ pp _ R a first a₁ more hm b L T h1 h2 hL hT hn hZ hTie =>
  ldOREAt_hyp F E Kc R a first a₁ more hm b L.segs T.tail h1 h2 (ldReqRef_segs E Kc pp _ _ _ L hL)
    (ldReqRef_tail F E Kc pp R b T hT) hn hZ hTie

end Cb
