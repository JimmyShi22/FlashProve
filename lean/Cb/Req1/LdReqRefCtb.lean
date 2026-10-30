-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefCtb.lean: positions, symbols and plain parts of the reference request are countable,
from conditions on the families that it sends, on each closing's link and on the list "more".

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs. Bookkeeping for the passage to one
random oracle (`CtbSh`, CompileK/ImplCountable.lean), by the lemmas of Cb/Obj/LdObjectCtb.lean,
Cb/Obj/LdObjectCtbPre.lean, Cb/Obj/LdObjectCtbReq.lean.
The reference request is the term `ldReqRef`, with its list L of segments S and its last segment T
(Cb/Req1/LdReqRef.lean). `Ctb` of a link says that positions, symbols and plain parts of every round
are countable; of a move, a list of moves, a segment, a request it is what
Cb/Obj/LdObjectCtbReq.lean asks for that. `ctb_req` there gives `r.chain.Ctb` from `r.Ctb`.

Why: the record of countability of the whole object (`Z.FinZ`, Cb/Obj/LdObjectCtbData.lean) asks of
the request's program `r.Ctb`, move by move (Cb/Obj/LdObjectCtbReq.lean). At the reference request
the program is a term, and most of its moves ask nothing.

Main names:
  No hypothesis beside whatever the arguments hold as proofs (the field is finite by type):
    `Spec.ldReqRefCtb_front`: the whole front `V.prog`: the shift, the assembled lookup, claims on
      values into one sum claim, all sumchecks, the steps between.
    `Spec.ldReqRefCtb_lk`: the digits' assembled lookup `X.lk`.
    `Spec.ldReqRefCtb_ten`: the batching of the tensor rows `X.prog`. `Spec.ldReqRefCtb_last`: the
      last three moves of a request `R.lastP`.
  `Spec.ldReqRefCtb_body`: the body of a reference segment: asked: the symbols of the two families
    that it sends are countable (`Sig.CtbSy`): the reads' (`D.N`) and the digits' (`D.N'`).
  `S.CtbD`, `L.CtbD`, `T.CtbD`: what is asked of a reference segment (the two families; the
    closing's link `S.l`; the closing's one sending), of a list of them (by recursion), of the last
    segment (the two families). `Spec.ldReqRefCtb_seg`, `Spec.ldReqRefCtb_segs`,
    `Spec.ldReqRefCtb_tail`: these give `S.seg.Ctb`, `L.segs.Ctb`, `T.tail.Ctb`.
  `Spec.ldReqRef_ctb`: the reference request: `first.N.CtbSy`, `more.Ctb`, `L.CtbD`, `T.CtbD` give
    `(ldReqRef R first a₁ more hm b L T).Ctb`.
  `Spec.ldReqRef1_ctb`: the same for the request with one first sending (`ldReqRef1`,
    Cb/Req1/LdReqRefStd.lean: the list "more" is empty): `first.N.CtbSy`, `L.CtbD`, `T.CtbD`.
  The entry and exit steps are steps without rounds: nothing is asked of them.

Limits: what is still asked of a term that is a parameter: `S.l.Ctb` (each closing's link from
bridge to fold) and `more.Ctb` (the list "more"; gone at `ldReqRef1`). This file says nothing on a
protocol. A bound to that, at least: `Spec.ldReqRef_ctb`, `Spec.ldReqRef1_ctb` conclude `Ctb` of the
reference request. It does not say that the conditions can be met: no instance here.
Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldReqRef_ctb` or
   `ldReqRef1_ctb` can be met together. -/
import Cb.Obj.LdObjectCtbReq
import Cb.Req1.LdReqRef
import Cb.Req1.LdReqRefStd

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain Cb.LdLkp

section Kit
variable {E Kc : Type} [Field E] [Fintype E]

theorem LdProg.ctb_app {a b c : LdStage E Kc} (p : LdProg a b) (q : LdProg b c) :
    (p.app q).Ctb ↔ p.Ctb ∧ q.Ctb := by
  induction q with
  | nil => rw [LdProg.app_nil]; exact ⟨fun h => ⟨h, LdProg.ctb_nil _⟩, fun h => h.1⟩
  | snoc q m ih => rw [LdProg.app_snoc, LdProg.ctb_snoc, LdProg.ctb_snoc, ih, and_assoc]

theorem LdProg.ctb_asSub {a b : LdStage E Kc} (p : LdProg a b) (h : p.Ctb) : p.asSub.Ctb := by
  induction p with
  | nil => rw [LdProg.asSub_nil]; exact LdProg.ctb_nil _
  | snoc p m ih =>
    rw [LdProg.asSub_snoc]
    exact (LdProg.ctb_snoc _ _).2
      ⟨ih ((LdProg.ctb_snoc p m).1 h).1, ctb_mv m ((LdProg.ctb_snoc p m).1 h).2⟩

/-- A block at the base as a move. -/
theorem ctb_mvA (a : LdStage E Kc) {St' : Type} (B : Rels Kc St' a.E₀ (a.S.Msg × a.Wp))
    (b : BkA Kc a.S.Msg a.St St' a.E₀ a.Wp) (h : b.Ctb) : (a.mvA B b).Ctb :=
  (Chain.ctb_one _).2 h

/-- One link as a move. -/
theorem ctb_subOne {a b : LdStage E Kc} (l : Link Kc a.J b.J) (h : l.Ctb) :
    (LdMv.sub a b (.one l)).Ctb :=
  (Chain.ctb_one _).2 h

end Kit

/-! ## The parts -/

section Parts
variable {E Kc : Type} [Field E] [Fintype E]

theorem ctb_frPsc (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) :
    (frPsc Kc T S E₀ Wp A0 msg).Ctb :=
  (LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, ctb_mvA _ _ _ (ctb_pscP T.par E₀)⟩

theorem ctb_frIn (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp)) (msg : S.Msg → Z.T.J → E) :
    (frIn Kc Z S E₀ Wp R0 msg).Ctb :=
  (LdProg.ctb_snoc _ _).2
    ⟨(LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, ctb_mvA _ _ _ (ctb_drawR _ _ E₀)⟩,
      ctb_mvA _ _ _ (ctb_pscP Z.T.par E₀)⟩

/-- Shift, step, assembled lookup, step. -/
theorem ctb_preD {S : Sig E} {E₀ : ExtSpec} {Wp : Type} (F : LdPreD E Kc S E₀ Wp) : F.prog.Ctb :=
  (LdProg.ctb_snoc _ _).2
    ⟨(LdProg.ctb_snoc _ _).2
        ⟨(LdProg.ctb_snoc _ _).2
            ⟨(LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, ctb_mvA _ _ _ (ctb_drawR _ _ E₀)⟩, trivial⟩,
          ctb_mvA _ _ _ (ctbA_chainA E₀ S.Msg Wp Kc F.A F.msg)⟩,
      trivial⟩

theorem ctb_frontTw {z : LdStage E Kc} (B : LdFrontTab E Kc z) : ∀ k, (B.tw k).Ctb
  | 0 => ctb_frPsc _ _ _ _ _ _
  | k + 1 =>
    (LdProg.ctb_app _ _).2
      ⟨(LdProg.ctb_snoc _ _).2 ⟨ctb_frontTw B k, trivial⟩, ctb_frPsc _ _ _ _ _ _⟩

theorem ctb_frontTab {z : LdStage E Kc} (B : LdFrontTab E Kc z) (h : B.pre.Ctb) : B.prog.Ctb :=
  (LdProg.ctb_snoc _ _).2
    ⟨(LdProg.ctb_app _ _).2
        ⟨(LdProg.ctb_snoc _ _).2 ⟨(LdProg.ctb_app _ _).2 ⟨h, ctb_frIn _ _ _ _ _ _⟩, trivial⟩,
          ctb_frontTw B B.m⟩,
      trivial⟩

/-- Read; send the reads; the ternary draw; derive; send the digits. -/
theorem ctb_rr {E₀ : ExtSpec} {Wp : Type} (D : LdRrD E Kc E₀ Wp)
    (h1 : D.N.CtbSy) (h3 : D.N'.CtbSy) : D.prog.Ctb :=
  (LdProg.ctb_snoc _ _).2
    ⟨(LdProg.ctb_snoc _ _).2
        ⟨(LdProg.ctb_snoc _ _).2
            ⟨(LdProg.ctb_snoc _ _).2 ⟨(LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, trivial⟩, h1⟩,
              ctb_subOne _ (ctb_drawR D.p.Chal (fun (st : D.St) Θ => (st, Θ)) E₀)⟩,
          trivial⟩,
      h3⟩

/-- Step; the shift; step; the lookup. -/
theorem ctb_dg {E₀ : ExtSpec} {Wp : Type} (Q : LdDgP E Kc E₀ Wp)
    (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (ent : Ms Q.T E₀ → Q.Nn → E) (n : ℕ)
    (lk : Chain Kc (Q.lkS mult).J (Q.lkT ent n).J) (h : lk.Ctb) : (Q.prog mult ent n lk).Ctb :=
  (LdProg.ctb_snoc _ _).2
    ⟨(LdProg.ctb_snoc _ _).2
        ⟨(LdProg.ctb_snoc _ _).2
            ⟨(LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, trivial⟩,
              ctb_subOne _ (ctb_drawR E (Prod.mk : Q.X₄ → E → Q.X₄ × E) E₀)⟩,
          trivial⟩,
      h⟩

theorem ctb_body {E₀ : ExtSpec} {Wp : Type} (Y : LdBodyD E Kc E₀ Wp) (z : LdStage E Kc)
    (tensor : LdProg Y.tgt z) (hf : Y.front.Ctb) (h1 : Y.G.Q.D.N.CtbSy) (h3 : Y.G.Q.D.N'.CtbSy)
    (hl : Y.lk.Ctb) (ht : tensor.Ctb) : (Y.body z tensor).Ctb :=
  (LdProg.ctb_app _ _).2
    ⟨(LdProg.ctb_snoc _ _).2
        ⟨(LdProg.ctb_app _ _).2 ⟨(LdProg.ctb_app _ _).2 ⟨hf, ctb_rr _ h1 h3⟩, ctb_dg _ _ _ _ _ hl⟩,
          trivial⟩,
      ht⟩

end Parts

/-! ## What is asked -/

/-- What is asked of a reference segment. -/
structure LdRefS.CtbD {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E}
    {a : LdStage E Kc} (S : LdRefS E Kc I a) : Prop where
  n1  : S.A.Xa.Q.D.N.CtbSy
  n3  : S.A.Xa.Q.D.N'.CtbSy
  l   : S.l.Ctb
  snd : S.Qc.snd.N.CtbSy

/-- What is asked of a list of reference segments. -/
def LdRefL.CtbD {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc} :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.CtbD ∧ S.CtbD

/-- What is asked of the last segment. -/
structure LdRefT.CtbD {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {R : LdORE F E Kc} {b : LdStage E Kc} (T : LdRefT R b) : Prop where
  n1 : T.A.Xa.Q.D.N.CtbSy
  n3 : T.A.Xa.Q.D.N'.CtbSy

namespace Spec

def ldReqRefCtb_front : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) (V : LdFrontRef E Kc z), V.prog.Ctb

def ldReqRefCtb_lk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E₀ : ExtSpec) (Wp : Type) (X : LdDgA E Kc E₀ Wp), X.lk.Ctb

def ldReqRefCtb_ten : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (St₁ : Type) (fz : X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))),
    (X.prog St₁ fz Az).Ctb

def ldReqRefCtb_last : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc),
    R.lastP.Ctb

/-- The body. -/
def ldReqRefCtb_body : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I) (St₁ : Type)
      (fz : A.X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh)))),
    A.Xa.Q.D.N.CtbSy → A.Xa.Q.D.N'.CtbSy → (A.body St₁ fz Az).Ctb

def ldReqRefCtb_seg : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc I a),
    S.CtbD → S.seg.Ctb

def ldReqRefCtb_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E)
      (a b : LdStage E Kc) (L : LdRefL E Kc I a b),
    L.CtbD → L.segs.Ctb

def ldReqRefCtb_tail : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (b : LdStage E Kc) (T : LdRefT R b),
    T.CtbD → T.tail.Ctb

/-- The reference request. -/
def ldReqRef_ctb : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc) (more : LdProg first.tgt a₁)
      (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b),
    first.N.CtbSy → more.Ctb → L.CtbD → T.CtbD → (ldReqRef R first a₁ more hm b L T).Ctb

/-- With one first sending. -/
def ldReqRef1_ctb : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (a : LdStage E Kc) (first : LdSendD a) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b),
    first.N.CtbSy → L.CtbD → T.CtbD → (ldReqRef1 R first b L T).Ctb

end Spec

theorem ldReqRefCtb_front : Spec.ldReqRefCtb_front := fun _ _ _ _ _ V =>
  ctb_frontTab V.tab (ctb_preD V.Fp)

theorem ldReqRefCtb_lk : Spec.ldReqRefCtb_lk := fun _ Kc _ _ E₀ Wp X =>
  (Chain.ctb_one _).2 (ctb_subN X.A X.ι X.Q.T E₀ Kc Wp X.Q.T.ents)

theorem ldReqRefCtb_ten : Spec.ldReqRefCtb_ten := fun _ _ _ _ X _ _ _ =>
  (LdProg.ctb_snoc _ _).2
    ⟨(LdProg.ctb_snoc _ _).2
        ⟨(LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, trivial⟩, ctb_subOne _ (ctb_batt X.bt X.C.E0)⟩,
      trivial⟩

theorem ldReqRefCtb_last : Spec.ldReqRefCtb_last := fun _ _ _ _ _ _ _ _ R =>
  (LdProg.ctb_snoc _ _).2
    ⟨(LdProg.ctb_snoc _ _).2
        ⟨(LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, trivial⟩,
          ctb_subOne _ (ctb_batt R.X.bt R.X.C.E0)⟩,
      trivial⟩

theorem ldReqRefCtb_body : Spec.ldReqRefCtb_body := fun E Kc _ _ _ A St₁ fz Az h1 h3 =>
  ctb_body A.Y (A.X.tgt St₁ Az) (A.X.prog St₁ fz Az) (ldReqRefCtb_front E Kc _ A.V) h1 h3
    (ldReqRefCtb_lk E Kc _ _ A.Xa) (ldReqRefCtb_ten E Kc A.X St₁ fz Az)

theorem ldReqRefCtb_seg : Spec.ldReqRefCtb_seg := fun E Kc _ _ I _ S h =>
  { body := (LdProg.ctb_app _ _).2
      ⟨(LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, trivial⟩,
        ldReqRefCtb_body E Kc I S.A S.K.St₁ S.K.fz S.K.Az h.n1 h.n3⟩
    fold := (LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, h.l⟩
    snd := h.snd }

theorem ldReqRefCtb_segs : Spec.ldReqRefCtb_segs := by
  intro E Kc _ _ I a b L
  induction L with
  | nil => intro _; rw [LdRefL.segs, LdSegs.Ctb]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.CtbD] at h
      rw [LdRefL.segs, LdSegs.Ctb]
      exact ⟨ih h.1, ldReqRefCtb_seg E Kc I _ S h.2⟩

theorem ldReqRefCtb_tail : Spec.ldReqRefCtb_tail := fun _ E Kc _ _ _ _ _ R _ T h =>
  (LdProg.ctb_snoc _ _).2
    ⟨(LdProg.ctb_app _ _).2
        ⟨(LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, trivial⟩,
          ldReqRefCtb_body E Kc R.ix T.A T.St₁ T.fz T.Az h.n1 h.n3⟩,
      trivial⟩

theorem ldReqRef_ctb : Spec.ldReqRef_ctb := fun F E Kc _ _ _ _ _ R _ _ _ _ _ b L T h1 h2 hL hT =>
  { first := h1
    more := h2
    segs := ldReqRefCtb_segs E Kc R.ix _ _ L hL
    last := LdProg.ctb_asSub _
      ((LdProg.ctb_app _ _).2 ⟨ldReqRefCtb_tail F E Kc R b T hT, ldReqRefCtb_last F E Kc R⟩) }

theorem ldReqRef1_ctb : Spec.ldReqRef1_ctb := fun F E Kc _ _ _ _ _ R a first b L T h1 hL hT =>
  ldReqRef_ctb F E Kc R a first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b L T h1
    (LdProg.ctb_nil _) hL hT

end Cb
