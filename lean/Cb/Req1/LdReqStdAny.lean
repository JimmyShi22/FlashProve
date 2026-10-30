-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqStdAny.lean: the reference request with standard senders, the pads' field chosen
sending by sending.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs: an assembly on
Cb/Req1/LdReqProtoStd.lean, Cb/Req1/LdReqRefStd.lean. Generic.
The pads' field is the first argument of `d.IsStd` (Cb/Req1/LdReqProtoStd.lean) and of a layout
`Sig.StdL` (Cb/Ld/LdSendStdL.lean). d is a sending (`LdSendD a`, Cb/Req1/LdSegKit.lean); L, S, T are
the list of segments, a segment and the last segment of the reference request
(Cb/Req1/LdReqRef.lean), A a body (`LdRefD`, Cb/Req1/LdSegRefAll.lean).

Why: Cb/Req1/LdReqRefStd.lean's record `LdReqRefDS` has, in its clause "std", one pads' field for
the whole request. In this protocol's technical report (lean/CREDITS.md) an oracle message all of
whose rows are over the base field has its pad entries in the base field, every other one has one
pad entry of E for each answer.
So sendings differ in their pads' field. Nothing in the proofs ties the sendings' fields together:
each sending's hypotheses follow from its own equation and conditions (`Spec.ldReqStdAny_send`).

Main names:
  `d.IsStdAny`: `d.IsStd Fp` for some pads' field Fp.
  `A.ProtoSA pp`, `S.ProtoSA pp`, `L.ProtoSA pp`: `ProtoS`'s clauses, letter for letter, with
    `IsStdAny` for `IsStd Fp`.
  `A.ProtoSA pp → A.Proto pp` (`LdRefD.ProtoSA.toProto`), `S.ProtoSA pp → S.Proto pp`,
    `Spec.ldReqStdAny_list`: `L.ProtoSA pp → L.Proto pp` (Cb/Req1/LdReqModel.lean's "Proto": the
    hypotheses on senders and links: theorems here).
  `LdReqRefDSA ..`: `LdReqRefDS` with `std : first.IsStdAny ∧ L.ProtoSA pp ∧ T.A.ProtoSA pp`; all
    other clauses as they are there.
  `Spec.ldReqStdAny_ofDS`: `LdReqRefDS .. → LdReqRefDSA ..` (so a guard of `LdReqRefDS` is one of
    `LdReqRefDSA`).
  `Spec.ldReqStdAny`: `LdReqRefDSA .. → LdReqRefD ..` (at more := the empty list).

Limits: declared differences that stay. Within one sending the pads' field is still one: a standard
layout (Cb/Ld/LdSendStdL.lean) has one field for the whole family sent in one prover message. And
the data and free entries of a standard layout are elements of E by type: a message whose words as
sent are over the base field is not covered at all (Cb/Req1/LdReqJohnSubNo.lean). So what is gained
here is small: pads in the base field for a sending in the plain format, which "evades" allows
within unique decoding.
What the heads of Cb/Req1/LdReqProtoStd.lean and Cb/Req1/LdReqRefStd.lean list as not said is not
said here either. This holds but for the clauses lay, layT, layB, fmt and the numbers of
`LdReqRefDSA`, which are `LdReqRefDS`'s as they are there. On what still speaks of more than data:
the head of Cb/Req1/LdReqRefStd.lean. This file says nothing on an instance with two different pads'
fields.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefStd

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open scoped ENNReal

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- The sending is the standard one, for some pads' field. -/
def LdSendD.IsStdAny {a : LdStage E Kc} (d : LdSendD a) : Prop :=
  ∃ (Fp : Type) (_ : Field Fp) (_ : Fintype Fp) (_ : Algebra Fp E), d.IsStd Fp

structure LdRefD.ProtoSA {I : LdRefIx E} (A : LdRefD E Kc I) (pp : ℕ) : Prop where
  front  : A.V.Proto pp
  ok     : A.Xa.Q.D.p.OK
  places : A.Xa.Q.Places
  uniq   : Uniq (2 * A.Xa.Q.D.p.D) A.Xa.Q.D.p.rdx A.Xa.Q.D.p.P pp
  send1  : A.Xa.Q.D.d1.IsStdAny
  send3  : A.Xa.Q.D.d3.IsStdAny
  tabQ   : A.Xa.Q.D.p.q ≤ 2 ^ A.Xa.Q.d
  tabH   : A.Xa.Q.D.p.H ≤ 2 ^ A.Xa.Q.d
  keys   : A.Xa.Q.K ≤ 2 ^ A.Xa.Q.v
  tags   : A.Xa.Q.tag 0 ≠ A.Xa.Q.tag 1
  inj    : Function.Injective A.Xa.ι
  named  : A.Xa.A.PlacesIn (fun j => j ∈ Set.range A.Xa.ι)
  adm    : A.Xa.A.H.lkb.Adm pp
  bits   : A.Xa.Bits
  reads  : A.Gr.Reads
  deg    : 2 ≤ A.nt
  ev     : A.Zt.OK

structure LdRefS.ProtoSA {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a) (pp : ℕ) :
    Prop where
  body  : S.A.ProtoSA pp
  ev    : S.K.Z.OK
  named : ∀ n, S.A.Gr.Named n → S.K.grp.mem n.1
  fold  : S.K.R.c1.fold.IsGrp S.l
  snd   : S.Qc.snd.IsStdAny

def LdRefL.ProtoSA {I : LdRefIx E} {a : LdStage E Kc} (pp : ℕ) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.ProtoSA pp ∧ S.ProtoSA pp

end

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The record, the pads' field chosen sending by sending. -/
structure LdReqRefDSA (pp : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) : Prop where
  duty   : LdModelDuty R L T
  std    : first.IsStdAny ∧ L.ProtoSA pp ∧ T.A.ProtoSA pp
  deg    : 2 ≤ R.n
  ev     : R.Z.OK
  tie    : R.Tie
  own    : R.X.Own
  lay    : L.LayJ pp (ldReqRef1 R first b L T).base₀
  layT   : T.A.ZkAt pp (fun f =>
    ∃ g,
      L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f)
  layB   : ∃ (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
    (∀ n, R.Rd n → Rd n) ∧
    ∃ g,
      L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g →
        T.tail.After Y
          (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M)
  fmt    : ∃ (px' : first.Wp' → R.Cf.conf.PIdx)
        (φb : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx b.J),
      (∀ w, px' (first.D.rest w).2 = w.2.1) ∧
      L.FmtP (first.tgt.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) Prod.snd px'
          ((LdStage.start E Kc (R.O.jReq core)).S.qSum first.N qφ first.t)) φb ∧
      T.FmtAt φb q
  bFirst : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞)
  bSegs  : L.Nums κ
  bTail  : T.A.Nums κ
  bLast  : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ

end

namespace Spec

def ldReqStdAny_send : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (d : LdSendD a), d.IsStdAny → d.Hyp

def ldReqStdAny_ofBody : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (I : LdRefIx E)
      (A : LdRefD E Kc I) (pp : ℕ),
    A.ProtoS F pp → A.ProtoSA pp

def ldReqStdAny_ofSeg : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (I : LdRefIx E)
      (a : LdStage E Kc) (S : LdRefS E Kc I a) (pp : ℕ),
    S.ProtoS F pp → S.ProtoSA pp

def ldReqStdAny_ofList : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (I : LdRefIx E)
      (a b : LdStage E Kc) (L : LdRefL E Kc I a b) (pp : ℕ),
    L.ProtoS F pp → L.ProtoSA pp

def ldReqStdAny_list : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a b : LdStage E Kc)
      (L : LdRefL E Kc I a b) (pp : ℕ),
    L.ProtoSA pp → L.Proto pp

/-- What meets the record with one pads' field meets this one. -/
def ldReqStdAny_ofDS : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ)
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    LdReqRefDS pp R core first b L T qφ q κ → LdReqRefDSA pp R core first b L T qφ q κ

/-- States: the record gives `LdReqRefD` (Cb/Req1/LdReqRefFinal.lean), at the empty list for
`more`. -/
def ldReqStdAny : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ)
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    LdReqRefDSA pp R core first b L T qφ q κ →
    LdReqRefD pp R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b L T qφ q κ

end Spec

theorem ldReqStdAny_send : Spec.ldReqStdAny_send := by
  intro E Kc _ _ a d ⟨Fp, _, _, _, h⟩
  exact ldReqProtoStd_send Fp E Kc a d h

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem LdRefD.ProtoSA.toProto {I : LdRefIx E} {A : LdRefD E Kc I} {pp : ℕ} (h : A.ProtoSA pp) :
    A.Proto pp :=
  ⟨h.front, h.ok, h.places, h.uniq, ldReqStdAny_send E Kc _ _ h.send1,
    ldReqStdAny_send E Kc _ _ h.send3, h.tabQ, h.tabH, h.keys, h.tags, h.inj, h.named, h.adm,
    h.bits, h.reads, h.deg, h.ev⟩

theorem LdRefS.ProtoSA.toProto
    {I : LdRefIx E} {a : LdStage E Kc} {S : LdRefS E Kc I a} {pp : ℕ} (h : S.ProtoSA pp) :
    S.Proto pp :=
  ⟨h.body.toProto, h.ev, h.named, ldReqProtoStd_fold E Kc _ _ h.fold,
    ldReqStdAny_send E Kc _ _ h.snd⟩

end

theorem ldReqStdAny_ofBody : Spec.ldReqStdAny_ofBody := fun F _ _ i1 i2 _ _ i3 _ _ _ h =>
  ⟨h.front, h.ok, h.places, h.uniq, ⟨F, i1, i2, i3, h.send1⟩, ⟨F, i1, i2, i3, h.send3⟩,
    h.tabQ, h.tabH, h.keys, h.tags, h.inj, h.named, h.adm, h.bits, h.reads, h.deg, h.ev⟩

theorem ldReqStdAny_ofSeg : Spec.ldReqStdAny_ofSeg := fun F E Kc i1 i2 _ _ i3 I _ S pp h =>
  ⟨ldReqStdAny_ofBody F E Kc I S.A pp h.body, h.ev, h.named, h.fold, ⟨F, i1, i2, i3, h.snd⟩⟩

theorem ldReqStdAny_ofList : Spec.ldReqStdAny_ofList := by
  intro F E Kc _ _ _ _ _ I a b L pp
  induction L with
  | nil => intro _; rw [LdRefL.ProtoSA]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.ProtoS] at h
      rw [LdRefL.ProtoSA]
      exact ⟨ih h.1, ldReqStdAny_ofSeg F E Kc I _ S pp h.2⟩

theorem ldReqStdAny_list : Spec.ldReqStdAny_list := by
  intro E Kc _ _ I a b L pp
  induction L with
  | nil => intro _; rw [LdRefL.Proto]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.ProtoSA] at h
      rw [LdRefL.Proto]
      exact ⟨ih h.1, h.2.toProto⟩

theorem ldReqStdAny_ofDS : Spec.ldReqStdAny_ofDS := by
  intro F E Kc _ _ _ _ _ pp R core first b L T qφ q κ h
  obtain ⟨Fp, i1, i2, i3, s1, s2, s3⟩ := h.std
  exact
    { duty := h.duty,
      std := ⟨⟨Fp, i1, i2, i3, s1⟩,
          ldReqStdAny_ofList Fp E Kc _ _ _ L pp s2,
          ldReqStdAny_ofBody Fp E Kc _ T.A pp s3⟩,
      deg := h.deg, ev := h.ev, tie := h.tie, own := h.own
      lay := h.lay, layT := h.layT, layB := h.layB, fmt := h.fmt, bFirst := h.bFirst,
        bSegs := h.bSegs, bTail := h.bTail, bLast := h.bLast }

theorem ldReqStdAny : Spec.ldReqStdAny := by
  intro F E Kc _ _ _ _ _ pp R core first b L T qφ q κ h
  obtain ⟨px', φb, f1, f2, f3⟩ := h.fmt
  exact
    { model := h.duty.model
      proto := ⟨ldReqStdAny_send E Kc _ _ h.std.1, LdProg.hyp_nilK _,
        ldReqStdAny_list E Kc _ _ _ L pp h.std.2.1, h.std.2.2.toProto, h.deg, h.ev, h.tie⟩
      own := h.own
      lay := h.lay
      layT := h.layT
      layB := h.layB
      fmt := ⟨px', _, φb, f1, (LdProg.fmt_nil _ _ _).2 rfl, f2, f3⟩
      bFirst := h.bFirst
      bMore := LdProg.below_nil _ κ
      bSegs := h.bSegs
      bTail := h.bTail
      bLast := h.bLast }

end Cb
