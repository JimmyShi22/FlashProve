-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefCross.lean: under the hypotheses of its statements, a wide fact on fresh masks that
is fresh at the segment's entry is fresh at two places late in the closed body of the reference
segment.

Definitions, statements and proofs. Rules of the framework only; nothing of a text is rendered
here.

Why: the masks of a segment's masked blocks are sent before the segment. Two of these blocks are
late in the body (Cb/Req1/LdSegRefAll.lean): the digits' lookup, after the front and two sendings;
the batching of the tensor rows, after the digits' lookup too. Here, under the hypotheses of the
statements below: a wide fact (Cb/Req1/LdSegCarry.lean) that is fresh at the segment's entry is
fresh at these two places.
Names: `LdSendD.NoLook`: Cb/Req1/LdSegRefCarry.lean; `LdProg.After`: Cb/Req1/LdReq.lean.

Main names (Mk is finite and not empty in the statements):
  `A.up`: an entry of the oracle messages that are open at the entry, as an entry of those that are
    open late in the body.
  `LdRefW A`: the wide reading: Rd, Rr over the messages at the entry; RdN, RrN, RdN', RrN' for the
    two families that are sent; `W.Rd2`, `W.Rr2`: over all.
  `A.own2`, `A.val2`: own entries and values, over all messages: none among the new ones.
  `LdRefF A`: the letters of the front's conditions (Cb/Req1/LdSegFrontRefZk.lean).
  `W.Pass F base own Mk val`: what is asked of a wide fact: it is in "base"; overwriting its masks
    changes no entry that the front's lookup or one of its sumchecks reads ("quiet") (exactly:
    `F.Quiet`: three clauses `ldQuiet`, Cb/Req1/LdSegFrontTabZk.lean); the two senders do not look.
  `Spec.ldSegRefX_sameOn`: under `Adm pp` (pp the characteristic of E), `X.A.MaskOK X.Dt` and
    `Nonempty E₀.Str`: the assembled lookup on the digits reads its data and its own masks only.
  `Spec.ldSegRefX_lk`: under `A.OK pp` (pp the characteristic of E), `A.Ghost κ`, `F.OK pp`,
    `W.Pass F base own Mk val` and `Nonempty I.C.E0.Str`: the fact is fresh before the digits'
    lookup.
  `Spec.ldSegRefX_tn`: and before the batching's block, if moreover `A.Xa.A.MaskOK A.Xa.Dt` and the
    digits' lookup reads only entries of the wide reading that are not own.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefAllProofs
import Cb.Req1.LdSegRefAsmZk
import Cb.Req1.LdSegFrontRefZk
import Cb.Req1.LdSegRefFact
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain

namespace LdRefD
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)

/-- an entry of the messages at the entry, among all entries -/
def up (n : A.Xa.Q.D.S.Ent) : A.Xa.Q.T.Ent := ⟨.inl (.inl n.1), n.2⟩

/-- own entries and values, over all messages -/
def own2 (own : A.Xa.Q.D.S.Ent → Prop) : A.Xa.Q.T.Ent → Prop :=
  (A.Xa.Q.D.S.sum A.Xa.Q.D.N).sumP A.Xa.Q.D.N'
    (A.Xa.Q.D.S.sumP A.Xa.Q.D.N own fun _ => False) fun _ => False
def val2 {Mk : Type} (val : Mk → A.Xa.Q.D.S.Ent → E) (M : Mk) : A.Xa.Q.T.Ent → E :=
  (A.Xa.Q.D.S.sum A.Xa.Q.D.N).sumV A.Xa.Q.D.N'
    (A.Xa.Q.D.S.sumV A.Xa.Q.D.N (val M) fun _ => 0) fun _ => 0

end LdRefD

/-- The wide reading. -/
structure LdRefW {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I) where
  Rd   : A.Xa.Q.D.S.Ent → Prop
  Rr   : A.Xa.Q.D.S.O → Prop
  RdN  : A.Xa.Q.D.N.Ent → Prop
  RrN  : A.Xa.Q.D.N.O → Prop
  RdN' : A.Xa.Q.D.N'.Ent → Prop
  RrN' : A.Xa.Q.D.N'.O → Prop

/-- The letters of the front's conditions. -/
structure LdRefF {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I) where
  Dt  : A.V.Fp.A0.J → Prop
  RdK : A.V.Fp.A0.J → Prop
  Cc  : A.V.Fp.St × E → (A.V.Fp.A0.J → E) → Prop
  Rd0 : A.V.Fp.Z.T.J → Prop
  RdS : ∀ i, (A.V.T i).J → Prop

namespace LdRefF
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {A : LdRefD E Kc I} (F : LdRefF A)

/-- the front's conditions, among them on places, on numbers and on the claim Cc (`ZkOK`,
Cb/Req1/LdSegRefLkpPreZk.lean) -/
structure OK (pp : ℕ) : Prop where
  lk   : A.V.Fp.ZkOK pp F.Dt F.RdK F.Cc
  own0 : A.V.Fp.Z.T.OwnOur F.Rd0
  own  : ∀ j ≤ A.V.m, (A.V.T j).OwnOur (F.RdS j)

/-- overwriting the masks of f changes no entry that the front reads (exactly: the three fields
below; `ldQuiet`: Cb/Req1/LdSegFrontTabZk.lean) -/
structure Quiet (f : MaskFact (A.Xa.Q.D.S.Wit × (I.C.PIdx × (A.W₁ × A.Gh)))) : Prop where
  lk  : ldQuiet A.Xa.Q.D.S f A.V.Fp.msg (A.V.Fp.A.srAll F.Dt)
  s0  : ldQuiet A.Xa.Q.D.S f A.V.Fp.msg0 F.Rd0
  s   : ∀ j ≤ A.V.m, ldQuiet A.Xa.Q.D.S f (A.V.msg j) (F.RdS j)

end LdRefF

namespace LdRefW
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {A : LdRefD E Kc I} (W : LdRefW A)

def Rd2 : A.Xa.Q.T.Ent → Prop :=
  (A.Xa.Q.D.S.sum A.Xa.Q.D.N).sumP A.Xa.Q.D.N' (A.Xa.Q.D.S.sumP A.Xa.Q.D.N W.Rd W.RdN) W.RdN'
def Rr2 : A.Xa.Q.T.O → Prop :=
  (A.Xa.Q.D.S.sum A.Xa.Q.D.N).sumO A.Xa.Q.D.N' (A.Xa.Q.D.S.sumO A.Xa.Q.D.N W.Rr W.RrN) W.RrN'

/-- the wide fact at the entry -/
def fact (own : A.Xa.Q.D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (val : Mk → A.Xa.Q.D.S.Ent → E) : MaskFact A.Xa.Q.D.s0.J.W :=
  A.Xa.Q.D.s0.wideFact W.Rd W.Rr own Mk val

/-- What is asked of a wide fact. -/
structure Pass (F : LdRefF A) (base : MaskFact A.V.Fp.s0.J.W → Prop) (own : A.Xa.Q.D.S.Ent → Prop)
    (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → A.Xa.Q.D.S.Ent → E) : Prop where
  inBase : base (W.fact own Mk val)
  quiet  : F.Quiet (W.fact own Mk val)
  send1  : A.Xa.Q.D.d1.NoLook W.Rd W.Rr own
  send3  : A.Xa.Q.D.d3.NoLook (A.Xa.Q.D.S.sumP A.Xa.Q.D.N W.Rd W.RdN)
    (A.Xa.Q.D.S.sumO A.Xa.Q.D.N W.Rr W.RrN) (A.Xa.Q.D.S.sumP A.Xa.Q.D.N own fun _ => False)

end LdRefW

namespace Spec

/-- States, under the hypotheses below: the assembled lookup on the digits reads its data and its
own masks only. -/
def ldSegRefX_sameOn : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp]
      (X : LdDgA E Kc E₀ Wp) [Nonempty E₀.Str],
    X.A.H.lkb.Adm pp → X.A.MaskOK X.Dt →
    (X.A.baseN X.ι E₀ X.Q.T.Msg Wp Kc X.Q.T.ents).SameOn X.Q.T.ents (X.A.srAll X.Dt)

/-- Fresh before the digits' lookup, given "base" (`LdProg.After`: Cb/Req1/LdReq.lean). (not all
hypotheses are named here: see the statement below) -/
def ldSegRefX_lk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (A : LdRefD E Kc I)
      [Nonempty I.C.E0.Str] (W : LdRefW A) (F : LdRefF A) (κ : A.Gh → Kc)
      (base : MaskFact A.V.Fp.s0.J.W → Prop) (own : A.Xa.Q.D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → A.Xa.Q.D.S.Ent → E),
    A.OK pp → A.Ghost κ → F.OK pp → W.Pass F base own Mk val →
    (A.Xa.Q.pre A.Xa.mult).After (A.Xa.Q.D.prog.After (A.V.prog.After base))
      ((A.Xa.Q.lkS A.Xa.mult).wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val))

/-- Fresh before the batching's block, given "base" (`LdMv.After`, `LdProg.After`:
Cb/Req1/LdReq.lean). (not all hypotheses are named here: see the statement below) -/
def ldSegRefX_tn : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (A : LdRefD E Kc I)
      [Nonempty I.C.E0.Str] (W : LdRefW A) (F : LdRefF A) (κ : A.Gh → Kc)
      (base : MaskFact A.V.Fp.s0.J.W → Prop) (own : A.Xa.Q.D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → A.Xa.Q.D.S.Ent → E),
    A.OK pp → A.Ghost κ → F.OK pp → W.Pass F base own Mk val → A.Xa.A.MaskOK A.Xa.Dt →
    (∀ n, A.Xa.A.srAll A.Xa.Dt n → W.Rd2 n ∧ ¬ A.own2 own n) →
    A.X.stepIn.After
      (A.Y.step.After
        ((A.Xa.Q.prog A.Xa.mult A.Xa.ent A.Xa.A.nRows A.Xa.lk).After
          (A.Xa.Q.D.prog.After (A.V.prog.After base))))
      (A.X.m0.wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val))

end Spec

theorem ldSegRefX_sameOn : Spec.ldSegRefX_sameOn := by
  intro E Kc E₀ Wp _ _ pp _ X _ hA hM
  have hC := ldSegRef_asm_reads E Kc E₀ Wp X
  exact sameOn_of_piece (b := X.A.baseN X.ι E₀ X.Q.T.Msg Wp Kc X.Q.T.ents)
    (show noOrcs (X.A.baseN X.ι E₀ X.Q.T.Msg Wp Kc X.Q.T.ents).R.shape
      from ldLkpAsm2F_noOrcs E X.A X.Q.Nn X.ι E₀ X.Q.T.Msg Wp Kc X.Q.T.ents)
    (mjp_full (b := X.A.baseN X.ι E₀ X.Q.T.Msg Wp Kc X.Q.T.ents)
      (ldLkpAsm2M_link E pp X.A X.Q.Nn X.ι X.A.ValidMu E₀ X.Q.T.Msg Wp Kc X.Q.T.ents X.Dt
        (X.A.srAll X.Dt) hA (ldLkpAsm2_muValid E X.A hA.1) hM (fun _ h => h) hC)
      (ldLkpAsm2N_plain E X.A X.Q.Nn X.ι E₀ X.Q.T.Msg Wp Kc X.Q.T.ents) (fun _ h => h)
      fun k k' st hk h => hC st k k' (fun j hj => hk j (Or.inl hj)) h)

theorem ldSegRefX_lk : Spec.ldSegRefX_lk := by
  intro E Kc _ _ pp _ I A _ W F κ base own Mk _ _ val h hG hF hP
  have f0 : A.V.prog.After base (W.fact own Mk val) :=
    ldSegFrontRefZk_carry E pp Kc A.Xa.Q.D.s0 A.V F.Dt F.RdK F.Cc F.Rd0 F.RdS base
      (W.fact own Mk val) h.front hF.lk hF.own0 hF.own hP.inBase hP.quiet.lk hP.quiet.s0 hP.quiet.s
  have f1 := ldSegRef_rr_carry _ _ A.Xa.Q.D (A.V.prog.After base) W.Rd W.Rr own Mk val W.RdN W.RrN
    W.RdN' W.RrN' (ldSegRefAll_noLook E Kc _ A κ hG _ _) h.send1 h.send3 hP.send1 hP.send3 f0
  exact ldSegRef_dg_carry _ _ A.Xa.Q A.Xa.mult _ _ _ _ Mk _ f1

theorem ldSegRefX_tn : Spec.ldSegRefX_tn := by
  intro E Kc _ _ pp _ I A _ W F κ base own Mk _ _ val h hG hF hP hM hap
  have f2 := ldSegRefX_lk E Kc pp _ A W F κ base own Mk val h hG hF hP
  -- through the digits' lookup
  have f3 : (A.Xa.Q.prog A.Xa.mult A.Xa.ent A.Xa.A.nRows A.Xa.lk).After
      (A.Xa.Q.D.prog.After (A.V.prog.After base))
      ((A.Xa.Q.lkT A.Xa.ent A.Xa.A.nRows).wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val)) := by
    unfold LdDgP.prog
    rw [LdProg.after_snoc]
    refine (freshGiven_one A.Xa.link _ _).2
      (Or.inr ⟨_, ((A.Xa.Q.lkS A.Xa.mult).wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val)).kc,
          ((A.Xa.Q.lkS A.Xa.mult).wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val)).put,
          f2, ?_⟩)
    exact blind_of_sameOn A.Xa.Q.T
      (ldLkpAsm2N_plain E A.Xa.A A.Xa.Q.Nn A.Xa.ι I.C.E0 A.Xa.Q.T.Msg _ Kc A.Xa.Q.T.ents)
      (ldSegRefX_sameOn E Kc _ _ pp A.Xa h.adm hM) _ Mk _ fun w w' M hw j hj =>
        (segWide_alike (A.Xa.Q.lkS A.Xa.mult) W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val) w w' M hw).1
          j (hap j hj).1 (hap j hj).2
  -- through the step that gathers the rows
  have f4 : A.Y.step.After _ (A.Y.tgt.wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val)) :=
    ldSegRef_ga_carry _ _ A.Gr A.Y.St₀ A.Y.g₀ A.Y.Ar _ _ _ _ Mk _ f3
  -- through the re-bracketing
  exact segWide_keep A.X.S _ _ _ _ I.C.E0 I.C.E0 A.X.src.A A.X.m0.A
    (sideF A.X.S fun x => (x.2.1, (x.1, x.2.2))) (sideG A.X.S (ExtMap.id I.C.E0))
    (sideM A.X.S (fun x => (x.2.1, (x.1, x.2.2))) fun _ w => w.2) (sideB A.X.S fun _ w => w.2)
    (fun x => ((x.1.2.1, (x.1.1, x.1.2.2)), x.2)) (fun _ w => w.2) _ _ _ _ Mk _ (fun _ _ => rfl)
    (fun _ _ _ _ _ => rfl) f4

end Cb
