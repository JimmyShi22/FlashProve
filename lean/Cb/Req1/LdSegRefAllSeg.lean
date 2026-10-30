-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefAllSeg.lean: the closed reference segment with one group: what zero knowledge asks
of it, beside its hypotheses; its format; its errors round by round; the masks that cross it.

Book-keeping: four statements on the closed body are carried over to the whole segment, body and
closing; the link bridge-to-fold l and the data Qc of the closing stay parameters.
Statements and proofs. An assembly: the closed body's theorems (Cb/Req1/LdSegRefAllZk*.lean,
Cb/Req1/LdSegRefFmt.lean, Cb/Req1/LdSegRefBelow.lean, Cb/Req1/LdSegRefTenLook.lean) are combined
with the rules for a segment with one group (Cb/Req1/LdSegWholeZk.lean, Cb/Req1/LdSegWholeFmt.lean,
Cb/Req1/LdSegBelowRef.lean, Cb/Req1/LdSegWholeAfter.lean). Nothing of a text is rendered here.

Main names (pp is the characteristic of E; Mk is finite and not empty in the statements):
  `Spec.ldSegRefAll_one_zk`: (K.seg l Qc).Zk base from the conditions of Spec.ldSegRefAll_zk: the
    closing asks nothing, beside its hypotheses.
  `Spec.ldSegRefAll_one_fmt`: its format, from `A.OK pp`, the readers of the record (`ρ.Laws`,
    `r₁`), the format of the link bridge-to-fold, the one sending's hypotheses and what it hands
    on, the demands backwards (the premises on `qm`, `qc`, `q'`).
  `Spec.ldSegRefAll_one_below`: its errors round by round, as probabilities, are at most κ
    (`(K.seg l Qc).Below κ`), from `A.Nums κ`, the rows' evader's number, the list of the link
    bridge-to-fold, the one sending's number, the locations' number. These errors are numbers that a
    link lists (the data field `Link.P.err`): that a link is sound at the numbers that it lists is
    not said by `Spec.ldSegRefAll_one_below`.
  `Spec.ldSegRefAll_one_old`: under the hypotheses of `Spec.ldSegRefX_out`
    (Cb/Req1/LdSegRefTenLook.lean): a wide fact that is fresh at the entry (`W.Pass`) and is read
    by neither late block crosses the whole segment, in this sense:
    `(K.seg l Qc).After base ⟨Kc₂, kc₂, Mk, put₂⟩`, if bridge-to-fold, the one sender and the cut
    of the locations do not look at it.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefAllZkProofs
import Cb.Req1.LdSegRefTenLook
import Cb.Req1.LdSegRefFmt
import Cb.Req1.LdSegRefBelow
import Cb.Req1.LdSegWholeAfter
import Cb.Req1.LdSegWholeFmt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain
open scoped ENNReal

namespace Spec

def ldSegRefAll_one_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (A : LdRefD E Kc I)
      [Nonempty I.C.E0.Str] (K : LdRefC1 A) (l : Link Kc K.R.c1.fold.src.J K.R.c1.fold.mid)
      (Qc : LdCloseD K.R.c1.fold) (W : LdRefW A) (F : LdRefF A) (κ : A.Gh → Kc)
      (RdL : A.Xa.Q.T.Ent → Prop) (base : MaskFact A.V.Fp.s0.J.W → Prop),
    A.OK pp → A.Ghost κ → F.OK pp → A.FrontFacts F base → A.Late W F RdL base → (K.seg l Qc).Zk base

def ldSegRefAll_one_fmt : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (E0 : ExtSpec) (Rc Pw : Type)
      (I : LdRefIx E) (A : LdRefD E Kc I) (K : LdRefC1 A)
      (l : Link Kc K.R.c1.fold.src.J K.R.c1.fold.mid) (Qc : LdCloseD K.R.c1.fold)
      (i : IxAt E0 I.C.E0) (ρ : LdRefR A Rc) (px : I.C.PIdx × (A.W₁ × A.Gh) → Pw)
      (px' : Qc.Wp' → Pw) (q : Finset A.Xa.Q.D.s0.Ex.Pos → Prop) (r₁ : K.St₁ → Rc)
      (qm : Finset K.R.c1.fold.mid.E.Pos → Prop)
      (qc : Finset K.R.c1.fold.tgt.Ex.Pos → Prop) (q' : Finset Qc.loc.tgt.Ex.Pos → Prop),
    A.OK pp → ρ.Laws → (∀ z, r₁ (K.fz z) = ρ.rT (A.X.stOf z).2) →
    l.Fmt (K.R.c1.fold.src.fmt i (fun st => r₁ st.2) px
        ((A.Xa.Q.D.S.sum A.Xa.Q.D.N).qSum
          A.Xa.Q.D.N' (A.Xa.Q.D.S.qSum A.Xa.Q.D.N q A.Xa.Q.D.t) A.Xa.Q.D.t'))
      (K.R.c1.fold.fmtMid i r₁ px qm) →
    (∀ U V, (∀ x, x ∈ V ↔ ∃ u ∈ U, x ∈ K.R.c1.fold.pE.src u) → qc U → qm V) → Qc.snd.Hyp →
    (∀ w, px' (Qc.Sn.rest w).2 = px w.2.2) →
    (∀ ϱ U, q' U → K.R.c1.fold.tgt.S.qSum Qc.N qc Qc.tN (Qc.loc.link.R.need ϱ U)) →
    (K.seg l Qc).Fmt (A.V.Fp.s0.fmt i ρ.rcV px q) (Qc.loc.tgt.fmt i (fun st => r₁ st.2) px' q')

def ldSegRefAll_one_below : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I) (K : LdRefC1 A)
      (l : Link Kc K.R.c1.fold.src.J K.R.c1.fold.mid) (Qc : LdCloseD K.R.c1.fold) (κ : ℝ≥0∞),
    A.Nums κ → (K.Z.err : ℝ≥0∞) ≤ κ * (Fintype.card K.Z.D : ℝ≥0∞) → Err.Below l.P.err κ →
    (ldSendFamErr Qc.N Qc.Sd Qc.L : ℝ≥0∞) ≤ κ * (Fintype.card Qc.Sd.D : ℝ≥0∞) →
    (((Fintype.card K.Pf - K.e - 1) ^ Qc.t : ℕ) : ℝ≥0∞) ≤
      κ * (Fintype.card (Fin Qc.t → K.Pf) : ℝ≥0∞) →
    (K.seg l Qc).Below κ

def ldSegRefAll_one_old : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (A : LdRefD E Kc I)
      [Nonempty I.C.E0.Str] (K : LdRefC1 A) (l : Link Kc K.R.c1.fold.src.J K.R.c1.fold.mid)
      (Qc : LdCloseD K.R.c1.fold) (W : LdRefW A) (F : LdRefF A) (κ : A.Gh → Kc)
      (base : MaskFact A.V.Fp.s0.J.W → Prop) (own : A.Xa.Q.D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → A.Xa.Q.D.S.Ent → E) (Kc₁ : Type) (kc₁ : K.R.c1.fold.tgt.J.W → Kc₁)
      (put₁ : Mk → Kc₁ → Kc₁) (Kc₂ : Type) (kc₂ : Qc.snd.tgt.J.W → Kc₂) (put₂ : Mk → Kc₂ → Kc₂),
    A.OK pp → A.Ghost κ → F.OK pp → W.Pass F base own Mk val → A.Xa.A.MaskOK A.Xa.Dt →
    (∀ n, A.Xa.A.srAll A.Xa.Dt n → W.Rd2 n ∧ ¬ A.own2 own n) → A.X.Own →
    (∀ n, A.Rdt n → W.Rd2 n ∧ ¬ A.own2 own n) →
    l.H.Blind ((A.X.tgt K.St₁ K.Az).wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val)).kc
      (fun w => kc₁ (K.R.c1.fold.pW w)) Mk
      ((A.X.tgt K.St₁ K.Az).wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val)).put put₁ →
    (∀ (w w' : K.R.c1.fold.tgt.W) M,
      kc₁ w' = put₁ M (kc₁ w) → ∀ k, Qc.Sn.put w' k = Qc.Sn.put w k) →
    (∀ (w w' : K.R.c1.fold.tgt.W) M (nw : Qc.N.Wit), kc₁ w' = put₁ M (kc₁ w) →
      kc₂ (K.R.c1.fold.tgt.S.join Qc.N (T := OMsg.Wit) (Qc.Sn.rest w').1 nw, (Qc.Sn.rest w').2) =
        put₂ M (kc₂
            (K.R.c1.fold.tgt.S.join Qc.N (T := OMsg.Wit) (Qc.Sn.rest w).1 nw, (Qc.Sn.rest w).2))) →
    (∀ (w w' : Qc.loc.src.J.W) M,
      kc₂ w' = put₂ M (kc₂ w) → Qc.loc.cut (Qc.loc.S.msgs w'.1) = Qc.loc.cut (Qc.loc.S.msgs w.1)) →
    (K.seg l Qc).After base ⟨Kc₂, kc₂, Mk, put₂⟩

end Spec

theorem ldSegRefAll_one_zk :
    Spec.ldSegRefAll_one_zk := fun E Kc _ _ pp _ _ A _ K l Qc W F κ RdL base h hG hF hFF hL =>
  ldSegWholeZk_one E Kc A.V.Fp.s0 K.R.c1 (K.R.Y.body K.R.c1.bat.src K.tensor) K.kinds l Qc base
    (ldSegRefAll_zk E Kc pp _ A W F κ RdL K.St₁ K.fz K.Az base h hG hF hFF hL)

theorem ldSegRefAll_one_fmt :
    Spec.ldSegRefAll_one_fmt := fun E Kc _ _ pp _ E0 Rc Pw _ A K l Qc i ρ px px' q r₁ qm qc q' h hρ hr hl hq hs hp hn =>
  ldSegWholeFmt_one E Kc E0 Rc Pw A.V.Fp.s0 K.R.c1 (K.R.Y.body K.R.c1.bat.src K.tensor)
    K.kinds l Qc _ i r₁ px px' _ qm qc q'
    (ldSegRefAll_fmt E Kc pp E0 Rc Pw _ A i ρ px q K.St₁ K.fz K.Az r₁ h hρ hr) hl hq hs hp hn

theorem ldSegRefAll_one_below :
    Spec.ldSegRefAll_one_below := fun E Kc _ _ _ A K l Qc κ h hZ hl hs ht =>
  ldSegBelowRef_one E Kc A.V.Fp.s0 K.R.c1 (K.R.Y.body K.R.c1.bat.src K.tensor) K.kinds l Qc κ
    (ldSegRefAll_below E Kc _ A K.St₁ K.fz K.Az κ h) hZ hl hs ht

theorem ldSegRefAll_one_old : Spec.ldSegRefAll_one_old := fun E Kc _ _ pp _ _ A _ K l Qc W F κ base own Mk _ _ val Kc₁ kc₁ put₁ Kc₂ kc₂ put₂ h hG hF hP hM hap hO hR hl h1 h2 h3 =>
  ldSegAfter_old E Kc A.V.Fp.s0 K.R.c1 (K.R.Y.body K.R.c1.bat.src K.tensor) K.kinds l Qc base
    ((A.X.tgt K.St₁ K.Az).wideFact W.Rd2 W.Rr2 (A.own2 own) Mk (A.val2 val)) Kc₁ kc₁ put₁ Kc₂ kc₂
    put₂ (ldSegRefX_out E Kc pp _ A W F κ base own Mk val K.St₁ K.fz K.Az h hG hF hP hM hap hO hR)
    hl h1 h2 h3

end Cb
