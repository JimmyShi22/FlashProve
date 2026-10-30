-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefClosePack.lean: the closing of the reference segment from a bundle.

Book-keeping: the data of a segment's closing are taken from one record (a bundle).
Definitions, statements as theorems, proofs. Generic: any data A of the reference segment's body
(Cb/Req1/LdSegRefAll.lean), any bundle over the signature at the end of the body
(Cb/Ld/LdGroupPack.lean).
A bundle (`GPack`, Cb/Ld/LdGroupPack.lean) is a record of a group with all that a closing needs:
the data, and proofs of the conditions on them.

Main names:
  `LdRefC1.ofPack A Z pk Zb St₁ fz A₀c : LdRefC1 A`: the closing's data: group, folded complex, its
    form, the held messages are the bundle's; Z: the evader of "many rows into one"; Zb: the
    bridge's evader; what the closing carries is a parameter.
  `refPack_fold`: its bridge-to-fold is `pk.fold ..`, by definition.
  `refPack_l`, `refPack_Q`: the link bridge-to-fold; the one sending and the locations.
  `refPack_hyp`: Zb.OK ⇒ K.R.c1.fold.Hyp l ∧ Qc.snd.Hyp ∧ (all named places lie in members, if
    every name with a named entry has mem) (K, l, Qc: the three terms above).
  `refPack_seg`: so `(K.seg l Qc).Hyp` from: `A.OK pp` (pp the characteristic of E); what is left
    goes over into what the closing carries; the two evaders evade; named ⇒ mem (`ldSegRefAll_one`,
    Cb/Req1/LdSegRefAllProofs.lean).
  `refPack_is`: that segment is the bundle's segment with all five parts (`pk.seg1`,
    Cb/Ld/LdGroupPack.lean) with the reference segment's body as its body, by definition.
  `refPack_fmt`: so, if Zb.OK and tl ≤ t, it has the format of a preamble if the body has it up to
    the demand before the closing (Cb/Ld/LdGroupPackFmt.lean).
  `refPack_zk`: zero knowledge asks of it what it asks of the body, beside their hypotheses.

Limits: this file does not say that A.OK and the condition on what is left can be met. It does not
say that the body has the format, or what zero knowledge asks of it.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefAllProofs
import Cb.Ld.LdGroupPackFmt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)
  (Z : Evader E A.Gr.B) {mem kp : A.Xa.Q.T.O → Prop} [DecidablePred kp] {clP : {o // kp o} → Prop}
  {Pn : Type} [Fintype Pn] {d e t : ℕ} {Lst mC mS mW : ℕ → ℕ} {L L₂ t₂ : ℕ}
  (pk : GPack A.Xa.Q.T mem kp clP Pn d e t Lst mC mS mW L L₂ t₂) (Zb : Evader E (pk.G.Row Unit))
  (St₁ : Type) (fz : A.X.bt.par.Mid → St₁)
  (A₀c : Rels Kc St₁ I.C.E0 ((A.Xa.Q.T.sub kp).Msg × (I.C.PIdx × (A.W₁ × A.Gh))))

/-- The closing's data. -/
@[reducible] def LdRefC1.ofPack : LdRefC1 A where
  Z := Z
  grp := pk.G
  kp := kp
  St₁ := St₁
  fz := fz
  A₀c := A₀c
  Pf := pk.G.P
  Cf := pk.Sh.Cf
  Stf := ((pk.Sh.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
    (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb).jOut pk.G.e).St
  slf := (pk.Sh.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
    (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb).slOut
  e := pk.G.e
  cl := pk.Hd.cl
  sW := pk.Hd.sW
  sJ := pk.Hd.sJ
  sQ := pk.Hd.sQ

theorem refPack_fold :
    (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.c1.fold =
      pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
        (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c := rfl

variable (dw : A.Xa.Q.T.Wit × (I.C.PIdx × (A.W₁ × A.Gh)))
  (w0 : (pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
      (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).tgt.S.Wit ×
    (pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
      (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).tgt.Wp) (tl : ℕ)

/-- the link bridge-to-fold; the one sending and the locations -/
def refPack_l :
    Link Kc (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.c1.fold.src.J
      (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.c1.fold.mid :=
  pk.link (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
    (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c dw
def refPack_Q : LdCloseD (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.c1.fold :=
  pk.close (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
    (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c w0 tl

theorem refPack_hyp (hZb : Zb.OK) :
    (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.c1.fold.Hyp (refPack_l A Z pk Zb St₁ fz A₀c dw) ∧
    (refPack_Q A Z pk Zb St₁ fz A₀c w0 tl).snd.Hyp ∧
    ((∀ n, A.Gr.Named n → mem n.1) →
      ∀ n, A.Gr.Named n → (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).grp.mem n.1) :=
  ⟨gPack_fold pk _ _ Zb A₀c dw hZb,
    gPack_snd pk _ _ Zb A₀c w0 tl,
    fun h n hn => (pk.memI n.1).2 (h n hn)⟩

/-- The reference segment with this closing: its hypotheses. -/
theorem refPack_seg (pp : ℕ) [CharP E pp] (hA : A.OK pp)
    (hE : A.X.Ends St₁ fz (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).Az) (hZ : Z.OK)
    (hZb : Zb.OK) (hn : ∀ n, A.Gr.Named n → mem n.1) :
    ((LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).seg
      (refPack_l A Z pk Zb St₁ fz A₀c dw) (refPack_Q A Z pk Zb St₁ fz A₀c w0 tl)).Hyp :=
  ldSegRefAll_one E Kc pp _ A (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c) _ _ hA hE hZ
    ((refPack_hyp A Z pk Zb St₁ fz A₀c dw w0 tl hZb).2.2 hn)
    (refPack_hyp A Z pk Zb St₁ fz A₀c dw w0 tl hZb).1
    (refPack_hyp A Z pk Zb St₁ fz A₀c dw w0 tl hZb).2.1

/-- the segment is the bundle's segment with the reference segment's body as its body -/
theorem refPack_is :
    (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).seg
        (refPack_l A Z pk Zb St₁ fz A₀c dw) (refPack_Q A Z pk Zb St₁ fz A₀c w0 tl) =
      pk.seg1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z Zb A₀c
        ((LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.Y.body
          (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.c1.bat.src
          (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).tensor)
        (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).kinds dw w0 tl := rfl

open Classical in
/-- The format, under `hZb` and `ht`, if the body has it up to the demand before the closing
(`hb`). -/
theorem refPack_fmt {E0 : ExtSpec} {Rc Pw : Type} (i : IxAt E0 I.C.E0)
    (rc : St₁ → Rc) (px : I.C.PIdx × (A.W₁ × A.Gh) → Pw)
    (q₂ : Finset
        (I.C.E0.prod
          (pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
            (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).S₂.ext).Pos → Prop)
    (φ : JFmt Kc E0 Rc Pw A.V.Fp.s0.J)
    (hb : ((LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.Y.body
        (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.c1.bat.src
        (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).tensor).Fmt
      φ ((LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.c1.bat.src.fmt
        i (fun st => rc st.2) px (pk.qIn (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z Zb A₀c q₂)))
    (hZb : Zb.OK) (ht : tl ≤ t) :
    ((LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).seg
        (refPack_l A Z pk Zb St₁ fz A₀c dw) (refPack_Q A Z pk Zb St₁ fz A₀c w0 tl)).Fmt
      φ ((refPack_Q A Z pk Zb St₁ fz A₀c w0 tl).loc.tgt.fmt i (fun st => rc st.2) px
        ((pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
            (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).S₂.qSum
          pk.V.N.N₀ q₂ fun _ => t₂)) :=
  gPack_seg1_fmt pk (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z Zb A₀c _
    (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).kinds dw w0 tl i rc px q₂ φ hb hZb ht

/-- Zero knowledge asks of the segment what it asks of the body, beside their hypotheses. -/
theorem refPack_zk (base : MaskFact A.V.Fp.s0.J.W → Prop)
    (hb : ((LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.Y.body
      (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.c1.bat.src
      (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).tensor).Zk base) :
    ((LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).seg
      (refPack_l A Z pk Zb St₁ fz A₀c dw) (refPack_Q A Z pk Zb St₁ fz A₀c w0 tl)).Zk base :=
  gPack_seg1_zk pk (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z Zb A₀c _
    (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).kinds dw w0 tl base hb

end
end Cb
