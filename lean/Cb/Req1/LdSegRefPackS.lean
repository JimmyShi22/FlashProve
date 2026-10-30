-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefPackS.lean: a reference segment of a request as a term: any body's data, the
closing from a bundle, the one sending with riders.

Book-keeping: the record that the reference request takes for one segment (`LdRefS`,
Cb/Req1/LdReqRef.lean) is filled from a body's data and a bundle, and two of the conditions asked
of it are shown under the hypotheses of `refPackS_proto`, `refPackS_nums`.
Definitions, statements as theorems, proofs: wiring. Nothing of a text is rendered here.
A bundle (`GPack`, Cb/Ld/LdGroupPack.lean) is a record of a group with all that a closing needs:
the data, and proofs of the conditions on them.

Why: the reference request (Cb/Req1/LdReqRef.lean) takes, for each segment, the closing's data K,
the link bridge-to-fold l and the second half Qc as parameters, and its record asks properties of
them. Here they are terms.

Main names:
  `LdRefS.ofPack ..`: l := the group's own link (bridge, arrangement, one fold of all variables);
    f, g, m, back: the entry step (the model's).
  `refPackS_proto`: `S.Proto pp` (Cb/Req1/LdReqModel.lean) from `A.Proto pp`; the two evaders
    evade; every named place lies in a message with "mem"; `Rd.OK`. The bundle holds the rest:
    conditions on codes, arrangement, packing, lists.
  `refPackS_nums`: `S.NumsAt κ` (Cb/Req1/LdReqRefFinal.lean) from `A.Nums κ` and inequalities
    between numbers: the batching's evader; the bridge's round (L · Zb.err against |Zb.D|); the
    fold's rounds (Cb/Ld/LdGroupLinkBelow.lean); the one sending's number; the locations'.

Limits: this file says nothing on the model's side (entry step, body's model, what is left goes
over into what the closing carries). It says nothing on formats. It says nothing on masks:
Cb/Req1/LdSegRefPackSLay.lean. It does not say that a bundle, riders, numbers exist at parameters
of a protocol. No instance of `LdRefS.ofPack ..` is part of this library.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefClosePack
import Cb.Ld.LdGroupNewRide
import Cb.Ld.LdGroupLinkBelow
import Cb.Req1.LdReqRefFinal
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood
open scoped ENNReal

section
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc} (A : LdRefD E Kc I)
  (Z : Evader E A.Gr.B) {mem kp : A.Xa.Q.T.O → Prop} [DecidablePred kp] {clP : {o // kp o} → Prop}
  {Pn : Type} [Fintype Pn] {d e t : ℕ} {Lst mC mS mW : ℕ → ℕ} {L L₂ t₂ : ℕ}
  (pk : GPack A.Xa.Q.T mem kp clP Pn d e t Lst mC mS mW L L₂ t₂) (Zb : Evader E (pk.G.Row Unit))
  (St₁ : Type) (fz : A.X.bt.par.Mid → St₁)
  (A₀c : Rels Kc St₁ I.C.E0 ((A.Xa.Q.T.sub kp).Msg × (I.C.PIdx × (A.W₁ × A.Gh))))
  (dw : A.Xa.Q.T.Wit × (I.C.PIdx × (A.W₁ × A.Gh)))
  (w0 : (pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
      (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).tgt.S.Wit ×
    (pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
      (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).tgt.Wp)
  (tl : ℕ)
  (Rd : RideD E
    ((pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
        (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).tgt.S.Wit ×
      (pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
        (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).tgt.Wp))
  (f : a.X → Option A.V.Fp.s0.X) (g : ExtMap a.Ex A.V.Fp.s0.Ex)
  (m : a.X × a.W → A.V.Fp.s0.X × A.V.Fp.s0.W) (back : a.X × a.Ex.Str → A.V.Fp.s0.W → a.W)

/-- the one sending with riders (the first oracle messages of what follows:
Cb/Ld/LdGroupNewRide.lean) and the locations, at the closing's bridge-to-fold -/
def refPack_QR : LdCloseD (LdRefC1.ofPack A Z pk Zb St₁ fz A₀c).R.c1.fold :=
  pk.closeR (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z Zb A₀c w0 tl Rd

/-- A reference segment from a bundle, with riders. -/
@[reducible] def LdRefS.ofPack : LdRefS E Kc I a where
  A := A
  K := LdRefC1.ofPack A Z pk Zb St₁ fz A₀c
  l := refPack_l A Z pk Zb St₁ fz A₀c dw
  Qc := refPack_QR A Z pk Zb St₁ fz A₀c w0 tl Rd
  f := f
  g := g
  m := m
  back := back

/-- The protocol's side. -/
theorem refPackS_proto (pp : ℕ) (hA : A.Proto pp) (hZ : Z.OK) (hZb : Zb.OK)
    (hn : ∀ n, A.Gr.Named n → mem n.1) (hR : Rd.OK) :
    (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Proto pp where
  body := hA
  ev := hZ
  named := fun n h => (pk.memI n.1).2 (hn n h)
  fold := gPack_fold pk _ _ Zb A₀c dw hZb
  snd := stdNewR_snd pk.V _ _ Zb A₀c w0 L₂ t₂ tl Rd pk.new hR

/-- The numbers. -/
theorem refPackS_nums (κ : ℝ≥0∞) (hA : A.Nums κ)
    (hbat : (Z.err : ℝ≥0∞) ≤ κ * (Fintype.card Z.D : ℝ≥0∞))
    (hb : ((L * Zb.err : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card Zb.D : ℝ≥0∞))
    (h0 : (Lst 0 : ℝ≥0∞) ≤ κ * (Fintype.card pk.Sh.Ch : ℝ≥0∞))
    (hi : ∀ i, i < pk.Sh.h + pk.Sh.g →
      ((mC (i + 1) + (if i + 1 ≤ pk.Sh.h then mS (i + 1) + mW (i + 1) else 0) +
          Lst i * pk.Sh.n : ℕ) : ℝ≥0∞) ≤
        κ * (Fintype.card pk.Sh.Ch : ℝ≥0∞))
    (hs : (ldSendFamErr (refPack_QR A Z pk Zb St₁ fz A₀c w0 tl Rd).N
        (refPack_QR A Z pk Zb St₁ fz A₀c w0 tl Rd).Sd
        (refPack_QR A Z pk Zb St₁ fz A₀c w0 tl Rd).L : ℝ≥0∞) ≤
      κ * (Fintype.card (refPack_QR A Z pk Zb St₁ fz A₀c w0 tl Rd).Sd.D : ℝ≥0∞))
    (hl : (((Fintype.card pk.G.P - pk.G.e - 1) ^ tl : ℕ) : ℝ≥0∞) ≤
      κ * (Fintype.card (Fin tl → pk.G.P) : ℝ≥0∞)) :
    (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).NumsAt κ where
  body := hA
  bat := hbat
  fold := ldGroup_link_below pk.Hd _ _ Zb A₀c pk.hc dw d t Lst mC mS mW L κ hb h0 hi
  snd := hs
  loc := hl

end
end Cb
