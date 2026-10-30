-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/WoAtLed.lean: THE NAMED SENTENCE `WoSays` AT A HEARING OF K4's TEXT IN A LATER
GROUP, AT THE SEVENTH STATE READ OFF THE TAPE, AGAINST THE ROW THAT `pendingRowO` RETURNS. A join on
the field wo, in a later group: the statements of these files laid together. Three statements and
their proofs.

  `aS7_parts`: the seventh state `aS7` (OnBytes/Desc/First/P1/TailAdds.lean) is the pair of what the
    typed merge reads of the typed batched sumcheck's output, and the reading of the element that
    the first round on the merge's tape drew. `aS7_k4`: the same at K4's data `k4Tail`.
  `woSays_at_led`: where `pendingRowO P.wsLay im o.wo claims S os = .ok (r, os')`: `WoSays Pf (aS7
    …) o.wo mm` holds exactly if the sum over the cube's rows of `pendWeight gl r.g j` times the
    committed matrix's row j read at the point `r.psi` turned round, plus the sum over the row's
    named mask entries of the entry times its factor, is the reading of `r.target`.

NO NEW ARGUMENT: `woSays_iff_row` (WoRow4.lean) at the list `crOf X.cl.toArray (tapeEps …)`; its
premises on the list by `led7_flat`, `led7_merge_pub34` (WoList.lean) and `crOf_co`, `crOf_fst`,
`FlatSpec.unit`, `FlatSpec.shape`, `FlatSpec.recs` (WoRecs.lean); its premise (H) by `ten_of_led`
(TenOfLed.lean) at the one matrix `starW`; the layout by the record's own field hlw.

Limits. A group that is not the first. PREMISES: `Led7` and the hearing's return; all that
`ten_of_led` asks (the fourth stage's claim; `OutIs` at the third and fourth stages; two numbers of
rounds; the numbering of the terms' end values; four sizes; a public record X : Pub34 with its ties
to the hearing and, by hD, htb, hL0 and hlk, to the typed value Pf; the table of scales; `ReadsTrue`
in some world, of which the conclusion names none; the two clauses on the lookup's point; that the
typed numbering is numK's), at the states `addsOf`; of X more than there: ALL of its claims'
environment is the hearing's (Xc), its reads are the plan's (Xrd); `NzT` (none of the seven further
challenges on the tape reads 0) stands in the type of `aS7`; hn: the plan has as many weight claims
as there are typed pairs; that `pendingRowO` returns; hidx: the index masks' entry that the row
names is the typed mask entry `Pf.msg mm Pf.c7`. The cells are `Pf.Wn (Pf.msg mm)` by the statement:
that another file's cells are these is not said. x, g7, idx, mm, im, os, claims and S are among the
letters: that the token point x.2 is what the tape drew is not asked; that a layers' link's end
calls `pendingRowO` at the index masks' number, the statement's messages, the plan's count and this
record is not said here. WHETHER THESE PREMISES CAN BE MET TOGETHER AT A YES IS NOT SHOWN HERE. By
the head of Johnson/Road/Rows/LayerEnds34.lean no record Pub34 exists at the small example (its
field hfl fails there): there this statement is empty. `verify-on-bytes`'s routine `wsPending`
stands in no statement here; it stays in a proof beneath (`woSays_iff_row`). An equivalence of two
sentences on numbers: no draw. Nothing on soundness.
-/
import Johnson.Road.K4.WoRow4
import Johnson.Road.K4.WoList
import Johnson.Road.K4.TenOfLed
import OnBytes.Desc.First.P1.TailParts
import OnBytes.Desc.First.P1.TailAdds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model (World Fork Psc Level Tsc powers)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT)
open OnBytes.Desc.First.K4 (hear engFl)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR Tg7 tapeEps tailT aS7 addsOf b4_z7 tz4)
open OnBytes.Slice (GE)
open Inst.Model (Scl)
open Cb.Pv.Lay.At (tval)
open VerifiableInference.Desc.First.Pend (pendingRowO)

variable [scl : Scl] {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
  {M X0 : Type} (Pf : FullPar GE M X0) {R : TailR} (W' : TailM (tailF Pf) R)

/-- **The seventh state read off a tape, in its two parts.** -/
theorem aS7_parts (k : Ks) (t : Tape) (nz : NzT (tailF Pf) k t) (x : Pf.XT) (g7 : Tg7) :
    (aS7 W' k t nz x g7 : St7 GE Pf.wp0.n × GE) =
      (Pf.ip.st7 Pf.num ((tailF Pf).b4 ((tailT W' k t nz (addsOf W' k t nz x g7)).z7 x)).2,
        gl.val (tapeEps (k.tcW t))) := by
  rw [b4_z7, tz4]
  rfl

/-- The same at K4's data `k4Tail`. -/
theorem aS7_k4 (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (x : Pf.XT) (g7 : Tg7) :
    (aS7 W' (ksOf P hp) (t0.drop 1) nz x g7 : St7 GE Pf.wp0.n × GE) =
      (Pf.ip.st7 Pf.num ((tailF Pf).b4
          ((k4Tail W' P hp t0 nz (addsOf W' (ksOf P hp) (t0.drop 1) nz x g7)).z7 x)).2,
        gl.val (tapeEps ((ksOf P hp).tcW (t0.drop 1)))) :=
  aS7_parts Pf W' (ksOf P hp) (t0.drop 1) nz x g7

/-- **The named sentence at a hearing, of the row that `pendingRowO` returns.** -/
theorem woSays_at_led (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = false)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (x : Pf.XT) (g7 : Tg7) (a : Adds7 (tailF Pf))
    (ha : a = addsOf W' (ksOf P hp) (t0.drop 1) nz x g7)
    (hc : (k4Tail W' P hp t0 nz a).d4.Claim ((k4Tail W' P hp t0 nz a).y4 x)) {p3 p4 : Psc}
    (O3 : OutIs gl (k4Tail W' P hp t0 nz a).d3 p3) (O4 : OutIs gl (k4Tail W' P hp t0 nz a).d4 p4)
    (k3 : (tailF Pf).s3.L.S.k = P.y.h.lt) (k4 : kS Pf.D = hp.lamS)
    (n3 : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q)
    (hNN : P.y.NN * P.y.Lam = Pf.D.nNu) (hLM : P.y.LamM = Pf.D.ne)
    (hNE : P.y.h.NE = Pf.D.nx) (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y)
    (X : Rows.Pub34 GE) (Xρ : X.ρ = gl) (XH : X.H = o.H)
    (Xc : X.c = { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := tT.r })
    (Xrd : X.rd = P.rd)
    (Xsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some X.p.shownT)
    (Xom : X.om = powers (tapeEps ((ksOf P hp).tc4 (t0.drop 1))) 2)
    (hD : X.D = Pf.D) (htb : X.tb = Pf.ip.tb) (hL0 : X.c.v.g * X.c.v.y.Lam = Pf.ip.L0)
    (hlk : X.lk = Pf.kW) (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam)
    (hz0 : ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2.st.z = zOf gl o.H.fo.zx o.H.fo.zy)
    (hz3 : Pf.ip.zP ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2.st .QK =
      zOf gl o.H.fo.zx o.H.fo.zy)
    (Wo : World GE) (Mm : Mats GE) (hRd : X.ReadsTrue Wo Mm)
    (hnum : ∀ i : Fin Pf.nW, ((numK Pf.D).symm (Pf.num i)).val = i.val)
    (hn : hp.NCL = Pf.nW) (claims : ℕ) (S : Params.LinShape)
    {im : ℕ} {os os' : Array Oracle} {r : TensorRow}
    (hr : pendingRowO P.wsLay im o.wo claims S os = .ok (r, os')) (idx : ℕ → GE) (mm : M)
    (hidx : ∀ y ∈ r.masks, idx y.1.index = Pf.msg mm Pf.c7) :
    WoSays Pf (aS7 W' (ksOf P hp) (t0.drop 1) nz x g7) o.wo mm ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl r.g j * rowAt gl P.wsLay.lk r.psi.reverse.toArray (Pf.Wn (Pf.msg mm)) j +
        (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target := by
  have hlay : X.c.wsLay = P.wsLay := by rw [Xc]
  have Xrs : X.c.rs = o.K.rs := by rw [Xc]
  have Xrt : X.c.rt = tT.r := by rw [Xc]
  have hl : OnBytes.Model.wsLayOf X.s true X.lk = .ok P.wsLay := by
    rw [← hlay]
    exact X.hlw
  have hkW : Pf.kW = P.wsLay.lk := by rw [← hlk, (unitOK_of_layout hl).1]
  have Sp := led7_flat Ld h hg X Xc Xrd
  have hn' : (crOf X.cl.toArray (tapeEps ((ksOf P hp).tcW (t0.drop 1)))).length = Pf.nW :=
    (crOf_length _ _).trans ((led7_merge_pub34 Ld h hg X Xc Xrd).1.trans hn)
  have key : ∀ st : St7 GE Pf.wp0.n × GE,
      st = (Pf.ip.st7 Pf.num ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2,
        gl.val (tapeEps ((ksOf P hp).tcW (t0.drop 1)))) →
      (WoSays Pf st o.wo mm ↔
        ∑ j ∈ range (2 ^ S.kRow),
            pendWeight gl r.g j *
              rowAt gl P.wsLay.lk r.psi.reverse.toArray (Pf.Wn (Pf.msg mm)) j +
          (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target) := by
    intro st hst
    have h1 : st.1 =
        Pf.ip.st7 Pf.num ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2 := by rw [hst]
    have h2 : st.2 = gl.val (tapeEps ((ksOf P hp).tcW (t0.drop 1))) := by rw [hst]
    have hco : ∀ i : Fin Pf.nW, st.2 ^ (i : ℕ) =
        gl.val ((crOf X.cl.toArray (tapeEps ((ksOf P hp).tcW (t0.drop 1)))).get
          (i.cast hn'.symm)).2 := by
      intro i
      rw [h2]
      exact crOf_co gl X.cl.toArray _ hn' i
    have H : ∀ i : Fin Pf.nW,
        tval (Pf.wp0.ten i st.1)
            (Inst.Model.Layout.Tensor.matOf (starW gl Pf.kW o.wo.rm (Pf.Wn (Pf.msg mm)))) =
          claimVal gl P.wsLay (starW gl Pf.kW o.wo.rm (Pf.Wn (Pf.msg mm)))
            ((crOf X.cl.toArray (tapeEps ((ksOf P hp).tcW (t0.drop 1)))).get
              (i.cast hn'.symm)).1 := by
      intro i
      obtain ⟨c0, e0, hW⟩ := ten_of_led Pf W' Ld nz a x hc O3 O4 k3 k4 n3 hNN hLM hNE hEnd X Xρ XH
        Xrs Xrt Xsh Xom hD htb hL0 hlk hscl hz0 hz3 Wo Mm hRd hnum i
      have e1 := crOf_fst X.cl.toArray (tapeEps ((ksOf P hp).tcW (t0.drop 1))) hn' i
      rw [List.getElem?_toArray] at e1
      rw [h1, ← Option.some.inj (e0.symm.trans e1), ← hlay]
      exact hW _
    exact woSays_iff_row Pf st o.wo mm P.wsLay hkW claims S
      (crOf X.cl.toArray (tapeEps ((ksOf P hp).tcW (t0.drop 1)))) hn' hco (Sp.unit hl _)
      (Sp.shape _) H Sp.recs hr idx hidx
  subst ha
  exact key _ (aS7_k4 Pf W' nz x g7)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.aS7_parts
#print axioms OnBytes.Road.K4.aS7_k4
#print axioms OnBytes.Road.K4.woSays_at_led
