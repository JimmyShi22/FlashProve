-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/WoAtLedFirst.lean: THE FIRST GROUP's NAMED SENTENCE `WoSaysF` AT A HEARING OF K4's
TEXT, AT THE SEVENTH STATE READ OFF THE TAPE, AGAINST THE ROW THAT `pendingRowO` RETURNS. The first
group's twin of WoAtLed.lean: a join on the field wo, in the first group: the statements of these
files laid together. Two statements and their proofs.

  `aS7F_parts`: of the seventh state `aS7` (OnBytes/Desc/First/P1/TailAdds.lean) at the first
    sub-proof's letters `tailW Pf`: its claims' state is what the first group's merge reads (`st7F`)
    off the tail's first statement x (with the three points) and the typed batched sumcheck's
    output; its combining element is the reading of the element that the first round on the merge's
    tape drew.
  `woSaysF_at_ledG`: where `pendingRowO P.wsLay im o.wo claims S os = .ok (r, os')`: `WoSaysF Pf
    (aS7 …).1.1 (aS7 …).2 o.wo mm` holds exactly if the sum over the cube's rows of `pendWeight gl
    r.g j` times the committed matrix's row j read at the point `r.psi` turned round, plus the sum
    over the row's named mask entries of the entry times its factor, is the reading of `r.target`.

NO NEW ARGUMENT: `woSaysF_iff_row` (WoLedFirst.lean) at the list `crOf (X.cl ++ [cE]).toArray
(tapeEps u5)`; its premises on the list by `ledG_flat` (WoListFirst.lean) and `crOf_co`, `crOf_fst`,
`FlatSpec.unit`, `FlatSpec.shape`, `FlatSpec.recs` (WoRecs.lean); (H) by `ten_of_ledF`
(TenOfLedFirst.lean) at the one matrix `starW`; the layout by the record's own field hlw; the tape's
first element by `LedG`'s field u5e.

Limits. The first group alone (hg). PREMISES: `LedG` and the hearing's return; all that
`ten_of_ledF` asks (the fourth stage's claim; `OutIs` at the third and fourth stages; two numbers of
rounds; the numbering of the terms' end values; four sizes; a public record X : Pub34 with its ties
to the hearing and, by hD, htb, hL0 and hlk, to the typed value Pf; the table of scales; `ReadsTrue`
in some world, of which the conclusion names none; the two clauses on the lookup's point; that the
typed numbering is numK's), at the states `addsOf`; ALL of X's claims' environment is the hearing's
(Xc), its reads are the plan's (Xrd); `NzT` (none of the seven further challenges on the tape reads
0) stands in the type of `aS7`; hn: the plan has one weight claim more than there are typed pairs;
(HE): THE ADDED PAIR `tenEF Pf` AT THE CLAIMS' STATE `(aS7 …).1.1` AND THE EMBEDDING's CLAIM,
whatever `claimE` returns at what was heard, TAKE ONE VALUE AT THE MATRIX `starW`: shown in no file
that this one imports; that `pendingRowO` returns; hidx: the index masks' entry that the row names
is the typed mask entry `Pf.msg mm Pf.c7`. The cells are `Pf.Wn (Pf.msg mm)` by the statement: that
another file's cells are these is not said. x, g7, idx, mm, im, os, claims and S are among the
letters: that x's three points are what the tape drew is not asked by a binder of its own; BUT (HE)
READS x: the claims' state holds x's two further points and the value's tokens at x (`st7F`), so
whoever pays (HE) ties these to what was heard and to P.tokv; that a layers' link's end calls
`pendingRowO` at the index masks' number, the statement's messages, the plan's count and this record
is not said here. WHETHER THESE PREMISES CAN BE MET TOGETHER AT A YES IS NOT SHOWN HERE. By the head
of Johnson/Road/Rows/LayerEnds34.lean no record Pub34 exists at the small example (its field hfl
fails there): there this statement is empty. `verify-on-bytes`'s routine `wsPending` stands in no
statement here; it stays in a proof beneath. An equivalence of two sentences on numbers: no draw.
Nothing on soundness.
-/
import Johnson.Road.K4.WoLedFirst
import Johnson.Road.K4.WoListFirst
import Johnson.Road.K4.TenOfLedFirst
import OnBytes.Desc.First.P1.TailParts
import OnBytes.Desc.First.P1.TailAdds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model (World Fork Psc Level Tsc WsClaim powers)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT)
open OnBytes.Desc.First.K4 (hear engFl k0 envOf)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR Tg7 tapeEps tailT aS7 addsOf b4_z7 tz4)
open OnBytes.Slice (GE)
open Inst.Model (Scl)
open Cb.Pv.Lay.At (tval)
open VerifiableInference.Desc.First.Pend (pendingRowO)

variable [scl : Scl] {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
  {M X0 : Type} (Pf : FullFPar GE M X0) {R : TailR} (W' : TailM (tailW Pf) R)

/-- **The seventh state read off a tape, at the first sub-proof's letters: two of its parts.** -/
theorem aS7F_parts (k : Ks) (t : Tape) (nz : NzT (tailW Pf) k t) (x : Pf.ofp.fs.X3) (g7 : Tg7) :
    (aS7 W' k t nz x g7).1.1 =
        Pf.st7F x ((tailW Pf).b4 ((tailT W' k t nz (addsOf W' k t nz x g7)).z7 x)).2 ∧
      (aS7 W' k t nz x g7).2 = gl.val (tapeEps (k.tcW t)) := by
  rw [b4_z7, tz4]
  exact ⟨rfl, rfl⟩

/-- **The first group's named sentence at a hearing, of the row that `pendingRowO` returns.** -/
theorem woSaysF_at_ledG
    (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = true)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (x : Pf.ofp.fs.X3) (g7 : Tg7)
    (a : Adds7 (tailW Pf)) (ha : a = addsOf W' (ksOf P hp) (t0.drop (k0 g)) nz x g7)
    (hc : (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.Claim
        ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).y4 x)) {p3 p4 : Psc}
    (O3 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d3 p3)
    (O4 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4 p4)
    (k3 : (tailW Pf).s3.L.S.k = P.y.h.lt) (k4 : kS Pf.D = hp.lamS)
    (n3 : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q)
    (hNN : P.y.NN * P.y.Lam = Pf.D.nNu) (hLM : P.y.LamM = Pf.D.ne)
    (hNE : P.y.h.NE = Pf.D.nx) (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y)
    (X : Rows.Pub34 GE) (Xρ : X.ρ = gl) (XH : X.H = o.H)
    (Xc : X.c = { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := tT.r })
    (Xrd : X.rd = P.rd)
    (Xsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some X.p.shownT)
    (Xom : X.om = powers (tapeEps ((ksOf P hp).tc4 (t0.drop (k0 g)))) 2)
    (hD : X.D = Pf.D) (htb : X.tb = Pf.ip.tb) (hL0 : X.c.v.g * X.c.v.y.Lam = Pf.ip.L0)
    (hlk : X.lk = Pf.kW) (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam)
    (hz0 : ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st.z =
      zOf gl o.H.fo.zx o.H.fo.zy)
    (hz3 : Pf.ip.zP ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st .QK =
      zOf gl o.H.fo.zx o.H.fo.zy)
    (Wo : World GE) (Mm : Mats GE) (hRd : X.ReadsTrue Wo Mm)
    (hnum : ∀ i : Fin Pf.nW, ((numK Pf.D).symm (Pf.num i)).val = i.val)
    (hn : hp.NCL = Pf.nW + 1) (mm : M)
    (HE : ∀ cE : WsClaim, (envOf P o).claimE o.H.ZE o.H.tkh P.V P.tokv = some cE →
      tval (tenEF Pf (aS7 W' (ksOf P hp) (t0.drop (k0 g)) nz x g7).1.1)
          (Inst.Model.Layout.Tensor.matOf (starW gl Pf.kW o.wo.rm (Pf.Wn (Pf.msg mm)))) =
        claimVal gl P.wsLay (starW gl Pf.kW o.wo.rm (Pf.Wn (Pf.msg mm))) cE)
    (claims : ℕ) (S : Params.LinShape)
    {im : ℕ} {os os' : Array Oracle} {r : TensorRow}
    (hr : pendingRowO P.wsLay im o.wo claims S os = .ok (r, os')) (idx : ℕ → GE)
    (hidx : ∀ y ∈ r.masks, idx y.1.index = Pf.msg mm Pf.c7) :
    WoSaysF Pf (aS7 W' (ksOf P hp) (t0.drop (k0 g)) nz x g7).1.1
        (aS7 W' (ksOf P hp) (t0.drop (k0 g)) nz x g7).2 o.wo mm ↔
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
  obtain ⟨cE, eE, hsz, Sp⟩ := ledG_flat Ld h hg X Xc Xrd
  have hlen : X.cl.length = Pf.nW := by
    have q : X.cl.length + 1 = hp.NCL := by
      rw [← hsz, List.size_toArray, List.length_append, List.length_singleton]
    omega
  have hn' : (crOf (X.cl ++ [cE]).toArray (tapeEps u5)).length = Pf.nW + 1 :=
    (crOf_length _ _).trans (hsz.trans hn)
  have key : ∀ (st : St7 GE Pf.wp0.n) (α : GE),
      st = Pf.st7F x ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2 →
      α = gl.val (tapeEps ((ksOf P hp).tcW (t0.drop (k0 g)))) →
      (∀ cE : WsClaim, (envOf P o).claimE o.H.ZE o.H.tkh P.V P.tokv = some cE →
        tval (tenEF Pf st)
            (Inst.Model.Layout.Tensor.matOf (starW gl Pf.kW o.wo.rm (Pf.Wn (Pf.msg mm)))) =
          claimVal gl P.wsLay (starW gl Pf.kW o.wo.rm (Pf.Wn (Pf.msg mm))) cE) →
      (WoSaysF Pf st α o.wo mm ↔
        ∑ j ∈ range (2 ^ S.kRow),
            pendWeight gl r.g j *
              rowAt gl P.wsLay.lk r.psi.reverse.toArray (Pf.Wn (Pf.msg mm)) j +
          (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target) := by
    intro st α h1 h2 hE
    have hco : ∀ i : Fin (Pf.nW + 1), α ^ (i : ℕ) =
        gl.val ((crOf (X.cl ++ [cE]).toArray (tapeEps u5)).get (i.cast hn'.symm)).2 := by
      intro i
      rw [h2, ← Ld.u5e]
      exact crOf_co gl (X.cl ++ [cE]).toArray _ hn' i
    have H : ∀ i : Fin Pf.nW,
        tval (Pf.wp0.ten i st)
            (Inst.Model.Layout.Tensor.matOf (starW gl Pf.kW o.wo.rm (Pf.Wn (Pf.msg mm)))) =
          claimVal gl P.wsLay (starW gl Pf.kW o.wo.rm (Pf.Wn (Pf.msg mm)))
            ((crOf (X.cl ++ [cE]).toArray (tapeEps u5)).get (i.castSucc.cast hn'.symm)).1 := by
      intro i
      obtain ⟨c0, e0, hW⟩ := ten_of_ledF Pf W' Ld nz a x hc O3 O4 k3 k4 n3 hNN hLM hNE hEnd X Xρ
        XH Xrs Xrt Xsh Xom hD htb hL0 hlk hscl hz0 hz3 Wo Mm hRd hnum x i
      have e1 := crOf_fst (X.cl ++ [cE]).toArray (tapeEps u5) hn' i.castSucc
      have hi : i.val < X.cl.length := by
        rw [hlen]
        exact i.isLt
      rw [List.getElem?_toArray, Fin.val_castSucc, List.getElem?_append_left hi] at e1
      rw [h1, ← Option.some.inj (e0.symm.trans e1), ← hlay]
      exact hW _
    have HE' : tval (tenEF Pf st)
          (Inst.Model.Layout.Tensor.matOf (starW gl Pf.kW o.wo.rm (Pf.Wn (Pf.msg mm)))) =
        claimVal gl P.wsLay (starW gl Pf.kW o.wo.rm (Pf.Wn (Pf.msg mm)))
          ((crOf (X.cl ++ [cE]).toArray (tapeEps u5)).get ((Fin.last Pf.nW).cast hn'.symm)).1 := by
      have e1 := crOf_fst (X.cl ++ [cE]).toArray (tapeEps u5) hn' (Fin.last Pf.nW)
      rw [List.getElem?_toArray, Fin.val_last] at e1
      have eL : (X.cl ++ [cE])[Pf.nW]? = some cE := by
        rw [← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      have e2 : cE = ((crOf (X.cl ++ [cE]).toArray (tapeEps u5)).get
          ((Fin.last Pf.nW).cast hn'.symm)).1 := Option.some.inj (eL.symm.trans e1)
      rw [← e2]
      exact hE cE eE
    exact woSaysF_iff_row Pf st α o.wo mm P.wsLay hkW claims S
      (crOf (X.cl ++ [cE]).toArray (tapeEps u5)) hn' hco (Sp.unit hl _) (Sp.shape _) H HE'
      Sp.recs hr idx hidx
  subst ha
  exact key _ _ (aS7F_parts Pf W' (ksOf P hp) (t0.drop (k0 g)) nz x g7).1
    (aS7F_parts Pf W' (ksOf P hp) (t0.drop (k0 g)) nz x g7).2 HE

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.aS7F_parts
#print axioms OnBytes.Road.K4.woSaysF_at_ledG
