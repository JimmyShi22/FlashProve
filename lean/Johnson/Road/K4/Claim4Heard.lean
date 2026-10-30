-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Claim4Heard.lean: THE FOURTH OF THE SEVEN EQUATIONS ON THE CLAIMED SUMS, AT A
HEARING OF K4's TEXT IN A GROUP THAT IS NOT THE FIRST: the typed batched sumcheck's claimed sum, at
the statement written out in the words of the tape (`aY4`, OnBytes/Desc/First/P1/TailAdds.lean), is
the reading of the target of K4's own record of that sumcheck. It is the premise h4 of that file's
`claims_of_firsts`. Two small lemmas and one theorem. Glue: `claim4` (Claim4.lean) with its ties
paid from the ledgers' facts of Johnson/Road/K4/OwnLedgers.lean. No draw, no count.

  `worldOf_zero_eq`: a ledger's world at the mask row 0 and entries 0 is the world of what was shown
    (`shownW`, OnBytes/Tie/Pv/Att/HearSaid.lean).
  `tapeCl_sent`: the first word that a tape's first round sent.
  `first4`: let Ld : Led7 … be the ledgers and tapes of a hearing, X : Pub34 a public record at that
    hearing's letters, P : FullPar at X's table of scales, sizes and tables. Then
    `(s4.cl (aY4 …) (the further scalars read)).1 = gl g.t4`, if g.t4 is the target of `stackRec` at
    the ledger G2 and the tape at which the batched sumcheck begins.

PAID HERE, from Led7 and laws of other files: the target reads as the start form's value at what G2
shows (`stack_target`, `public_value`) · the sent sum of the terms is what G2 shows under its slot
(`tsc_cl_shown`) · the drawn element reads om[1] (`powers_val`) · G2 shows 0 under the slots of the
terms' hiding coefficients, and the terms' target reads as its start form's value (`terms_shown`) ·
the lookup's end form has one value at what F and at what G2 shows (`kept_value`).

Limits. PREMISES THAT STAY: the ties of X to the hearing (hρ hH hD htb hα hθ hT hom hst: among
what Johnson/Road/K4/PubOfHearTied.lean's `pub34_of_hear_run` concludes; hfo: what the lookup heard
stands in o.H; hscl: the table of scales is the one that X's own letters make) · O3: the typed
output of the terms' sumcheck is K4's record, read (`OutIs`) · hz0, hk0: the letters zOf and kTg at
the first statement are the lookup's point and `kTgAt fo F` · hfil: the lookup's end form names
filled slots alone of the ledger in front. A group that is not the first.
-/
import Johnson.Road.K4.Claim4
import Johnson.Road.K4.OwnLedgers
import OnBytes.Desc.First.P1.TailAdds
import OnBytes.Desc.First.P1.BatchPoint
import OnBytes.Tie.Pv.Att.HearSaid
import OnBytes.Tie.Pv.Lay.HearTieL

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading World Aff Fork Forest.Heard Level Tsc powers)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Road.Rows (Pub34)
open OnBytes.Tie.Pv.Att (shownW public_value)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl Ks NzT TailM TailR Tg7 aY4 aD3 sentOf tapeEps tapeCl powers_val)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

/-- A ledger's world at the mask row 0 and entries 0 is the world of what was shown. -/
theorem worldOf_zero_eq {K : Type} [CommRing K] (ρ : Reading K) (F : Fork) :
    F.worldOf ρ (fun _ => 0) (fun _ _ _ => 0) = shownW ρ F := by
  unfold Fork.worldOf shownW
  simp

/-- The first word that a tape's first round sent. -/
theorem tapeCl_sent (t : Tape) : tapeCl t = (sentOf t).getD 0 zeroE := by
  cases t with
  | nil => rfl
  | cons r u =>
    show r.sent.headD zeroE = r.sent.getD 0 zeroE
    cases r.sent <;> rfl

variable [scl : Scl] {M Xs : Type}

/-- **The fourth equation on the claimed sums, at a hearing.** -/
theorem first4 (P : FullPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.own.toOwn.tail R) {Pp : Pub}
    {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard}
    {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
    (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (X : Pub34 Cb.Gl.E) (hρ : X.ρ = Reading.gl) (hH : X.H = o.H) (hfo : o.H.fo = fo)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (hD : X.D = P.D) (htb : X.tb = P.tb)
    (hα : X.alpha = o.H.fo.alpha) (hθ : X.theta = o.H.fo.theta) (hT : o.H.tT = some X.tT)
    (hom : X.om = powers (tapeEps ((ksOf Pp hp).tc4 (t0.drop 1))) 2)
    (hst : stackStart o.v o.H G2 ((ksOf Pp hp).tc4 (t0.drop 1)) = startOf X.H X.om X.parts)
    (w : ℕ → LW Cb.Gl.E) (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7)
    (ht4 : g7.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop 1))).target)
    (O3 : OutIs gl (aD3 W (ksOf Pp hp) (t0.drop 1) nz x g7) tT.p)
    (hz0 : P.zOf x.1 = zAt fo) (hk0 : P.kTg x.1 = kTgAt fo F) (hfil : Fo.FilledA F fo.cEnd) :
    (P.own.toOwn.tail.s4.cl (aY4 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (Johnson.L5.Layers.rd gl P.own.toOwn.tail.s4.n
        (sentOf (((ksOf Pp hp).tc4 (t0.drop 1)).drop 1)))).1 = gl.val g7.t4 := by
  obtain ⟨u1, _, hTm⟩ := Ld.nt
  have eT : X.tT = { tT with p := { tT.p with rowMade := true } } :=
    Option.some.inj (hT.symm.trans Ld.kTT)
  have sh := terms_shown gl Ld.s1 hTm X.tT hT G2 (Fo.Later.refl G2)
  have ht : gl.val g7.t4 = (startOf X.H X.om X.parts).value Reading.gl
      (G2.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0) := by
    rw [ht4, public_value gl G2 _ _ (stack_target Ld.c4), hst, worldOf_zero_eq]
  refine claim4 X hρ hscl P hD htb F G2 w _ _ _ rfl g7.t4 ht (by rw [hH]; exact hα)
    (by rw [hH]; exact hθ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (sh.2 _)
  · rw [hH, hfo]
    exact hz0
  · rw [hH, hfo]
    exact hk0
  · rw [eT]
    show _ = gl.val (G2.vp.getD tT.sCl zeroE)
    rw [tsc_cl_shown Ld.s1 Ld.c3 G2 Ld.l1, tapeCl_sent]
    rfl
  · rw [hom, powers_val gl _ 2 1 (by decide), pow_one]
    rfl
  · rw [eT]
    exact O3.fin
  · rw [eT]
    exact O3.eps
  · rw [hH, hfo]
    exact kept_value gl Ld.l2 fo.cEnd hfil _ _
  · intro j h1 h2
    rw [sh.1 j h1 h2]
    exact gl.zero

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.first4
