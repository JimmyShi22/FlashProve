-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/KtLed.lean: THE FORM KT OF THE TERMS' STRETCH, IN A WORLD WITH MASKS, AT A HEARING.
K4's text makes of the terms' token sumcheck the form `KT`: that sumcheck's own row without summand
and kept terms, scaled by minus the inverse of eps (OnBytes/Desc/First/K4/Hear.lean, `hearTerms`).
The library writes "the row's other members, divided by eps" as `overAt` (Cb/Pv/Lay/Over.lean).
Under the record `Led7` of a hearing in a group that is not the first
(Johnson/Road/K4/OwnLedgers.lean), at the chain's data read off the hearing's tape with the states
`addsOf`: the two are one value, at one m, in the world of any ledger later than the hearing's last.
Statements and proofs.

  `tsc_d2`: (D2) where a token sumcheck's call `Fl.tscIn` returns out of a ledger with arrays of the
    right sizes, for every later ledger, from the typed half hinc.
  `led7_terms`: off `Led7`: `o.H.KT = (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps))`, and
    there is a ledger with arrays of the right sizes from which the run of the terms' row's hiding
    coefficients leads to G2.
  `ho_of_led`: `overAt P.ip.Y3 (aD3 …).out m = o.H.KT.value gl (Hl.worldOf gl mask entry)`.

NO NEW ARGUMENT: `scaled_over_at` (OnBytes/Desc/First/P1/RowValueAt.lean), `stgT_said`
(OwnRows.lean), `tsc_recAt`, `pscRow_made` (OwnRecs.lean), `d1_ended_at`, `d2_of_public`
(OwnD12Calls.lean, OwnD2.lean), `TokL.pick_ok` (the lawful pick), `hearTerms_calls`,
`tscIn_heard`, `tsc_world`, `filledA_of_publicPart`. That the terms' summand has no public part
holds by unfolding.

Limits. All letters are the caller's, but one ledger inside `led7_terms`, which is spent inside
`ho_of_led`. PREMISES: `Led7`; `NzT` (no further challenge reads 0); g7.t3 is the record's target;
`TailM.Ok`; `StgFits` at the third stage; Hl later than G; hw3 (which entry serves as which
coefficient of the hiding polynomial); hinc3 (the typed half of (D2)); hk (the reading of minus the
inverse of eps, times the reading of eps, is -1). A group that is not the first. One world: no draw.
Nothing on soundness.
-/
import Johnson.Road.K4.OwnD12Calls
import Johnson.Road.K4.OwnRows
import Johnson.Road.K4.OwnLedgers
import OnBytes.Desc.First.P1.RowValueAt
import OnBytes.Desc.First.P1.TailAdds
import Cb.Pv.Lay.At.OwnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Johnson.L5.Layers
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard Level Tsc Psc World Aff)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Tie.Pv (slotP)
open OnBytes.Tie.Pv.Lay (StgFits)
open OnBytes.PscRun (hideRun_ok)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aD3 aS3 tscWs tscIn_heard tsc_world pscRow_spec
  filledA_of_publicPart scaled_over_at)
open OnBytes.Slice (GE)
open Inst.Model (Scl)

/-- **(D2) where a token sumcheck's call returns.** -/
theorem tsc_d2 (Y : PscPar GE) (st : Y.St) {P : Array E} {lt n dY : ℕ} {F G H : Fork} {t u : Tape}
    {o : Tsc} (h : Fl.tscIn P lt n dY F t = some (o, G, u)) (hs : OnBytes.PscRun.Sized F)
    (hL : Fo.Later G H) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) (m : Y.J → GE)
    (hinc : Y.inc st m = maskSum H (Aff.slot o.sCl) mask - entSum (Aff.slot o.sCl) entry) :
    Y.inc st m = gl.val o.p.target - o.p.start.value gl (H.worldOf gl mask entry) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hst, hcl, _, _, v, G0, hG0, hpub, _, _, _, hG⟩ :=
    tscIn_heard h
  have hF' : OnBytes.PscRun.Sized ({ F with next := F.next + 1 } : Fork) := hs
  obtain ⟨_, hS0, _, _⟩ := hideRun_ok _ G0 F.next _ oneE hF' hG0
  have hS0' : OnBytes.PscRun.Sized
      ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork) := hS0
  have hpub' : ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } :
      Fork).publicPart (Aff.slot F.next) = some o.p.target := hpub
  refine d2_of_public Y st ?_ (fun _ => mask) (fun _ => entry) m ?_
  · rw [hst, Fo.publicPart_later ((Fo.hideRun_later hS0' hG).trans hL) _
      (filledA_of_publicPart hpub')]
    exact hpub'
  · rw [hst, ← hcl]
    exact hinc

variable {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- **What `Led7` holds of the terms' row**, off its fields `nt`, `kTT` and `s1`. -/
theorem led7_terms (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4) :
    o.H.KT = (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps)) ∧
      ∃ Gx : Fork, OnBytes.PscRun.Sized Gx ∧
        Gx.hideRun tT.p.first (Array.replicate tT.p.walk.1.length zeroE) (subE zeroE oneE) =
          some G2 := by
  obtain ⟨u1, _, h2⟩ := Ld.nt
  obtain ⟨tT', Gx, ux, row, p', b1, _, b3, b4⟩ := hearTerms_calls h2
  have e1 := pscRow_made b3
  obtain ⟨r1, _, r3⟩ := pscRow_spec b3
  have k := Ld.kTT
  rw [b4] at k
  have k2 : p' = { tT.p with rowMade := true } := congrArg Tsc.p (Option.some.inj k)
  have hpp : ({ tT'.p with rowMade := true } : Psc) = { tT.p with rowMade := true } :=
    e1.symm.trans k2
  have hrow : tT'.p.rowForm zeroE {} = tT.p.rowForm zeroE {} := by
    have q := congrArg (fun q : Psc => q.rowForm zeroE {}) hpp
    exact q
  have heps : tT'.p.eps = tT.p.eps := by
    have q := congrArg Psc.eps hpp
    exact q
  have hfirst : tT'.p.first = tT.p.first := by
    have q := congrArg Psc.first hpp
    exact q
  have hwalk : tT'.p.walk = tT.p.walk := by
    have q := congrArg (fun q : Psc => q.walk) hpp
    exact q
  refine ⟨?_, Gx, (tsc_world gl (fun _ => 0) (fun _ _ _ => 0) Ld.s1 b1).2.1, ?_⟩
  · rw [b4, r1]
    show (tT'.p.rowForm zeroE {}).scale (negE (invE tT'.p.eps)) = _
    rw [hrow, heps]
  · rw [← hfirst, ← hwalk]
    exact r3

variable [scl : Scl] {M Xs : Type} (P : FullPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM P.own.toOwn.tail R)

/-- **The form KT is the library's `overAt` at the terms' typed output**, at one m. -/
theorem ho_of_led (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) (ht3 : g7.t3 = tT.p.target) (ok : W.Ok)
    (f3 : StgFits gl P.own.toOwn.tail.s3 (aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (tscWs (H1.ztF.toList.take Pp.y.h.lt)) Pp.y.h.lt 1)
    (Ex : ExtSpec) (y : Ex.Str) {Hl : Fork}
    (hL : Fo.Later G Hl) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (m : P.ip.Y3.J → Cb.Gl.E)
    (hw3 : ∀ q, m (P.ip.Y3.wAt q) = mask (slotP P.ip.Y3.fmt tT.p.first q))
    (hinc3 : P.ip.Y3.inc (aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (Aff.slot tT.sCl) mask - entSum (Aff.slot tT.sCl) entry)
    (hk : gl.val (negE (invE tT.p.eps)) * gl.val tT.p.eps = -1) :
    overAt P.ip.Y3 (aD3 W (ksOf Pp hp) (t0.drop 1) nz x g7).out m =
      o.H.KT.value gl (Hl.worldOf gl mask entry) := by
  obtain ⟨hKT, Gx, hSx, hrow⟩ := led7_terms Ld
  obtain ⟨e, s⟩ := stgT_said W.w3.num (ksOf Pp hp).k3 _ nz.b3
    (aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7) g7.t3 rfl (tsc_recAt Ld.c3) ht3 f3
  obtain ⟨C, τ, first, a⟩ := (tsc_recAt Ld.c3).psc
  have hlt := (tscIn_heard Ld.c3).1
  have hlen : (tscWs (H1.ztF.toList.take Pp.y.h.lt)).length = Pp.y.h.lt := by
    unfold tscWs
    rw [List.length_map, List.length_take, Array.length_toList]
    exact Nat.min_eq_left hlt
  have hfmt : P.own.toOwn.tail.s3.L.T.par.fmt =
      List.replicate (tscWs (H1.ztF.toList.take Pp.y.h.lt)).length (pfCube GE 2) ++
        [pDummy GE 1] := by
    rw [hlen, W.w3.hf, ok.s3.k, f3.k, ok.s3.dy, f3.dY]
  have D1 := d1_ended_at P.own.toOwn.tail.s3.L.T.par (aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7) a
    (fun w hw' => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw'
      rfl) hfmt hSx hrow (Ld.g2.trans hL) mask entry m hw3
  have D2 := tsc_d2 P.own.toOwn.tail.s3.L.T.par (aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7) Ld.c3
    Ld.s1 (Ld.g1'.trans hL) mask entry m hinc3
  have key := scaled_over_at gl s P.tp.tm.pick_ok Ex y (Hl.worldOf gl mask entry) m D1 D2 _ hk
  rw [hKT, key, ← e]
  exact (add_zero _).symm

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tsc_d2
#print axioms OnBytes.Road.K4.led7_terms
#print axioms OnBytes.Road.K4.ho_of_led
