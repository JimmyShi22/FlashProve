-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/KtLedFirst.lean: THE FIRST GROUP's TWIN OF KtLed.lean's PART "AT A HEARING": THE
FORM KT OF THE TERMS' STRETCH, IN A WORLD WITH MASKS. K4's text makes of the terms' token sumcheck
the form `KT`: that sumcheck's own row without summand and kept terms, scaled by minus the inverse
of eps (OnBytes/Desc/First/K4/Hear.lean, `hearTerms`). The library writes "the row's other members,
divided by eps" as `overAt` (Cb/Pv/Lay/Over.lean). Under the record `LedG` of a hearing in any group
(Johnson/Road/K4/OwnLedgersG.lean), at the letters `tailW P` of the first sub-proof's chain behind
its three points (Cb/Pv/Lay/End/FirstShare.lean) and the chain's data read off the tape behind the
points in front (`t0.drop (k0 g)`) with the states `addsOf`: the two are one value, at one m, in the
world of any ledger later than the hearing's last. Two statements and their proofs.

  `led7_termsF`: off `LedG`: `o.H.KT = (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps))`, and
    there is a ledger with arrays of the right sizes from which the run of the terms' row's hiding
    coefficients leads to G2.
  `ho_of_ledF`: `overAt P.ip.Y3 (aD3 ...).out m = o.H.KT.value gl (Hl.worldOf gl mask entry)`.

NO NEW ARGUMENT: KtLed.lean's two proofs, turned to these letters by program; `tsc_d2` is taken
from KtLed.lean as it stands (it speaks of no group).

Limits. All letters are the caller's, but one ledger inside `led7_termsF`, which is spent inside
`ho_of_ledF`. PREMISES: `LedG`; `NzT` (no further challenge reads 0); g7.t3 is the record's target;
`TailM.Ok`; `StgFits` at the third stage; Hl later than G; hw3 (which entry serves as which
coefficient of the hiding polynomial); hinc3 (the typed half of (D2)); hk (the reading of minus the
inverse of eps, times the reading of eps, is -1). THE GROUP g IS A LETTER: nothing here says that it
is the first; the typed letters are the first sub-proof's. One world: no draw. Nothing on
soundness.
-/
import Johnson.Road.K4.KtLed
import Johnson.Road.K4.OwnLedgersG
import Cb.Pv.Lay.End.FirstShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Cb.Pv.Lay.End.Gated Johnson.L5.Layers
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard Level Tsc Psc World Aff)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Tie.Pv (slotP)
open OnBytes.Tie.Pv.Lay (StgFits)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aD3 aS3 tscWs tscIn_heard tsc_world pscRow_spec
  scaled_over_at)
open OnBytes.Slice (GE)
open Inst.Model (Scl)

variable {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u u5 : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork}

/-- **What `LedG` holds of the terms' row**, off its fields `nt`, `kTT` and `s1`. -/
theorem led7_termsF (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5) :
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

variable [scl : Scl] {M Xs : Type} (P : FullFPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM (tailW P) R)

/-- **The form KT is the library's `overAt` at the terms' typed output**, at one m. -/
theorem ho_of_ledF (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW P) (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) (ht3 : g7.t3 = tT.p.target) (ok : W.Ok)
    (f3 : StgFits gl (tailW P).s3 (aS3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (tscWs (H1.ztF.toList.take Pp.y.h.lt)) Pp.y.h.lt 1)
    (Ex : ExtSpec) (y : Ex.Str) {Hl : Fork}
    (hL : Fo.Later G Hl) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (m : P.ip.Y3.J → Cb.Gl.E)
    (hw3 : ∀ q, m (P.ip.Y3.wAt q) = mask (slotP P.ip.Y3.fmt tT.p.first q))
    (hinc3 : P.ip.Y3.inc (aS3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
      maskSum Hl (Aff.slot tT.sCl) mask - entSum (Aff.slot tT.sCl) entry)
    (hk : gl.val (negE (invE tT.p.eps)) * gl.val tT.p.eps = -1) :
    overAt P.ip.Y3 (aD3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7).out m =
      o.H.KT.value gl (Hl.worldOf gl mask entry) := by
  obtain ⟨hKT, Gx, hSx, hrow⟩ := led7_termsF Ld
  obtain ⟨e, s⟩ := stgT_said W.w3.num (ksOf Pp hp).k3 _ nz.b3
    (aS3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) g7.t3 rfl (tsc_recAt Ld.c3) ht3 f3
  obtain ⟨C, τ, first, a⟩ := (tsc_recAt Ld.c3).psc
  have hlt := (tscIn_heard Ld.c3).1
  have hlen : (tscWs (H1.ztF.toList.take Pp.y.h.lt)).length = Pp.y.h.lt := by
    unfold tscWs
    rw [List.length_map, List.length_take, Array.length_toList]
    exact Nat.min_eq_left hlt
  have hfmt : (tailW P).s3.L.T.par.fmt =
      List.replicate (tscWs (H1.ztF.toList.take Pp.y.h.lt)).length (pfCube GE 2) ++
        [pDummy GE 1] := by
    rw [hlen, W.w3.hf, ok.s3.k, f3.k, ok.s3.dy, f3.dY]
  have D1 := d1_ended_at (tailW P).s3.L.T.par (aS3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) a
    (fun w hw' => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw'
      rfl) hfmt hSx hrow (Ld.g2.trans hL) mask entry m hw3
  have D2 := tsc_d2 (tailW P).s3.L.T.par (aS3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) Ld.c3
    Ld.s1 (Ld.g1'.trans hL) mask entry m hinc3
  have key := scaled_over_at gl s P.tp.tm.pick_ok Ex y (Hl.worldOf gl mask entry) m D1 D2 _ hk
  rw [hKT, key, ← e]
  exact (add_zero _).symm

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.led7_termsF
#print axioms OnBytes.Road.K4.ho_of_ledF
