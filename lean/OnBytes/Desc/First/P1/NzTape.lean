-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/NzTape.lean: ON THE TAPE OF A WRITTEN TRANSCRIPT NO FURTHER CHALLENGE OF THE
SEVEN SUMCHECKS READS 0, if each further variable's written round draws its element by the rule
"other than 0". So the premise `NzT` (TailTape.lean) is paid by what is asked of the written rounds
(`TailDs`, OwnMaps.lean). Statements and proofs.

  `beta_nz`: a written round whose first drawn element is drawn other than 0 (`IsNZ`,
    OnBytes/Slice/Draws.lean): the reading of the first word that it drew is not 0.
  `midY_nz`, `pscT_nz`: so of `midY` (StageView.lean), and of `pscT`'s field beta on a tape.
  `nzT_of_ds`: `NzT T k t` from `TailDs T R`, the numbers' fit, and that t is the tape of a written
    transcript over `R.all`.

NO NEW ARGUMENT: `elemsV_nz` (a typed value that is drawn other than 0 is not 0) with
`drawn_head` (RoundRead.lean).

Limits. It speaks of WRITTEN transcripts: there a verifier's message is typed, and a value "other
than 0" is so by its type. Of a tape that is not the tape of a written transcript nothing is said.
Nothing on soundness.
-/
import OnBytes.Desc.First.P1.TailTape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers
open OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Psc (Weight)
open _root_.Run (ckP)

variable {M : Type}

theorem beta_nz (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal)
    (hz : IsNZ (Fmt.dsOf d.entry d.kind) 0) :
    gl.val ((drawnE d c).headD OnBytes.zeroE) ≠ 0 := by
  rw [drawn_head d m c]
  exact elemsV_nz _ 0 hz _

theorem midY_nz {dY dV : RDT} (hz : IsNZ (Fmt.dsOf dY.entry dY.kind) 0) : ∀ (vs : List RDT)
    (σ : Tr (uLT (ckP .two) (vs ++ [dY, dV]))), gl.val (midY dY dV vs σ).2 ≠ 0
  | [], (m, c, _) => beta_nz dY m c hz
  | _ :: vs, (_, _, σ) => midY_nz hz vs σ

theorem pscT_nz {f : Fmt.RoundView → Fmt.RoundView} (hf : KeepsWords f) {r : ScR} {bs : List RDT}
    {c : Tr (uLT (ckP .two) (r.all ++ bs))} {t : Tape} (h : IsTape f (r.all ++ bs) c t) {k : ℕ}
    (hk : r.vs.length = k) (hz : IsNZ (Fmt.dsOf r.dY.entry r.dY.kind) 0) (n : ℕ) :
    gl.val (pscT n k t).beta ≠ 0 := by
  subst hk
  obtain ⟨_, _, _, a4, _⟩ := IsTape.stage hf h (List.replicate r.vs.length (Weight.plain 3))
    List.length_replicate (Weight.atZero 1)
  show gl.val (roundAt (Weight.atZero 1) (t.drop (r.vs.length + 1))).2.2 ≠ 0
  rw [a4]
  exact midY_nz hz r.vs _

/-- **No further challenge reads 0.** -/
theorem nzT_of_ds {f : Fmt.RoundView → Fmt.RoundView} (hf : KeepsWords f) {X : Type} {T : LayTail GE M X}
    {R : TailR} {k : Ks} (hk : k.Fit R) {τ : Tr (uLT (ckP .two) R.all)} {t : Tape}
    (h : IsTape f R.all τ t) (H : TailDs T R) : NzT T k t :=
  have c := tapeCuts hk h
  ⟨pscT_nz hf c.g1 hk.k1 H.s1.mid.yNZ _, pscT_nz hf c.g2 hk.k2 H.s2.mid.yNZ _,
    pscT_nz hf c.g3 hk.k3 H.s3.mid.yNZ _, pscT_nz hf c.h4 hk.k4 H.s4.mid.yNZ _,
    pscT_nz hf c.g5 hk.k5 H.s5.mid.yNZ _, pscT_nz hf c.g6 hk.k6 H.s6.mid.yNZ _,
    pscT_nz hf c.g7 hk.k7 H.s7.mid.yNZ _⟩

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.beta_nz
#print axioms OnBytes.Desc.First.P1.nzT_of_ds
