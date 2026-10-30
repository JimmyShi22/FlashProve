-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetInstFFAll.lean: no wrap-around in a feed-forward segment: the assembly, at a variable
number p.

"No wrap-around": what holds modulo p of the cells' small integers is shown to hold over the
integers, for a variable number p with 2^61 - 1 ≤ p (the class `Big p`: Inst/Model/Bound/Base.lean;
that p is prime is not assumed).

Main names:
  `part1`, `part2`, `part3`: from the segment's field relation formed in `ZMod p` (`h`: `RFraw`,
    Inst/Model/FF/Cast.lean), each under the hypotheses of its statement, among them size
    conditions (`AdmN` at p in all three; `AdmP` at p and `SzR` in `part1`, `part3`; `AdmS` at p in
    `part2`, `part3`): `Part1`, `Part2`, `Part3` (Inst/Model/FF/Trace.lean) for layer l: equations
    and bounds over the integers that tie the cells' values to the program's steps
    (Inst/Model/Program.lean).

Why: `Big p` enters through the theorems of Cm/TargetInstFFUnit.lean and
Cm/TargetInstFFRouter.lean; `intRel` and `part2` do not need it.

Limits: the namespace is `Cm.TI`. What `Part1`, `Part2`, `Part3` say: the head of
Inst/Model/FF/NoWrap.lean. (The limits on the prime: the head of Inst/Model/Bound/Base.lean.)
Terms: lean/GLOSSARY.md.
-/
import Inst.Model.FF.NoWrap
import Cm.TargetInstFFRouter


set_option autoImplicit false

/- The default table of scales is not in sight in this file (`Scl.ref` is no instance here): what
reads a table reads the variable `scl`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cm.TI.FFSeg

open Inst.Model Inst.Model.FFSeg

variable {p : ℕ} [Big p]

variable [scl : Scl]

open Finset hiding val

namespace NWA
open Inst.Model.FFSeg.NWA
open Inst.Model.FFSeg.NWR (SzR WFabs)

variable {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {w : ℕ → LayerW} {emb : Mat}
  {tok : ℕ → ℕ} {t : Cell → ℤ}

omit [Big p] in
/-- the relation over `ZMod p`, as congruences -/
theorem intRel (h : RFraw D tb L0 first (ZMod p) w emb tok t) :
    IntRel D tb L0 first (p : ℤ) w emb tok t := by
  exact intRel_of_rfraw p h

variable (h : RFraw D tb L0 first (ZMod p) w emb tok t)
  (aN : AdmN (p : ℤ) D) (aP : AdmP (p : ℤ) D tb L0 w) (S : SzR D)
include h aN aP S

/-- **Lemma S15.4 (i).** -/
theorem part1 {l : ℕ} (hl : l < D.nl) : Part1 D tb w L0 t l := by
  have hI := intRel h
  have hW := WFabs.of_wf (aP.wf l hl)
  have n1 := fun i (hi : i < D.T) => norm1_at hI aN hl hi
  have n2 := fun i (hi : i < D.T) => norm2_at hI aN hl hi
  have qk := fun i (hi : i < D.T) c (hc : c < D.dqk) => qk_at hI aP hl hi (n1 i hi).2.2.1 hc
  have vv := fun i (hi : i < D.T) c (hc : c < D.dkv) => v_at hI aP hl hi (n1 i hi).2.2.1 hc
  have gt := fun i (hi : i < D.T) x (hx : x < D.f) => NWU.gate_facts h hl hx hi aP.tab S.toSz
  have sh := fun i (hi : i < D.T) x (hx : x < D.f) (hr : routed D l x = false) =>
    NWU.shared_facts h hl hx hi aP.tab S.toSz hr (NWR.m_abs (n2 i hi).2.2.1)
      (fun j _ => hW.Wg j x) (fun j _ => hW.Wu j x)
  refine
    { att := fun i hi => ?_
      aw := fun i hi => (n1 i hi).2.1
      a := fun i hi => (n1 i hi).2.2.1
      qkw := fun i hi c hc => (qk i hi c hc).1
      q := fun i hi c hc => ?_
      kx := fun i hi c hc => ?_
      vw := fun i hi c hc => (vv i hi c hc).1
      v := fun i hi c hc => ?_
      n2 := fun i hi => (n2 i hi).1
      mw := fun i hi => (n2 i hi).2.1
      m := fun i hi => (n2 i hi).2.2.1
      led := fun n hn i hi => ?_
      bound := fun n hn i hi =>
        (ledger_at hI aN (ν := 2 * l + n) (show 2 * l + n < 2 * D.nl by omega) hi).2.2.2.2.1
      g0 := fun i hi x hx => (gt i hi x hx).1
      ghR := fun i hi x hx => (gt i hi x hx).2.1
      gc := fun i hi x hx => (gt i hi x hx).2.2.1
      sl := fun i hi x hx => (gt i hi x hx).2.2.2.1
      upR := fun i hi x hx => (gt i hi x hx).2.2.2.2.1
      gwS := fun i hi x hx hr => (sh i hi x hx hr).1
      upS := fun i hi x hx hr => (sh i hi x hx hr).2 }
  · have hi' : i < D.T := by rw [aP.T]; exact hi
    refine ⟨(n1 i hi').1, fun c hc => ?_, fun c hc => ?_⟩
    · rw [← (qk i hi' c hc).1]
      exact (qk i hi' c hc).2.1
    · rw [← (vv i hi' c hc).1]
      exact (vv i hi' c hc).2.1
  · have hc' : c < D.dqk := Nat.lt_of_lt_of_le hc (Nat.le_add_right _ _)
    have := (qk i hi c hc').2.2.1
    rw [if_pos hc, (qk i hi c hc').1] at this
    exact this
  · have hc' : D.dq + c < D.dqk := Nat.add_lt_add_left hc _
    have := (qk i hi (D.dq + c) hc').2.2.1
    rw [if_neg (by omega), Nat.add_sub_cancel_left, (qk i hi (D.dq + c) hc').1] at this
    exact this
  · have := (vv i hi c hc).2.2.1
    rw [(vv i hi c hc).1] at this
    exact this
  · obtain ⟨a1, a2, a3, -⟩ :=
      ledger_at hI aN (ν := 2 * l + n) (show 2 * l + n < 2 * D.nl by omega) hi
    exact ⟨a1, a2, a3⟩

omit [Big p] in
omit aP S in
/-- **Lemma S15.4 (ii)**: (PL7), with (FA12). (not all hypotheses are named here: see the statement
below) -/
theorem part2 (aS : AdmS (p : ℤ) D L0 w) (ho : OBound D t) {l : ℕ} (hl : l < D.nl) :
    Part2 D w t l :=
  fun i hi _ hc => (pl7_at (intRel h) aN aS hl hi (ho l hl i hi) hc).1

/-- **Lemma S15.5**: the feed-forward block, with (FL19). (not all hypotheses are named here: see
the statement below) -/
theorem part3 (aS : AdmS (p : ℤ) D L0 w) (hlast : LastBound D t) {l : ℕ} (hl : l < D.nl) :
    Part3 D tb w L0 t l := by
  have hI := intRel h
  have hW := WFabs.of_wf (aP.wf l hl)
  have n2 := fun i (hi : i < D.T) => norm2_at hI aN hl hi
  have rf := fun (he : isExpL l = true) i (hi : i < D.T) =>
    NWR.router_facts h hl hi aP.tab S hW (n2 i hi).2.2.1 he
  have hf := fun i (hi : i < D.T) x (hx : x < D.f) =>
    NWR.hidden_facts h hl hi aP.tab S hW (n2 i hi).2.2.1 aS.even hx
  refine
    { ly := fun he i hi e hx => ((rf he i hi).1 e hx).1
      l3 := fun he i hi e hx => ((rf he i hi).1 e hx).2.1
      lr := fun he i hi e hx => ((rf he i hi).1 e hx).2.2.1
      sel := fun he i hi e hx => ((rf he i hi).1 e hx).2.2.2.2
      sc := fun he i hi => (rf he i hi).2.2.1
      xr := fun he i hi j hj => ((rf he i hi).2.2.2 j hj).1
      slP := fun i hi x hx => (hf i hi x hx).1
      upP := fun i hi x hx => (hf i hi x hx).2.1
      ok := fun i hi => ?_
      out := fun i hi c hc => ?_ }
  · have hi' : i < D.T := by rw [aP.T]; exact hi
    exact NWR.ok_facts h hl hi' aP.tab S hW (n2 i hi').2.2.1 aS.even (n2 i hi').1
  · exact (pl13_at hI aN aS hl hi hc (stream_bound hI aN hlast (by omega) hi hc)
      (Ad_eq (fun x hx => (hf i hi x hx).1) (fun x hx => (hf i hi x hx).2.1) aS
        (fun he e hx => ((rf he i hi).1 e hx).2.2.2.2) c)
      (fun j hj => NWR.hh_abs h hl hi aP.tab S hW (n2 i hi).2.2.1 aS.even hj)).1

end NWA

end Cm.TI.FFSeg
