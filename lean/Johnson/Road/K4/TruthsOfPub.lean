-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/TruthsOfPub.lean: the records of true tables that
Johnson/Road/K4/FrontDictOf.lean asks, all at once, at the library's public record of a layer
sub-proof, Pub34 (Johnson/Road/Rows/LayerEnds34.lean), from "every table of the reads holds what it
says of the matrices Mm" (ReadsTrue).

  `truths_of_pub34`: PortFits (and in it Fits), TrueAt2, TrueAt3, TrueAt4, Laid and Switches, at the
    record's own letters: the cells are those of Mm; the points are the readings of the verifier's
    own points (the last la coordinates of the three product layers' challenges among them).
It lays theorems side by side: worlds_of_holds, sigFits_of_look (through sigFits_of_pub34,
Johnson/Road/K4/StackPub34.lean), trueAt3_of_holds, admitted_of_layout; and trueAt4_of_holds
(Johnson/Road/K4/TrueAt4.lean).
Limits. A record and ReadsTrue are premises. With a second product layer alone. Nothing on a draw,
on soundness or on hiding.


-/
import Johnson.Road.K4.StackPub34
import Johnson.Road.K4.TrueAt4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (World Level lastOf)
open Inst.Model (Scl)

variable {K : Type} [Field K]

/-- **The records of true tables at a record Pub34, on true reads.** -/
theorem truths_of_pub34 (X : Rows.Pub34 K) (Wo : World K) (Mm : Mats K)
    (hRd : X.ReadsTrue Wo Mm) {o2 : Level} (h2 : X.hd2 = some o2) :
    letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
    ∃ ZV ZA ZB, lastOf X.H.wpl.r X.p.v.y.h.la = .ok ZV ∧ lastOf X.hd.r X.p.v.y.h.la = .ok ZA ∧
      lastOf o2.r X.p.v.y.h.la = .ok ZB ∧
      PortFits X.ρ Wo X.p.v X.D (cellsAt X.p.v.y Mm) (cellsOf X.D (cellsAt X.p.v.y Mm))
        (pt X.ρ X.Zp) (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt) ∧
      TrueAt2 X.ρ Wo X.p.v X.D.lT (cellsAt X.p.v.y Mm) (pt X.ρ X.Zp) (pt X.ρ X.c.rt) ∧
      TrueAt3 X.ρ Wo X.p.v X.D.lT (cellsAt X.p.v.y Mm) (pt X.ρ ZV)
        (fun j => pt X.ρ ZV (X.p.v.y.ls + j)) (pt X.ρ X.H.PV) (pt X.ρ X.H.tV.r) (pt X.ρ X.H.ZE)
        (fun j => pt X.ρ X.H.ZE (X.p.v.y.ls + j)) ∧
      TrueAt4 X.ρ Wo X.p.v X.D.lT (cellsAt X.p.v.y Mm) (pt X.ρ ZA)
        (fun j => pt X.ρ ZA (X.p.v.y.ls + j)) (pt X.ρ ZB) (fun j => pt X.ρ ZB (X.p.v.y.ls + j)) ∧
      Laid X.p.v.y ∧ Switches X.p.v.y.h := by
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  have A := admitted_of_layout X.hy X.S.p3
  have hlt : X.p.v.y.h.lt = X.D.lT := by rw [A.shape, X.Z.lT]
  obtain ⟨-, T2, -, -⟩ := worlds_of_holds X.ρ Wo X.hy X.S X.hg X.hrd X.hl X.ht X.Z X.hZ X.hzt
    X.h4 X.hcrt X.htm X.hNM X.hpts X.hfun X.hT Mm hRd
  obtain ⟨ZV, hZV, T3⟩ := trueAt3_of_holds X.ρ Wo X.hy X.S X.hg X.hrd X.hl X.ht X.htm X.hNM
    X.hpts X.hfun Mm hRd
  have hp' := X.hpts
  rw [h2] at hp'
  obtain ⟨ZA, ZB, hA, hB, T4⟩ := trueAt4_of_holds X.ρ Wo X.hy X.S X.hg X.hrd X.hl X.ht X.htm
    X.hNM hp' X.hfun Mm hRd
  rw [hlt] at T3 T4
  rw [← X.Z.lT] at T2
  exact ⟨ZV, ZA, ZB, hZV, hA, hB, (sigFits_of_pub34 X Wo Mm hRd).port, T2, T3, T4, A.laid,
    by rw [A.shape]; exact X.S⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.truths_of_pub34
