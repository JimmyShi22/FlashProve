-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3PackNames.lean: bounds on list decoding and on mutual
correlated agreement for codes of length 8 with the laws (`LdCode.Laws`, Cb/Ld/LdRel.lean) and the
distance 5 at the radius 3, in the form in which test instances of a folding step cite them.


This file proves the fold's record "below the Johnson radius",
and so its hypotheses, for any parameters at the eight positions that meet the hypotheses of the
statements. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold
as proofs.

Restatements. A guard against empty theorems; no parameter of a protocol.
The analogue, in namespace `Cb.GlJ3`, of the part of Cb/GlVal/GlToyPackNames.lean that depends on
the radius: `list5`, `list74`, `toy_par_hyp`, `toy_par_hyp74`. UNCHANGED, and taken from Cb.Gl: C74,
plc5, plc5_inj.
Against Cb/GlVal/GlToyPackNames.lean. There the radius 1 lies within a third of the distance, where
agreement follows from laws and distance. Here agreement is by the count of sets of positions, which
at eight positions is at most the count `bJ3` of the statement on codes (head of
Cb/GlVal/GlJ3Base.lean: `mcaJ3`, `rowsJ3`).

Main names:
  `toy_par_john`: `Y.John 5 eJ3 t bJ3 bJ3 bJ3` (Cb/Obj/LdObjectTowerJohn.lean), for parameters Y of
    a fold (`SumPar`) under the eleven hypotheses `hC` to `hzk` of its statement.
  `toy_par_hyp`: `Y.Hyp 5 eJ3 1 (LJ3) (bJ3) (bJ3) (bJ3)`; `toy_par_hyp74`:
    `Y.Hyp 5 eJ3 3 (LJ3) (bJ3) (bJ3) (bJ3)`; each under the eleven hypotheses `hC` to `hzk` of its
    own statement.

Notation: `eJ3`: the radius; `LJ3`: the bound on lists; `bJ3`: the count for agreement (all three:
Cb/GlVal/GlJ3Base.lean); `P84`: the positions of the code `C84` (Cb/GlVal/GlToyBase4.lean); `P5`,
`P74`: two more names of `P84` (Cb/GlVal/GlToyStdNames.lean).

Limits: this file does not say the size of `bJ3`.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyPackNames
import Cb.Obj.LdObjectTowerJohn
import Cb.GlVal.GlJ3StdNames

set_option autoImplicit false

namespace Cb.GlJ3
open Iop Prob Hiop Blocks IOR Cb.Ood Cb.Gl

theorem list5 (D : LdCode E P5) (hL : D.Laws) (hD : D.Dist 5) : D.ListAt eJ3 LJ3 := listJ3 D hL hD
theorem list74 (D : LdCode E P74) (hL : D.Laws) (hD : D.Dist 5) : D.ListAt eJ3 LJ3 := listJ3 D hL hD

/-- The fold's record below the Johnson radius, for any parameters at the toy's eight positions.
(not all hypotheses are named here: see the statement below) -/
theorem toy_par_john (Y : SumPar E P84) (t : ℕ) (hC : Y.C.Laws) (hCD : Y.C.Dist 5) (hZ : Y.Z.Laws)
    (hZD : Y.Z.Dist 5) (hW : Y.Zw.Laws) (hWD : Y.Zw.Dist 5) (hn : 2 ≤ Y.n)
    (hv : Function.Injective Y.val) (hP : Y.PackOK) (hQ : Y.QwDeg) (hzk : Y.Zw.Zk t) :
    Y.John 5 eJ3 t bJ3 bJ3 bJ3 where
  lawsC := hC
  lawsZ := hZ
  lawsW := hW
  distC := hCD
  distZ := hZD
  distW := hWD
  john := inJ3
  mcaC := rowsJ3 _ hC
  mcaZ := rowsJ3 _ hZ
  mcaW := rowsJ3 _ hW
  inj := hv
  deg := hn
  pack := hP
  qw := hQ
  zk := ld_zk_il E P84 _ _ t hzk

theorem toy_par_hyp (Y : SumPar E P5) (hC : Y.C.Laws) (hCD : Y.C.Dist 5) (hZ : Y.Z.Laws)
    (hZD : Y.Z.Dist 5) (hW : Y.Zw.Laws) (hWD : Y.Zw.Dist 5) (hn : 2 ≤ Y.n)
    (hv : Function.Injective Y.val) (hP : Y.PackOK) (hQ : Y.QwDeg) (hzk : Y.Zw.Zk 1) :
    Y.Hyp 5 eJ3 1 (fun _ => LJ3) (fun _ => bJ3) (fun _ => bJ3) (fun _ => bJ3) :=
  (toy_par_john Y 1 hC hCD hZ hZD hW hWD hn hv hP hQ hzk).hyp

theorem toy_par_hyp74 (Y : SumPar E P74) (hC : Y.C.Laws) (hCD : Y.C.Dist 5) (hZ : Y.Z.Laws)
    (hZD : Y.Z.Dist 5) (hW : Y.Zw.Laws) (hWD : Y.Zw.Dist 5) (hn : 2 ≤ Y.n)
    (hv : Function.Injective Y.val) (hP : Y.PackOK) (hQ : Y.QwDeg) (hzk : Y.Zw.Zk 3) :
    Y.Hyp 5 eJ3 3 (fun _ => LJ3) (fun _ => bJ3) (fun _ => bJ3) (fun _ => bJ3) :=
  (toy_par_john Y 3 hC hCD hZ hZD hW hWD hn hv hP hQ hzk).hyp

end Cb.GlJ3
