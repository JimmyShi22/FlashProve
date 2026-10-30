-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/MeetsMid.lean: the honest side of the kind "lookup" (K3).
Conditional: from "keys and bits are honest" to the specification's relation at a run. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there keys and bits are honest, relation after the challenge,
trace's bundles, specification, sort and full size. In this file: L is a structure of keys and bits
in the library's field (`LookIn`, Honest/K3/Wit.lean); `L.hidden` is the same in the program's
elements, as a row is handed it; h is a lookup's shape.

What is shown.
  `mid_of_meets`: from `FoNums.ok h` and `L.Meets h lm`: the relation after the challenge at the
    specification's data at a run, `(dataAt (fun theta => Fo.numsF h lm jLK theta) w p).Mid`
    (`dataAt`, Honest/K3/JobsSpec.lean), at w := `L.hidden`, at all points p and every jLK.
  `midG`, `midA`, `midH`, `midZ`: the same at the keys and bits of the four sorts of lookup
    (`lookG`, `lookA`, `lookH`, `lookZ`, Honest/K3/WitFill.lean).
Two halves are composed here. Honest/K3/WitFill.lean and Honest/K3/WitDigits.lean end at
`LookIn.Meets h lm` (Honest/K3/WitLaw.lean). `specAt_real` and `lawful_real`
(Honest/K3/Law/SpecReal.lean) assume the relation above, of the structure that a row is handed.

Hypotheses that remain.
  `hok`: `FoNums.ok` of the shape: public.
  `M`: (in `mid_of_meets`) `L.Meets h lm`. The proof does not use its first clause, on the place
    that reads 0.
  `N`, `Q`, `M`, `L`, `hg`: (in `midG`, `midA`, `midH`) the trace's four bundles `NamesFit X T`,
    `LookPub X`, `MeetsAll X i x T`, `PlanesLaid X i x T`; g < 12.
  `hF`, `hm`: (in `midZ`) `Fo.ZPlan.FromPieces tl` and `MzFits tl`: public both. At any size.

Imported. Honest/K3/WitDigits.lean imports Johnson/HonestTrace/DigitsAtTrace.lean.

Users. Honest/K3/Law/MeetsSite.lean [not in this library] calls `mid_of_meets`;
Honest/K3/Law/Thread/LeftAtCallsMid.lean imports this file.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
An instance of `Meets` alone is `pairLook` (`pairLook_meets`, WitLaw.lean), whose shape does not
pass `FoNums.ok`. The hypotheses of `midG`, `midA` and `midH` hold at the full size alone
(`NamesFit`). The library has a theorem for each of the trace's four bundles at its own honest
trace, in files that this one does not import (Honest/K3/GLOSSARY.md, "trace's bundles").
That the structure which a course's input yields is `L.hidden` of one of these four, and that the
course's face is the face of that shape, is for whoever seats the row to show.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitDigits
import Johnson.Desc.ProofFile.Honest.K3.JobsSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law
open OnBytes.HonestTrace (fsAt pubHAt cellOf entryOf NamesFit LookPub MeetsAll PlanesLaid Tr MzFits)
open OnBytes.Road (Hd.shapeA)
open Inst.Model (Instance ppref)
open ProofFile.Honest.K8 (zzOf)

/-- **From the hypothesis on keys and bits to the specification's relation at a run.** Conditional
on `FoNums.ok h` (public) and `L.Meets h lm`. An instance of `Meets`: `pairLook`
(Honest/K3/WitLaw.lean), whose shape does not pass `FoNums.ok`; so no instance of the two hypotheses
together is exhibited in this file. -/
theorem mid_of_meets (L : LookIn) (h : OnBytes.Model.Forest.Shape) (lm jLK : ℕ)
    (hok : FoNums.ok h = true) (M : L.Meets h lm) (p : Pts) :
    (dataAt (fun theta => _root_.Fo.numsF h lm jLK theta) L.hidden p).Mid := by
  obtain ⟨kv, nu, -, hk, hb, hm⟩ := M
  have hkey : (fun x => up (L.hidden.key p.theta 0 x)) =
      OnBytes.Ends.jointKey h kv (up p.theta) := by
    funext x
    exact (hidden_key L p.theta 0 x).trans (hk _ x)
  have hbit : ∀ u < 2 ^ h.d, ∀ j < 32,
      nu ((_root_.Fo.numsF h lm jLK (up p.theta)).bAt u j) =
        (if j < FoNums.n + 2 then up (L.hidden.bit u j) else 0) := by
    intro u hu j hj
    have hj' : j < FoNums.n + 2 := hj
    rw [if_pos hj']
    exact ((hidden_bit L u j).trans (hb (up p.theta) jLK u j hu hj)).symm
  have h1 := midP_congr hbit (hm (up p.theta) (up p.alpha) jLK)
  show Cb.Lkp.MidP (FoNums.v' h + 1) h.d 5 32 (fun x => up (L.hidden.key p.theta 0 x))
    (_root_.Fo.tabF h (up p.theta)) (FoNums.pads h)
    (fun u j => if j < FoNums.n + 2 then up (L.hidden.bit u j) else 0) (up p.alpha)
  rw [← Cb.Fo.ok_v hok, OnBytes.HonestTrace.Look.tabF_eq hok, hkey]
  exact h1

section
variable {X : OnBytes.Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- A group's layers. Conditional on `FoNums.ok X.y.fo`, `NamesFit X T`, `LookPub X`,
`MeetsAll X i x T`, `PlanesLaid X i x T` and g < 12: at the full size alone. No instance of these
hypotheses is exhibited in this file. -/
theorem midG (hok : FoNums.ok X.y.fo = true) (N : NamesFit X T) (Q : LookPub X)
    (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ} (hg : g < 12) (jLK : ℕ) (p : Pts) :
    (dataAt (fun theta => _root_.Fo.numsF X.y.fo X.y.h.lmb jLK theta)
      (lookG X g ⟨cellOf X T⟩ ⟨entryOf i⟩).hidden p).Mid :=
  mid_of_meets _ _ _ jLK hok (lookG_meets N Q M L hg) p

/-- A group's attention. Conditional on `FoNums.ok (fsAt X g)` and the same bundles: at the full
size alone. No instance of these hypotheses is exhibited in this file. -/
theorem midA {g : ℕ} (hok : FoNums.ok (fsAt X g) = true) (N : NamesFit X T) (Q : LookPub X)
    (M : MeetsAll X i x T) (L : PlanesLaid X i x T) (hg : g < 12) (jLK : ℕ) (p : Pts) :
    (dataAt (fun theta => _root_.Fo.numsF (fsAt X g) (Hd.shapeA X g).cf.lmb jLK theta)
      (lookA X g ⟨cellOf X T⟩).hidden p).Mid :=
  mid_of_meets _ _ _ jLK hok (lookA_meets N Q M L hg) p

/-- The head. Conditional on `FoNums.ok X.HLy.fs` and the same bundles: at the full size alone.
No instance of these hypotheses is exhibited in this file. -/
theorem midH (hok : FoNums.ok X.HLy.fs = true) (N : NamesFit X T) (Q : LookPub X)
    (M : MeetsAll X i x T) (L : PlanesLaid X i x T) (jLK : ℕ) (p : Pts) :
    (dataAt (fun theta => _root_.Fo.numsF X.HLy.fs X.hS.lmbH jLK theta)
      (lookH X (pubHAt X x) ⟨cellOf X T⟩ ⟨entryOf i⟩).hidden p).Mid :=
  mid_of_meets _ _ _ jLK hok (lookH_meets N Q M L) p

end

/-- The digits, at the smallness test's own array ZZ: at every list of where the matrices are read,
all cells and every sampled matrix. Conditional on `Fo.ZPlan.FromPieces tl` and `MzFits tl` (public
both). At any size. No instance of these hypotheses is exhibited in this file. -/
theorem midZ {tl : OnBytes.Model.HTailF2} (hF : Fo.ZPlan.FromPieces tl) (hm : MzFits tl)
    (mats : List (ℕ × String × ℕ)) (C : Cells) (ts : List Int) (jLK : ℕ) (p : Pts) :
    (dataAt (fun theta => _root_.Fo.numsF tl.f9 5 jLK theta)
      (lookZ tl (zzOf tl mats C ts)).hidden p).Mid :=
  mid_of_meets _ _ _ jLK (OnBytes.HonestTrace.nums_Z hF).1 (digits_meets hF hm mats C ts) p

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.mid_of_meets
#print axioms ProofFile.Honest.K3.Law.midG
#print axioms ProofFile.Honest.K3.Law.midA
#print axioms ProofFile.Honest.K3.Law.midH
#print axioms ProofFile.Honest.K3.Law.midZ
