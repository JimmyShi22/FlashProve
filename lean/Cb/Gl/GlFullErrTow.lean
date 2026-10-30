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
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlFullErrTow.lean: over Goldilocks' cubic extension, for one test on
a group with a tower of the library's codes below the Johnson radius (`RunGlJAt`), the whole test,
its errors overwritten by the full list, is in order, with nothing assumed beyond the hypotheses of
its statement
(`RunGlJAt D Tw d`, and the proofs inside its records): neither the premise on agreement
(`Gl.AgreeJ`) nor the statement from which it is drawn (`Cb.BCHKS46At`, Cb/Gen/CodeListRSAt.lean).

Statements (in `Cb.Gl.Spec`) and proofs. In plain terms: with every round's error put to its trivial
value, the number of all values of that round's verifier message (`Err.full`, Cb/Gen/FullErr.lean),
the conditions `RunGlJAt D Tw d` give `D.full.OK` without the premise `AgreeJ`.

Why the full list (the head of Cb/Gen/FullErr.lean): the records `GoodT`, `GoodB`, `PieceTr`,
`TailTr` hold the knowledge side in one field, `know`, beside the honest and neutral ones. Where
`know` at the true errors needs a fact that is only assumed (agreement of codes: `Gl.AgreeJ`), the
whole record is had only under that fact. At the full list `know` says nothing (the count of bad
verifier messages is at most their number): so a record at the full list is the honest half.
The field is `E` (Cb/Gl/GlField.lean). A test on a group is a record `D : LdRunD S`
(Cb/Ld/LdLinCloseRuns.lean); its whole test is the field `D.T`. "In order" is `LdRunD.OK`: `D.Z.OK`,
at most `D.L` codewords of the group's complex within the joint radius, `D.G.Fits`, and `D.T` is a
tail of a chain that needs at most `D.t` long positions. A tower is the data of a whole test: folds
and code switches in turn, then a base case (`LdTowJ`, `LdTowGJ`, Cb/Obj/LdObjectTowerJohn.lean).
The library's codes are those built from families of plain Reed-Solomon codes (`GlJ`,
Cb/Gl/GlLdJ.lean; `GlC`, Cb/Gl/GlLd.lean). `TowGlJ`, `TowGGlJ`: Cb/GlVal/GlJohn.lean; `RunGlJAt`:
Cb/Gl/GlObjMix.lean.
`AgreeJ` (Cb/Gl/GlFinalAg.lean) asserts: `IsGlJ C d t e bad` and InJohnson |P| d e give
`C.MCArows e bad`: mutual correlated agreement with at most bad exceptional values, for every number
of rows.
In Cb/Gen/FullErrTow.lean: `T.full` puts all counts of bad challenges of a tower to the number of
all field elements; `D.full` is D with the errors of its whole test overwritten by the full list;
`D.PreJD Tw d` is `D.PreJ Tw d` (Cb/Obj/LdObjectTowerJohn.lean) with `Tw.full.John` for `Tw.John`.

Main names:
  `Spec.glFull_runOK`: `RunGlJAt D Tw d` ⇒ `D.full.OK`: the honest half of what `glAg_runAt` with
    `ldTowGJ_run` gives under the premise `AgreeJ`: of D's own reduction and honest side:
      point structures;
      locality;
      acceptance of the honest prover;
      exactness of its views (`GoodT`, Ior/KnowCollGood.lean: `exact : H.Exact A.rel P.bud`);
      what the formats bear.

Why: `Spec.glFull_fold`, `Spec.glFull_tower`, `Spec.glFull_towerG` (G.P nonempty) and
`Spec.glFull_runAt` are twins by hand of `glAg_fold`, `glAg_tower`, `glAg_towerG`, `glAg_runAt`
(Cb/Gl/GlFinalAg.lean) without the premise `AgreeJ`, at the counts |E|: the three fields on
agreement of a fold (and the base's one) hold at the count "all field elements", by
`ldCode_mcaRowsFull` and `ldCode_mcaAtFull` (Cb/Gen/FullErrTow.lean).

Notation:
  `Y`: the parameters of the block (`SumPar E P`, Cb/Ld/LdSum.lean);
  `Y.John d e t bC bZ bW`: a fold below the Johnson radius (`SumPar.John`,
    Cb/Obj/LdObjectTowerJohn.lean);
  `d`, `e`, `t`, `bC`, `bZ`, `bW`: numbers; of them `Spec.glFull_fold` asks `GlJ Y.C d 0 e bC`,
    `GlJ Y.Z d 0 e bZ`, `GlJ Y.Zw d t e bW` and InJohnson |P| d e;
  `bC`, `bZ`, `bW` as letters of a tower's constructors: its counts of bad challenges at a fold
    (Cb/Gen/FullErrTow.lean);
  `d` in `RunGlJAt D Tw d`: a number (Cb/Gl/GlObjMix.lean).

Limits: nothing on the chance of a cheating prover. This file says nothing on an object or a
compiled scheme: that an object whose four tests of a session are overwritten so has the same
sub-protocols is not stated here. This file gives no value of any parameter of the protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.FullErrTow
import Cb.Gl.GlFinalAg

set_option autoImplicit false

namespace Cb.Gl
open Iop Prob Iop.IOR

namespace Spec

def glFull_fold : Prop :=
  ∀ (P : Type) [Fintype P] (Y : SumPar E P) (d e t bC bZ bW : ℕ), GlJ Y.C d 0 e bC →
    GlJ Y.Z d 0 e bZ → GlJ Y.Zw d t e bW → InJohnson (Fintype.card P) d e →
    Function.Injective Y.val → 2 ≤ Y.n → Y.PackOK → Y.QwDeg →
    Y.John d e t (Fintype.card E) (Fintype.card E) (Fintype.card E)

def glFull_tower : Prop := ∀ (a : LdJoint E) (T : LdTowJ a), TowGlJ T → T.full.John

def glFull_towerG : Prop :=
  ∀ (B : Type) [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    TowGGlJ T → T.full.John

def glFull_runAt : Prop :=
  ∀ (S : Sig E) (D : LdRunD S) (Tw : D.TowJ) (d : ℕ), RunGlJAt D Tw d → D.PreJD Tw d

def glFull_runOK : Prop :=
  ∀ (S : Sig E) (D : LdRunD S) (Tw : D.TowJ) (d : ℕ), RunGlJAt D Tw d → D.full.OK

end Spec

theorem glFull_fold : Spec.glFull_fold := fun P _ Y d e t bC bZ bW hC hZ hW hJ hi hn hp hq =>
  have gC := glC_code P _ d 0 (glJ_glC P _ d 0 e bC hC)
  have gZ := glC_code P _ d 0 (glJ_glC P _ d 0 e bZ hZ)
  have gW := glC_code P _ d t (glJ_glC P _ d t e bW hW)
  { lawsC := gC.1, lawsZ := gZ.1, lawsW := gW.1, distC := gC.2.2.2.1, distZ := gZ.2.2.2.1,
    distW := gW.2.2.2.1, john := hJ
    mcaC := ldCode_mcaRowsFull _ _, mcaZ := ldCode_mcaRowsFull _ _, mcaW := ldCode_mcaRowsFull _ _
    inj := hi, deg := hn, pack := hp, qw := hq,
      zk := (glC_code P Y.Cw d t (.il _ (glJ_glC P _ d t e bW hW))).2.2.2.2 }

theorem glFull_tower : Spec.glFull_tower := by
  intro a T
  induction T with
  | base a t cov d b =>
    rintro ⟨h, hJ⟩
    have g := glC_code a.P a.C d 0 (glJ_glC a.P a.C d 0 a.e b h)
    exact ⟨g.1, g.2.2.2.1, hJ, ldCode_mcaAtFull _ _, g.2.1⟩
  | step Y sl e S d bC bZ bW e' d' rest ih =>
    rintro ⟨⟨hC, hZ, hW, hJ, hi, hn, hp, hq⟩, ⟨hN, hJ', hZo, hZb, hP⟩, hr⟩
    refine ⟨glFull_fold _ (Y.reform sl) d e S.ts bC bZ bW hC hZ hW hJ hi hn hp hq,
      rest.full_q.symm ▸ glJ_switch _ _ _ (S.D e) d' e' rest.toC.q hN ?_ hJ' hZo hZb hP,
      ih hr⟩
    exact glC_mono _ _ d 0 0 0
      (.pair (glJ_glC _ _ d 0 e bC hC)
        (.pair (glJ_glC _ _ d 0 e bZ hZ)
          (glC_mono _ _ d S.ts d 0 (glJ_glC _ _ d S.ts e bW hW) le_rfl (Nat.zero_le _))))
      (Nat.zero_le _) le_rfl

theorem glFull_towerG : Spec.glFull_towerG := by
  intro B _ S G _ Sb sl Z T h
  cases T with
  | plain T => exact glFull_tower _ T h
  | shaped Sh Sw d bC bZ bW e' d' rest =>
    obtain ⟨⟨hv, hm1, hm2, hz, h1⟩, ⟨hB, hZ, hW, hJ, hi, hn, hp, hq⟩,
        ⟨hN, hJ', hZo, hZb, hP⟩, hr⟩ := h
    have hC : GlJ Sh.par.C d 0 G.e bC := .il _ hB
    have hI : GlC (Sw.D G.e).Cin 0 0 :=
      glC_mono _ _ d 0 0 0
        (.pair (glJ_glC _ _ d 0 G.e bC hC)
          (.pair (glJ_glC _ _ d 0 G.e bZ hZ)
            (glC_mono _ _ d Sw.ts d 0 (glJ_glC _ _ d Sw.ts G.e bW hW) le_rfl (Nat.zero_le _))))
        (Nat.zero_le _) le_rfl
    exact ⟨⟨hv,
      (glC_code _ _ d 0 (glJ_glC _ _ d 0 G.e bC hB)).1,
      (glC_code _ _ d 0 (glJ_glC _ _ d 0 G.e bZ hZ)).1,
      fun r => by
        split
        · next b hb => exact hm1 r b hb
        · next j hj => exact hm2 r j hj, hz, h1⟩, glFull_fold _ Sh.par d G.e Sw.ts bC bZ bW hC hZ hW hJ hi hn hp hq, rest.full_q.symm ▸ glJ_switch _ _ _ (Sw.D G.e) d' e' rest.toC.q hN hI hJ' hZo hZb hP, glFull_tower _ rest hr⟩

theorem glFull_runAt : Spec.glFull_runAt := by
  rintro S D Tw d ⟨h1, h2, h3, hG, hJ, hF, hZ, hT⟩
  exact ⟨h1, h2, h3, fun a => (glC_code D.G.P _ d 0 (hG a)).1,
    fun a => (glC_code D.G.P _ d 0 (hG a)).2.2.2.1, hJ, hZ, hF,
    glFull_towerG _ S D.G D.Sb D.sl D.Z Tw hT⟩

theorem glFull_runOK : Spec.glFull_runOK := fun S D Tw d h =>
  ldRunD_fullOK E S D Tw d (glFull_runAt S D Tw d h)

end Cb.Gl
