-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerThird.lean: within a third of the distance: the blocks of a test on a group with no
hypothesis on lists or on agreement.

In standard terms: for codes that have their laws (`LdCode.Laws`, Cb/Ld/LdRel.lean) and radii within
a third of the distance of the code as it is read under its transformation (`LdCode.Dist`,
Cb/Ld/LdRel.lean), counted in long positions, the bounds on list size and on mutual correlated
agreement that the steps of a proximity test take as hypotheses are theorems; this file puts them
into each step's record of hypotheses.
The laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the encoder
`C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from native words
to long words, are linear over E; the encoder sends only the zero message with zero randomness to
zero; and, for every long position x, any two native words that agree at the native positions
`C.src x` have the same long symbol at x. In this file's statements the laws are premises.

Statements (each a `Prop`, for a finite field E, in `Cb.Spec`) and proofs (an assembly, but for
`ldThird_err`: by definition of the blocks' numbers). No protocol, no code.

Why: the blocks of a proximity test (fold, code switch, base case; the bridge in front of a test on
a group) take bounds on lists and on mutual correlated agreement as hypotheses: beyond unique
decoding this library does not prove them, but for bounds of four kinds that this library has. For
lists: below the Johnson radius (`ld_list_johnson`, Cb/Ld/LdRelJohnson.lean). For agreement: the
weak count of `ld_mca_sets` (Cb/Ld/LdRelAny.lean); at one toy code (one symbol at two positions, 2 e
= d), a count of 1 (`LdBaseTest.rep2_mca`, Cb/Ld/LdBaseTest.lean); and the count of all field
elements, which holds of every code (`ldCode_mcaAtFull`, Cb/Gen/FullErrTow.lean).
If the radius e of a joint lies within a third of the distance d of its codes as they are read
(3 e < d), both are theorems, for every code read under a transformation that has its laws: lists
have at most one member (Cb/Ld/LdRelJohnson.lean: `ld_list_unique`; 2 e < d is enough); at most
e + 1 values are exceptional on a line (Cb/Ld/LdBaseCode.lean: `ld_mca_third`).
Interleavings, pairs and complexes keep laws and distance (Cb/Ld/LdRel.lean,
Cb/Obj/LdObjectToyKit.lean). So each block's own record of hypotheses is met from laws and distances
alone, beside what it asks on other matters.

Main names, each under the hypotheses of its statement; what stands behind "Left:" are further
premises of the statement:
  `Spec.ldThird_errOK`: the fold: `Y.ErrOK e` at lists 1 and agreement e + 1, e + 1, e + 1: lists at
    all k + 1 stages, agreement at the stages at which `ErrOK` asks it.
  `Spec.ldThird_fold`: so the fold's own hypotheses `Y.Hyp d e t` (Cb/Ld/LdTowerSumMain.lean). Left:
    challenges are distinct, degree at least 2, the packing's law and degrees, the fresh mask's
    encoding hides t long positions.
  `Spec.ldThird_switch`: the code switch: `D.Hyp e' 1 t'` (Cb/Ld/LdTower.lean), from laws and
    distance d' of the new code, 2 e' < d'. Left: the input code's laws (`D.Cin.Laws`), the new
    code's format, that is: its long symbol at x depends only on the native positions `src x`
    (`D.Cout.Reads`), the sample and the batching's evader (`D.Zo.OK`, `D.Zb.OK`), privacy of the
    first (`D.Zo.PrivateSim E`), the new encoding hides t' long positions (`D.Cout.Zk t'`).
  `Spec.ldThird_base`: the base case: `a.BaseHyp d (e + 1) 1`. Left: the transformation is
    transparent.
  `Spec.ldThird_bridge`: the bridge of a test on a group: the complex of the group has lists of at
    most 1, from the laws and distances of the members as they are read at the common long
    positions, 2 e < d.
  `Spec.ldThird_run`: so `D.OK` for a whole test on a group with D.L = 1
    (Cb/Ld/LdLinCloseRuns.lean). Left: the evader (`D.Z.OK`), "the joint radius implies each
    member's own" (`D.G.Fits`), the test on the complex is a tail (`D.T.OK D.t`).
The errors (counts of values of one verifier message), written out (`Spec.ldThird_err` for the first
three; by definition of the blocks' numbers):
  fold: 1; then in round i + 1: (e + 1) [+ 2 (e + 1) while the masks are halved] + n (n the degree);
  switch: 0 (no pair of list members: (1 choose 2) = 0);
    then (|P| - e - 1)^t · |seeds of the batching| + |P|^t · (the batching's number);
  base: (e + 1) + 1; then (|P| - e - 1)^t;
  bridge: 1 · (the evader's number) (`LdTl.cons`, Cb/Ld/LdLinCloseRuns.lean).

Limits: this file does not say that a protocol's radii lie within a third of its distances.
It says nothing beyond a third: there the bounds stay hypotheses; but on lists the file speaks up to
2 e < d: it is agreement that stops at a third.
It says nothing on zero knowledge of encodings, samples, evaders, packings: they are premises here,
each block's own other hypotheses.
No tower is assembled here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerSumMain
import Cb.Ld.LdBaseCode
import Cb.Ld.LdRelJohnsonProofs
import Cb.Obj.LdObjectToyKit
import Cb.Ld.LdLinCloseRuns

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

/-- The fold: lists and agreement at the stages of `ErrOK`. -/
def ldThird_errOK : Prop :=
  ∀ (P : Type) [Fintype P] (Y : SumPar E P) (d e : ℕ), Y.C.Laws → Y.Z.Laws → Y.Zw.Laws →
    Y.C.Dist d → Y.Z.Dist d → Y.Zw.Dist d → 3 * e < d →
    Y.ErrOK e (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1)

/-- The fold's own hypotheses. -/
def ldThird_fold : Prop :=
  ∀ (P : Type) [Fintype P] (Y : SumPar E P) (d e t : ℕ), Y.C.Laws → Y.Z.Laws → Y.Zw.Laws →
    Y.C.Dist d → Y.Z.Dist d → Y.Zw.Dist d → 3 * e < d → Function.Injective Y.val → 2 ≤ Y.n →
    Y.PackOK → Y.QwDeg → Y.Cw.Zk t →
    Y.Hyp d e t (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1)

/-- The code switch's own hypotheses. -/
def ldThird_switch : Prop :=
  ∀ (P P' St : Type) [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (D : LdSw E P P' St) (d' e' t' : ℕ),
    D.Cout.Laws → D.Cout.Dist d' → 2 * e' < d' → D.Cin.Laws → D.Cout.Reads → D.Zo.OK → D.Zb.OK →
    D.Zo.PrivateSim E → D.Cout.Zk t' → D.Hyp e' 1 t'

/-- The base case's own hypotheses. -/
def ldThird_base : Prop :=
  ∀ (a : LdJoint E) (d : ℕ),
    a.C.Laws → a.C.Dist d → 3 * a.e < d → a.C.Transparent → a.BaseHyp d (a.e + 1) 1

/-- Under the hypotheses below, the complex of a group has lists of at most one member. -/
def ldThird_bridge : Prop :=
  ∀ (S : Sig E) (G : Grp S) (d : ℕ), (∀ a : G.A, ((S.om a.1).C.atPos (G.pos a)).Laws) →
    (∀ a : G.A, ((S.om a.1).C.atPos (G.pos a)).Dist d) → 2 * G.e < d → G.C.ListAt G.e 1

/-- A whole test on a group. -/
def ldThird_run : Prop :=
  ∀ (S : Sig E) (D : LdRunD S) (d : ℕ), D.L = 1 →
    (∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Laws) →
    (∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Dist d) →
    2 * D.G.e < d → D.Z.OK → D.G.Fits → D.T.OK D.t → D.OK

/-- The errors, written out. -/
def ldThird_err : Prop :=
  (∀ (P : Type) [Fintype P] (Y : SumPar E P) (e : ℕ),
    Y.err (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1) =
      (1, sErr Y.n Y.k fun i =>
          (e + 1) + (if i + 1 ≤ Y.h then (e + 1) + (e + 1) else 0) + 1 * Y.n)) ∧
  (∀ (P P' St : Type) [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
        (D : LdSw E P P' St) (e : ℕ),
      D.W.err1 1 = 0 ∧
      D.W.err2 e 1 =
        (Fintype.card P - e - 1) ^ D.W.t * Fintype.card D.W.Zb.D +
          Fintype.card P ^ D.W.t * D.W.Zb.err) ∧
  (∀ (P : Type) [Fintype P] [Nonempty P] (C : LdCode E P) (t e : ℕ),
    ldBaseErr C t e (e + 1) 1 = ((e + 1) + 1, ((Fintype.card P - e - 1) ^ t, ())))

end
end Spec

section
variable (E : Type) [Field E] [Fintype E]

theorem ldThird_errOK : Spec.ldThird_errOK E := by
  intro P _ Y d e hC hZ hW dC dZ dW h3
  have h2 : 2 * e < d := by omega
  refine ⟨fun j _ => ?_, fun j _ _ => ?_, fun j _ _ => ?_, fun j _ _ => ?_⟩
  · exact ld_list_unique E P (Y.stage j) d e
      (ld_laws_pair E P _ _ (ld_laws_il E P Y.C _ hC)
        (ld_laws_pair E P _ _ (ld_laws_il E P Y.Z _ hZ) (ld_laws_il E P Y.Zw _ hW)))
      (ld_dist_pair E P _ _ d (ld_dist_il E P Y.C _ d dC)
        (ld_dist_pair E P _ _ d (ld_dist_il E P Y.Z _ d dZ) (ld_dist_il E P Y.Zw _ d dW))) h2
  · exact ld_mca_third E P _ d e (ld_laws_il E P Y.C _ hC) (ld_dist_il E P Y.C _ d dC) h3
  · exact ld_mca_third E P _ d e (ld_laws_il E P Y.Z _ hZ) (ld_dist_il E P Y.Z _ d dZ) h3
  · exact ld_mca_third E P _ d e (ld_laws_il E P Y.Zw _ hW) (ld_dist_il E P Y.Zw _ d dW) h3

theorem ldThird_fold : Spec.ldThird_fold E := fun P _ Y d e t hC hZ hW dC dZ dW h3 hi hn hp hq hz =>
  ⟨⟨⟨hC, hZ, hW⟩, ⟨dC, dZ, dW⟩, by omega⟩,
    ldThird_errOK E P Y d e hC hZ hW dC dZ dW h3, hi, hn, hp, hq, hz⟩

theorem ldThird_switch :
    Spec.ldThird_switch E := fun _ P' _ _ _ _ _ D d' e' _ hL hD h2 hI hR hO hB hP hZ =>
  ⟨hI, hR, ld_list_unique E P' D.Cout d' e' hL hD h2, hO, hB, hP, hZ⟩

theorem ldThird_base : Spec.ldThird_base E := fun a d hL hD h3 hT =>
  ⟨hL, hT, by omega,
    ld_mca_third E a.P a.C d a.e hL hD h3,
    ld_list_unique E a.P (a.C.il Bool) d a.e (ld_laws_il E a.P a.C Bool hL)
      (ld_dist_il E a.P a.C Bool d hD) (by omega)⟩

theorem ldThird_bridge : Spec.ldThird_bridge E := fun _ G d hL hD h2 =>
  ld_list_unique E G.P G.C d G.e (ld_laws_fam E G.P G.A _ hL) (ld_dist_fam _ d hD) h2

theorem ldThird_run : Spec.ldThird_run E := fun S D d h1 hL hD h2 hZ hF hT =>
  ⟨hZ, h1 ▸ ldThird_bridge E S D.G d hL hD h2, hF, hT⟩

theorem ldThird_err : Spec.ldThird_err E :=
  ⟨fun _ _ _ _ => rfl, fun P P' St _ _ _ _ D e => ⟨by
      show Nat.choose 1 2 * D.W.Zo.err = 0
      rw [Nat.choose_eq_zero_of_lt (by decide), Nat.zero_mul], by
      show _ + Fintype.card P ^ D.W.t * (1 * D.W.Zb.err) = _
      rw [Nat.one_mul]⟩, fun _ _ _ _ _ _ => rfl⟩

end
end Cb
