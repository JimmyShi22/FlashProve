-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerJohn.lean: below the Johnson radius: the blocks of a test on a group with no hypothesis
on lists, and agreement asked of the codes in the records only, "whatever the number of rows".

In standard terms: for codes that have their laws (`LdCode.Laws`, Cb/Ld/LdRel.lean) and radii below
the Johnson radius of the distance as the codes are read (`LdCode.Dist`), the bound on list size
that the steps of a proximity test (fold, code switch, base case, bridge) ask as a hypothesis is a
theorem; mutual correlated agreement stays a hypothesis, asked of the codes themselves.
The laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the encoder
`C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from native words
to long words, are linear over E; the encoder sends only the zero message with zero randomness to
zero; and, for every long position x, any two native words that agree at the native positions
`C.src x` have the same long symbol at x. In this file's statements the laws are premises.

Statements (each a `Prop` in `Cb.Spec`) and proofs (an assembly, but for `ldJohn_lt`: proved here,
and `ldJohn_err`: by definition of the blocks' numbers). Generic: any finite field, any codes read
under a transformation. No protocol, no code, no assumed theorem. For radii beyond a third of the
distance.

Why: the blocks of a proximity test (fold, code switch, base case; the bridge in front of a test on
a group) take bounds on lists and on mutual correlated agreement as hypotheses, of interleavings,
pairs and complexes of the codes that stand in their records.
  Lists are a theorem. If the radius e lies below the Johnson radius of the distance d as the codes
  are read (`InJohnson` |P| d e: |P| (|P| - d) < (|P| - e)^2), every code read under a
  transformation that has its laws and the distance d has lists of at most `listMax` |P| d e members
  (stated in Cb/Ld/LdRelJohnson.lean: `ld_list_johnson`). Interleavings, pairs and complexes keep
  laws and distance: so the bound does not grow with rows or members.
  Agreement is not. Beyond a third it does not follow from laws and distance, but for the weak count
  of `ld_mca_sets` (Cb/Ld/LdRelAny.lean) and the count of all field elements (`ldCode_mcaAtFull`,
  Cb/Gen/FullErrTow.lean). Agreement is asked here, for the fold, in one form, of the codes in the
  records themselves: `C.MCArows e b` (Cb/Ld/LdRelRows.lean), which is `(C.il R).MCAat e b`
  (Cb/Ld/LdRel.lean) for every finite set R of rows. Who has it is an instance's matter. For
  families of plain Reed-Solomon codes whose message and randomness fill the dimension, under the
  conditions of `IsGlJ` (over p = 2^64 - 2^32 + 1) and `InJohnson` |P| d e, it follows
  (Cb/Gl/GlLdJ.lean: `Spec.glJ_mca`) from one statement of the literature, taken as a hypothesis by
  name (`BCHKS46F`, Cb/Gen/CodeListRSF.lean), and from a lemma of this library's own, proved
  (`rows_cost_nothingF`, in the same file); and, under the further premise 2 e < d, also without
  that hypothesis (`Gl.agreeHalf`, Cb/Gl/GlAgreeHalf.lean). (The source of the statement on codes:
  the head of Cb/Gen/CodeListRS.lean.) That statement is for two words (a line; no rows). The lemma
  says that rows cost nothing: a table is one word over an extension field on the same points, and
  that statement's count does not depend on the field.
`listMax n d e` (Cb/Gen/JohnsonList.lean) is the Johnson bound on a list, in whole numbers:
n (d - e) / ((n - e)^2 - n (n - d)), rounded down. It has a meaning only under `InJohnson n d e`.

Main names, each under the hypotheses of its statement; what stands behind "Left:" are further
premises of the statement:
  `Spec.ldJohn_fold`: the fold's own hypotheses `Y.Hyp d e t` (Cb/Ld/LdTowerSumMain.lean) at lists
    `listMax` |P| d e and agreement bC, bZ, bW. Left: challenges are distinct, degree at least 2,
    the packing's law and degrees, the fresh mask's encoding hides t long positions.
  `Spec.ldJohn_switch`: the code switch: `D.Hyp` e' (`listMax` |P'| d' e') t' (Cb/Ld/LdTower.lean):
    it asks a list only. Left: as in Cb/Ld/LdTowerThird.lean (`Spec.ldThird_switch`).
  `Spec.ldJohn_base`: the base case: `a.BaseHyp` d b (`listMax` |P| d e), from `a.C.MCAat` e b.
    Left: the transformation is transparent.
  `Spec.ldJohn_run`: `D.OK` (Cb/Ld/LdLinCloseRuns.lean) for a whole test on a group with
    D.L = `listMax` |P| d e. Left: the evader, `Fits`, the test on the complex is a tail.
The errors (counts of values of one verifier message), written out (`Spec.ldJohn_err` for the first
three; by definition of the blocks' numbers), L := the list bound of the joint:
  fold: L; then in round i + 1: bC [+ bZ + bW while the masks are halved] + L · n (n the degree);
  switch: (L' choose 2) · (the sample's number);
    then (|P| - e - 1)^t · |seeds of the batching| + |P|^t · (L' · the batching's number);
  base: b + L2; then (|P| - e - 1)^t;
  bridge: L · (the evader's number) (`LdTl.cons`, Cb/Ld/LdLinCloseRuns.lean).

Limits: this file does not say that any code has `MCArows` beyond a third, or that these errors are
small.
It says nothing between the Johnson radius and capacity.
It says nothing on zero knowledge of encodings, samples, evaders, packings: they are premises here,
each block's own other hypotheses.
No tower is assembled here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerThird
import Cb.Ld.LdRelRows

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

namespace Spec

def ldJohn_lt : Prop := ∀ n d e : ℕ, InJohnson n d e → e < d

section
variable (E : Type) [Field E] [Fintype E]

/-- The fold: lists and agreement at the stages of `ErrOK`. -/
def ldJohn_errOK : Prop :=
  ∀ (P : Type) [Fintype P] (Y : SumPar E P) (d e bC bZ bW : ℕ), Y.C.Laws → Y.Z.Laws → Y.Zw.Laws →
    Y.C.Dist d → Y.Z.Dist d → Y.Zw.Dist d → InJohnson (Fintype.card P) d e → Y.C.MCArows e bC →
    Y.Z.MCArows e bZ → Y.Zw.MCArows e bW →
    Y.ErrOK e (fun _ => listMax (Fintype.card P) d e) (fun _ => bC) (fun _ => bZ) (fun _ => bW)

/-- The fold's own hypotheses. -/
def ldJohn_fold : Prop :=
  ∀ (P : Type) [Fintype P] (Y : SumPar E P) (d e t bC bZ bW : ℕ), Y.C.Laws → Y.Z.Laws → Y.Zw.Laws →
    Y.C.Dist d → Y.Z.Dist d → Y.Zw.Dist d → InJohnson (Fintype.card P) d e → Y.C.MCArows e bC →
    Y.Z.MCArows e bZ → Y.Zw.MCArows e bW → Function.Injective Y.val → 2 ≤ Y.n → Y.PackOK → Y.QwDeg →
    Y.Cw.Zk t →
    Y.Hyp d e t (fun _ => listMax (Fintype.card P) d e) (fun _ => bC) (fun _ => bZ) (fun _ => bW)

/-- The code switch's own hypotheses: a list only. -/
def ldJohn_switch : Prop :=
  ∀ (P P' St : Type) [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (D : LdSw E P P' St) (d' e' t' : ℕ),
    D.Cout.Laws → D.Cout.Dist d' → InJohnson (Fintype.card P') d' e' → D.Cin.Laws → D.Cout.Reads →
    D.Zo.OK → D.Zb.OK → D.Zo.PrivateSim E → D.Cout.Zk t' →
    D.Hyp e' (listMax (Fintype.card P') d' e') t'

/-- The base case's own hypotheses. -/
def ldJohn_base : Prop :=
  ∀ (a : LdJoint E) (d b : ℕ), a.C.Laws → a.C.Dist d → InJohnson (Fintype.card a.P) d a.e →
    a.C.MCAat a.e b → a.C.Transparent → a.BaseHyp d b (listMax (Fintype.card a.P) d a.e)

/-- Under the hypotheses below, the complex of a group has lists of at most `listMax` |G.P| d G.e.
-/
def ldJohn_bridge : Prop :=
  ∀ (S : Sig E) (G : Grp S) (d : ℕ), (∀ a : G.A, ((S.om a.1).C.atPos (G.pos a)).Laws) →
    (∀ a : G.A, ((S.om a.1).C.atPos (G.pos a)).Dist d) →
    InJohnson (Fintype.card G.P) d G.e → G.C.ListAt G.e (listMax (Fintype.card G.P) d G.e)

/-- A whole test on a group. -/
def ldJohn_run : Prop :=
  ∀ (S : Sig E) (D : LdRunD S) (d : ℕ), D.L = listMax (Fintype.card D.G.P) d D.G.e →
    (∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Laws) →
    (∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Dist d) →
    InJohnson (Fintype.card D.G.P) d D.G.e → D.Z.OK → D.G.Fits → D.T.OK D.t → D.OK

/-- The errors, written out. -/
def ldJohn_err : Prop :=
  (∀ (P : Type) [Fintype P] (Y : SumPar E P) (L bC bZ bW : ℕ),
    Y.err (fun _ => L) (fun _ => bC) (fun _ => bZ) (fun _ => bW) =
      (L, sErr Y.n Y.k fun i => bC + (if i + 1 ≤ Y.h then bZ + bW else 0) + L * Y.n)) ∧
  (∀ (P P' St : Type) [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
        (D : LdSw E P P' St) (e L : ℕ),
      D.W.err1 L = L.choose 2 * D.W.Zo.err ∧
      D.W.err2 e L =
        (Fintype.card P - e - 1) ^ D.W.t * Fintype.card D.W.Zb.D +
          Fintype.card P ^ D.W.t * (L * D.W.Zb.err)) ∧
  (∀ (P : Type) [Fintype P] [Nonempty P] (C : LdCode E P) (t e b L2 : ℕ),
    ldBaseErr C t e b L2 = (b + L2, ((Fintype.card P - e - 1) ^ t, ())))

end
end Spec

theorem ldJohn_lt : Spec.ldJohn_lt := by
  intro n d e h
  by_contra hn
  have hde : d ≤ e := Nat.le_of_not_lt hn
  have h1 : n - e ≤ n - d := Nat.sub_le_sub_left hde n
  have h2 : (n - e) ^ 2 ≤ n * (n - d) := by
    calc (n - e) ^ 2 = (n - e) * (n - e) := by ring
      _ ≤ n * (n - d) := Nat.mul_le_mul (Nat.sub_le n e) h1
  exact absurd h (Nat.not_lt.2 h2)

section
variable (E : Type) [Field E] [Fintype E]

theorem ldJohn_errOK : Spec.ldJohn_errOK E := by
  intro P _ Y d e bC bZ bW hC hZ hW dC dZ dW hJ mC mZ mW
  refine ⟨fun j _ => ?_, fun j _ _ => mC _, fun j _ _ => mZ _, fun j _ _ => mW _⟩
  exact ld_list_johnson E P (Y.stage j) d e
    (ld_laws_pair E P _ _ (ld_laws_il E P Y.C _ hC)
      (ld_laws_pair E P _ _ (ld_laws_il E P Y.Z _ hZ) (ld_laws_il E P Y.Zw _ hW)))
    (ld_dist_pair E P _ _ d (ld_dist_il E P Y.C _ d dC)
      (ld_dist_pair E P _ _ d (ld_dist_il E P Y.Z _ d dZ) (ld_dist_il E P Y.Zw _ d dW))) hJ

theorem ldJohn_fold :
    Spec.ldJohn_fold E := fun P _ Y d e _ bC bZ bW hC hZ hW dC dZ dW hJ mC mZ mW hi hn hp hq hz =>
  ⟨⟨⟨hC, hZ, hW⟩, ⟨dC, dZ, dW⟩, ldJohn_lt _ d e hJ⟩,
    ldJohn_errOK E P Y d e bC bZ bW hC hZ hW dC dZ dW hJ mC mZ mW, hi, hn, hp, hq, hz⟩

theorem ldJohn_switch :
    Spec.ldJohn_switch E := fun _ P' _ _ _ _ _ D d' e' _ hL hD hJ hI hR hO hB hP hZ =>
  ⟨hI, hR, ld_list_johnson E P' D.Cout d' e' hL hD hJ, hO, hB, hP, hZ⟩

theorem ldJohn_base : Spec.ldJohn_base E := fun a d _ hL hD hJ hM hT =>
  ⟨hL, hT, ldJohn_lt _ d a.e hJ, hM,
    ld_list_johnson E a.P (a.C.il Bool) d a.e (ld_laws_il E a.P a.C Bool hL)
      (ld_dist_il E a.P a.C Bool d hD) hJ⟩

theorem ldJohn_bridge : Spec.ldJohn_bridge E := fun _ G d hL hD hJ =>
  ld_list_johnson E G.P G.C d G.e (ld_laws_fam E G.P G.A _ hL) (ld_dist_fam _ d hD) hJ

theorem ldJohn_run : Spec.ldJohn_run E := fun S D d h1 hL hD hJ hZ hF hT =>
  ⟨hZ, h1 ▸ ldJohn_bridge E S D.G d hL hD hJ, hF, hT⟩

theorem ldJohn_err : Spec.ldJohn_err E :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ _ _ _ _ => rfl⟩

end
end Cb
