-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupFold.lean: this file says how several oracle messages are arranged for a sumcheck that
folds them, and gives batching round, arrangement and fold as one reduction.

In standard terms: the fold is a sumcheck over the cube of k variables; it replaces 2^k interleaved
rows by their combination with the multilinear equality weights at a point γ that the verifier's
challenges fix (`foldV`, Cb/Ld/LdRel.lean). A shape (`GShape`) says how the members' rows, as they
were sent, are placed on that cube. A kept row is repeated at every corner of the cube, so that this
combination returns it unchanged. "Row" has two senses here: a row of an interleaved code, as above,
and a linear claim on messages (`Slf.Holds`, Cb/Ld/LdRel.lean).

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdGroupFoldProofs.lean.
It builds on Cb/Ld/LdGroup.lean (a run on a group), Cb/Ld/LdBatShape.lean (a code in another shape;
rows that are not sent), Cb/Ld/LdSum.lean (the zero-knowledge sumcheck that folds) and
Cb/Ld/LdTowerSum.lean (the fold as a block).
In `Spec.ldGroup_block` and `Spec.ldGroup_fold` the group's set of common long positions, `G.P`, is
nonempty.

A group of Cb/Ld/LdBatSig.lean is any family of whole oracle messages read at common long positions
with one joint radius. `GShape G` says what more is asked of a group here. Data:
  `Cb`, `Zb`: the base code and the mask code.
  `Rm a`, `Rz a`: the main rows and the mask rows of the member a, as they were sent. Either may be
    empty: a member without main rows is mask-only; a kept message has no mask rows (not asked by
    name: the limits of Cb/Ld/LdGroupSeg.lean).
  `view`: a `Reshape` of Cb/Ld/LdBatShape.lean; the identity for messages that are declared as main
    rows under Cb beside mask rows under Zb.
  `h`, `g`: the mask rows are on the cube of the first h variables, the main rows on the cube of all
    k = h + g variables.
  `Kp`: the kept slots. The group is read in 2^k super-rows, each of 1 + |Kp| base rows: slot "none"
    holds an ordinary row, slot "some j" a kept row.
  `dst`, `ord`, `kept`, `dstZ`, `ordZ`: where the rows go: see their doc comments.
  `n`, `Ch`, `val`, `AaW`, `TW`, `srcW`, `pk`, `Qw`: what the fold needs beside codes and forms
    (Cb/Ld/LdSum.lean): degree, challenges, the reading of the fresh mask, the packing of the hiding
    coefficients.
Rows that are not sent are virtual: the slot none of a super-row that holds nothing is zero; the
slot some j of every super-row is a copy of the kept row j; a form's coefficients on a kept row are
on the copy in the super-row 0 .. 0, zeros on the other copies.
  `Sh.block`: the block of a proximity test: arrangement (no round), the batched form cut in two (no
    round), the fold (k + 1 rounds).

Main names:
  `Spec.ldGroup_block`: `Sh.OK` and the fold's own hypotheses (`SumPar.Hyp` of
    Cb/Ld/LdTowerSumMain.lean) → the block is a piece: one long position of the complex for each
    long position of the folded words.
  `Spec.ldGroup_fold`: the first half of a closing. Under `Sh.OK`, `Sh.par.Hyp d G.e t Lst mC mS mW`
    and the hypotheses of `Spec.ldGroup_run` (Cb/Ld/LdGroup.lean) other than that on the block:
    bridge, arrangement, fold, beside the carried part, is a piece of a chain
      from `S.over` (rows (linear claims) on G, beside A₀ of the kept messages), relaxed by decoding
        with a sample, on collision-free statements that also meet the base joint's own condition
        (`on` of `Sig.over`, Cb/Ld/LdSig.lean),
      to (`Sh.Cf`, the three folded forms, the same joint radius), relaxed existentially, beside
        `(S.sub kp).over A₀`, relaxed by decoding with a sample.
    k + 2 rounds. Errors in a row: L · (the evader's number); the list of the complex with the fresh
    mask; then for j = 1 .. k the fold's.
  `Spec.ldGroup_list`: if `Sh.OK`, a bound on the list of the full interleaving (`Sh.Cin`: virtual
    rows counted) at a radius is a bound on the list of the complex as it was sent (`G.C`), which is
    what the bridge asks.
  `Spec.ldGroup_fold_kept`: the fold returns the kept rows: for every point γ, the slot some j of
    the folded main word is the kept row j as it was sent, symbol by symbol; and the same for
    message and randomness of an arranged witness (`Sh.rho.up w`; an honest one is of this kind). No
    scalar, no condition on γ: the weights of the corners of a cube sum to 1.
  `Spec.ldGroup_fold_kept_near`: if `Sh.OK`, the same for every (message, randomness) whose encoding
    is within e of an arranged word, if e is below the distances of Cb and Zb (and view is a
    bijection there): such a pair is arranged. What comes after the fold (the locations) needs the
    two together: a relaxed witness of the fold's input need not be honest.

`PieceTr`, a piece of a chain, asks of a reduction between two joints the bundle `IOR.GoodT` and
three further clauses, `noHid`, `noTie` and `bears`, which Cb/Ld/LdTowerKit.lean states (`bears`
through `IOR.Bears`, Ior/Bears.lean); `IOR.Piece` (Ior/Tail.lean) asks the same over `IOR.Good`.
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Limits:
This file says nothing on the second half of a closing (the new oracle messages, their samples, the
locations): bridge, arrangement and fold are the first part of what a write-up of ours
(lean/CREDITS.md) calls a run, whose two ends are both relaxed by decoding. The fresh mask goes out
in the fold's first message;
sending it earlier is another lemma. This file does not say that the carried predicates read the
same kept cells before and after a closing: that is the locations' matter
(`Spec.ldGroup_place_cells`, Cb/Ld/LdGroupPlace.lean; `Spec.ldSeg_kept`, Cb/Req1/LdSeg.lean);
`Spec.ldGroup_fold_kept` is what it rests on. No bound on a list or on agreement: such bounds are
hypotheses (`G.C.ListAt G.e L`, `Sh.par.Hyp ..`); `Spec.ldGroup_list` carries one over.

Declared differences to the write-up. (a) Numbers of rows and
message lengths need not be powers of two but for the cubes; 1 + |Kp| is any number. (b) "The mask
code's length divides the base code's" and "its rate is at most .." are not said: Cb and Zb are any
two codes read at common long positions (a repetition is one way: `LdCode.rep`).
(a') Any main row of any member may stand in a kept slot; in the write-up the kept rows are
the rows of kept messages (oracle messages of their own, without mask rows): wider here; the block
of the locations will ask for whole messages (`GHeld`, Cb/Ld/LdGroupSeg.lean).
(c) The size condition on the mask's message is the packing's (Cb/Ld/LdSumPack.lean: an injection of
its columns). (d) Rows over the small field and rows over E side by side: the format of an oracle
message (Cb/Ld/LdSig.lean) says what may be sent; the codes here are over E. (e) One mask code for a
class of groups: a matter of which Zb the groups of a protocol name.
Fold and main relation follow the paper that this protocol builds on, and the notion of a group goes
back to advice; for the super-rows with copies the file follows this protocol's technical report
(lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdGroup
import Cb.Ld.LdBatShapeBlock
import Cb.Ld.LdTowerSumMain
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

/-- The shape of a group: the data. -/
structure GShape {E : Type} [Field E] {S : Sig E} (G : Grp S) where
  /-- the base code and the mask code, read at the group's long positions -/
  Cb : LdCode E G.P
  Zb : LdCode E G.P
  /-- the kept slots -/
  Kp : Type
  [finKp : Fintype Kp]
  [decKp : DecidableEq Kp]
  /-- mask rows on the cube of h variables, main rows on the cube of h + g -/
  h : ℕ
  g : ℕ
  /-- the rows of a member, as sent -/
  Rm : G.A → Type
  [finRm : ∀ a, Fintype (Rm a)]
  [decRm : ∀ a, DecidableEq (Rm a)]
  Rz : G.A → Type
  [finRz : ∀ a, Fintype (Rz a)]
  [decRz : ∀ a, DecidableEq (Rz a)]
  /-- the members' codes are main rows under Cb beside mask rows under Zb -/
  view : Reshape G.C (LdCode.fam fun a => (Cb.il (Rm a)).pair (Zb.il (Rz a)))
  /-- where a main row goes; what is in the slot none of a super-row; which row is kept in a slot -/
  dst : (Σ a, Rm a) → (Fin (h + g) → Bool) ⊕ Kp
  ord : (Fin (h + g) → Bool) → Option (Σ a, Rm a)
  kept : Kp → Σ a, Rm a
  /-- the same for mask rows -/
  dstZ : (Σ a, Rz a) → Fin h → Bool
  ordZ : (Fin h → Bool) → Option (Σ a, Rz a)
  /-- what the fold needs beside codes and forms -/
  n : ℕ
  Ch : Type
  [finCh : Fintype Ch]
  [neCh : Nonempty Ch]
  val : Ch → E
  AaW : Type
  TW : Zb.Word → G.P → AaW → E
  srcW : G.P → Finset Zb.NP
  pk : (HIdx (sVars E n (h + g)) → E) → (Fin h → Bool) × Zb.J → E
  Qw : Slf E (Fin (h + g) → E) Zb.J

attribute [instance] GShape.finKp GShape.decKp GShape.finRm GShape.decRm GShape.finRz GShape.decRz
  GShape.finCh GShape.neCh

namespace GShape
variable {E : Type} [Field E] {S : Sig E} {G : Grp S} (Sh : GShape G)

/-- The arrangement of the main rows: the slot none of a super-row holds what ord says; the slot
some j of every super-row is a copy of the kept row j; coefficients on a kept row are on the copy in
the super-row 0 .. 0. -/
def am : Arr (Σ a, Sh.Rm a) ((Fin (Sh.h + Sh.g) → Bool) × Option Sh.Kp) where
  src := fun n => match n.2 with
    | none => Sh.ord n.1
    | some j => some (Sh.kept j)
  rep := fun r => match Sh.dst r with
    | .inl b => (b, none)
    | .inr j => (fun _ => false, some j)

/-- the arrangement of the mask rows -/
def az : Arr (Σ a, Sh.Rz a) (Fin Sh.h → Bool) := ⟨Sh.ordZ, Sh.dstZ⟩

/-- a super-row: 1 + |Kp| base rows -/
abbrev Cs : LdCode E G.P := Sh.Cb.il (Option Sh.Kp)

/-- The fold's input code. -/
abbrev Cin : LdCode E G.P := (Sh.Cs.il (Fin (Sh.h + Sh.g) → Bool)).pair (Sh.Zb.il (Fin Sh.h → Bool))

/-- all rows as sent: main rows under Cb beside mask rows under Zb -/
abbrev Cflat : LdCode E G.P := (Sh.Cb.il (Σ a, Sh.Rm a)).pair (Sh.Zb.il (Σ a, Sh.Rz a))

/-- view, then gather -/
def flat : Reshape G.C Sh.Cflat := (Reshape.gather Sh.Rm Sh.Rz Sh.Cb Sh.Zb).comp Sh.view

/-- From the group's complex to the fold's input code: view, gather, arrange main rows and mask
rows, re-bracket the super-rows. -/
def rho : Reshape G.C Sh.Cin :=
  ((Reshape.curry Sh.Cb (Fin (Sh.h + Sh.g) → Bool) (Option Sh.Kp)).pairL
      (Sh.Zb.il (Fin Sh.h → Bool))).comp
    ((((Sh.az.reshape Sh.Zb).pairR (Sh.Cb.il ((Fin (Sh.h + Sh.g) → Bool) × Option Sh.Kp))).comp
      ((Sh.am.reshape Sh.Cb).pairL (Sh.Zb.il (Σ a, Sh.Rz a)))).comp Sh.flat)

/-- The fold's parameters; the forms are put in by `SumPar.reform`. -/
def par : SumPar E G.P where
  h := Sh.h
  g := Sh.g
  n := Sh.n
  Ch := Sh.Ch
  val := Sh.val
  C := Sh.Cs
  Z := Sh.Zb
  AaW := Sh.AaW
  TW := Sh.TW
  srcW := Sh.srcW
  St := Unit
  StS := Unit
  sl := fun _ _ => 0
  slS := fun _ _ => 0
  pk := Sh.pk
  Qw := Sh.Qw

/-- The folded complex: a super-row; the carried mask; the fresh mask. -/
abbrev Cf : LdCode E G.P := Sh.par.Cout

/-- The laws of a shape. -/
structure OK : Prop where
  view : Sh.view.Laws
  base : Sh.Cb.Laws
  mask : Sh.Zb.Laws
  /-- every main row is where dst says -/
  main : ∀ r, match Sh.dst r with
    | .inl b => Sh.ord b = some r
    | .inr j => Sh.kept j = r
  /-- every mask row is where dstZ says -/
  rowsZ : ∀ r, Sh.ordZ (Sh.dstZ r) = some r
  /-- at least one variable -/
  one : 1 ≤ Sh.h + Sh.g

end GShape

section
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))

/-- the batched form, carried to the fold's input code -/
abbrev GShape.form : Slf E ((∀ ν, G.RowSt Sb ν) × Z.D) Sh.Cin.J :=
  Sh.rho.sl (Slf.bat Z.ze (G.rows sl))

/-- the fold with the two parts of that form as its forms -/
abbrev GShape.fold : SumPar E G.P := Sh.par.reform (Sh.form Sb sl Z)

/-- The block: arrangement, cut, fold. d: the threshold of the fold's corrector of erasures; t: the
long positions that the fresh mask's encoding hides (t : ℕ; `Y.Cw.Zk t` is the field zk of
`SumPar.Hyp`, Cb/Ld/LdTowerSumMain.lean, a premise of `Spec.ldGroup_block` and
`Spec.ldGroup_fold`); Lst, mC, mS, mW: the numbers in the fold's errors. -/
def GShape.block (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) :
    LdBlock (G.joint Sb sl Z) ((Sh.fold Sb sl Z).jOut G.e) :=
  (ldShapeBlock Sh.rho (Slf.bat Z.ze (G.rows sl)) G.e).seq
    (ldSumAfter Sh.par G.e t Lst mC mS mW (Sh.form Sb sl Z) ((Sh.fold Sb sl Z).ext d))

end

namespace Spec

/-- States: if `Sh.OK`, the arrangement has the laws; below the distances of Cb and Zb a codeword
close to an arranged word is arranged, if that holds of view (`Sh.view.Fix e`). -/
def ldGroup_shape_laws : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (G : Grp S) (Sh : GShape G), Sh.OK →
    Sh.rho.Laws ∧
    ∀ d dz e : ℕ, Sh.Cb.Dist d → e < d → Sh.Zb.Dist dz → e < dz → Sh.view.Fix e → Sh.rho.Fix e

/-- States: if `Sh.OK`, the list of the full interleaving bounds the list of the complex as sent. -/
def ldGroup_list : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (G : Grp S) (Sh : GShape G) (e L : ℕ),
    Sh.OK → Sh.Cin.ListAt e L → G.C.ListAt e L

/-- States: for `G.P` nonempty, if `Sh.OK` and `Sh.par.Hyp d G.e t Lst mC mS mW`, the block is a
piece, of h + g + 1 rounds. -/
def ldGroup_block : Prop :=
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
      (d t : ℕ) (Lst mC mS mW : ℕ → ℕ),
    Sh.OK → Sh.par.Hyp d G.e t Lst mC mS mW →
    (Sh.block Sb sl Z d t Lst mC mS mW).OK t t ∧
    (Sh.block Sb sl Z d t Lst mC mS mW).R.shape.length = Sh.h + Sh.g + 1

open Classical in
/-- The first half of a closing: bridge, arrangement, fold, beside the carried part. -/
def ldGroup_fold : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (L : ℕ) (E₀ : ExtSpec)
      (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o) (dw : S.Wit × Wp)
      (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) (qi : Finset (E₀.prod S.ext).Pos → Prop)
      (qF : Finset (LdCarE kp E₀).Pos → Prop),
    Sh.OK → Sh.par.Hyp d G.e t Lst mC mS mW → Z.OK → G.C.ListAt G.e L → G.Fits →
    (∀ U, besideQ ((G.joint Sb sl Z).atMost t) qF U → qi (U.biUnion (ldBrG G kp E₀).src)) →
    PieceTr (ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW))
      (ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW))
      (S.over
        (claimRels (fun x m => Slf.All sl x (G.msg m)) (onMsgRels (S.res (T := OMsg.Msg) kp) A₀)))
      (IOR.Rels.beside (Sh.Cf.rels (Sh.fold Sb sl Z).slOut G.e fun _ => ()) ((S.sub kp).over A₀))
      (ldRunGX G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW) hc dw)
      (ldRunGN G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW) Kc (L * Z.err)) qi
      (besideQ (((Sh.fold Sb sl Z).jOut G.e).atMost t) qF) ∧
    (ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).shape.length = Sh.h + Sh.g + 2

/-- The fold returns the kept rows: words, messages, randomness. -/
def ldGroup_fold_kept : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (G : Grp S) (Sh : GShape G)
      (γ : Fin (Sh.h + Sh.g) → E) (j : Sh.Kp),
    (∀ (f : G.C.Word) (p : Sh.Cb.NP) (s : Sh.Cb.NS p),
      SumPar.foldW Sh.Cs γ (LdCode.fstW (Sh.rho.wd f)) p (some j, s) =
        LdCode.fstW (C₁ := Sh.Cb.il (Σ a, Sh.Rm a)) (C₂ := Sh.Zb.il (Σ a, Sh.Rz a))
          (Sh.flat.wd f) p (Sh.kept j, s)) ∧
    (∀ (w : (G.C.J → E) × (G.C.Q → E)) (c : Sh.Cb.J),
      foldV γ (fun a => (Sh.rho.up w).1 (.inl a)) (some j, c) =
        (Sh.flat.up w).1 (.inl (Sh.kept j, c))) ∧
    (∀ (w : (G.C.J → E) × (G.C.Q → E)) (c : Sh.Cb.Q),
      foldV γ (fun a => (Sh.rho.up w).2 (.inl a)) (some j, c) =
        (Sh.flat.up w).2 (.inl (Sh.kept j, c)))

/-- The same for every pair close to an arranged word, below the distances.
(not all hypotheses are named here: see the statement below) -/
def ldGroup_fold_kept_near : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (G : Grp S) (Sh : GShape G) (d dz e : ℕ), Sh.OK →
    Sh.Cb.Dist d → e < d → Sh.Zb.Dist dz → e < dz → Sh.view.Fix e →
    ∀ (f : G.C.Word) (w' : (Sh.Cin.J → E) × (Sh.Cin.Q → E)),
      Sh.Cin.Near e (Sh.rho.wd f) (Sh.Cin.enc w'.1 w'.2) →
      ∀ (γ : Fin (Sh.h + Sh.g) → E) (j : Sh.Kp),
        (∀ c : Sh.Cb.J, foldV γ (fun a => w'.1 (.inl a)) (some j, c) =
          (Sh.flat.up (Sh.rho.dn w')).1 (.inl (Sh.kept j, c))) ∧
        (∀ c : Sh.Cb.Q, foldV γ (fun a => w'.2 (.inl a)) (some j, c) =
          (Sh.flat.up (Sh.rho.dn w')).2 (.inl (Sh.kept j, c)))

end Spec
end Cb
