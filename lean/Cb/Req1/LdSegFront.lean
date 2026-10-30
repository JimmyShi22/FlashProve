-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFront.lean: the front of a segment's body: the lookup; then zerocheck and sumchecks,
again for each map that is never sent; as one list of moves.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegFrontProofs.lean.

Why: Cb/Req1/LdSegRef.lean builds the reference segment from its parts; its largest parameter is
"front" (`LdBodyD.front`, Cb/Req1/LdSegRefBody.lean), any list of moves that ends at "packing, and
claims on the virtual cells". Here the front is a term over blocks, of any length, so that the
composition typechecks from the segment's entry to that stage, and its hypotheses are reduced to the
blocks' own and to conditions "the claims that one block leaves are the claims that the next one
takes". All blocks of the front speak of the same objects: the oracle messages S that are open at
the segment's entry (nothing is sent), further oracles E₀, a further witness Wp: so, at any S, for
the blocks `frIn`, `frPsc` below; of the frame's blocks the type asks only that each begins and ends
at a stage over S, E₀, Wp (`LdFrontD.blk`), and the entry stage a is any stage (`LdFrontD.a`). A
block reduces some claims; the others wait: each block is stated "beside any joint that rides
along", and the waiting claims are in that joint.

1. The frame (`LdFrontD`; its fields: see the record): n blocks, each any list of moves, with a step
   without rounds after it; "pre", any list of moves from the entry stage a to the first block's
   stage (the shift, a step, the lookup, a step: Cb/Req1/LdSegRefLkpPre.lean); a last step.
   `F.prog` = pre ; block 0 ; step 0 ; .. ; block (n - 1) ; step (n - 1) ; last step.
2. The blocks of the table, as lists of moves.
   `frIn Z ..`: claims on values into one sum claim, then the sumcheck: two moves. Z (`PscIn`,
     Cb/Ld/LdZero.lean): the claims, the evader that joins them (one verifier message), the sumcheck
     that follows. The zerocheck on a cube and the line step are cases.
   `frPsc T ..`: the sumcheck alone, from its true sum claim: one move. "Again for each map that is
     never sent": the step before it writes a claim on a value of such a map as a sum claim; no
     verifier message lies between two sumchecks.
   msg: how the entries are read off the messages: any function: virtual cells are entries in this
     sense.
   `frFact T .. Rd`: the fact that the sumcheck needs for its item "masked messages": its own masks,
     read among the entries Rd. A fact is a `MaskFact` (Cb/Req1/LdSegFresh.lean). A `MaskFact W` is
     a reading `kc` of witnesses of type W into a type `Kc`, a finite, non-empty type `Mk`, and a
     map `put : Mk → Kc → Kc`.

Main names:
  `Spec.ldSegFront_hyp`: `F.prog.Hyp` from `F.OK`: `F.pre.Hyp`; `(F.blk i).Hyp`; for each step four
    clauses at the base joints (forwards on exact relations; conditions; cores; backwards on relaxed
    relations).
  `Spec.ldSegFront_kinds`: the kinds of pre and of the blocks, and steps: if a predicate k on kinds
    holds of "step", of all moves of pre and of all moves of each block, it holds of all moves of
    the front.
  `Spec.ldSegFront_nums`: rounds of both kinds (`nAll`, `nVer`) and the two numbers (`pBad`,
    `pHid`): pre's, and the sum over the blocks.
  `Spec.ldSegFront_zk`: `F.prog.Zk base` from `F.pre.Zk base` and: each block has its Zk at the
    facts that are fresh where it begins. The steps ask nothing, beside their hypotheses.
  `Spec.ldSegFront_in_hyp`, `Spec.ldSegFront_psc_hyp`: the two blocks' hypotheses from: `Link`,
    `Back`, the evader's law (these three for `frIn` alone); `VarsOK`, `DegX`, `DegY`, `ValInj` of
    the sumcheck.
  `Spec.ldSegFront_in_zk`, `Spec.ldSegFront_psc_zk`: (for the first, under `Z.Link`, `Z.Back`,
    `Z.ev.OK`) their Zk from: the sumcheck's link is a masked block with the letters `frMask ..`,
    and its fact is fresh where the block begins. The draw asks nothing, beside its hypotheses, and
    does not look.
  `Spec.ldSegFront_in_nums`, `Spec.ldSegFront_psc_nums`: the number of rounds `nAll` of
    `frIn ..` is 1 + (`Z.T.fmt.length` + 3), of `frPsc ..` it is `T.fmt.length` + 3; their kinds:
    "sub"; nothing is withheld, in this sense: `pBad` = 0 and `pHid` = 0 of both. What pBad and pHid
    bound: `GoodB`, Ior/Masked.lean; `Nums`, Ior/Chain.lean.

Limits: this file does not say which claims a model's segment has, or that the four clauses hold for
them: the model's side. It does not say that the facts stay fresh from block to block (rules:
Cb/Req1/LdSegCarry.lean; `mvA_carry`, Cb/Req1/LdSegRefPsc.lean). The degrees of the summands stay
hypotheses.
The order of the blocks restates a table of a segment in a write-up of ours that is not in this
repository in our own words (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefPsc
import Cb.Req1.LdSegRefKit
import Cb.Req1.LdSegClose
import Cb.Ld.LdPscGood
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR
open scoped ENNReal

/-! ## 1. The frame -/

/-- The front: the data. -/
structure LdFrontD (E Kc : Type) [Field E] [Fintype E] : Type 1 where
  S   : Sig E
  E₀  : ExtSpec
  Wp  : Type
  /-- the blocks -/
  n   : ℕ
  Xs  : ℕ → Type
  Xt  : ℕ → Type
  As  : ∀ i, Rels Kc (Xs i) E₀ (S.Msg × Wp)
  At  : ∀ i, Rels Kc (Xt i) E₀ (S.Msg × Wp)
  blk : ∀ i, LdProg (⟨S, Xs i, E₀, Wp, As i⟩ : LdStage E Kc) ⟨S, Xt i, E₀, Wp, At i⟩
  /-- the steps after them: maps of the explicit part -/
  g   : ∀ i, Xt i → Xs (i + 1)
  /-- the entry stage, and what comes before the first block -/
  a   : LdStage E Kc
  pre : LdProg a ⟨S, Xs 0, E₀, Wp, As 0⟩
  /-- where the front ends, and the last step -/
  Stz : Type
  Az  : Rels Kc Stz E₀ (S.Msg × Wp)
  gz  : Xs n → Stz

namespace LdFrontD
variable {E Kc : Type} [Field E] [Fintype E] (F : LdFrontD E Kc)

/-- the two stages of the block i -/
@[reducible] def s (i : ℕ) : LdStage E Kc := ⟨F.S, F.Xs i, F.E₀, F.Wp, F.As i⟩
@[reducible] def t (i : ℕ) : LdStage E Kc := ⟨F.S, F.Xt i, F.E₀, F.Wp, F.At i⟩

/-- the step after the block i; the last step -/
def step (i : ℕ) : LdMv (F.t i) (F.s (i + 1)) :=
  ldStepF F.S (F.At i) (F.As (i + 1)) (F.g i)
@[reducible] def z : LdStage E Kc := ⟨F.S, F.Stz, F.E₀, F.Wp, F.Az⟩
def post : LdMv (F.s F.n) F.z := ldStepF F.S (F.As F.n) F.Az F.gz

/-- the first k blocks, each with the step after it -/
def mid : (k : ℕ) → LdProg (F.s 0) (F.s k)
  | 0 => .nil _
  | k + 1 => ((mid k).app (F.blk k)).snoc (F.step k)

/-- The front. -/
def prog : LdProg F.a F.z := (F.pre.app (F.mid F.n)).snoc F.post

/-- What is asked of a step: four clauses at the base joints. -/
structure StepOK {St St' : Type} (A : Rels Kc St F.E₀ (F.S.Msg × F.Wp))
    (A' : Rels Kc St' F.E₀ (F.S.Msg × F.Wp)) (f : St → St') : Prop where
  fw   : ∀ st y w, A.rel st y w → A'.rel (f st) y w
  on   : ∀ st y, A.on (st, y) → A'.on (f st, y)
  core : ∀ w, A'.core w = A.core w
  bw   : ∀ st y w, A.on (st, y) → A'.relR (f st, y) w → A.relR (st, y) w

/-- What is asked of the front. -/
structure OK : Prop where
  pre   : F.pre.Hyp
  block : ∀ i < F.n, (F.blk i).Hyp
  step  : ∀ i < F.n, F.StepOK (F.At i) (F.As (i + 1)) (F.g i)
  post  : F.StepOK (F.As F.n) F.Az F.gz

end LdFrontD

/-! ## 2. The blocks of the table -/

section
variable {E : Type} [Field E] [Fintype E] (Kc : Type)

/-- the stages of a sumcheck: its true sum claim; its output claims; beside A0 -/
@[reducible] def frPscS (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) : LdStage E Kc :=
  ⟨S, E × T.St, E₀, Wp, T.baseIn A0 fun w => msg w.1⟩
@[reducible] def frPscT (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) : LdStage E Kc :=
  ⟨S, T.par.Out, E₀, Wp, T.par.baseOut A0 fun w => msg w.1⟩

/-- the sumcheck's link -/
def frPscL (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) :
    Link Kc (frPscS Kc T S E₀ Wp A0 msg).J (frPscT Kc T S E₀ Wp A0 msg).J :=
  (frPscS Kc T S E₀ Wp A0 msg).linkA
    (T.par.baseOut A0 fun w => msg w.1) (pscBk T E₀ S.Msg Wp Kc msg)

/-- The sumcheck alone. -/
def frPsc (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) :
    LdProg (frPscS Kc T S E₀ Wp A0 msg) (frPscT Kc T S E₀ Wp A0 msg) :=
  .snoc (.nil _)
    ((frPscS Kc T S E₀ Wp A0 msg).mvA
      (T.par.baseOut A0 fun w => msg w.1) (pscBk T E₀ S.Msg Wp Kc msg))

/-- the letters of its item "masked messages", and the fact that it needs -/
def frMask (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (Rd : T.J → Prop) :
    MaskData (frPscL Kc T S E₀ Wp A0 msg).R (S.Wit × Wp) :=
  T.par.maskSig S E₀ Wp msg (T.own Rd)
def frFact (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (Rd : T.J → Prop) :
    MaskFact (S.Wit × Wp) :=
  (frMask Kc T S E₀ Wp A0 msg Rd).fact

/-- the stage "all claims, and R0" -/
@[reducible] def frInS (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp)) (msg : S.Msg → Z.T.J → E) : LdStage E Kc :=
  ⟨S, Z.St0, E₀, Wp, Z.relsIn R0 msg⟩

/-- Claims on values into one sum claim, then the sumcheck. -/
def frIn (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp)) (msg : S.Msg → Z.T.J → E) :
    LdProg (frInS Kc Z S E₀ Wp R0 msg) (frPscT Kc Z.T S E₀ Wp (Z.ride R0) msg) :=
  .snoc (.snoc (.nil _)
      ((frInS Kc Z S E₀ Wp R0 msg).mvA (Z.relsOut R0 msg) (inBk Z E₀ S.Msg Wp Kc)))
    ((frPscS Kc Z.T S E₀ Wp (Z.ride R0) msg).mvA
      (Z.T.par.baseOut (Z.ride R0) fun w => msg w.1) (pscBk Z.T E₀ S.Msg Wp Kc msg))

end

/-! ## The statements -/

namespace Spec

/-- States: `F.OK` gives `F.prog.Hyp`. -/
def ldSegFront_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (F : LdFrontD E Kc), F.OK → F.prog.Hyp

def ldSegFront_kinds : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (F : LdFrontD E Kc) (k : LdTag → Prop),
    k .step → F.pre.All k → (∀ i < F.n, (F.blk i).All k) → F.prog.All k

def ldSegFront_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (F : LdFrontD E Kc),
    F.prog.nAll = F.pre.nAll + ∑ i ∈ Finset.range F.n, (F.blk i).nAll ∧
    F.prog.nVer = F.pre.nVer + ∑ i ∈ Finset.range F.n, (F.blk i).nVer ∧
    F.prog.pBad = F.pre.pBad + ∑ i ∈ Finset.range F.n, (F.blk i).pBad ∧
    F.prog.pHid = F.pre.pHid + ∑ i ∈ Finset.range F.n, (F.blk i).pHid

/-- What zero knowledge asks of the front, beside its hypotheses. -/
def ldSegFront_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (F : LdFrontD E Kc) (base : MaskFact F.a.J.W → Prop),
    F.pre.Zk base → (∀ i < F.n, (F.blk i).Zk ((F.pre.app (F.mid i)).After base)) → F.prog.Zk base

/-- The blocks' hypotheses from the conditions on T and Z. -/
def ldSegFront_psc_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E),
    T.VarsOK → T.DegX → T.DegY → T.ValInj → (frPsc Kc T S E₀ Wp A0 msg).Hyp

def ldSegFront_in_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp)) (msg : S.Msg → Z.T.J → E),
    Z.Link → Z.Back → Z.ev.OK → Z.T.VarsOK → Z.T.DegX → Z.T.DegY →
    Z.T.ValInj → (frIn Kc Z S E₀ Wp R0 msg).Hyp

/-- What zero knowledge asks of them, beside their hypotheses. -/
def ldSegFront_psc_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (Rd : T.J → Prop)
      (base : MaskFact (frPscS Kc T S E₀ Wp A0 msg).J.W → Prop),
    (frPscL Kc T S E₀ Wp A0 msg).GoodM (frMask Kc T S E₀ Wp A0 msg Rd) →
    base (frFact Kc T S E₀ Wp A0 msg Rd) → (frPsc Kc T S E₀ Wp A0 msg).Zk base

def ldSegFront_in_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp)) (msg : S.Msg → Z.T.J → E) (Rd : Z.T.J → Prop)
      (base : MaskFact (frInS Kc Z S E₀ Wp R0 msg).J.W → Prop),
    Z.Link → Z.Back → Z.ev.OK →
    (frPscL Kc Z.T S E₀ Wp (Z.ride R0) msg).GoodM (frMask Kc Z.T S E₀ Wp (Z.ride R0) msg Rd) →
    base (frFact Kc Z.T S E₀ Wp (Z.ride R0) msg Rd) → (frIn Kc Z S E₀ Wp R0 msg).Zk base

/-- Their rounds and kinds. -/
def ldSegFront_psc_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E),
    (frPsc Kc T S E₀ Wp A0 msg).nAll = T.fmt.length + 3 ∧
    (frPsc Kc T S E₀ Wp A0 msg).pBad = 0 ∧
    (frPsc Kc T S E₀ Wp A0 msg).pHid = 0 ∧
    (frPsc Kc T S E₀ Wp A0 msg).All fun t => t = .sub

def ldSegFront_in_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp)) (msg : S.Msg → Z.T.J → E),
    (frIn Kc Z S E₀ Wp R0 msg).nAll = 1 + (Z.T.fmt.length + 3) ∧
    (frIn Kc Z S E₀ Wp R0 msg).pBad = 0 ∧
    (frIn Kc Z S E₀ Wp R0 msg).pHid = 0 ∧
    (frIn Kc Z S E₀ Wp R0 msg).All fun t => t = .sub

end Spec
end Cb
