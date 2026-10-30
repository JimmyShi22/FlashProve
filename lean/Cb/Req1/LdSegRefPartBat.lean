-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefPartBat.lean: some rows into one, the others untouched: a batching inside a body,
as a list of moves.

This file is about one batching step of a segment's body: some of a family of linear claims (rows)
are replaced by one random linear combination of them; the others (if `D.Part`) are copied. It is
written as a sequence of reductions (a list of moves).
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegRefPartBatProofs.lean.

Why: in this protocol's technical report (lean/CREDITS.md) the range check ends with a batching of
its own: the rows of the range check and the rows and the output claim of the lookup on its digits
are turned into one row,
by one verifier message (the seed of an evader of its own); no prover message, nothing masked.
All other rows of the segment (the claims on cell maps, ..) are copied.
The block is in the list as a sub-protocol (kind "sub"), since a body holds sendings, sub-protocols
and steps only.

Main names:
  `LdPbD`: the data: S (the oracle messages that are open); a family of rows on all entries (B, Sb,
    sl); the partition: i₁ : B₁ → B (the rows that are batched), i₂ : B₂ → B (the rows that are
    copied); the evader Z for B₁; what else is claimed (St₀, Wp, E₀, A₀).
  `D.Part`: every name of a row is i₁ of a name or i₂ of a name.
  `D.bat`: the data of "many rows into one" (`LdBatD`, Cb/Req1/LdSegKit.lean) for the rows i₁ b,
    with the rows i₂ b riding in "what else is claimed".
  `D.B'`, `D.Sb'`, `D.sl'`: the new family: one row (the combination), and the rows i₂ b.
  `D.prog`: the three moves.
    step, `D.src` → `D.bat.src`, no round: the rows that are copied go inside what rides along.
    sub, `D.bat.src` → `D.bat.tgt`, 1 round: many rows into one.
    step, `D.bat.tgt` → `D.tgt`, no round: the rows come out again, beside the one row.
  `D.src`: rows indexed B, beside A₀; `D.tgt`: rows indexed Unit ⊕ B₂, beside A₀: both have the
    form of the stage at which a closing, or a batching of tensor rows, begins.
  `Spec.ldPartBat_hyp`: `D.prog.Hyp` from `D.Part` and the evader's law.
  `Spec.ldPartBat_kinds`: the kinds of the moves are those that a body may hold.
  `Spec.ldPartBat_nums`: 1 round; nothing withheld, in this sense:
    `D.prog.nAll = 1 ∧ D.prog.pBad = 0 ∧ D.prog.pHid = 0` (see `GoodB`, Ior/Masked.lean).
  `Spec.ldPartBat_zk`: under `D.Z.OK`: D.prog.Zk base, for every base: the block has exact
    honest-verifier zero knowledge of its own (the clause `exact` of `GoodT`,
    Ior/KnowCollGood.lean, at `D.bat.link`: `Spec.ldSeg_mvT`, Cb/Req1/LdSeg.lean, at the move
    `LdMv.bat D.bat`, under its hypotheses).
  `Spec.ldPartBat_carry`: for Mk finite and not empty: the wide fact crosses the list, whatever it
    is.
  `Spec.ldPartBat_fmt`: its format.
  `Spec.ldPartBat_below`: its errors: the evader's number against the number of its seeds. If
    `D.Z.err` ≤ κ times the number of elements of `D.Z.D`, then `D.prog.Below κ`.
  `Spec.ldPartBat_supp`: public supports: if all rows of the old family are 0 at an entry at all
    states, so are all rows of the new one.

Limits: the body of Cb/Req1/LdSegRefBody.lean (`LdBodyD`) does not have this batching (declared
there).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefFmt
import Cb.Req1.LdSegRefBelow
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

/-- Some rows into one: the data. -/
structure LdPbD (E Kc : Type) [Field E] : Type 1 where
  S   : Sig E
  B   : Type
  Sb  : B → Type
  sl  : ∀ b, Slf E (Sb b) S.Ent
  B₁  : Type
  [finB₁ : Fintype B₁]
  B₂  : Type
  i₁  : B₁ → B
  i₂  : B₂ → B
  Z   : Evader E B₁
  St₀ : Type
  Wp  : Type
  E₀  : ExtSpec
  A₀  : IOR.Rels Kc St₀ E₀ (S.Msg × Wp)

attribute [instance] LdPbD.finB₁

namespace LdPbD
variable {E Kc : Type} [Field E] (D : LdPbD E Kc)

def Part : Prop := ∀ b, (∃ b₁, D.i₁ b₁ = b) ∨ ∃ b₂, D.i₂ b₂ = b

/-- the explicit part of the rows that are copied -/
abbrev X₂ : Type := (D.B₂ → E) × (∀ b, D.Sb (D.i₂ b))

/-- Many rows into one, with the copied rows riding. -/
@[reducible] def bat : LdBatD E Kc :=
  { S := D.S, B := D.B₁, Sb := fun b => D.Sb (D.i₁ b), sl := fun b => D.sl (D.i₁ b), Z := D.Z,
    St₀ := D.X₂ × D.St₀, Wp := D.Wp, E₀ := D.E₀,
    A₀ := claimRels (fun x m => Slf.All (fun b => D.sl (D.i₂ b)) x (D.S.ents m)) D.A₀ }

/-- The new family. -/
abbrev B' : Type := Unit ⊕ D.B₂
def Sb' : D.B' → Type
  | .inl _ => (∀ b, D.Sb (D.i₁ b)) × D.Z.D
  | .inr b => D.Sb (D.i₂ b)
def sl' : ∀ b, Slf E (D.Sb' b) D.S.Ent
  | .inl _ => Slf.bat D.Z.ze fun b => D.sl (D.i₁ b)
  | .inr b => D.sl (D.i₂ b)

@[reducible] def src : LdStage E Kc :=
  ⟨D.S, ((D.B → E) × (∀ b, D.Sb b)) × D.St₀, D.E₀, D.Wp,
    claimRels (fun x m => Slf.All D.sl x (D.S.ents m)) D.A₀⟩
@[reducible] def tgt : LdStage E Kc :=
  ⟨D.S, ((D.B' → E) × (∀ b, D.Sb' b)) × D.St₀, D.E₀, D.Wp,
    claimRels (fun x m => Slf.All D.sl' x (D.S.ents m)) D.A₀⟩

/-- the maps of the explicit parts -/
def fIn (x : ((D.B → E) × (∀ b, D.Sb b)) × D.St₀) : D.bat.src.St :=
  ((fun b => x.1.1 (D.i₁ b), fun b => x.1.2 (D.i₁ b)),
    ((fun b => x.1.1 (D.i₂ b), fun b => x.1.2 (D.i₂ b)), x.2))
def fOut (x : D.bat.tgt.St) : ((D.B' → E) × (∀ b, D.Sb' b)) × D.St₀ :=
  ((fun b => match b with | .inl _ => x.1.1 | .inr b => x.2.1.1 b, fun b => match b with | .inl _ => x.1.2 | .inr b => x.2.1.2 b), x.2.2)

variable [Fintype E]

def stepIn : LdMv D.src D.bat.src := ldStepF D.S D.src.A D.bat.src.A D.fIn
def stepOut : LdMv D.bat.tgt D.tgt := ldStepF D.S D.bat.tgt.A D.tgt.A D.fOut

/-- The three moves. -/
def prog : LdProg D.src D.tgt :=
  (((LdProg.nil D.src).snoc D.stepIn).snoc
    (.sub D.bat.src D.bat.tgt (.one D.bat.link))).snoc D.stepOut

end LdPbD

namespace Spec

def ldPartBat_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdPbD E Kc), D.Part → D.Z.OK → D.prog.Hyp

def ldPartBat_kinds : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdPbD E Kc),
    D.prog.All fun t => t = .send ∨ t = .sub ∨ t = .step

def ldPartBat_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdPbD E Kc),
    D.prog.nAll = 1 ∧ D.prog.pBad = 0 ∧ D.prog.pHid = 0

def ldPartBat_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdPbD E Kc) (base : MaskFact D.src.J.W → Prop),
    D.Z.OK → D.prog.Zk base

def ldPartBat_carry : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdPbD E Kc) (base : MaskFact D.src.J.W → Prop)
      (Rd : D.S.Ent → Prop) (Rr : D.S.O → Prop) (own : D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → D.S.Ent → E),
    base (D.src.wideFact Rd Rr own Mk val) → D.prog.After base (D.tgt.wideFact Rd Rr own Mk val)

def ldPartBat_fmt : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (D : LdPbD E Kc)
      (i : IxAt E0 D.E₀) (rc : D.St₀ → Rc) (px : D.Wp → Pw) (q : Finset D.src.Ex.Pos → Prop),
    D.prog.Fmt (D.src.fmt i (fun x => rc x.2) px q) (D.tgt.fmt i (fun x => rc x.2) px q)

def ldPartBat_below : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdPbD E Kc) (κ : ℝ≥0∞),
    (D.Z.err : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞) → D.prog.Below κ

def ldPartBat_supp : Prop :=
  ∀ (E Kc : Type) [Field E] (D : LdPbD E Kc) (n : D.S.Ent),
    (∀ b st, D.sl b st n = 0) → ∀ b st, D.sl' b st n = 0

end Spec
end Cb
