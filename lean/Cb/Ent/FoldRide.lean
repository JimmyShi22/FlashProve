-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ent/FoldRide.lean: the fold and the base case whose own oracle was sent earlier: the fold's fresh
mask, the base case's masking word, ride in an oracle of an earlier round. Round-by-round knowledge
soundness of "an earlier reduction, then the block", from the library's blocks, by the pass of
Ior/PullC.lean on the two in a row.

Definitions and statements; the proofs are in Cb/Ent/FoldRideProofs.lean.
The library's fold sends its fresh mask in its first round, the base case its masking word in its
first round. Here these rounds send no oracle. K₁ is any reduction into the block's input statement,
read behind any maps F₁ from a shape s₁; `rd` says where in a transcript of s₁ the rider is read.
The maps of the block's rounds put the rider into its round (`Carry.app`: the maps of the second
part may read the transcript of the first). The fold's later rounds are short
(Cb/Ent/FoldShort.lean); the running claim starts from the target that K₁ outputs. The blocks are
used as they are.
With Cb/Ent/ColRound.lean: s₁ begins with a round of columns, F₁ cuts them, `rd` is `L.rider`.
Compare `IOR.hoist` (Ior/Hoist.lean): a narrower way to send a part ahead of the rest, which keeps
the honest side.

Main names:
  `Y.round0N`, `Y.shapeR`: the fold's first round without its oracle; the fold's rounds as sent.
  `Y.carR fx t₀ z`, `Y.upR fx t₀ z τ`: the maps and the image of a transcript, at the target t₀ and
    the fresh mask z.
  `ldBaseShapeN C t`, `ldBaseCarR C t g`, `ldBaseUpR C t g τ`: the same for the base case, at the
    masking word g.
  `tgtOf K₁ F₁ a τ₁`: the target of the statement that K₁ outputs on the image of τ₁ (0 if none).
  `Y.carRide fx K₁ F₁ rd`, `ldBaseCarRide C t K₁ F₁ rd`: the maps of the two parts in a row.
  `Spec.ldEnt_ride_tr`, `Spec.ldEnt_ride_fib`, `Spec.ldEnt_ride_chal`: images and fibres of the
    blocks' maps; as many verifier messages as the blocks have.
  `Y.impR z`, `Spec.ldEnt_ride_imp`: the fold's new implicit instance at the fresh mask z.
  `Spec.ldEnt_rideFold_know`: under `Y.HypK` (Cb/Ent/TowerKnow.lean), knowledge soundness of K₁ into
    the fold's relaxed relation, and fibres ws₁ of F₁: knowledge soundness of the two in a row, as
    sent.
  `Spec.ldEnt_rideBase_know`: the same for the base case, under the four conditions of
    `LdJoint.BaseHypK`.
  `D.colL`, `D.shC`, `D.carC`, `D.riderC`: an earlier block: the code switch (Cb/Ld/LdSwitch.lean)
    whose new word lies with a rider in the leaves of one tree. `Spec.ldEnt_rideSwitchFold_know`:
    that switch, a step without rounds, whose knowledge soundness is a premise, then the fold whose
    fresh mask is the rider.
  `Spec.ldEnt_rideFold_out`: the verifier of the two in a row, in closed form: no check of the
    fold's is left, if `fx.2` is an inverse of the "sum" of the power that is left out.
  `Spec.ldEnt_rideBase_out`: the same for the base case: its test, with the rider as the masking
    word. `Spec.ldEnt_colSwitch_out`: the switch behind columns: it never rejects; its new implicit
    instance is the new word cut out of the columns.

Limits: the statements on knowledge soundness hold for any `rd` and any fx: that `rd` reads what a
program sends as the mask is an instance's matter; `rd` may be any function of the earlier
transcript, its verifier messages too. With an fx that is no inverse the verifier still checks the
round equations on the completed polynomials: the statements on knowledge soundness alone are not
about a verifier without checks: that takes the premise of `Spec.ldEnt_rideFold_out`. Not that any
Y, C or D meets the conditions, or that the errors are small: lists and agreement are conditions,
with any numbers. No program is compared here. The statements are on reductions (`Reduction.pullC`):
no IOR is built: its new implicit instance and declarations on positions would be arguments
(Ior/PullC.lean: `Spec.know_pullC_seq_ior`, `Spec.imp_pullC_app`, for which `Spec.ldEnt_ride_imp` is
the fold's share); to the trivial statement the implicit instance is no matter. One rider for one
block: a chain with several riders takes one `Carry.app` for each block. The block stands last: for
a block in the middle of a chain bracketed to the right, use `Spec.know_pullC` on the whole chain
with `Y.carR` under nested `Carry.app`. Nothing on an honest prover: no completeness, no zero
knowledge. Error counts: K₁'s times ws₁; the blocks' own; as lists by `Spec.mulErr_ones_toList`; as
many verifier messages by `Spec.ldEnt_ride_chal`.

Terms: lean/GLOSSARY.md.

-/
import Cb.Ent.FoldShort
import Cb.Ent.TowerKnow
import Cb.Ent.ColRound
import Cb.Ld.LdBase
import Cb.Ld.LdSwitch

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks

/-! ## The fold -/

namespace SumPar
variable {E P : Type} [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)

/-- the fold's first round without its oracle: the sum in the clear; the coefficient -/
@[reducible] def round0N : Round := plainRound E Y.Ch 0

/-- the fold's rounds as sent: the first without its oracle, then the short rounds -/
abbrev shapeR : Shape := Y.round0N :: Y.roundsS

/-- The maps of the fold, at the target t₀ of its statement and the fresh mask z. -/
def carR (t₀ : E) (z : Y.Cw.Word) : Carry Y.shapeR Y.shape :=
  (fun m => (z, m.2), fun _ c => some c, fun m c => sCar Y.val Y.n fx Y.k (m.2 + t₀ * Y.val c))

/-- The image of a transcript. -/
def upR (t₀ : E) (z : Y.Cw.Word) (τ : Tr Y.shapeR) : Tr Y.shape :=
  ((z, τ.1.2), τ.2.1, sUp Y.val Y.n fx Y.k (τ.1.2 + t₀ * Y.val τ.2.1) τ.2.2)

/-- the verifier messages, as those of the block -/
def upRhoR (ρ : Rho Y.shapeR) : Rho Y.shape := (ρ.1, sUpRho Y.n Y.k ρ.2)

/-- The new implicit instance, at the fresh mask z: the three tables, folded: the words of
`SumPar.imp`. -/
def impR (z : Y.Cw.Word) (y : Y.Cin.Word) (τ : Tr Y.shapeR) : Y.Cout.Word :=
  LdCode.mkW (foldW Y.C (Y.pt (Y.upRhoR τ.rho)) (LdCode.fstW y))
    (LdCode.mkW (C₁ := Y.Z) (C₂ := Y.Zw) (foldW Y.Z (Y.pre (Y.pt (Y.upRhoR τ.rho))) (LdCode.sndW y))
      (foldW Y.Zw (Y.pre (Y.pt (Y.upRhoR τ.rho))) z))

end SumPar

/-! ## The base case -/

section Base
variable {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (t : ℕ)

/-- the base case's two rounds, the first without its oracle -/
abbrev ldBaseShapeN : Shape := [plainRound E E 0, plainRound C.MR (Fin t → P) 0]

/-- The maps of the base case, at the masking word g. -/
def ldBaseCarR (g : C.Word) : Carry (ldBaseShapeN C t) (ldBaseShape C t) :=
  (fun m => (g, m.2), fun _ c => some c, fun _ _ => Carry.id _)

/-- The image of a transcript. -/
def ldBaseUpR (g : C.Word) (τ : Tr (ldBaseShapeN C t)) : Tr (ldBaseShape C t) :=
  ((g, τ.1.2), τ.2.1, τ.2.2)

end Base

/-! ## Two in a row -/

section Two
variable {E A S Yy : Type} [Zero E]

/-- The target of the statement that K₁ outputs on the image of τ₁; 0 if there is none. -/
def tgtOf (K₁ : Reduction A ((E × S) × Yy)) {s₁ : Shape} (F₁ : A → Carry s₁ K₁.shape) (a : A)
    (τ₁ : Tr s₁) : E :=
  match ((F₁ a).tr τ₁).bind (K₁.out a) with
  | some b => b.1.1
  | none => 0

end Two

/-- K₁ behind F₁, then the fold as sent: the maps. -/
def SumPar.carRide {E P A : Type} [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)
    (K₁ : Reduction A (Y.Xi × Y.Cin.ext.Str)) {s₁ : Shape} (F₁ : A → Carry s₁ K₁.shape)
    (rd : Tr s₁ → Y.Cw.Word) : A → Carry (s₁ ++ Y.shapeR) (K₁.shape ++ Y.shape) := fun a =>
  (F₁ a).app fun τ₁ => Y.carR fx (tgtOf K₁ F₁ a τ₁) (rd τ₁)

/-- K₁ behind F₁, then the base case as sent: the maps. -/
def ldBaseCarRide {E P A St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P]
    (C : LdCode E P) (t : ℕ) (K₁ : Reduction A ((E × St) × C.ext.Str)) {s₁ : Shape}
    (F₁ : A → Carry s₁ K₁.shape) (rd : Tr s₁ → C.Word) :
    A → Carry (s₁ ++ ldBaseShapeN C t) (K₁.shape ++ ldBaseShape C t) := fun a =>
  (F₁ a).app fun τ₁ => ldBaseCarR C t (rd τ₁)

/-! ## An earlier block: the code switch, its new word and a rider in one tree -/

section Switch
variable {E P P' Pw St : Type} [Field E] [Fintype P] [Nonempty P] (D : LdSw E P P' St)
  (Cw : LdCode E Pw) (Pt : Type)
  (lf : D.Cout.NP → Pt) (lfW : Cw.NP → Pt)

/-- The layout: the switch's new word and a native word of Cw in the leaves Pt. -/
def LdSw.colL : ColLay (D.Cout.sendRound Unit D.Zo.D ()) Cw.Word :=
  D.Cout.colLay Cw Pt lf lfW Unit D.Zo.D ()

/-- the switch's two rounds, the first a round of columns -/
abbrev LdSw.shC : Shape :=
  [(D.colL Cw Pt lf lfW).round, plainRound (D.Zo.S → E) ((Fin D.t → P) × D.Zb.D) fun _ => 0]

/-- The maps: the columns are cut. -/
def LdSw.carC : Carry (D.shC Cw Pt lf lfW) D.sh :=
  (D.colL Cw Pt lf lfW).car (D.Cout.sendPoint _ _ _) _

/-- the rider, read in a transcript of the switch as sent -/
def LdSw.riderC (τ : Tr (D.shC Cw Pt lf lfW)) : Cw.Word := (D.colL Cw Pt lf lfW).rider τ.1.1

end Switch

/-- a step without rounds, as a reduction (as an IOR: `IOR.pure`, with `Spec.know_pure`,
Ior/KnowRules.lean) -/
@[reducible] def stepRed {A B : Type} (f : A → Option B) : Reduction A B := ⟨[], fun a _ => f a⟩

namespace Spec

/-- Every transcript of the blocks as sent has an image. -/
def ldEnt_ride_tr : Prop :=
  (∀ (E P : Type) [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E) (t₀ : E) (z : Y.Cw.Word)
      (τ : Tr Y.shapeR), (Y.carR fx t₀ z).tr τ = some (Y.upR fx t₀ z τ)) ∧
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (t : ℕ)
      (g : C.Word) (τ : Tr (ldBaseShapeN C t)),
    (ldBaseCarR C t g).tr τ = some (ldBaseUpR C t g τ)

/-- One verifier message goes to one. -/
def ldEnt_ride_fib : Prop :=
  (∀ (E P : Type) [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E) (t₀ : E) (z : Y.Cw.Word),
    (Y.carR fx t₀ z).Fib (Err.ones Y.shapeR)) ∧
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (t : ℕ)
      (g : C.Word), (ldBaseCarR C t g).Fib (Err.ones (ldBaseShapeN C t))

/-- The fold's implicit instance at the rider is the block's on the image, whatever the target: with
`Spec.ldEnt_ride_tr`, the second premise of `Iop.Spec.imp_pullC_app` (Ior/PullC.lean) at
`im₂ τ₁ := Y.impR (rd τ₁)`. -/
def ldEnt_ride_imp : Prop :=
  ∀ (E P : Type) [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E) (t₀ : E) (z : Y.Cw.Word)
      (y : Y.Cin.Word) (τ : Tr Y.shapeR),
    Y.impR z y τ = Y.imp y (Y.upR fx t₀ z τ)

/-- The rounds as sent have as many verifier messages as the blocks'. -/
def ldEnt_ride_chal : Prop :=
  (∀ (E P : Type) [Field E] (Y : SumPar E P), Y.shapeR.chalList = Y.shape.chalList) ∧
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (t : ℕ),
    (ldBaseShapeN C t).chalList = (ldBaseShape C t).chalList

/-- An earlier reduction, then the fold whose fresh mask rode in the earlier rounds, with short
rounds: round-by-round knowledge soundness. This is said under the hypotheses that stand in the
statement itself, which this comment does not list; it is no claim that they hold. -/
def ldEnt_rideFold_know : Prop :=
  ∀ (E P A WA : Type) [Field E] [Fintype E] [Fintype P] (Y : SumPar E P)
      (fx : Fin (Y.n + 1) × E) (K₁ : Reduction A (Y.Xi × Y.Cin.ext.Str)) (s₁ : Shape)
      (F₁ : A → Carry s₁ K₁.shape) (ws₁ : Err s₁) (rd : Tr s₁ → Y.Cw.Word) (on : A → Prop)
      (RA : A → WA → Prop) (e₁ : A → Tr K₁.shape → Y.Cin.N.Wit → WA) (ε₁ : Err K₁.shape) (d₀ : WA)
      (d e : ℕ) (Lst mC mS mW : ℕ → ℕ),
    K₁.Know on RA (ConL Y.Cin.N e Y.slIn.Holds) e₁ ε₁ → (∀ a, on a → (F₁ a).Fib ws₁) →
    Y.HypK d e Lst mC mS mW →
    ((K₁.seq Y.ior.red).pullC (s₁ ++ Y.shapeR) (Y.carRide fx K₁ F₁ rd)).Know on RA
      (ConL Y.Cout.N e Y.slOut.Holds)
      ((K₁.seq Y.ior.red).extC (s₁ ++ Y.shapeR) (Y.carRide fx K₁ F₁ rd)
        (Reduction.extSeq K₁ Y.ior.red e₁ (Y.ext d) d₀) d₀)
      (Err.app (mulErr s₁ K₁.shape ws₁ ε₁)
        (mulErr Y.shapeR Y.shape (Err.ones Y.shapeR) (Y.err Lst mC mS mW)))

/-- An earlier reduction, then the base case whose masking word rode in the earlier rounds. -/
def ldEnt_rideBase_know : Prop :=
  ∀ (E P A WA St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P)
      (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) (K₁ : Reduction A ((E × St) × C.ext.Str))
      (s₁ : Shape) (F₁ : A → Carry s₁ K₁.shape) (ws₁ : Err s₁) (rd : Tr s₁ → C.Word)
      (on : A → Prop) (RA : A → WA → Prop) (e₁ : A → Tr K₁.shape → C.N.Wit → WA)
      (ε₁ : Err K₁.shape) (d₀ : WA) (d e bad L2 : ℕ),
    K₁.Know on RA (C.rels sl e fun _ => ()).relR e₁ ε₁ → (∀ a, on a → (F₁ a).Fib ws₁) →
    C.Laws → e < d → C.MCAat e bad → (C.il Bool).ListAt e L2 →
    ((K₁.seq (ldBaseIOR C sl t cov).red).pullC (s₁ ++ ldBaseShapeN C t)
        (ldBaseCarRide C t K₁ F₁ rd)).Know on RA trivRels.relR
      ((K₁.seq (ldBaseIOR C sl t cov).red).extC (s₁ ++ ldBaseShapeN C t)
        (ldBaseCarRide C t K₁ F₁ rd)
        (Reduction.extSeq K₁ (ldBaseIOR C sl t cov).red e₁ (ldBaseExt C t d) d₀) d₀)
      (Err.app (mulErr s₁ K₁.shape ws₁ ε₁)
        (mulErr (ldBaseShapeN C t) (ldBaseShape C t) (Err.ones _) (ldBaseErr C t e bad L2)))

/-- A code switch whose tree bears the next fold's fresh mask, a step without rounds f (with
knowledge soundness between the two relaxed relations, extractor eM), then that fold, as sent: the
switch's conditions (`LdSw.HypK`), the fold's (`SumPar.HypK`). Errors: the switch's, then the
fold's. -/
def ldEnt_rideSwitchFold_know : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (D : LdSw E P P' St) (Y : SumPar E P') (fx : Fin (Y.n + 1) × E) (Pt : Type)
      (lf : D.Cout.NP → Pt) (lfW : Y.Cw.NP → Pt)
      (f : (E × D.St') × D.Cout.ext.Str → Option (Y.Xi × Y.Cin.ext.Str))
      (eM : (E × D.St') × D.Cout.ext.Str → Tr [] → Y.Cin.N.Wit → D.Cout.N.Wit)
      (e₀ e L d : ℕ) (Lst mC mS mW : ℕ → ℕ) (d₀ : D.Cin.N.Wit),
    D.HypK e L →
    (stepRed f).Know (fun _ => True) (ConL D.Cout.N e D.sl'.Holds) (ConL Y.Cin.N e Y.slIn.Holds)
      eM () →
    Y.HypK d e Lst mC mS mW →
    ((((ldSwitch D).red.seq (stepRed f)).seq Y.ior.red).pullC
        (D.shC Y.Cw Pt lf lfW ++ Y.shapeR)
        (Y.carRide fx ((ldSwitch D).red.seq (stepRed f)) (fun _ => D.carC Y.Cw Pt lf lfW)
          (D.riderC Y.Cw Pt lf lfW))).Know (fun _ => True)
      (ConL D.Cin.N e₀ D.sl.Holds) (ConL Y.Cout.N e Y.slOut.Holds)
      ((((ldSwitch D).red.seq (stepRed f)).seq Y.ior.red).extC
        (D.shC Y.Cw Pt lf lfW ++ Y.shapeR)
        (Y.carRide fx ((ldSwitch D).red.seq (stepRed f)) (fun _ => D.carC Y.Cw Pt lf lfW)
          (D.riderC Y.Cw Pt lf lfW))
        (Reduction.extSeq ((ldSwitch D).red.seq (stepRed f)) Y.ior.red
          (Reduction.extSeq (ldSwitch D).red (stepRed f) (fun _ _ w' => D.back w') eM d₀)
          (Y.ext d) d₀) d₀)
      (Err.app
        (mulErr (D.shC Y.Cw Pt lf lfW) D.sh (Err.ones _) (D.W.err1 L, (D.W.err2 e₀ L, ())))
        (mulErr Y.shapeR Y.shape (Err.ones Y.shapeR) (Y.err Lst mC mS mW)))

/-- The verifier of the two in a row, in closed form: K₁'s behind F₁; then, from its output b, the
fold's new statement at the running claim's last value, over the tables folded with the rider as the
fresh mask. No check of the fold's is left. -/
def ldEnt_rideFold_out : Prop :=
  ∀ (E P A : Type) [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E),
    fx.2 * (HVar.plain E Y.n).mon fx.1 = 1 →
    ∀ (K₁ : Reduction A (Y.Xi × Y.Cin.ext.Str)) (s₁ : Shape) (F₁ : A → Carry s₁ K₁.shape)
      (rd : Tr s₁ → Y.Cw.Word) (a : A) (τ₁ : Tr s₁) (τ₂ : Tr Y.shapeR),
      ((K₁.seq Y.ior.red).pullC (s₁ ++ Y.shapeR) (Y.carRide fx K₁ F₁ rd)).out a (Tr.app τ₁ τ₂) =
        ((K₁.pullC s₁ F₁).out a τ₁).map fun b =>
          (Y.newX b.1 (Y.upRhoR τ₂.rho)
              (sClaim Y.val Y.n fx Y.k (τ₂.1.2 + b.1.1 * Y.val τ₂.2.1) τ₂.2.2),
            Y.impR (rd τ₁) b.2 τ₂)

open Classical in
/-- The verifier of the two in a row, in closed form: K₁'s behind F₁; then the base case's test,
with the rider as the masking word. -/
def ldEnt_rideBase_out : Prop :=
  ∀ (E P A St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P)
      (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) (K₁ : Reduction A ((E × St) × C.ext.Str))
      (s₁ : Shape) (F₁ : A → Carry s₁ K₁.shape) (rd : Tr s₁ → C.Word) (a : A) (τ₁ : Tr s₁)
      (τ₂ : Tr (ldBaseShapeN C t)),
    ((K₁.seq (ldBaseIOR C sl t cov).red).pullC (s₁ ++ ldBaseShapeN C t)
        (ldBaseCarRide C t K₁ F₁ rd)).out a (Tr.app τ₁ τ₂) =
      ((K₁.pullC s₁ F₁).out a τ₁).bind fun b =>
        if LdwAccept (ldCw C) (ldForm sl b.1) b.1.1 (C.T b.2) (C.T (rd τ₁)) τ₂.1.2 τ₂.2.1
            τ₂.2.2.1.2 τ₂.2.2.2.1
        then some ((), ()) else none

/-- The verifier of the code switch behind columns, in closed form: it never rejects; the new
statement is the switch's; the new implicit instance is the new word, cut out of the columns. -/
def ldEnt_colSwitch_out : Prop :=
  ∀ (E P P' Pw St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
      [Nonempty P'] (D : LdSw E P P' St) (Cw : LdCode E Pw) (Pt : Type) (lf : D.Cout.NP → Pt)
      (lfW : Cw.NP → Pt) (a : (E × St) × D.Cin.ext.Str) (τ : Tr (D.shC Cw Pt lf lfW)),
    ((ldSwitch D).red.pullC (D.shC Cw Pt lf lfW) fun _ => D.carC Cw Pt lf lfW).out a τ =
      some ((D.W.tgt' a.1.1 τ.2.2.1.2 (D.Cin.T a.2) τ.2.2.2.1,
          (D.stOf a.1.2 τ.2.1 τ.2.2.2.1.1, τ.2.2.2.1.2)),
        (D.colL Cw Pt lf lfW).main (D.Cout.sendPoint _ _ _) τ.1.1)

end Spec
end Cb
