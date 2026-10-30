-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwFlat.lean.
A typed transcript of the lookup's chain, read as plain data.

Definitions, and one law at a concatenation.
Main names:
  `Fl E b`: a block's transcripts as plain data (`TwV.Rounds E`). `fseq` (by `Tr.fst`, `Tr.snd`),
    `fchain`, `fdraw`; `fseq_app`: at `Tr.app τ₁ τ₂` the plain data are the two lists in a row.
  `flFull`, `flCore`, `flStep`, `flTie`, `flHead`, `flLine`, `flLev`, `flTree`, `flRoot`,
    `flForest`, `flEnd`, `flBit`, `flChn Ex A`: block by block, in the chain's own nesting. A draw's
    value as a list: one element, or the point's coordinates from 0 on.
Limits: at the filling `SK₀` (Cb/Pv/Lookup/Out/TwFill.lean) alone. These definitions, with `flS`,
`flS0`, `flSc`, `flScC` of Cb/Pv/Lookup/Out/TwSc.lean, are the one reading on which the meaning of
the equations in Cb/Pv/Lookup/Out/TwState.lean and OnBytes/Tie/Pv/Lookup/Out/TwOutEq.lean hangs:
they are to be read. The reading takes the transcript alone, holds no arithmetic, and leaves out
only components of type Unit. That, and that entry i comes from round i, is no theorem: it is seen
by reading these definitions. A law beside it: `flChn_un` (Cb/Pv/Lookup/Out/TwLift.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Out.TwFill
import Cb.Pv.Lookup.Out.TwSc
import Cb.Pv.Lookup.Out.TwTraceOf

set_option autoImplicit false

namespace Tw
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3

noncomputable section

section
variable (E : Type) {X₁ X₂ X₃ : Type} {Ex : ExtSpec}

/-- A block's transcripts as plain data. -/
abbrev Fl (b : BkK X₁ X₂ Ex) : Type := Tr b.R.shape → Rounds E

variable {E}

def fseq {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} (f : Fl E a) (g : Fl E b) : Fl E (a.seq b) :=
  fun τ => f (Tr.fst τ) ++ g (Tr.snd (s := a.R.shape) τ)

theorem fseq_app {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} (f : Fl E a) (g : Fl E b) (τ₁ : Tr a.R.shape)
    (τ₂ : Tr b.R.shape) : fseq f g (Tr.app τ₁ τ₂) = f τ₁ ++ g τ₂ := by
  unfold fseq
  rw [Tr.fst_app, Tr.snd_app]

def fdraw {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (Ex : ExtSpec)
    (err : ℕ) (dl : D → List E) : Fl E (drawK D nx Ex err) := fun τ => [([], dl (drawn τ))]

def fchain (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (f : ∀ l, Fl E (b l)) :
    ∀ n, Fl E (BkK.chain X b n)
  | 0 => f 0
  | n + 1 => fseq (fchain X b f n) (f (n + 1))

end

variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec)

def flFull (Y : PscPar E) (sh : List Y.A) : Fl E ((SK₀ E Ex).full Y) := flSc Y sh
def flCore (Y : PscPar E) : Fl E ((SK₀ E Ex).core Y) := flScC Y

def flStep (D : TieF E) (l : ℕ) : Fl E (D.stepK (SK₀ E Ex) l) := flFull Ex (D.lv l).T.par (tieSh D
    l)
def flTie (D : TieF E) (n : ℕ) : Fl E (D.tieK (SK₀ E Ex) n) :=
  fchain (fun l => E × (D.lv l).T.St) (D.stepK (SK₀ E Ex)) (flStep Ex D) n
def flHead (H : LkHeadF E) : Fl E (H.headK (SK₀ E Ex)) :=
  fseq (a := drawK E (Prod.mk : H.St → E → H.St × E) Ex (2 ^ H.v - 1))
    (b := (H.tie.tieK (SK₀ E Ex) H.n).preM fun x => ((0 : E), x))
    (fdraw E (Prod.mk : H.St → E → H.St × E) Ex (2 ^ H.v - 1) fun β => [β]) (flTie Ex H.tie H.n)

def flLine (D : TreeP E) (l : ℕ) : Fl E (D.lineK Ex l) :=
  fdraw (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex (D.cube l).toLine.toIn.ev.err
    fun ρ : E => [ρ]
def flLev (D : TreeP E) (l : ℕ) : Fl E (D.levK (SK₀ E Ex) l) :=
  fseq (flFull Ex (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true]) (flLine Ex D l)
def flTree (D : TreeP E) (n : ℕ) : Fl E (D.treeK (SK₀ E Ex) n) :=
  fchain (fun l => E × (D.lv l).T.St) (D.levK (SK₀ E Ex)) (flLev Ex D) n

variable (A : LkAsmH E)

def flRoot : Fl E (A.rootK Ex) :=
  fdraw A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.ev.err fun ϱ : Fin (A.w + 0) → E => List.ofFn ϱ
def flForest : (l : ℕ) → Fl E (A.forestK (SK₀ E Ex) l)
  | 0 => flTree Ex (A.IK.setV (A.v' + 1)).DK A.v'
  | l + 1 => fseq (flForest l) (flLev Ex A.D l)
def flEnd : Fl E (A.endK (SK₀ E Ex)) := flCore Ex A.En.par
def flBit : Fl E (A.bitK (SK₀ E Ex)) :=
  fseq (a := drawK A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.ev.err)
    (fdraw A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.ev.err fun β => List.ofFn β.2)
    (flFull Ex A.Bt.zc.next.par [()])

/-- THE CHAIN's TRANSCRIPT AS PLAIN DATA. -/
def flChn : Fl E (A.chnK (SK₀ E Ex)) :=
  fseq (fseq (fseq (fseq (flHead Ex A.H) (flRoot Ex A)) (flForest Ex A A.d)) (flEnd Ex A)) (flBit Ex
      A)

end
end Tw
