-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwOut.lean.
What the assembled lookup's verifier puts out, as a function of the statement and the transcript,
for every filling of its sumchecks whose verifiers never refuse.

Definitions, and theorems with their proofs. The value functions here are typed over the library's
shapes and stand in theorems alone: no code is asked of them.
Main names:
  `bk_seq_red`, `bk_chain_red`, `headK_red`, `tieK_red`, `levK_red`, `treeK_red`, `forestK_red`,
    `chainK_red`, `chnK_red`: at each `seq` of the chain the reduction of the whole is the parts'
    reductions joined by `Reduction.seq`, as an equation of reductions, for every letter SK
    (`PscLtK`, Cb/Pv/Lookup/Know/LtK.lean: the sumcheck's verifiers as a parameter) and every
    assembly A.
  `bk_postM_out`, `bk_preM_out`: the steps without rounds, at the level of out, for all inputs.
  `Val b`, `bseqV`, `bpostV`, `bpreV`, `drawV`, `chainV` with `tot_bseq`, `tot_bpost`, `tot_bpre`,
    `tot_draw`, `tot_chain`: a block's value and its rules.
  `PscLtV SK`: a value function for each sumcheck of the letter SK. `FullV`, `CoreV`: at Y the
    verifier is total (`Tot`, Cb/Pv/Lookup/Alg/TwSeq.lean) with that value. `LtV SV A`: so it is at
    the lookup's own sumchecks.
  `chnV SV A`, `baseV SV A`: the chain's last state and the out-statement, block by block in the
    chain's own nesting.
  `chnK_tot`, `baseKS_tot`, `chnK_out`, `baseKS_out`: under `LtV SV A`, for all inputs, the verifier
    does not refuse and puts out that value.
Limits: `LtV SV A` is a premise here; it is met at one filling in Cb/Pv/Lookup/Out/TwFill.lean. The
recursions in the numbers of steps and levels stay recursions; nothing is unrolled at numerals. The
verifier's side alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Know.AsmK
import Cb.Pv.Lookup.Alg.TwSeq

set_option autoImplicit false

namespace Tw
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn

noncomputable section

/-! ### blocks -/
section
variable {X₁ X₂ X₃ : Type} {Ex : ExtSpec}

/-- The type of a block's value function. -/
abbrev Val (b : BkK X₁ X₂ Ex) : Type := X₁ → Tr b.R.shape → X₂

theorem bk_seq_red (a : BkK X₁ X₂ Ex) (b : BkK X₂ X₃ Ex) : (a.seq b).R.red = a.R.red.seq b.R.red :=
  red_seq_eq a.R b.R

theorem bk_postM_out (b : BkK X₁ X₂ Ex) (φ : X₂ → X₃) (a : X₁ × Ex.Str) (τ : Tr b.R.shape) :
    (b.postM φ).R.red.out a τ = (b.R.red.out a τ).map fun c => (φ c.1, c.2) :=
  red_post_out b.R φ a τ

theorem bk_preM_out (b : BkK X₂ X₃ Ex) (φ : X₁ → X₂) (a : X₁ × Ex.Str) (τ : Tr b.R.shape) :
    (b.preM φ).R.red.out a τ = b.R.red.out (φ a.1, a.2) τ := rfl

theorem bk_chain_red (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (n : ℕ) :
    (BkK.chain X b (n + 1)).R.red = (BkK.chain X b n).R.red.seq (b (n + 1)).R.red :=
  bk_seq_red (BkK.chain X b n) (b (n + 1))

def bseqV {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} (f : Val a) (g : Val b) : Val (a.seq b) := seqV f g
def bpostV {b : BkK X₁ X₂ Ex} (f : Val b) (φ : X₂ → X₃) : Val (b.postM φ) := fun x τ => φ (f x τ)
def bpreV {b : BkK X₂ X₃ Ex} (f : Val b) (φ : X₁ → X₂) : Val (b.preM φ) := fun x τ => f (φ x) τ
def drawV {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (Ex : ExtSpec)
    (err : ℕ) : Val (drawK D nx Ex err) := fun x τ => nx x (drawn τ)

def chainV (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (f : ∀ l, Val (b l)) :
    ∀ n, Val (BkK.chain X b n)
  | 0 => f 0
  | n + 1 => bseqV (chainV X b f n) (f (n + 1))

theorem tot_bseq {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} {f : Val a} {g : Val b} (h₁ : Tot a.R f)
    (h₂ : Tot b.R g) : Tot (a.seq b).R (bseqV f g) := h₁.seq h₂
theorem tot_bpost {b : BkK X₁ X₂ Ex} {f : Val b} (h : Tot b.R f) (φ : X₂ → X₃) :
    Tot (b.postM φ).R (bpostV f φ) := h.post φ
theorem tot_bpre {b : BkK X₂ X₃ Ex} {f : Val b} (h : Tot b.R f) (φ : X₁ → X₂) :
    Tot (b.preM φ).R (bpreV f φ) := h.pre φ
theorem tot_draw {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (err : ℕ) :
    Tot (drawK D nx Ex err).R (drawV D nx Ex err) := Tot.draw D nx

theorem tot_chain (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (f : ∀ l, Val (b l)) (n : ℕ) :
    (∀ l ≤ n, Tot (b l).R (f l)) → Tot (BkK.chain X b n).R (chainV X b f n) := by
  induction n with
  | zero => exact fun h => h 0 (Nat.le_refl 0)
  | succ n ih =>
    intro h
    exact tot_bseq (ih fun l hl => h l (Nat.le_succ_of_le hl)) (h (n + 1) (Nat.le_refl _))

end

/-! ### the letter's value -/

/-- A value function for each of the two verifiers (full, core) that the letter SK gives at a
sumcheck's parameters Y. That it is their value is `FullV`, `CoreV`: no part of this record. -/
structure PscLtV {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} (SK : PscLtK E Ex) where
  full : (Y : PscPar E) → Val (SK.full Y)
  core : (Y : PscPar E) → Val (SK.core Y)

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} {SK : PscLtK E Ex} (SV : PscLtV SK)

def PscLtV.FullV (Y : PscPar E) : Prop := Tot (SK.full Y).R (SV.full Y)
def PscLtV.CoreV (Y : PscPar E) : Prop := Tot (SK.core Y).R (SV.core Y)

/-! ### the blocks' values -/

def stepV (D : TieF E) (l : ℕ) : Val (D.stepK SK l) := bpostV (SV.full (D.lv l).T.par) (D.nxt l)
def tieV (D : TieF E) (n : ℕ) : Val (D.tieK SK n) :=
  chainV (fun l => E × (D.lv l).T.St) (D.stepK SK) (stepV SV D) n
def headV (H : LkHeadF E) : Val (H.headK SK) :=
  bseqV (drawV E (Prod.mk : H.St → E → H.St × E) Ex (2 ^ H.v - 1))
    (bpreV (tieV SV H.tie H.n) fun x => ((0 : E), x))

variable (Ex) in
def lineV (D : TreeP E) (l : ℕ) : Val (D.lineK Ex l) :=
  drawV (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex (D.cube l).toLine.toIn.ev.err
def levV (D : TreeP E) (l : ℕ) : Val (D.levK SK l) :=
  bseqV (SV.full (D.lv l).T.par) (lineV Ex D l)
def treeV (D : TreeP E) (n : ℕ) : Val (D.treeK SK n) :=
  chainV (fun l => E × (D.lv l).T.St) (D.levK SK) (levV SV D) n
def segKV (I : LkInst E) (v' : ℕ) (tK : I.X → E) : Val (segKK I v' tK SK) :=
  bpreV (treeV SV (I.setV (v' + 1)).DK v') (enterK (I.setV (v' + 1)) tK)
def chainKV (Z : PscIn E) : Val (chainK Z SK) :=
  bseqV (drawV Z.ev.D Z.nxX Ex Z.ev.err) (SV.full Z.T.par)

variable (A : LkAsmH E)

variable (Ex) in
def rootV : Val (A.rootK Ex) := drawV A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.ev.err
def forestV : (l : ℕ) → Val (A.forestK SK l)
  | 0 => bpostV (segKV SV A.IK A.v' fun x => A.tK (A.oR x)) A.enterT
  | l + 1 => bseqV (forestV l) (levV SV A.D l)
def endV : Val (A.endK SK) := SV.core A.En.par
def bitV : Val (A.bitK SK) := chainKV SV A.Bt.zc.toIn
def chnV : Val (A.chnK SK) :=
  bseqV (bseqV (bseqV (bseqV (headV SV A.H) (rootV Ex A)) (forestV SV A A.d)) (endV SV A)) (bitV SV
      A)
/-- The value of the lookup's verifier. -/
def baseV : Val (A.baseKS SK) := bpostV (chnV SV A) A.rd

/-- What is asked of the letter's value: `FullV` or `CoreV` at the lookup's own sumchecks, and
nowhere else. -/
structure LtV : Prop where
  tie  : ∀ l ≤ A.n, SV.FullV (A.H.tie.lv l).T.par
  keys : ∀ l ≤ A.v', SV.FullV ((A.IK.setV (A.v' + 1)).DK.lv l).T.par
  tab  : ∀ l < A.d, SV.FullV (A.D.lv l).T.par
  clo  : SV.CoreV A.En.par
  bit  : SV.FullV A.Bt.zc.next.par

end

/-! ### the chain's reduction is the blocks' joined by Reduction.seq -/
section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} (SK : PscLtK E Ex)

theorem headK_red (H : LkHeadF E) : (H.headK SK).R.red =
    (drawK E (Prod.mk : H.St → E → H.St × E) Ex (2 ^ H.v - 1)).R.red.seq
      ((H.tie.tieK SK H.n).preM fun x => ((0 : E), x)).R.red := bk_seq_red _ _
theorem tieK_red (D : TieF E) (n : ℕ) :
    (D.tieK SK (n + 1)).R.red = (D.tieK SK n).R.red.seq (D.stepK SK (n + 1)).R.red :=
  bk_chain_red _ _ n
theorem levK_red (D : TreeP E) (l : ℕ) :
    (D.levK SK l).R.red = (SK.full (D.lv l).T.par).R.red.seq (D.lineK Ex l).R.red := bk_seq_red _ _
theorem treeK_red (D : TreeP E) (n : ℕ) :
    (D.treeK SK (n + 1)).R.red = (D.treeK SK n).R.red.seq (D.levK SK (n + 1)).R.red :=
  bk_chain_red _ _ n
theorem chainK_red (Z : PscIn E) : (chainK Z SK).R.red =
    (drawK Z.ev.D Z.nxX Ex Z.ev.err).R.red.seq (SK.full Z.T.par).R.red := bk_seq_red _ _
theorem forestK_red (A : LkAsmH E) (l : ℕ) :
    (A.forestK SK (l + 1)).R.red = (A.forestK SK l).R.red.seq (A.D.levK SK l).R.red :=
  bk_seq_red _ _

/-- The whole chain's reduction is its five blocks' reductions, joined from the left. -/
theorem chnK_red (A : LkAsmH E) : (A.chnK SK).R.red =
    (((((A.H.headK SK).R.red.seq (A.rootK Ex).R.red).seq (A.forestK SK A.d).R.red).seq
      (A.endK SK).R.red).seq (A.bitK SK).R.red) := by
  have h1 := bk_seq_red (A.H.headK SK) (A.rootK Ex)
  have h2 := (bk_seq_red ((A.H.headK SK).seq (A.rootK Ex)) (A.forestK SK A.d)).trans
    (congrArg (fun K => K.seq (A.forestK SK A.d).R.red) h1)
  have h3 := (bk_seq_red (((A.H.headK SK).seq (A.rootK Ex)).seq (A.forestK SK A.d))
    (A.endK SK)).trans (congrArg (fun K => K.seq (A.endK SK).R.red) h2)
  exact (bk_seq_red ((((A.H.headK SK).seq (A.rootK Ex)).seq (A.forestK SK A.d)).seq (A.endK SK))
    (A.bitK SK)).trans (congrArg (fun K => K.seq (A.bitK SK).R.red) h3)

/-! ### each block's out is total -/
variable {SK} (SV : PscLtV SK)

theorem stepK_tot (D : TieF E) (l : ℕ) (h : SV.FullV (D.lv l).T.par) :
    Tot (D.stepK SK l).R (stepV SV D l) := tot_bpost h _
theorem tieK_tot (D : TieF E) (n : ℕ) (h : ∀ l ≤ n, SV.FullV (D.lv l).T.par) :
    Tot (D.tieK SK n).R (tieV SV D n) :=
  tot_chain _ _ _ n fun l hl => stepK_tot SV D l (h l hl)
theorem headK_tot (H : LkHeadF E) (h : ∀ l ≤ H.n, SV.FullV (H.tie.lv l).T.par) :
    Tot (H.headK SK).R (headV SV H) :=
  tot_bseq (tot_draw _ _ _) (tot_bpre (tieK_tot SV H.tie H.n h) _)
theorem levK_tot (D : TreeP E) (l : ℕ) (h : SV.FullV (D.lv l).T.par) :
    Tot (D.levK SK l).R (levV SV D l) := tot_bseq h (tot_draw _ _ _)
theorem treeK_tot (D : TreeP E) (n : ℕ) (h : ∀ l ≤ n, SV.FullV (D.lv l).T.par) :
    Tot (D.treeK SK n).R (treeV SV D n) :=
  tot_chain _ _ _ n fun l hl => levK_tot SV D l (h l hl)
theorem segKK_tot (I : LkInst E) (v' : ℕ) (tK : I.X → E)
    (h : ∀ l ≤ v', SV.FullV ((I.setV (v' + 1)).DK.lv l).T.par) :
    Tot (segKK I v' tK SK).R (segKV SV I v' tK) := tot_bpre (treeK_tot SV _ v' h) _
theorem chainK_tot (Z : PscIn E) (h : SV.FullV Z.T.par) : Tot (chainK Z SK).R (chainKV SV Z) :=
  tot_bseq (tot_draw _ _ _) h

theorem forestK_tot (A : LkAsmH E) (hK : ∀ l ≤ A.v', SV.FullV ((A.IK.setV (A.v' + 1)).DK.lv
    l).T.par)
    (l : ℕ) : (∀ l' < l, SV.FullV (A.D.lv l').T.par) → Tot (A.forestK SK l).R (forestV SV A l) := by
  induction l with
  | zero => exact fun _ => tot_bpost (segKK_tot SV A.IK A.v' _ hK) _
  | succ l ih =>
    intro hT
    exact tot_bseq (ih fun l' h => hT l' (Nat.lt_succ_of_lt h))
      (levK_tot SV A.D l (hT l (Nat.lt_succ_self l)))

theorem chnK_tot (A : LkAsmH E) (h : LtV SV A) : Tot (A.chnK SK).R (chnV SV A) :=
  tot_bseq (tot_bseq (tot_bseq (tot_bseq (headK_tot SV A.H h.tie) (tot_draw _ _ _))
    (forestK_tot SV A h.keys A.d h.tab)) h.clo) (chainK_tot SV A.Bt.zc.toIn h.bit)

theorem baseKS_tot (A : LkAsmH E) (h : LtV SV A) : Tot (A.baseKS SK).R (baseV SV A) :=
  tot_bpost (chnK_tot SV A h) _

/-- The chain's out, for all inputs. -/
theorem chnK_out (A : LkAsmH E) (h : LtV SV A) (a : A.St × Ex.Str) (τ : Tr (A.chnK SK).R.shape) :
    (A.chnK SK).R.red.out a τ = some (chnV SV A a.1 τ, a.2) := (chnK_tot SV A h).red_out a τ

/-- The lookup's verifier's out, for all inputs. -/
theorem baseKS_out (A : LkAsmH E) (h : LtV SV A) (a : A.St × Ex.Str)
    (τ : Tr (A.baseKS SK).R.shape) :
    (A.baseKS SK).R.red.out a τ = some (A.rd (chnV SV A a.1 τ), a.2) :=
  (baseKS_tot SV A h).red_out a τ

end
end
end Tw
#print axioms Tw.chnK_red
#print axioms Tw.chnK_tot
#print axioms Tw.chnK_out
#print axioms Tw.baseKS_out
