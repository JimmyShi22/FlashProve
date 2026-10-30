-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/ObjBits.lean: the object that four sub-protocols with records form, taken at a record, and
the numbers on its three lists of rounds.

Definitions and statements; the proofs are in Cond/ObjBitsProof.lean.

Main names:
  `Err.sumPr`: the sum of the errors of a list, as probabilities.
  `SubsR.obj S r`: the object at the record r, an `BatchProtocol` (Iop/Batch.lean); `witAt`: its witness map.
  `SubsR.Bits`: numbers of test bits for the rounds of the five lists, with `Bits.T`, `Bits.L`,
    `Bits.B` on the shapes of the object.
  `Nums.errT`, `errL`, `errB`: the three lists of errors on the shapes of the object.
  `Nums.BelowG g c`: all five lists meet `Err.BelowG` at c, each with the bits that g gives it.
  `Nums.total`: the sum of all round errors of the five lists, without proof of work.
  `SubsR.Wk`: the proof of work by the names of the sub-protocols' rounds; `Wk.at`, `wkAt`: in the
    compiler's form; `Nums.BelowO`: what is asked of the lists with proof of work.

Limits: this file does not say that any sub-protocols have such lists. No object is named, no number
chosen.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecMainProof
import Hiop.WholeProof
import Hiop.RecSoundProof
import CompileK.WideLang
import Ior.GrindKLists
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open scoped ENNReal

/-- The sum of the errors of a list, as probabilities. -/
def Err.sumPr : {s : Shape} → Err s → ℝ≥0∞
  | [], _ => 0
  | r :: _, (e, ε) => (e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞) + Err.sumPr ε

end Iop

namespace Hiop
open Iop Prob
open scoped ENNReal

namespace SubsR
variable {C : ConfigurationWithOutOfDomainSample} (S : SubsR C)

/-- The object at the record r: an `BatchProtocol` (Iop/Batch.lean), which has no records. -/
abbrev obj (r : C.Rec) : BatchProtocol C.I C.X := S.lhr.atRec r

/-- Its witness map. It is wide: it may read the whole local transcript. -/
abbrev witAt (r : C.Rec) :
    C.X → (oneExternalString (S.obj r).wordLength (S.obj r).Symbol).Str → Tr (S.obj r).onlineBatch.loc.shape → C.Cells :=
  fun x y τ => S.wit (x, r) y τ

/-- Numbers of test bits for the rounds of the five lists. -/
structure Bits where
  wf     : GBits S.wf.shape
  linOff : GBits S.linOff.shape
  link   : GBits S.link.shape
  req    : GBits S.req.shape
  linOn  : GBits S.linOn.ior.shape

variable {S}

/-- The three lists of bits on the shapes of the object. -/
def Bits.T (g : S.Bits) (r : C.Rec) : GBits (S.obj r).offline.shape :=
  (GBits.app g.wf g.linOff : GBits (S.wf.shape ++ S.linOff.shape))
def Bits.L (g : S.Bits) (r : C.Rec) : GBits (S.obj r).link.shape := g.link
def Bits.B (g : S.Bits) (r : C.Rec) : GBits (S.obj r).onlineBatch.loc.shape :=
  (GBits.app g.req g.linOn : GBits (S.req.shape ++ S.linOn.ior.shape))

/-- The three lists of errors on the shapes of the object. -/
def Nums.errT (P : S.Nums) (r : C.Rec) : Err (S.obj r).offline.shape :=
  (Err.app P.wf.err P.linOff.err : Err (S.wf.shape ++ S.linOff.shape))
def Nums.errL (P : S.Nums) (r : C.Rec) : Err (S.obj r).link.shape := P.link.err
def Nums.errB (P : S.Nums) (r : C.Rec) : Err (S.obj r).onlineBatch.loc.shape :=
  (Err.app P.req.err P.linOn.err : Err (S.req.shape ++ S.linOn.ior.shape))

/-- All five lists meet `Err.BelowG` (Iop/Grind.lean) at c, each with the bits that g gives it. -/
structure Nums.BelowG (P : S.Nums) (g : S.Bits) (c : ℝ≥0∞) : Prop where
  wf     : Err.BelowG g.wf P.wf.err c
  linOff : Err.BelowG g.linOff P.linOff.err c
  link   : Err.BelowG g.link P.link.err c
  req    : Err.BelowG g.req P.req.err c
  linOn  : Err.BelowG g.linOn P.linOn.err c

/-- The stricter count: the sum of all round errors of the five lists, without proof of work. -/
def Nums.total (P : S.Nums) : ℝ≥0∞ :=
  P.wf.err.sumPr + P.linOff.err.sumPr + P.link.err.sumPr + P.req.err.sumPr + P.linOn.err.sumPr

variable (S) in
/-- The proof of work, by the names of the sub-protocols' rounds. -/
structure Wk (Nn : Type) where
  Dg : GrData Nn
  nb : ℕ
  g  : S.Bits

/-- The proof of work in the compiler's form (`Compile.Batch.Work`). -/
def Wk.at {Nn : Type} (w : S.Wk Nn) (r : C.Rec) : Compile.Batch.Work Nn (S.obj r) :=
  ⟨w.Dg, w.nb, w.g.T r, w.g.L r, w.g.B r⟩

/-- The same for an option. -/
def wkAt {Nn : Type} (r : C.Rec) (o : Option (S.Wk Nn)) :
    Option (Compile.Batch.Work Nn (S.obj r)) :=
  o.map fun w => w.at r

/-- What is asked of the lists with proof of work; without it nothing is asked. -/
def Nums.BelowO {Nn : Type} (P : S.Nums) (c : ℝ≥0∞) : Option (S.Wk Nn) → Prop
  | none => True
  | some w => P.BelowG w.g c

end SubsR
end Hiop

noncomputable section

namespace TopC
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.ProgDraw Hiop
open Compile.BatchLife (Sims)
open scoped ENNReal

namespace Spec

/-- States that every error of a list, as a probability, is at most any bound on the sum of its
errors. `err_sumPr_app` states the sum of two lists in a row. -/
def err_below_sumPr : Prop := ∀ (s : Shape) (ε : Err s) (c : ℝ≥0∞), ε.sumPr ≤ c → Err.Below ε c
def err_sumPr_app : Prop :=
  ∀ (s t : Shape) (ε : Err s) (ε' : Err t), (Err.app ε ε').sumPr = ε.sumPr + ε'.sumPr

/-- States that the stricter count bounds every round, with and without proof of work; it is the sum
over the three lists of the object. -/
def target_below_total : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums),
    P.Below P.total ∧
    (∀ g : S.Bits, P.BelowG g P.total) ∧
    ∀ r : C.Rec, P.total = (P.errT r).sumPr + (P.errL r).sumPr + (P.errB r).sumPr

/-- What ε is. -/
def target_eps : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b : ℕ) (εs : ℝ≥0∞)
      (r : C.Rec) (lam : ℕ) (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ)
      (o : Option (S.Wk Nn)) (c : ℝ≥0∞) (tC tP : ℕ),
    epsB (D.WO (SubsR.wkAt r o)) (D.numsO (P.lh b εs) κ₀ n c (SubsR.wkAt r o)) tC tP =
      ((tC + tP + tVB (D.WO (SubsR.wkAt r o)) + 1 : ℕ) : ℝ≥0∞) *
          (κ₀ ^ D.dr.K * (if o.isSome then c else εs)) +
        2 * ((tC + tP + tVB (D.WO (SubsR.wkAt r o)) + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

end Spec
end TopC
