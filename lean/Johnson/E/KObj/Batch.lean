-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/Batch.lean: typed lists of blocks for the instances of a batch.

Definitions, statements and proofs; every proof is a call of the library's rules on `IOR.KnowB` and
`IOR.KnowBInto` (Ior/BatchSeq.lean, Ior/KnowWideB.lean).

Main names:
  `KObj.JB`: a joint with `adm`: what the statements of one batch have in common.
  `KObj.BB`: a bare block with an annotation of its rounds (local or shared) and the extractor's
    value where the verifier rejects.
  `KObj.BB.GoodC`: point queries, locality, a coherent annotation, `KnowBInto`. `KObj.BB.Good`:
    that, and `adm` is carried.
  `KObj.LB`, `KObj.LB.blk`: a typed list and its one block: reductions, annotations and errors in a
    row.
  `KObj.LB.good`: if every block has its property, the list's one block has `GoodC`.
  `KObj.BB.ofLocal`, `KObj.BB.good_ofLocal`: a plain block with its property is a batch block with
    its property, in local rounds, at the same errors, for any `adm` that it carries.
Limits: "in local rounds" is a claim on the protocol: a plain block enters at the same errors only
as rounds in which every slot has its own verifier message. If one message is drawn for a whole
batch, the block is a shared one and its price is another (Johnson/E/KObj/BatchShared.lean
[not in this library]).
Nothing is said of any value.
-/
import Johnson.E.KObj.Blocks
import Ior.KnowWideB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob IOR

variable {N : ℕ}

/-- (B1) a batch joint -/
structure JB (N : ℕ) : Type 1 where
  J   : JK
  adm : (Fin N → Option (J.X × J.E.Str)) → Prop

/-- a batch block -/
structure BB (A B : JB N) : Type 1 where
  b   : BK A.J B.J
  ann : RoundSplits b.R.shape
  d   : A.J.W

/-- what a list's one block has -/
structure BB.GoodC {A B : JB N} (x : BB A B) : Prop where
  point   : Nonempty x.b.R.shape.IsPoint
  isLocal : x.b.R.IsLocal
  coh     : x.ann.Coherent
  know    : x.b.R.KnowBInto x.ann N A.adm A.J.on B.J.on A.J.relR B.J.relR x.b.ext x.b.err

/-- the property of a batch block: that, and adm is carried -/
structure BB.Good {A B : JB N} (x : BB A B) : Prop extends x.GoodC where
  adm : ∀ a, A.adm a → ∀ τ : BTr N x.b.R.shape x.ann,
    B.adm fun j => (a j).bind fun aj => x.b.R.red.out aj (τ.slot j)

/-- two in a row -/
noncomputable def BB.seq {A B C : JB N} (x : BB A B) (y : BB B C) : BB A C where
  b := x.b.seq y.b x.d
  ann := RoundSplits.app x.ann y.ann
  d := x.d

theorem BB.goodC_seq {A B C : JB N} (x : BB A B) (y : BB B C) (hx : x.Good) (hy : y.GoodC) :
    (x.seq y).GoodC where
  point := hx.point.elim fun p₁ => hy.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩
  isLocal := hx.isLocal.seq hy.isLocal
  coh := RoundSplits.app_coherent hx.coh hy.coh
  know := by
    refine knowBInto_seq_ext _ _ _ _ _ _ _ _ _ x.b.R y.b.R x.ann y.ann N A.adm B.adm A.J.on B.J.on
      C.J.on A.J.relR B.J.relR C.J.relR x.b.ext y.b.ext _ x.b.err y.b.err hx.know hy.know hx.adm
      fun a τ b w hb => ?_
    have hb' : Option.map (fun xo => (xo, x.b.R.imp a.2 (Tr.fst τ)))
        (x.b.R.out a.1 a.2 (Tr.fst τ)) = some b := hb
    show IOR.extSeq x.b.R y.b.R x.b.ext y.b.ext x.d a τ w = _
    simp only [IOR.extSeq, Reduction.extSeq]
    rw [hb']

/-- (B3) a typed list of batch blocks -/
inductive LB : JB N → JB N → Type 1
  | one {A B : JB N} (x : BB A B) : LB A B
  | cons {A B C : JB N} (x : BB A B) (l : LB B C) : LB A C

namespace LB

/-- every block has its property; of the last one "adm is carried" is not asked -/
def Each : {A B : JB N} → LB A B → Prop
  | _, _, .one x => x.GoodC
  | _, _, .cons x l => x.Good ∧ l.Each

/-- THE ONE BLOCK OF A LIST -/
noncomputable def blk : {A B : JB N} → LB A B → BB A B
  | _, _, .one x => x
  | _, _, .cons x l => x.seq l.blk

theorem each_one {A B : JB N} (x : BB A B) : (LB.one x).Each ↔ x.GoodC := by rw [LB.Each]
theorem each_cons {A B C : JB N} (x : BB A B) (l : LB B C) :
    (LB.cons x l).Each ↔ x.Good ∧ l.Each := by rw [LB.Each]
theorem blk_one {A B : JB N} (x : BB A B) : (LB.one x).blk = x := by rw [LB.blk]
theorem blk_cons {A B C : JB N} (x : BB A B) (l : LB B C) :
    (LB.cons x l).blk = x.seq l.blk := by rw [LB.blk]

/-- (B4) -/
theorem good {A B : JB N} (l : LB A B) : l.Each → l.blk.GoodC := by
  induction l with
  | one x =>
    intro h
    rw [blk_one]
    exact (each_one x).1 h
  | cons x l ih =>
    intro h
    rw [blk_cons]
    exact BB.goodC_seq x _ ((each_cons x l).1 h).1 (ih ((each_cons x l).1 h).2)

end LB

/-- (B5) a plain block in every slot, in local rounds -/
@[reducible] def BB.ofLocal {A B : JK} (b : BK A B) (d : A.W)
    (admA : (Fin N → Option (A.X × A.E.Str)) → Prop) (admB : (Fin N → Option (B.X × B.E.Str)) →
        Prop) :
    BB (⟨A, admA⟩ : JB N) ⟨B, admB⟩ :=
  ⟨b, RoundSplits.const RAnn.allLocal b.R.shape, d⟩

theorem BB.goodC_ofLocal {A B : JK} (b : BK A B) (d : A.W)
    (admA : (Fin N → Option (A.X × A.E.Str)) → Prop) (admB : (Fin N → Option (B.X × B.E.Str)) →
        Prop)
    (h : b.Good) : (BB.ofLocal b d admA admB).GoodC where
  point := h.point
  isLocal := h.isLocal
  coh := RoundSplits.const_coherent (f := RAnn.allLocal) (fun r => RAnn.ofSlot_coherent .lo r) _
  know := knowB_conseq _ _ _ _ _ _ b.R _ N (fun _ => True) admA A.on A.on A.relR A.relR _ _ b.ext
      b.err
    (knowB_local _ _ _ _ _ _ b.R RAnn.allLocal (fun _ => rfl) N A.on A.relR
      (Reduction.orOff B.on B.relR) b.ext b.err h.know)
    (fun _ _ => trivial) (fun _ ha => ha) (fun _ _ _ hw => hw) (fun _ _ hw => hw)

theorem BB.good_ofLocal {A B : JK} (b : BK A B) (d : A.W)
    (admA : (Fin N → Option (A.X × A.E.Str)) → Prop) (admB : (Fin N → Option (B.X × B.E.Str)) →
        Prop)
    (h : b.Good)
    (hadm : ∀ a, admA a → ∀ τ : BTr N b.R.shape (RoundSplits.const RAnn.allLocal b.R.shape),
      admB fun j => (a j).bind fun aj => b.R.red.out aj (τ.slot j)) :
    (BB.ofLocal b d admA admB).Good :=
  { BB.goodC_ofLocal b d admA admB h with adm := hadm }

#print axioms KObj.BB.goodC_seq
#print axioms KObj.LB.good
#print axioms KObj.BB.goodC_ofLocal
#print axioms KObj.BB.good_ofLocal

end KObj
