-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/Merge.lean: the merge of the output head's sub-proof as a typed block, with its knowledge
soundness.

The programs' verifier (wsForkMerge in OnBytes/Model/Merge.lean, called by the head's check with one
claim on the committed weights) draws one element, of which it uses the powers below the number of
claims: with one claim that is the power 0 alone, so nothing reads the element. Then comes a masked
sumcheck with lk plain rounds of degree 2, one for each column bit of the matrix, a round of degree
1 in the further variable Y, and one end value. In a plain round the linear coefficient is the one
that is not sent; in the round in Y it is the constant one. The claim: the sum over the corners b of
the cube of fv(b) equals a hidden value that was shown earlier, under a mask.

Here the sumcheck is a value of the library's masked sumcheck (Cb/Ld/LdPsc.lean: PscOur, through the
builder of Cb/Part/LdPartPsc.lean) with short messages. The summand is one map fv, a letter: a
function of the public state, the committed entries and the point, of degree at most 2 in each
variable. tg is the scalar that was shown for the hidden value; slS is that value's mask, as a form
(its factor at its mask entry); cAt is the mask entry of the end value, which may lie in another
message than the sub-proof's mask row.

Main names: fixPl, fixPl_ok (which coefficients are left out, and that this is lawful); MergeAt (the
letters at a size); MergeAt.R, A, B, err (the block, its joints, its errors); merge_knowAt; HMerge,
hMerge (the property in the form of a named hypothesis, and its proof); merge_nums; merge_out (the
block never rejects); merge_sum (what the claim before the block says).

The same sumcheck stands in Cb/Pv/Lay/Merge.lean (MergeL), written for the layers. This file's is a
value of it, by definition; its block has one draw more, in front.

Not claimed. Nothing on hiding. What fv reads, that the programs' routine computes this block's
output, and what becomes of the row on the end value are said elsewhere. More claims than one are
not treated. Completeness is not stated here.

-/
import Cb.G6.Value
import Cb.G6.Join
import Cb.Part.LdPartPscProofs
import Cb.Ld.LdPscProofsOur

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Merge
open Iop Prob Cb TWhole Johnson.L5.Layers Johnson.L5.Door

noncomputable section

section Pick
variable (E : Type) [Field E] [Fintype E]

/-- The variables: k plain ones of degree 2, then Y of degree D. -/
abbrev plVars (D k : ℕ) : List (HVar E) :=
  pVars (ldPartFmt E k (fun _ => 2) ++ [pDummy E D])
    (PDats.snoc (ldPartFmt E k fun _ => 2) (ldPartDat E k (fun _ => 2) fun _ => none)
      (pDummy E D) (pDummyD E D))

/-- In a plain round the linear coefficient is left out, in the round in Y the constant one; both
inverses are 1. -/
def fixPl (D : ℕ) : (k : ℕ) → HFixs (plVars E D k)
  | 0 => (((0 : Fin (D + 1)), (1 : E)), ())
  | k + 1 => (((1 : Fin 3), (1 : E)), fixPl D k)

theorem fixPl_ok (D : ℕ) : ∀ k : ℕ, HFixs.OK (plVars E D k) (fixPl E D k)
  | 0 =>
    ⟨by
      show (1 : E) * ∑ _x : Unit, (1 : E) * (0 : E) ^ (((0 : Fin (D + 1)) : ℕ)) = 1
      simp, trivial⟩
  | k + 1 =>
    ⟨by
      show (1 : E) * ∑ b : Bool, (1 : E) * (if b then (1 : E) else 0) ^ (1 : ℕ) = 1
      rw [Fintype.sum_bool]
      simp, fixPl_ok D k⟩

theorem fmt_ns : ∀ (k c : ℕ), (ldPartFmt E k fun _ => c).map PFmt.n = List.replicate k c
  | 0, _ => rfl
  | k + 1, c => congrArg (c :: ·) (fmt_ns k c)

end Pick

/-- All that a size of this kind of block is made of, but for the number lk of column bits. St: the
statements before the block. -/
structure MergeAt (E St J M Wp Kc : Type) [Field E] [Fintype E] (Ex : ExtSpec) (lk : ℕ) where
  /-- what was shown for the hidden value that the sum must equal -/
  tg : St → E
  /-- the summand -/
  fv : St → (J → E) → (Fin lk → E) → E
  deg : ∀ st m, Alg.DegLE (fun _ => 2) (fv st m)
  /-- the mask of the hidden value, as a form in the entries -/
  slS : Slf E St J
  /-- the places of the hiding polynomial's coefficients and of the end value's mask -/
  wAt : PIdx (ldPartFmt E lk (fun _ => 2) ++ [pDummy E 1]) → J
  cAt : J
  /-- the base joint that rides along, and how the committed messages are read as entries -/
  A0 : IOR.Rels Kc St Ex (M × Wp)
  msg : M → J → E

variable {E St J M Wp Kc : Type} [Field E] [Fintype E] [Fintype J] {Ex : ExtSpec} {lk : ℕ}
  (a : MergeAt E St J M Wp Kc Ex lk)

@[reducible] def MergeAt.sm : LdPartSm E St J where
  k := lk
  A := Unit
  F := fun st m _ z => a.fv st m z
  terms := [⟨fun _ _ => 1, [()]⟩]
  w := fun _ _ => none

@[reducible] def MergeAt.mk' : LdPartMk a.sm := ⟨fun _ => 2, 1, a.slS, a.wAt, fun _ => a.cAt⟩

omit [Fintype J] in
theorem merge_part : a.sm.OK a.mk' (fun _ _ => 2) where
  map := fun st m _ => a.deg st m
  fit := fun t ht => by
    rw [List.mem_singleton.1 ht]
    exact ⟨fun _ => 0, fun _ => Alg.DegLE.const _ _, fun _ => Nat.le_refl 2⟩
  plain := fun _ _ _ => Nat.le_succ 1
  dy := fun t ht => by
    rw [List.mem_singleton.1 ht]
    exact Nat.le_refl 1

/-- The sumcheck, as the library's instance with the further variable Y, and as parameters of its
block; which coefficients are left out. -/
abbrev MergeAt.T : PscOur E := a.sm.our a.mk'
abbrev MergeAt.Y : PscPar E := a.T.par
abbrev MergeAt.F : ∀ st, HFixs (a.Y.vars st) := fun _ => fixPl E 1 lk

theorem merge_pick : ∀ st, HFixs.OK (a.Y.vars st) (a.F st) := fun _ => fixPl_ok E 1 lk

theorem merge_conds : a.Y.VarsOK ∧ a.Y.DegOK ∧ a.Y.ValInj := by
  obtain ⟨hV, hI, hX, hY⟩ := ldPartPsc_ok E _ _ _ _ _ (merge_part a)
  exact ⟨(psc_our_ok E a.T).1 hV, psc_our_deg E a.T hX hY, (psc_our_ok E a.T).2 hI⟩

/-- The draw's step: the sumcheck's target and state. The drawn element is read by nothing. -/
abbrev MergeAt.nx : St → E → E × St := fun x _ => (a.tg x, x)

/-- The block: the draw, then the sumcheck with short messages. -/
abbrev MergeAt.R : IOR St Ex a.Y.Out Ex := (IOR.draw E a.nx Ex).seq (shortR a.Y a.F Ex)

/-- The joints: before the block the sum claim at the shown scalar; between the draw and the
sumcheck, and behind the block, the sumcheck's own. -/
abbrev MergeAt.A : IOR.Rels Kc St Ex (M × Wp) :=
  a.Y.baseRels a.A0 (fun w : M × Wp => a.msg w.1) (fun x => x)
    fun x m => a.Y.SumHolds (a.tg x, x) m
abbrev MergeAt.Mid : IOR.Rels Kc (E × St) Ex (M × Wp) := a.Y.baseIn a.A0 fun w => a.msg w.1
abbrev MergeAt.B : IOR.Rels Kc a.Y.Out Ex (M × Wp) := a.Y.baseOut a.A0 fun w => a.msg w.1

abbrev MergeAt.err : Err a.R.shape :=
  Err.app (IOR.Nums.draw Kc E a.nx Ex 0).err (shortE a.Y Ex)

theorem merge_draw :
    KnowAt (IOR.draw E a.nx Ex) a.A a.Mid (fun _ _ _ wp => wp)
      (IOR.Nums.draw Kc E a.nx Ex 0).err :=
  knowAt_draw a.nx a.A a.Mid 0 (fun _ _ _ h => h) fun _ _ _ _ =>
    le_of_eq (cnt_false fun _ hb => by
      obtain ⟨_, h1, h2⟩ := hb
      exact h2 h1)

theorem merge_knowAt : KnowAt a.R a.A a.B (fun _ _ _ wp => wp) a.err :=
  knowAt_seq (merge_draw a)
    (short_knowAt a.Y a.F Ex (merge_conds a).1 (merge_conds a).2.1 (merge_conds a).2.2 M Wp Kc
      a.A0 a.msg)

/-- The property of this kind of block, in the form of a named hypothesis: at each size of a
written list, knowledge soundness for each fixed tuple of committed messages. -/
def HMerge (sizes : List ℕ) (at' : ∀ lk, MergeAt E St J M Wp Kc Ex lk) : Prop :=
  ∀ s ∈ sizes, ∀ m, (at' s).R.red.Know (at' s).A.on (fun x wp => (at' s).A.relR x (m, wp))
    (fun b wp => (at' s).B.relR b (m, wp)) (fun _ _ wp => wp) (at' s).err

/-- It holds, at every size. -/
theorem hMerge (sizes : List ℕ) (at' : ∀ lk, MergeAt E St J M Wp Kc Ex lk) :
    HMerge sizes at' := fun s _ m => (merge_knowAt (at' s)).know m

theorem merge_degs : a.Y.fmt.map PFmt.n = List.replicate lk 2 ++ [1] :=
  (psc_our_degs E a.T).trans (congrArg (· ++ [1]) (fmt_ns E lk 2))

/-- The errors, as counts of draws: 0 for the batching element, 1 for eps, 2 for each column bit,
1 for Y, 0 for the end value. -/
theorem merge_nums : errList a.err = 0 :: 1 :: ((List.replicate lk 2 ++ [1]) ++ [0]) :=
  (errList_app _ _).trans (congrArg (fun l => 0 :: l)
    ((shortE_nums a.Y Ex).trans (congrArg (fun l => 1 :: (l ++ [0])) (merge_degs a))))

/-- The block never rejects. -/
theorem merge_out (x : St × Ex.Str) (τ : Tr a.R.shape) : ∃ b, a.R.red.out x τ = some b :=
  ⟨_, (ior_seq_some (IOR.draw E a.nx Ex) (shortR a.Y a.F Ex)
    (fun x _ => ((a.tg x.1, x.1), x.2)) (fun _ _ => rfl) x τ).trans
      (short_red_out a.Y a.F Ex (merge_pick a) _ _)⟩

/-- What the claim before the block says: the sum of fv over the corners, plus the mask's form, is
the shown scalar. -/
theorem merge_sum (st : St) (m : J → E) :
    a.Y.SumHolds (a.tg st, st) m ↔
      ∑ b : Fin lk → Bool, a.fv st m (Alg.corner b) + ∑ j, a.slS st j * m j = a.tg st := by
  refine ((psc_our_sum E a.T (a.tg st, st) m).trans
    (ldPartPsc_sum E _ _ _ _ (a.tg st) st m)).trans ?_
  have e : ∀ b : Fin lk → Bool,
      (∏ i, ldPartWt (a.sm.w st i) (b i)) * a.sm.val st m (Alg.corner b) =
        a.fv st m (Alg.corner b) := by
    intro b
    have h1 : (∏ i, ldPartWt (a.sm.w st i) (b i)) = 1 := Finset.prod_eq_one fun _ _ => rfl
    rw [h1, one_mul]
    show (1 * (a.fv st m (Alg.corner b) * 1) + 0 : E) = _
    rw [mul_one, one_mul, add_zero]
  simp only [e]

end

end Cb.Pv.Head.Merge
