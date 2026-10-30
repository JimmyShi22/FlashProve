-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/TokMeans.lean: what the joints of the token sumcheck say, written out, and its numbers.

tok_tsum: the scalar of which the caller's claim speaks before the block is the extension, at the
public point, of the summand's table, plus the mask entry of the first slot. tok_val: the output
claim on an end value says that the map's extension at the drawn point, plus the value's mask entry
times the last drawn element, is what was sent. tok_s0: the public part of the output row is the
summand on the values that were sent. tok_row: the output row written out. tok_nums: the block's
errors are the list TokKind.errs. tok_len: the block has as many rounds as TokKind.rounds lists.
tok_out: the block rejects nothing.

What is not claimed: see Cb/Pv/Head/Tok.lean. The drawn point and the last drawn element stay in the
library's letters (outPt, outB); the hiding polynomial in tok_row stays the library's hU.


-/
import Cb.Pv.Head.Tok
import Cb.G6.Carried

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Tok
open Iop Prob Finset Johnson.L5.Layers Johnson.L5.Door TWhole

section
variable {E : Type} [Field E]

theorem ext_eq_mle (g : ℕ) (v : ℕ → E) (z : Fin g → E) :
    Blocks.ext g v (Blocks.nat z) = Alg.mle (fun b => v (Alg.num b)) z := by
  rw [← Alg.mleN_eq_mle]
  unfold Blocks.ext Alg.mleN
  exact sum_congr rfl fun X _ => by rw [Blocks.eqN_nat]

theorem ext_corner (g : ℕ) (v : ℕ → E) (b : Fin g → Bool) :
    Blocks.ext g v (Blocks.nat (Alg.corner b)) = v (Alg.num b) := by
  rw [ext_eq_mle, Alg.mle_corner]

/-- The summand's table: at an index, the sum of the products of two tables under the weights. -/
def tokAt (k : TokKind) (W : TokWorld E k) (st : TokSt E W.Pb k) (m : W.J → E) (i : ℕ) : E :=
  ∑ j : Fin k.np, st.om j *
    (W.tab st.pb m (k.pairs.get j).1 i * W.tab st.pb m (k.pairs.get j).2 i)

/-- The summand on values of the maps. -/
def tokOn (k : TokKind) (om : Fin k.np → E) (v : Fin k.shown → E) : E :=
  ∑ j : Fin k.np, om j * (v (k.pairs.get j).1 * v (k.pairs.get j).2)

variable [Fintype E]

theorem tok_sum (k : TokKind) (W : TokWorld E k) (τ : E) (st : TokSt E W.Pb k) (m : W.J → E) :
    (tokT k W).SumHolds (τ, st) m ↔
      Blocks.ext k.vars (tokAt k W st m) (Blocks.nat st.pt) + m (W.msk k.sCl) = τ := by
  rw [ldPartPsc_sum E, ext_eq_mle]
  have e : ∀ b : Fin k.vars → Bool,
      (tokSm k W).val st m (Alg.corner b) = tokAt k W st m (Alg.num b) := by
    intro b
    unfold LdPartSm.val LdPartSm.pol tokAt
    rw [List.map_map, Fin.sum_univ_def]
    refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      ext_corner]
  have s : ∑ j, (tokMk k W).slS st j * m j = m (W.msk k.sCl) := by
    simp
  simp only [e]
  rw [s]
  rfl

/-- What the caller's claim speaks of before the block. -/
theorem tok_tsum (k : TokKind) (W : TokWorld E k) (st : TokSt E W.Pb k) (m : W.J → E) :
    Cb.Pv.Lay.tsum (tokT k W).par st m =
      Blocks.ext k.vars (tokAt k W st m) (Blocks.nat st.pt) + m (W.msk k.sCl) :=
  ((tok_sum k W _ st m).1
    ((psc_our_sum E (tokT k W) (_, st) m).1 (Cb.Pv.Lay.tsum_holds (tokT k W).par st m))).symm

/-- What the output claim on an end value says. -/
theorem tok_val (k : TokKind) (W : TokWorld E k) (o : (tokT k W).par.Out) (m : W.J → E)
    (a : Fin k.shown) :
    (tokT k W).par.EHolds o m a ↔
      Blocks.ext k.vars (W.tab (TokSt.pb (k := k) o.st) m a)
          (Blocks.nat ((tokSm k W).outPt (tokMk k W) o)) +
        m (W.msk (k.sEnd + a)) * (tokSm k W).outB (tokMk k W) o = o.vals a :=
  ldPartPsc_val E _ _ (tokSm k W) (tokMk k W) o m a

/-- A map at the drawn point, in the library's letters for a point, is the extension of its table at
outPt. -/
theorem tok_F (k : TokKind) (W : TokWorld E k) (o : (tokT k W).par.Out) (m : W.J → E)
    (a : Fin k.shown) :
    (tokT k W).F o.st m a ((tokT k W).ini o.st ((tokT k W).par.hp o.st o.pt)) =
      Blocks.ext k.vars (W.tab (TokSt.pb (k := k) o.st) m a)
        (Blocks.nat ((tokSm k W).outPt (tokMk k W) o)) := by
  unfold LdPartSm.outPt
  rw [← ldPartVars_ini E (tokSm k W).k (tokMk k W).n
    (ldPartDat E (tokSm k W).k (tokMk k W).n ((tokSm k W).w o.st))
    (pDummy E (tokMk k W).DY) (pDummyD E (tokMk k W).DY) o.pt]
  rfl

/-- The last coordinate of the drawn point is outB. -/
theorem tok_lst (k : TokKind) (W : TokWorld E k) (o : (tokT k W).par.Out) :
    (tokT k W).lst o.st ((tokT k W).par.hp o.st o.pt) = (tokSm k W).outB (tokMk k W) o := by
  unfold LdPartSm.outB
  rw [← ldPartVars_last E (tokSm k W).k (tokMk k W).n
    (ldPartDat E (tokSm k W).k (tokMk k W).n ((tokSm k W).w o.st))
    (pDummy E (tokMk k W).DY) (pDummyD E (tokMk k W).DY) o.pt]
  rfl

/-- The public part of the output row: the summand on the values that were sent. -/
theorem tok_s0 (k : TokKind) (W : TokWorld E k) (o : (tokT k W).par.Out) :
    (tokT k W).par.S0 o.st ((tokT k W).par.hp o.st o.pt) o.vals =
      tokOn k (TokSt.om (k := k) o.st) o.vals := by
  rw [ldPartPsc_s0 E _ _ (tokSm k W) (tokMk k W) o]
  unfold LdPartSm.pol tokOn
  rw [List.map_map, Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  simp only [Function.comp, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-- The form that comes in with the claim reads the mask entry of the first slot. -/
theorem tok_inc (k : TokKind) (W : TokWorld E k) (st : TokSt E W.Pb k) (m : W.J → E) :
    (tokT k W).par.inc st m = m (W.msk k.sCl) := by
  show ∑ j, (if j = W.msk k.sCl then (1 : E) else 0) * m j = _
  simp

/-- What the output row on the hiding polynomial's coefficients says: the hiding polynomial at the
drawn point, plus the drawn factor times the product of the public polynomials times the mask entry
of the first slot, is the last value less the factor times the summand on the values that were
sent. -/
theorem tok_row (k : TokKind) (W : TokWorld E k) (o : (tokT k W).par.Out) (m : W.J → E) :
    (tokT k W).par.UHolds o m ↔
      hU ((tokT k W).par.vars o.st) ((tokT k W).par.W o.st m) ((tokT k W).par.hp o.st o.pt) +
          o.eps * hPsi ((tokT k W).par.vars o.st) ((tokT k W).par.hp o.st o.pt) *
            m (W.msk k.sCl) =
        o.fin - o.eps * tokOn k (TokSt.om (k := k) o.st) o.vals := by
  have hz : (∑ b, (tokT k W).par.S1 o.st ((tokT k W).par.hp o.st o.pt) o.vals b *
      (tokT k W).par.Gb o.st m b ((tokT k W).par.hp o.st o.pt)) = 0 :=
    Finset.sum_eq_zero fun b _ => Empty.elim b
  unfold PscPar.UHolds
  rw [hz, mul_zero, add_zero, tok_s0, tok_inc]

/-- The block rejects no transcript, so its soundness property is not empty. -/
theorem tok_out (k : TokKind) (W : TokWorld E k) (Ex : ExtSpec) (x : TokSt E W.Pb k) (y : Ex.Str)
    (τ : Tr (tokR k W Ex).shape) : ∃ b, (tokR k W Ex).out x y τ = some b := by
  obtain ⟨o, ho⟩ := short_accepts (tokT k W).par Ex (rTarget (tokT k W).par τ, x)
    (F₀ (tokT k W).par x) (F₀_ok _ (tok_eq0 k W) x) y (unride (tokT k W).par τ)
  exact ⟨_, congrArg (Option.map fun o => ((x, rTarget (tokT k W).par τ), o)) ho⟩

theorem fmt_nums : ∀ g : ℕ, (ldPartFmt E g fun _ => 2).map PFmt.n = List.replicate g 2
  | 0 => rfl
  | g + 1 => congrArg (2 :: ·) (fmt_nums g)

theorem errList_len : ∀ {s : Shape} (ε : Err s), (errList ε).length = s.length
  | [], _ => rfl
  | _ :: _, (_, ε) => congrArg (· + 1) (errList_len ε)

/-- The block's errors are the written list. -/
theorem tok_nums (k : TokKind) (W : TokWorld E k) (Ex : ExtSpec) :
    errList (tokErr k W Ex) = k.errs := by
  have h : errList (errS (tokT k W).par) = (tokT k W).par.fmt.map PFmt.n ++ [0] :=
    errList_s (tokT k W).par (tokT k W).par.fmt
  have f : (tokT k W).par.fmt.map PFmt.n = List.replicate k.vars 2 ++ [2] := by
    show ((ldPartFmt E k.vars fun _ => 2) ++ [pDummy E 2]).map PFmt.n = _
    rw [List.map_append, fmt_nums]
    rfl
  show 1 :: errList (errS (tokT k W).par) = _
  rw [h, f]
  rfl

/-- The block has as many rounds as the written list. -/
theorem tok_len (k : TokKind) (W : TokWorld E k) (Ex : ExtSpec) :
    (tokR k W Ex).shape.length = k.rounds.length := by
  have e : (errList (tokErr k W Ex)).length = (tokR k W Ex).shape.length := errList_len _
  rw [← e, tok_nums]
  simp [TokKind.errs, TokKind.rounds]

end

end Cb.Pv.Head.Tok

#print axioms Cb.Pv.Head.Tok.tok_sum
#print axioms Cb.Pv.Head.Tok.tok_tsum
#print axioms Cb.Pv.Head.Tok.tok_val
#print axioms Cb.Pv.Head.Tok.tok_s0
#print axioms Cb.Pv.Head.Tok.tok_row
#print axioms Cb.Pv.Head.Tok.tok_out
#print axioms Cb.Pv.Head.Tok.tok_nums
#print axioms Cb.Pv.Head.Tok.tok_len
