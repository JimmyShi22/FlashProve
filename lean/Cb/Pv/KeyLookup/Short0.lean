-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Short0.lean: the short sumcheck as a value of the letter PscLtK.

Definitions, statements and proofs. PscLtK (Cb/Pv/Lookup/Know/LtK.lean) is the sumcheck as a letter:
for
every PscPar a verifier and its errors. SK₀ fills it with the short block of
Cb/G6/Carried.lean and Cb/G6/Core.lean at the pick F₀ (Cb/G6/Pick.lean):
in
every round with a polynomial the coefficient of power 0 is not sent. No honest side is named.

Main names:
  SK₀ E Ex : PscLtK E Ex := ⟨fun Y => ⟨shortR Y (F₀ Y) Ex, shortE Y Ex⟩,
    fun Y => ⟨shortRC Y (F₀ Y) Ex, shortEC Y Ex⟩⟩.
  Each of the following has the statement of its twin at PscLtK.lib, with SK₀ in its place.
  SK₀_fullK, SK₀_coreK: under Y.VarsOK, Y.DegOK, Y.ValInj, and no premise on the pick: FullK, CoreK.
  SK₀_ourK: under T.VarsOK, T.DegX, T.DegY, T.ValInj: FullK at T.par.
  SK₀_passes, SK₀_copies, SK₀_passesC, SK₀_copiesC: the verifier passes its state on and only copies
    its oracles: no premise.
  SK₀_errs, SK₀_vals, SK₀_errsC, SK₀_valsC: read by Err.toList and Shape.chalList, its errors and
    numbers of values are those of PscLtK.lib.
  SK₀_ll: a sumcheck with k cube variables and the further variable: pscErrs k n DY, pscVals q k.
  SK₀_out, SK₀_outC: under TWhole.Eq0 Y (every variable's weights sum to 1) the verifier rejects
    nothing: out x y τ = some (shortV Y (F₀ Y) x τ), some (shortVC Y (F₀ Y) x τ).
  errList_toList: errList of Cb/G6/Cut.lean is Err.toList.

Limits: at a Y without Eq0 the block is knowledge sound and rejects; SK₀_out does not apply there.

-/
import Cb.G6.Pick
import Cb.G6.Value
import Cb.Pv.Lookup.Know.LtK
import Cb.Ld.LdLkpAsmErrProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.LdLkp.Kn Johnson.L5.Layers

noncomputable section
variable (E : Type) [Field E] [Fintype E] (Ex : ExtSpec)

/-- The short sumcheck, at the pick «power 0», as a value of the letter. -/
def SK₀ : PscLtK E Ex :=
  ⟨fun Y => ⟨TWhole.shortR Y (TWhole.F₀ Y) Ex, TWhole.shortE Y Ex⟩,
    fun Y => ⟨TWhole.shortRC Y (TWhole.F₀ Y) Ex, TWhole.shortEC Y Ex⟩⟩

end

/-- `TWhole.errList` is `Err.toList`. -/
theorem errList_toList : ∀ {s : Shape} (ε : Err s), TWhole.errList ε = ε.toList
  | [], _ => rfl
  | _ :: _, (e, ε) => congrArg (List.cons e) (errList_toList ε)

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

theorem SK₀_fullK (M Wp Kc : Type) (Y : PscPar E) (msg : M → Y.J → E) (h1 : Y.VarsOK)
    (h2 : Y.DegOK) (h3 : Y.ValInj) : (SK₀ E Ex).FullK M Wp Kc Y msg := fun A0 =>
  TWhole.short_knowAt Y (TWhole.F₀ Y) Ex h1 h2 h3 M Wp Kc A0 msg

theorem SK₀_coreK (M Wp Kc : Type) (Y : PscPar E) (msg : M → Y.J → E) (h1 : Y.VarsOK)
    (h2 : Y.DegOK) (h3 : Y.ValInj) : (SK₀ E Ex).CoreK M Wp Kc Y msg := fun A0 =>
  TWhole.short_knowAtC Y (TWhole.F₀ Y) Ex h1 h2 h3 M Wp Kc A0 msg

theorem SK₀_ourK (M Wp Kc : Type) (T : PscOur E) (msg : M → T.J → E) (hV : T.VarsOK)
    (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj) : (SK₀ E Ex).FullK M Wp Kc T.par msg :=
  SK₀_fullK M Wp Kc T.par msg ((psc_our_ok E T).1 hV) (psc_our_deg E T hX hY)
    ((psc_our_ok E T).2 hI)

variable (Ex) (Y : PscPar E)

theorem SK₀_passes : ((SK₀ E Ex).full Y).R.Passes Prod.snd PscPar.Out.st := fun x y _ o h =>
  TWhole.psc_st Y Ex x y _ o h

theorem SK₀_copies : ((SK₀ E Ex).full Y).R.OnlyCopies :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem SK₀_passesC : ((SK₀ E Ex).core Y).R.Passes Prod.snd PscPar.Mid.st := fun x _ _ z h =>
  Y.outC_st x _ z h

theorem SK₀_copiesC : ((SK₀ E Ex).core Y).R.OnlyCopies :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

omit [Fintype E] in
theorem sRounds_list :
    ∀ l : List (PFmt E), Shape.chalList (sRounds l) = Shape.chalList (pRounds l)
  | [] => rfl
  | f :: l => congrArg (List.cons (Fintype.card f.Ch)) (sRounds_list l)

/-- The errors are the long block's. -/
theorem SK₀_errs : ((SK₀ E Ex).full Y).e.toList = ((PscLtK.lib E Ex).full Y).e.toList := by
  show (TWhole.shortE Y Ex).toList = (Y.err Ex).toList
  rw [← errList_toList, TWhole.shortE_nums]
  refine ((Err.toList_app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
    (Y.errC Ex) (0, ())).trans ?_).symm
  show (1 :: (pErr Y.fmt).toList) ++ [0] = _
  rw [pErr_list]
  rfl

theorem SK₀_errsC : ((SK₀ E Ex).core Y).e.toList = ((PscLtK.lib E Ex).core Y).e.toList := by
  show (TWhole.shortEC Y Ex).toList = (Y.errC Ex).toList
  rw [← errList_toList, TWhole.shortEC_nums]
  show _ = 1 :: (pErr Y.fmt).toList
  rw [pErr_list]

/-- The numbers of values of the draws are the long block's. -/
theorem SK₀_vals :
    ((SK₀ E Ex).full Y).R.shape.chalList = ((PscLtK.lib E Ex).full Y).R.shape.chalList := by
  show Fintype.card E :: Shape.chalList (sRounds Y.fmt ++ [pRoundV E Y.A]) =
    Fintype.card E :: Shape.chalList (pRounds Y.fmt ++ [pRoundV E Y.A])
  rw [Shape.chalList_append, Shape.chalList_append, sRounds_list]

theorem SK₀_valsC :
    ((SK₀ E Ex).core Y).R.shape.chalList = ((PscLtK.lib E Ex).core Y).R.shape.chalList := by
  show Fintype.card E :: Shape.chalList (sRounds Y.fmt) =
    Fintype.card E :: Shape.chalList (pRounds Y.fmt)
  rw [sRounds_list]

/-- One sumcheck with k cube variables and Y: the library's lists. -/
theorem SK₀_ll (T : PscOur E) (k n : ℕ) (hf : T.fmt = List.replicate k (pfCube E n)) :
    ((SK₀ E Ex).full T.par).e.toList = pscErrs k n T.DY ∧
    ((SK₀ E Ex).full T.par).R.shape.chalList = pscVals (Fintype.card E) k :=
  ⟨(SK₀_errs Ex T.par).trans (ll_psc T k n hf Ex Unit).1,
    (SK₀_vals Ex T.par).trans (ll_psc T k n hf Ex Unit).2⟩

/-- Under «every variable's weights sum to 1» the short verifier rejects nothing. -/
theorem SK₀_out (h : TWhole.Eq0 Y) (x : E × Y.St) (y : Ex.Str) (τ : Tr (shapeS Y)) :
    ((SK₀ E Ex).full Y).R.out x y τ = some (TWhole.shortV Y (TWhole.F₀ Y) x τ) :=
  TWhole.short_out Y (TWhole.F₀ Y) Ex (TWhole.F₀_ok Y h) x y τ

theorem SK₀_outC (h : TWhole.Eq0 Y) (x : E × Y.St) (y : Ex.Str) (τ : Tr (TWhole.shapeSC Y)) :
    ((SK₀ E Ex).core Y).R.out x y τ = some (TWhole.shortVC Y (TWhole.F₀ Y) x τ) :=
  TWhole.short_outC Y (TWhole.F₀ Y) Ex (TWhole.F₀_ok Y h) x y τ

end
end Lk6

#print axioms Lk6.SK₀_fullK
#print axioms Lk6.SK₀_coreK
#print axioms Lk6.SK₀_ourK
#print axioms Lk6.SK₀_passes
#print axioms Lk6.SK₀_copies
#print axioms Lk6.SK₀_passesC
#print axioms Lk6.SK₀_copiesC
#print axioms Lk6.SK₀_errs
#print axioms Lk6.SK₀_errsC
#print axioms Lk6.SK₀_vals
#print axioms Lk6.SK₀_valsC
#print axioms Lk6.SK₀_ll
#print axioms Lk6.SK₀_out
#print axioms Lk6.SK₀_outC
