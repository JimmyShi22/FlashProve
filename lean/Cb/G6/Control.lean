-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Control.lean: checks on the cut of Cb/G6/Cut.lean and on the letter of Cb/G6/Letter.lean: what
fills them, what does not, and that they fit the library's rule for oracle messages.

Statements with their proofs, and one definition.

Main names:
  `long_knowAt`, `long_honAt`, `long_knowAtC`: the library's long block has `KnowAt` and `HonAt` at
    the same joints: out of the library's `psc_goodAt`, `psc_core_goodAt` through `goodAt_iff`.
  `long_not_short`: the long block's rounds are not the letter's, whenever there is a variable: a
    long round's message has another number of values than a short round's.
  `short_sig`: the library's `sigLift_know` (Cb/Ld/LdSigLift.lean), whose type names no honest side,
    takes the clause `know` of `KnowAt` as it stands: the short block's knowledge soundness over a
    signature.
  `letter_sig`, `letter_sigV`, `letter_sigC`: the same for every filling of the letter.
  `toy_chain`, `toy_nums`: the rules of Cb/G6/Join.lean used once: a draw, then the letter:
    `KnowAt`, and its list of errors.
  `rejectK`: the letter lays no law on what its verifier puts out: the verifier that rejects
    everything fills `ShortK`, with no premise.

Premises: `Y.VarsOK`, `Y.DegOK`, `Y.ValInj` (the library's) in all but `long_not_short`, `toy_nums`,
`rejectK`; `toy_chain` also takes the two premises of `knowAt_draw`.
Limits: nothing on zero knowledge.

-/
import Cb.G6.Pick
import Cb.G6.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole
open Iop Prob Cb Johnson.L5.Layers

variable {E : Type} [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec)

/-- The library's long block has `KnowAt` at the sumcheck's joints. -/
theorem long_knowAt (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (M Wp Kc : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) :
    KnowAt (Y.psc Ex) (Y.baseIn A0 fun w => msg w.1) (Y.baseOut A0 fun w => msg w.1)
      (fun _ _ _ wp => wp) (Y.nums Ex Kc).err :=
  ((goodAt_iff _ _ _ _ _ _).1 (psc_goodAt E Y Ex M Wp Kc A0 msg hV hD hI)).1

/-- It has `HonAt` there. -/
theorem long_honAt (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (M Wp Kc : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) :
    HonAt (Y.psc Ex) (Y.hon Ex fun w : M × Wp => msg w.1) (Y.baseIn A0 fun w => msg w.1)
      (Y.baseOut A0 fun w => msg w.1) (Y.nums Ex Kc) :=
  ((goodAt_iff _ _ _ _ _ _).1 (psc_goodAt E Y Ex M Wp Kc A0 msg hV hD hI)).2

/-- The same for round 0 and the rounds of the variables alone. -/
theorem long_knowAtC (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (M Wp Kc : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) :
    KnowAt (Y.core Ex) (Y.baseIn A0 fun w => msg w.1) (Y.baseMid A0 fun w => msg w.1)
      (fun _ _ _ wp => wp) (Y.numsC Ex Kc).err :=
  ((goodAt_iff _ _ _ _ _ _).1 (psc_core_goodAt E Y Ex M Wp Kc A0 msg hV hD hI)).1

omit [Fintype E] in
/-- A long round's message has another type than a short round's. -/
theorem plain_ne [Finite E] (f : PFmt E) : (pRound f).Plain ≠ (sRound f).Plain := fun h => by
  haveI := Fintype.ofFinite E
  have h1 : Nat.card (Fin (f.n + 1) → E) = Nat.card (Fin f.n → E) := congrArg Nat.card h
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] at h1
  have h2 : 1 < Fintype.card E := Fintype.one_lt_card
  exact absurd (Nat.pow_right_injective h2 h1) (Nat.succ_ne_self _)

/-- The long block's rounds are not the letter's, whenever there is a variable. -/
theorem long_not_short (f : PFmt E) (l : List (PFmt E)) (hf : Y.fmt = f :: l) :
    (Y.psc Ex).shape ≠ shapeS Y := fun h => by
  have h1 : pRound0 E :: (pRounds Y.fmt ++ [pRoundV E Y.A]) =
      pRound0 E :: (sRounds Y.fmt ++ [pRoundV E Y.A]) := h
  rw [hf] at h1
  have h2 : pRound f = sRound f := (List.cons.inj (List.cons.inj h1).2).1
  exact plain_ne f (congrArg Round.Plain h2)

/-- The short block's knowledge soundness over a signature. This is said under the hypotheses that
stand in the statement itself, which this comment does not list; it is no claim that they hold. -/
theorem short_sig (F : ∀ st, HFixs (Y.vars st)) (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj)
    (S : Sig E) (Kc Wp : Type) (A0 : IOR.Rels Kc Y.St Ex (S.Msg × Wp)) (msg : S.Msg → Y.J → E) :
    ((shortR Y F Ex).keep S.Smp S.ext).red.Know (S.over (Y.baseIn A0 fun w => msg w.1)).on
      (S.over (Y.baseIn A0 fun w => msg w.1)).relR (S.over (Y.baseOut A0 fun w => msg w.1)).relR
      (fun _ _ w => (w.1, w.2)) (shortE Y Ex) :=
  sigLift_know E S Kc (E × Y.St) Y.Out Wp Wp Ex Ex (shortR Y F Ex) _ _ (fun _ _ _ wp => wp)
    (shortE Y Ex) (short_knowAt Y F Ex hV hD hI S.Msg Wp Kc A0 msg).know

/-- The same for every filling K of the letter. -/
theorem letter_sig (K : ShortK Y Ex) (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj)
    (S : Sig E) (Kc Wp : Type) (A0 : IOR.Rels Kc Y.St Ex (S.Msg × Wp)) (msg : S.Msg → Y.J → E) :
    (K.R.keep S.Smp S.ext).red.Know (S.over (Y.baseIn A0 fun w => msg w.1)).on
      (S.over (Y.baseIn A0 fun w => msg w.1)).relR (S.over (Y.baseOut A0 fun w => msg w.1)).relR
      (fun _ _ w => (w.1, w.2)) K.ε :=
  sigLift_know E S Kc (E × Y.St) Y.Out Wp Wp Ex Ex K.R _ _ (fun _ _ _ wp => wp) K.ε
    (K.know hV hD hI S.Msg Wp Kc A0 msg).know

/-- The same with the letter as a total function of the parameters. -/
theorem letter_sigV (V : ∀ (Y : PscPar E) (Ex : ExtSpec), ShortK Y Ex) (hV : Y.VarsOK)
    (hD : Y.DegOK) (hI : Y.ValInj) (S : Sig E) (Kc Wp : Type)
    (A0 : IOR.Rels Kc Y.St Ex (S.Msg × Wp)) (msg : S.Msg → Y.J → E) :
    ((V Y Ex).R.keep S.Smp S.ext).red.Know (S.over (Y.baseIn A0 fun w => msg w.1)).on
      (S.over (Y.baseIn A0 fun w => msg w.1)).relR (S.over (Y.baseOut A0 fun w => msg w.1)).relR
      (fun _ _ w => (w.1, w.2)) (V Y Ex).ε :=
  letter_sig Y Ex (V Y Ex) hV hD hI S Kc Wp A0 msg

/-- The same for the letter without the round of values. -/
theorem letter_sigC (K : ShortKC Y Ex) (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj)
    (S : Sig E) (Kc Wp : Type) (A0 : IOR.Rels Kc Y.St Ex (S.Msg × Wp)) (msg : S.Msg → Y.J → E) :
    (K.R.keep S.Smp S.ext).red.Know (S.over (Y.baseIn A0 fun w => msg w.1)).on
      (S.over (Y.baseIn A0 fun w => msg w.1)).relR (S.over (Y.baseMid A0 fun w => msg w.1)).relR
      (fun _ _ w => (w.1, w.2)) K.ε :=
  sigLift_know E S Kc (E × Y.St) Y.Mid Wp Wp Ex Ex K.R _ _ (fun _ _ _ wp => wp) K.ε
    (K.know hV hD hI S.Msg Wp Kc A0 msg).know

/-- The rules for joining used once: a draw, then the letter. -/
theorem toy_chain (V : ∀ (Y : PscPar E) (Ex : ExtSpec), ShortK Y Ex) (hV : Y.VarsOK) (hD : Y.DegOK)
    (hI : Y.ValInj) (M Wp Kc X D : Type) [Fintype D] [Nonempty D]
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) (nx : X → D → E × Y.St)
    (A : IOR.Rels Kc X Ex (M × Wp)) (err : ℕ)
    (hon : ∀ x y β, A.on (x, y) → (Y.baseIn A0 fun w => msg w.1).on (nx x β, y))
    (hcnt : ∀ x y (m : M), A.on (x, y) →
      cnt (fun β => ∃ wp, (Y.baseIn A0 fun w => msg w.1).relR (nx x β, y) (m, wp) ∧
        ¬ A.relR (x, y) (m, wp)) ≤ err) :
    KnowAt ((IOR.draw D nx Ex).seq (V Y Ex).R) A (Y.baseOut A0 fun w => msg w.1)
      (fun _ _ _ wp => wp) (Err.app (IOR.Nums.draw Kc D nx Ex err).err (V Y Ex).ε) :=
  knowAt_seq (knowAt_draw nx A _ err hon hcnt) ((V Y Ex).know hV hD hI M Wp Kc A0 msg)

/-- Its list of errors. -/
theorem toy_nums (V : ∀ (Y : PscPar E) (Ex : ExtSpec), ShortK Y Ex) (Kc X D : Type) [Fintype D]
    [Nonempty D] (nx : X → D → E × Y.St) (err : ℕ) :
    errList (Err.app (IOR.Nums.draw Kc D nx Ex err).err (V Y Ex).ε) =
      err :: 1 :: (Y.fmt.map PFmt.n ++ [0]) :=
  (errList_app _ _).trans (by rw [(V Y Ex).nums]; rfl)

/-- The letter lays no law on what its verifier puts out: the verifier that rejects everything fills
`ShortK`, with no premise. -/
noncomputable def rejectK : ShortK Y Ex where
  R := { shape := shapeS Y, blinded := fun _ => true, extReads := fun _ => ∅, reads := fun _ => ∅,
         out := fun _ _ _ => none, imp := fun y _ => y, srcE := fun _ q => {q},
         srcO := fun _ _ => ∅, tie := fun _ _ => ∅ }
  shape := rfl
  ε := shortE Y Ex
  nums := shortE_nums Y Ex
  know := fun _ _ _ _ _ _ _ _ =>
    { point := ⟨(pRound0_point, Johnson.L5.Door.sRounds_point Y.fmt _ (pRoundV_point Y.A, ()))⟩
      isLocal := { out := fun _ _ _ _ _ _ _ _ _ => rfl
                   imp := fun _ _ _ _ q _ _ h _ => h q (Finset.mem_singleton_self q) }
      onOut := fun _ _ _ _ hb => by simp at hb
      know := fun _ _ _ => Doomed.of_forall _ _ fun _ _ _ hb _ => by simp at hb }

end TWhole
