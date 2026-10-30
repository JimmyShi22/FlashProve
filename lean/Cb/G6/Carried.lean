-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Carried.lean: the letter of Cb/G6/Letter.lean filled (to fill a letter is to give such a
record): the library's sumcheck block carried to short messages, for every `PscPar` and every pick
of the power that each variable leaves out.

Definitions, statements and proofs. A pick F gives, at each state st, `F st : HFixs (Y.vars st)`
(Cb/Ld/LdHideShort.lean): for each variable the power that is left out, and an element meant as the
inverse of its "sum".

Main names:
  `shortR Y F Ex`: the reduction, on the short rounds. Its verifier completes each message by the
    library's `hFill` (`carryS`, Cb/G6/Johnson/Layers/Short.lean) and then is the library's verifier
    of the long block.
  `shortE`, `shortE_nums`: its errors are the long block's, read on the short rounds: 1, n_j for
    each variable, 0.
  `short_copy`: the library's generic clause `PscCopy` (Cb/Ld/LdPscProofsIor.lean).
  `short_know_at`: the block's knowledge soundness, for each fixed tuple of messages, under the
    library's three premises alone. No premise on F.
  `short_knowAt`; `shortK Y F Ex : ShortK Y Ex`: the half on the verifier, filled.
  `shortHon`: the honest side: the library's own strategy, each message without the coefficient that
    is left out. `Coin = Unit`, `Bad = ∅`, `Hid = ∅`, by rfl (`shortHon_coin`, `shortHon_bad`,
    `shortHon_hid`).
  `short_run`, `short_keeps`, `short_honAt`; `shortH`: the half on the honest prover, filled, under
    `HFixs.OK` in addition.

Limits: at a pick that is not lawful (`HFixs.OK` fails) the block is still sound (`short_know_at`
has no premise on F), but at a state where the pick is not lawful it is not proved that the verifier
accepts any transcript: a completed polynomial need not meet the library's check, and neither
`short_accepts`, `short_out` nor the half on the honest prover is to be had. That the honest run's
end statement is what the verifier puts out is proved only where the sum claim holds (`short_run`:
with `HFixs.OK`, `Y.VarsOK`, `Y.DegOK`); off the claim nothing is stated. Nothing on zero knowledge.

-/
import Cb.G6.Letter
import Cb.G6.Johnson.Door.Ride

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole
open Iop Prob Cb Johnson.L5.Layers Johnson.L5.Door

variable {E : Type} [Field E] [Fintype E] (Y : PscPar E) (F : ∀ st, HFixs (Y.vars st))
  (Ex : ExtSpec)

/-- The reduction. -/
noncomputable def shortR : IOR (E × Y.St) Ex Y.Out Ex where
  shape := shapeS Y
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun x y τ => (Y.psc Ex).out x y ((carryS Y x (F x.2) Ex).tr τ)
  imp := fun y _ => y
  srcE := fun _ q => {q}
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- Its errors: the long block's, read on the short rounds. -/
noncomputable def shortE : Err (shapeS Y) := errTo (shapeS Y) (Y.psc Ex).shape (Y.err Ex)

omit [Fintype E] in
theorem errList_s : ∀ l : List (PFmt E),
    errList (errTo (sRounds l ++ [pRoundV E Y.A]) (pRounds l ++ [pRoundV E Y.A])
      (Err.app (pErr l) ((0, ()) : Err [pRoundV E Y.A]))) = l.map PFmt.n ++ [0]
  | [] => rfl
  | f :: l => congrArg (f.n :: ·) (errList_s l)

theorem shortE_nums : errList (shortE Y Ex) = 1 :: (Y.fmt.map PFmt.n ++ [0]) :=
  congrArg (1 :: ·) (errList_s Y Y.fmt)

theorem noOrc_S : NoOrc (shapeS Y) :=
  ⟨inferInstanceAs (Subsingleton Unit),
    noOrc_s Y.fmt _ ⟨inferInstanceAs (Subsingleton Unit), trivial⟩⟩

/-- The long block's verifier copies the state. -/
theorem psc_st (x : E × Y.St) (y : Ex.Str) (τ : Tr (Y.psc Ex).shape) (o : Y.Out)
    (h : (Y.psc Ex).out x y τ = some o) : o.st = x.2 := by
  have h' : (Y.psc Ex).out x y (Tr.app (Tr.fst τ) (Tr.snd (s := (Y.core Ex).shape) τ)) =
      some o := by
    rw [Tr.app_fst_snd]; exact h
  exact Y.outC_st x _ _ (Y.psc_out_some Ex x y _ _ o h')

/-- The library's generic clause (`PscCopy`, Cb/Ld/LdPscProofsIor.lean): the reduction copies the
state and the oracles, and a claim that is false of m stays false of m, but for the errors. -/
theorem short_copy (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) :
    PscCopy (shortR Y F Ex) Prod.snd PscPar.Out.st Y.SumHolds Y.OutHolds (shortE Y Ex) where
  st := fun x y _ o h => psc_st Y Ex x y _ o h
  imp := fun _ _ => rfl
  sound := fun x y m hx => short_doomed Y Ex hV hD hI x (F x.2) y m hx

theorem short_local : (shortR Y F Ex).IsLocal where
  out := fun x y y' τ τ' h1 h2 _ _ => by
    rw [tr_ext (noOrc_S Y) τ τ' h1 h2]
    show (Y.psc Ex).out _ y _ = (Y.psc Ex).out _ y' _
    exact (psc_local E Y Ex).out _ y y' _ _ rfl rfl (fun p hp => absurd hp (by
      show p ∉ (Y.psc Ex).extReads _
      simp [PscPar.psc, IOR.seq, PscPar.core, PscPar.ends])) fun _ _ => rfl
  imp := fun y y' _ _ q _ _ h _ => h q (Finset.mem_singleton_self q)

/-- The block's knowledge soundness, for each fixed tuple of messages, under the library's three
premises alone: no premise on F. -/
theorem short_know_at (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (M Wp Kc : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) (m : M) :
    (shortR Y F Ex).red.Know (Y.baseIn A0 fun w => msg w.1).on
      (fun a wp => (Y.baseIn A0 fun w => msg w.1).relR a (m, wp))
      (fun b wp => (Y.baseOut A0 fun w => msg w.1).relR b (m, wp)) (fun _ _ wp => wp)
      (shortE Y Ex) :=
  (short_copy Y F Ex hV hD hI).know_at A0 msg m

theorem short_knowAt (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (M Wp Kc : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) :
    KnowAt (shortR Y F Ex) (Y.baseIn A0 fun w => msg w.1) (Y.baseOut A0 fun w => msg w.1)
      (fun _ _ _ wp => wp) (shortE Y Ex) where
  point := ⟨(pRound0_point, sRounds_point Y.fmt _ (pRoundV_point Y.A, ()))⟩
  isLocal := short_local Y F Ex
  onOut := fun a τ b ha hb => (short_copy Y F Ex hV hD hI).carry_base A0 a τ b ha hb
  know := short_know_at Y F Ex hV hD hI M Wp Kc A0 msg

/-- The half on the verifier, filled. -/
noncomputable def shortK : ShortK Y Ex where
  R := shortR Y F Ex
  shape := rfl
  ε := shortE Y Ex
  nums := shortE_nums Y Ex
  know := short_knowAt Y F Ex

/-! ### The honest half -/

/-- The draws, read as the long block's. -/
def rhoS (ρ : Rho (shapeS Y)) : Rho (Y.psc Ex).shape := (ρ.1, rhoL Y.fmt [pRoundV E Y.A] ρ.2)

/-- A strategy of the long block, made short. -/
def shortStrat {β : Type} (st : Y.St) (L : Strat (Y.psc Ex).shape β) : Strat (shapeS Y) β :=
  (L.1, fun ε => sStrat Y.fmt (Y.dat st) (F st) [pRoundV E Y.A] (L.2 ε))

theorem shortStrat_run {β : Type} (st : Y.St) (L : Strat (Y.psc Ex).shape β)
    (ρ : Rho (shapeS Y)) :
    (shortStrat Y F Ex st L).run ρ =
      (((L.run (rhoS Y Ex ρ)).1.1, ρ.1,
          dShort Y.fmt (Y.dat st) (F st) [pRoundV E Y.A] (L.run (rhoS Y Ex ρ)).1.2.2),
        (L.run (rhoS Y Ex ρ)).2) := by
  obtain ⟨m0, k0⟩ := L
  obtain ⟨c, ρ'⟩ := ρ
  show ((m0, c, ((sStrat Y.fmt (Y.dat st) (F st) [pRoundV E Y.A] (k0 c)).run ρ').1),
    ((sStrat Y.fmt (Y.dat st) (F st) [pRoundV E Y.A] (k0 c)).run ρ').2) = _
  rw [Johnson.L5.Door.sStrat_run]
  rfl

variable {Wt : Type} (msg : Wt → Y.J → E)

/-- The honest side: the library's own, each message without the coefficient that is left out. -/
noncomputable def shortHon : (shortR Y F Ex).Honest Wt Wt where
  Coin := Unit
  strat := fun w x _ => shortStrat Y F Ex x.2 ((Y.hon Ex msg).strat w x ((), ()))
  Bad := ∅
  Hid := fun _ _ => ∅

theorem shortHon_coin : (shortHon Y F Ex msg).Coin = Unit := rfl
theorem shortHon_bad : (shortHon Y F Ex msg).Bad = ∅ := rfl
theorem shortHon_hid (w : Wt) (x : E × Y.St) : (shortHon Y F Ex msg).Hid w x = ∅ := rfl

/-- The block's numbers: its errors; `pBad = 0`, `pHid = 0`, `bud` always true, `cov` empty. -/
noncomputable def shortN (Kc : Type) : IOR.Nums Kc (shortR Y F Ex) :=
  ⟨shortE Y Ex, 0, 0, fun _ _ => True, fun _ => ∅⟩

/-- The honest run is the library's own run, made short: under `HFixs.OK`, `Y.VarsOK`, `Y.DegOK` and
the sum claim the verifier puts out the run's end statement, and the output claims hold. -/
theorem short_run (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (hV : Y.VarsOK) (hD : Y.DegOK)
    (w : Wt) (x : E × Y.St) (hS : Y.SumHolds x (msg w)) (c : (shortHon Y F Ex msg).Coin)
    (y : Ex.Str) (ρ : Rho (shapeS Y)) :
    (shortR Y F Ex).out x y (((shortHon Y F Ex msg).strat w x c).run ρ).1 =
        some (((shortHon Y F Ex msg).strat w x c).run ρ).2.1 ∧
      Y.OutHolds (((shortHon Y F Ex msg).strat w x c).run ρ).2.1 (msg w) := by
  have hA := psc_acc_base E Y Ex Wt Unit
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ msg hV hD
  have hρ : rhoS Y Ex ρ ∉ (Y.hon Ex msg).withheld w x := by
    rintro ((hb | hb) | (hb | ⟨_, _, hb⟩)) <;> exact hb
  obtain ⟨h1, h2⟩ := hA x y w ((), ()) (rhoS Y Ex ρ) ⟨trivial, hS⟩ hρ
  have hk := psc_keeps E Y Ex Wt msg w x ((), ()) (rhoS Y Ex ρ)
  have hr := shortStrat_run Y F Ex x.2 ((Y.hon Ex msg).strat w x ((), ())) ρ
  have hr' : ((shortHon Y F Ex msg).strat w x c).run ρ = _ := hr
  rw [hr']
  have h3 := h2.2
  rw [hk] at h3
  refine ⟨?_, h3⟩
  have hc : ρ.1 = (((Y.hon Ex msg).strat w x ((), ())).run (rhoS Y Ex ρ)).1.2.1 :=
    (congrArg Prod.fst (Strat.rho_run ((Y.hon Ex msg).strat w x ((), ())) (rhoS Y Ex ρ))).symm
  have ho := short_onto Y Ex x (F x.2) (hF x.2) y _ _ h1
  show (Y.psc Ex).out x y ((carryS Y x (F x.2) Ex).tr _) = _
  rw [hc]
  have ho' : (carryS Y x (F x.2) Ex).tr
      (dropS Y x (F x.2) Ex (((Y.hon Ex msg).strat w x ((), ())).run (rhoS Y Ex ρ)).1) = _ := ho
  exact (congrArg (fun τ => (Y.psc Ex).out x y τ) ho').trans h1

theorem short_keeps (w : Wt) (x : E × Y.St) (c : (shortHon Y F Ex msg).Coin)
    (ρ : Rho (shapeS Y)) : (((shortHon Y F Ex msg).strat w x c).run ρ).2.2 = w := by
  have hk := psc_keeps E Y Ex Wt msg w x ((), ()) (rhoS Y Ex ρ)
  have hr := shortStrat_run Y F Ex x.2 ((Y.hon Ex msg).strat w x ((), ())) ρ
  have hr' : ((shortHon Y F Ex msg).strat w x c).run ρ = _ := hr
  rw [hr']
  exact hk

theorem short_honAt (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (hV : Y.VarsOK) (hD : Y.DegOK)
    (M Wp Kc : Type) (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) :
    HonAt (shortR Y F Ex) (shortHon Y F Ex fun w : M × Wp => msg w.1)
      (Y.baseIn A0 fun w => msg w.1) (Y.baseOut A0 fun w => msg w.1) (shortN Y F Ex Kc) where
  acc := fun x y w c ρ hw _ => by
    obtain ⟨h1, h2⟩ := short_run Y F Ex (fun w : M × Wp => msg w.1) hF hV hD w x hw.2 c y ρ
    have h4 := short_keeps Y F Ex (fun w : M × Wp => msg w.1) w x c ρ
    have h5 := psc_st Y Ex x y _ _ h1
    refine ⟨h1, ?_⟩
    show A0.rel _ y _ ∧ Y.OutHolds _ _
    rw [h4, h5]
    exact ⟨hw.1, h2⟩
  keeps := fun w x c ρ =>
    congrArg A0.core (short_keeps Y F Ex (fun w : M × Wp => msg w.1) w x c ρ)
  prBad := by
    show prRho (∅ : Set (Rho (shapeS Y))) ≤ 0
    simp [prRho]
  cover := fun _ _ _ h => h
  prCov := fun _ => by simp [prRho, shortN]
  same := fun w x c ρ =>
    congrArg Prod.fst (short_keeps Y F Ex (fun w : M × Wp => msg w.1) w x c ρ)

/-- The half on the honest prover, filled, under `HFixs.OK` in addition. -/
noncomputable def shortH (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) : ShortH (shortK Y F Ex) where
  H := fun {M Wp} msg => shortHon Y F Ex fun w : M × Wp => msg w.1
  P := fun Kc => shortN Y F Ex Kc
  err := fun _ => rfl
  hon := short_honAt Y F Ex hF

end TWhole
