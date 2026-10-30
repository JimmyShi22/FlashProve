-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Core.lean: the letter of Cb/G6/Letter.lean filled for round 0 and the rounds of the variables
alone (to `Y.Mid`), and what that block's verifier puts out as a total function.

Definitions, statements and proofs. The recursions of Cb/G6/Johnson/Layers (`cShort`, `dShort`,
`sStrat`, `rhoL`) carry a tail t of further rounds, and `l ++ []` is not `l` by unfolding. So the
same recursions are written here without a tail (`cShort0`, `dShort0`, `sStrat0`, `rhoL0`), with
their laws.

Main names:
  `shortRC Y F Ex`: the reduction, on round 0 and the short rounds. Its verifier completes each
    message by the library's `hFill` and then is the library's `outC`.
  `short_know_atC`, `short_knowAtC`; `shortKC : ShortKC Y Ex`: the half on the verifier, filled; the
    two theorems take the library's three premises `Y.VarsOK`, `Y.DegOK`, `Y.ValInj`. No premise on
    the pick F.
  `shortHonC`: the library's `honC`, each message without the coefficient that is left out.
    `shortHC`: the half on the honest prover, filled, under `HFixs.OK`.
  `vFin`, `shortVC Y F x τ : Y.Mid`: a total function: it completes each message, evaluates at the
    draw and collects the point.
  `short_outC`: under `HFixs.OK` the verifier of `shortRC` puts out just that, for all inputs.

Limits: as in Cb/G6/Carried.lean, with `short_outC`, `short_runC` for `short_out`, `short_run`;
there is no theorem like `short_accepts` here. `shortVC` has code. Its loop does not read the
finiteness of a challenge set, but a format carries it as data, so to build the parameters is to
enumerate each variable's challenge set: this is not code for a large field. (An argument in words.)

-/
import Cb.G6.Carried

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole
open Iop Prob Cb Johnson.L5.Layers Johnson.L5.Door

section Foot
variable {E : Type} [Field E]

def cShort0 : (l : List (PFmt E)) → (d : PDats l) → HFixs (pVars l d) → E →
    Carry (sRounds l) (pRounds l)
  | [], _, _, _ => ()
  | f :: l, d, F, σ =>
    (fun m => ((), hFill (f.var d.1) F.1 σ m.2), id,
      fun m c => cShort0 l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)))

theorem cShort0_inj : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E),
    (cShort0 l d F σ).Inj
  | [], _, _, _ => trivial
  | _ :: l, d, F, _ => ⟨Function.injective_id, fun _ _ => cShort0_inj l d.2 F.2 _⟩

theorem cShort0_cons : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)),
    HFixs.OK (pVars l d) F → ∀ (σ : E) (τ : Tr (sRounds l)),
    HCons (pVars l d) σ (pQ l d ((cShort0 l d F σ).tr τ).plains)
      (pH l d (pG l ((cShort0 l d F σ).tr τ).rho))
  | [], _, _, _, _, _ => trivial
  | f :: l, d, F, hF, σ, (m, c, τ) =>
    ⟨phi_fill (f.var d.1) F.1 hF.1 σ m.2,
      cShort0_cons l d.2 F.2 hF.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) τ⟩

def dShort0 : (l : List (PFmt E)) → (d : PDats l) → HFixs (pVars l d) →
    Tr (pRounds l) → Tr (sRounds l)
  | [], _, _, τ => τ
  | _ :: l, d, F, (m, c, τ) => (((), fun i => m.2 (F.1.1.succAbove i)), c, dShort0 l d.2 F.2 τ)

theorem cShort0_dShort0 : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)),
    HFixs.OK (pVars l d) F → ∀ (σ : E) (τ : Tr (pRounds l)),
    HCons (pVars l d) σ (pQ l d τ.plains) (pH l d (pG l τ.rho)) →
    (cShort0 l d F σ).tr (dShort0 l d F τ) = τ
  | [], _, _, _, _, _, _ => rfl
  | f :: l, d, F, hF, σ, (m, c, τ), hc => by
    have e1 : hFill (f.var d.1) F.1 σ (fun i => m.2 (F.1.1.succAbove i)) = m.2 := by
      have e := fill_drop (f.var d.1) F.1 hF.1 m.2
      have e2 : (f.var d.1).phi m.2 = σ := hc.1
      rw [e2] at e
      exact e
    show (((), hFill (f.var d.1) F.1 σ (fun i => m.2 (F.1.1.succAbove i))), c,
      (cShort0 l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ fun i => m.2 (F.1.1.succAbove i))
        (f.val c))).tr (dShort0 l d.2 F.2 τ)) = (m, c, τ)
    rw [e1, cShort0_dShort0 l d.2 F.2 hF.2 (hev m.2 (f.val c)) τ hc.2]

def sStrat0 {β : Type} : (l : List (PFmt E)) → (d : PDats l) → HFixs (pVars l d) →
    Strat (pRounds l) β → Strat (sRounds l) β
  | [], _, _, σ => σ
  | _ :: l, d, F, (m, k) =>
    (((), fun i => m.2 (F.1.1.succAbove i)), fun c => sStrat0 l d.2 F.2 (k c))

def rhoL0 : (l : List (PFmt E)) → Rho (sRounds l) → Rho (pRounds l)
  | [], ρ => ρ
  | _ :: l, (c, ρ) => (c, rhoL0 l ρ)

theorem sStrat0_run {β : Type} : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d))
    (σ : Strat (pRounds l) β) (ρ : Rho (sRounds l)),
    (sStrat0 l d F σ).run ρ = (dShort0 l d F (σ.run (rhoL0 l ρ)).1, (σ.run (rhoL0 l ρ)).2)
  | [], _, _, _, _ => rfl
  | f :: l, d, F, (m, k), (c, ρ) => by
    show ((((), fun i => m.2 (F.1.1.succAbove i)), c, ((sStrat0 l d.2 F.2 (k c)).run ρ).1),
      ((sStrat0 l d.2 F.2 (k c)).run ρ).2) = _
    rw [sStrat0_run l d.2 F.2 (k c) ρ]
    rfl

theorem noOrc_s0 : ∀ l : List (PFmt E), NoOrc (sRounds l)
  | [] => trivial
  | _ :: l => ⟨inferInstanceAs (Subsingleton Unit), noOrc_s0 l⟩

def sRounds_point0 : (l : List (PFmt E)) → Shape.IsPoint (sRounds l)
  | [] => ()
  | f :: l => (sRound_point f, sRounds_point0 l)

theorem errList_s0 : ∀ l : List (PFmt E),
    errList (errTo (sRounds l) (pRounds l) (pErr l)) = l.map PFmt.n
  | [] => rfl
  | f :: l => congrArg (f.n :: ·) (errList_s0 l)

/-- The loop of `shortVC`: the last value and the point. -/
def vFin : (l : List (PFmt E)) → (d : PDats l) → HFixs (pVars l d) → E → Tr (sRounds l) →
    E × PPt l
  | [], _, _, σ, _ => (σ, ())
  | f :: l, d, F, σ, (m, c, τ) =>
    ((vFin l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) τ).1,
      (f.val c, (vFin l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) τ).2))

theorem vFin_fin : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E)
    (τ : Tr (sRounds l)),
    hFin (pVars l d) σ (pQ l d ((cShort0 l d F σ).tr τ).plains)
      (pH l d (pG l ((cShort0 l d F σ).tr τ).rho)) = (vFin l d F σ τ).1
  | [], _, _, _, _ => rfl
  | f :: l, d, F, σ, (m, c, τ) =>
    vFin_fin l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) τ

theorem vFin_pt : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E)
    (τ : Tr (sRounds l)), pG l ((cShort0 l d F σ).tr τ).rho = (vFin l d F σ τ).2
  | [], _, _, _, _ => rfl
  | f :: l, d, F, σ, (m, c, τ) =>
    congrArg (fun p => (f.val c, p))
      (vFin_pt l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) τ)

end Foot

variable {E : Type} [Field E] [Fintype E] (Y : PscPar E) (F : ∀ st, HFixs (Y.vars st))
  (Ex : ExtSpec)

def carryC (x : E × Y.St) (G : HFixs (Y.vars x.2)) : Carry (shapeSC Y) Y.shapeC :=
  (id, id, fun m ε => cShort0 Y.fmt (Y.dat x.2) G (m.2 + ε * x.1))

theorem carryC_inj (x : E × Y.St) (G : HFixs (Y.vars x.2)) : (carryC Y x G).Inj :=
  ⟨Function.injective_id, fun _ _ => cShort0_inj _ _ _ _⟩

/-- The reduction. -/
noncomputable def shortRC : IOR (E × Y.St) Ex Y.Mid Ex where
  shape := shapeSC Y
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun x _ τ => Y.outC x ((carryC Y x (F x.2)).tr τ)
  imp := fun y _ => y
  srcE := fun _ q => {q}
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

def shortEC : Err (shapeSC Y) := errTo (shapeSC Y) Y.shapeC (Y.errC Ex)

theorem shortEC_nums : errList (shortEC Y Ex) = 1 :: Y.fmt.map PFmt.n :=
  congrArg (1 :: ·) (errList_s0 Y.fmt)

theorem noOrc_SC : NoOrc (shapeSC Y) := ⟨inferInstanceAs (Subsingleton Unit), noOrc_s0 Y.fmt⟩

theorem short_copyC (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) :
    PscCopy (shortRC Y F Ex) Prod.snd PscPar.Mid.st Y.SumHolds Y.MidHolds (shortEC Y Ex) where
  st := fun x _ _ z h => Y.outC_st x _ z h
  imp := fun _ _ => rfl
  sound := fun x _ m hx =>
    Doomed.carry (carryC Y x (F x.2)) (Y.errC Ex) _ _ (carryC_inj Y x (F x.2)) (fun _ hτ => hτ)
      (psc_core_sound_at E Y Ex hV hD hI x m hx)

theorem short_localC : (shortRC Y F Ex).IsLocal where
  out := fun x _ _ τ τ' h1 h2 _ _ => by
    rw [tr_ext (noOrc_SC Y) τ τ' h1 h2]
    rfl
  imp := fun y y' _ _ q _ _ h _ => h q (Finset.mem_singleton_self q)

/-- The block's knowledge soundness, for each fixed tuple of messages. -/
theorem short_know_atC (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (M Wp Kc : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) (m : M) :
    (shortRC Y F Ex).red.Know (Y.baseIn A0 fun w => msg w.1).on
      (fun a wp => (Y.baseIn A0 fun w => msg w.1).relR a (m, wp))
      (fun b wp => (Y.baseMid A0 fun w => msg w.1).relR b (m, wp)) (fun _ _ wp => wp)
      (shortEC Y Ex) :=
  (short_copyC Y F Ex hV hD hI).know_at A0 msg m

theorem short_knowAtC (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (M Wp Kc : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) :
    KnowAt (shortRC Y F Ex) (Y.baseIn A0 fun w => msg w.1) (Y.baseMid A0 fun w => msg w.1)
      (fun _ _ _ wp => wp) (shortEC Y Ex) where
  point := ⟨(pRound0_point, sRounds_point0 Y.fmt)⟩
  isLocal := short_localC Y F Ex
  onOut := fun a τ b ha hb => (short_copyC Y F Ex hV hD hI).carry_base A0 a τ b ha hb
  know := short_know_atC Y F Ex hV hD hI M Wp Kc A0 msg

/-- The half on the verifier, filled. -/
noncomputable def shortKC : ShortKC Y Ex where
  R := shortRC Y F Ex
  shape := rfl
  ε := shortEC Y Ex
  nums := shortEC_nums Y Ex
  know := short_knowAtC Y F Ex

/-! ### The honest half -/

def rhoSC (ρ : Rho (shapeSC Y)) : Rho Y.shapeC := (ρ.1, rhoL0 Y.fmt ρ.2)

def shortStratC {β : Type} (st : Y.St) (L : Strat Y.shapeC β) : Strat (shapeSC Y) β :=
  (L.1, fun ε => sStrat0 Y.fmt (Y.dat st) (F st) (L.2 ε))

theorem shortStratC_run {β : Type} (st : Y.St) (L : Strat Y.shapeC β) (ρ : Rho (shapeSC Y)) :
    (shortStratC Y F st L).run ρ =
      (((L.run (rhoSC Y ρ)).1.1, ρ.1, dShort0 Y.fmt (Y.dat st) (F st) (L.run (rhoSC Y ρ)).1.2.2),
        (L.run (rhoSC Y ρ)).2) := by
  obtain ⟨m0, k0⟩ := L
  obtain ⟨c, ρ'⟩ := ρ
  show ((m0, c, ((sStrat0 Y.fmt (Y.dat st) (F st) (k0 c)).run ρ').1),
    ((sStrat0 Y.fmt (Y.dat st) (F st) (k0 c)).run ρ').2) = _
  rw [sStrat0_run]
  rfl

variable {Wt : Type} (msg : Wt → Y.J → E)

noncomputable def shortHonC : (shortRC Y F Ex).Honest Wt Wt where
  Coin := Unit
  strat := fun w x _ => shortStratC Y F x.2 ((Y.honC Ex msg).strat w x ())
  Bad := ∅
  Hid := fun _ _ => ∅

theorem shortHonC_coin : (shortHonC Y F Ex msg).Coin = Unit := rfl
theorem shortHonC_bad : (shortHonC Y F Ex msg).Bad = ∅ := rfl
theorem shortHonC_hid (w : Wt) (x : E × Y.St) : (shortHonC Y F Ex msg).Hid w x = ∅ := rfl

def shortNC (Kc : Type) : IOR.Nums Kc (shortRC Y F Ex) :=
  ⟨shortEC Y Ex, 0, 0, fun _ _ => True, fun _ => ∅⟩

/-- A long transcript that the library's verifier accepts is the completion of its short form. -/
theorem short_ontoC (x : E × Y.St) (G : HFixs (Y.vars x.2)) (hG : HFixs.OK (Y.vars x.2) G)
    (τ : Tr Y.shapeC) (z : Y.Mid) (h : Y.outC x τ = some z) :
    (carryC Y x G).tr (τ.1, τ.2.1, dShort0 Y.fmt (Y.dat x.2) G τ.2.2) = τ := by
  have hc : HCons (Y.vars x.2) (Y.mu τ + Y.eps τ * x.1) (Y.qs x.2 τ) (Y.hp x.2 (Y.pt τ)) := by
    by_contra hn
    have e : Y.outC x τ = none := by
      unfold PscPar.outC
      rw [if_neg hn]
    rw [e] at h
    simp at h
  obtain ⟨m, ε, τ'⟩ := τ
  show (m, ε, (cShort0 Y.fmt (Y.dat x.2) G (m.2 + ε * x.1)).tr
    (dShort0 Y.fmt (Y.dat x.2) G τ')) = (m, ε, τ')
  rw [cShort0_dShort0 Y.fmt (Y.dat x.2) G hG (m.2 + ε * x.1) τ' hc]

theorem short_runC (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (hV : Y.VarsOK) (hD : Y.DegOK)
    (w : Wt) (x : E × Y.St) (hS : Y.SumHolds x (msg w)) (c : (shortHonC Y F Ex msg).Coin)
    (y : Ex.Str) (ρ : Rho (shapeSC Y)) :
    (shortRC Y F Ex).out x y (((shortHonC Y F Ex msg).strat w x c).run ρ).1 =
        some (((shortHonC Y F Ex msg).strat w x c).run ρ).2.1 ∧
      Y.MidHolds (((shortHonC Y F Ex msg).strat w x c).run ρ).2.1 (msg w) ∧
      (((shortHonC Y F Ex msg).strat w x c).run ρ).2.2 = w := by
  have hA := psc_core_acc_base E Y Ex Wt Unit
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ msg hV hD
  have hρ : rhoSC Y ρ ∉ (Y.honC Ex msg).withheld w x := by
    rintro (hb | hb) <;> exact hb
  obtain ⟨h1, h2⟩ := hA x y w () (rhoSC Y ρ) ⟨trivial, hS⟩ hρ
  have hk : (((Y.honC Ex msg).strat w x ()).run (rhoSC Y ρ)).2.2 = w :=
    congrArg Prod.snd (psc_run E Y Ex Wt msg w x (rhoSC Y ρ)).2.2.2
  have hr := shortStratC_run Y F x.2 ((Y.honC Ex msg).strat w x ()) ρ
  have hr' : ((shortHonC Y F Ex msg).strat w x c).run ρ = _ := hr
  rw [hr']
  have h3 := h2.2
  rw [hk] at h3
  refine ⟨?_, h3, hk⟩
  have hc : ρ.1 = (((Y.honC Ex msg).strat w x ()).run (rhoSC Y ρ)).1.2.1 :=
    (congrArg Prod.fst (Strat.rho_run ((Y.honC Ex msg).strat w x ()) (rhoSC Y ρ))).symm
  have ho := short_ontoC Y x (F x.2) (hF x.2) _ _ h1
  show Y.outC x ((carryC Y x (F x.2)).tr _) = _
  rw [hc]
  exact (congrArg (fun τ => Y.outC x τ) ho).trans h1

theorem short_keepsC (w : Wt) (x : E × Y.St) (c : (shortHonC Y F Ex msg).Coin)
    (ρ : Rho (shapeSC Y)) : (((shortHonC Y F Ex msg).strat w x c).run ρ).2.2 = w := by
  have hk : (((Y.honC Ex msg).strat w x ()).run (rhoSC Y ρ)).2.2 = w :=
    congrArg Prod.snd (psc_run E Y Ex Wt msg w x (rhoSC Y ρ)).2.2.2
  have hr := shortStratC_run Y F x.2 ((Y.honC Ex msg).strat w x ()) ρ
  have hr' : ((shortHonC Y F Ex msg).strat w x c).run ρ = _ := hr
  rw [hr']
  exact hk

theorem short_honAtC (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (hV : Y.VarsOK) (hD : Y.DegOK)
    (M Wp Kc : Type) (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) :
    HonAt (shortRC Y F Ex) (shortHonC Y F Ex fun w : M × Wp => msg w.1)
      (Y.baseIn A0 fun w => msg w.1) (Y.baseMid A0 fun w => msg w.1) (shortNC Y F Ex Kc) where
  acc := fun x y w c ρ hw _ => by
    obtain ⟨h1, h2, h4⟩ := short_runC Y F Ex (fun w : M × Wp => msg w.1) hF hV hD w x hw.2 c y ρ
    have h5 := Y.outC_st x _ _ h1
    refine ⟨h1, ?_⟩
    show A0.rel _ y _ ∧ Y.MidHolds _ _
    rw [h4, h5]
    exact ⟨hw.1, h2⟩
  keeps := fun w x c ρ =>
    congrArg A0.core (short_keepsC Y F Ex (fun w : M × Wp => msg w.1) w x c ρ)
  prBad := by
    show prRho (∅ : Set (Rho (shapeSC Y))) ≤ 0
    simp [prRho]
  cover := fun _ _ _ h => h
  prCov := fun _ => by simp [prRho, shortNC]
  same := fun w x c ρ =>
    congrArg Prod.fst (short_keepsC Y F Ex (fun w : M × Wp => msg w.1) w x c ρ)

/-- The half on the honest prover, filled, under `HFixs.OK`. -/
noncomputable def shortHC (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) : ShortHC (shortKC Y F Ex) where
  H := fun {M Wp} msg => shortHonC Y F Ex fun w : M × Wp => msg w.1
  P := fun Kc => shortNC Y F Ex Kc
  err := fun _ => rfl
  hon := short_honAtC Y F Ex hF

/-! ### What the verifier puts out -/

/-- What the verifier puts out under `HFixs.OK` (`short_outC`). -/
def shortVC (x : E × Y.St) (τ : Tr (shapeSC Y)) : Y.Mid :=
  ⟨x.2, τ.2.1, (vFin Y.fmt (Y.dat x.2) (F x.2) (τ.1.2 + τ.2.1 * x.1) τ.2.2).2,
    (vFin Y.fmt (Y.dat x.2) (F x.2) (τ.1.2 + τ.2.1 * x.1) τ.2.2).1⟩

theorem short_outC (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (x : E × Y.St) (y : Ex.Str)
    (τ : Tr (shapeSC Y)) : (shortRC Y F Ex).out x y τ = some (shortVC Y F x τ) := by
  obtain ⟨m, ε, τ⟩ := τ
  have hc := cShort0_cons Y.fmt (Y.dat x.2) (F x.2) (hF x.2) (m.2 + ε * x.1) τ
  have hc' : HCons (Y.vars x.2)
      (Y.mu ((carryC Y x (F x.2)).tr (m, ε, τ)) + Y.eps ((carryC Y x (F x.2)).tr (m, ε, τ)) * x.1)
      (Y.qs x.2 ((carryC Y x (F x.2)).tr (m, ε, τ)))
      (Y.hp x.2 (Y.pt ((carryC Y x (F x.2)).tr (m, ε, τ)))) := hc
  show Y.outC x ((carryC Y x (F x.2)).tr (m, ε, τ)) = _
  unfold PscPar.outC
  rw [if_pos hc']
  have e1 : Y.pt ((carryC Y x (F x.2)).tr (m, ε, τ)) =
      (vFin Y.fmt (Y.dat x.2) (F x.2) (m.2 + ε * x.1) τ).2 :=
    vFin_pt Y.fmt (Y.dat x.2) (F x.2) (m.2 + ε * x.1) τ
  have e2 : hFin (Y.vars x.2)
      (Y.mu ((carryC Y x (F x.2)).tr (m, ε, τ)) + Y.eps ((carryC Y x (F x.2)).tr (m, ε, τ)) * x.1)
      (Y.qs x.2 ((carryC Y x (F x.2)).tr (m, ε, τ)))
      (Y.hp x.2 (Y.pt ((carryC Y x (F x.2)).tr (m, ε, τ)))) =
      (vFin Y.fmt (Y.dat x.2) (F x.2) (m.2 + ε * x.1) τ).1 :=
    vFin_fin Y.fmt (Y.dat x.2) (F x.2) (m.2 + ε * x.1) τ
  rw [e2, e1]
  rfl

end TWhole
