-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/Short.lean: the rule for a second zero test at the sumcheck with short messages
(`shortR`, Cb/G6/Carried.lean): which short round draws which coordinate, and the rule at `KnowAt`
and at `GoodAt`.

Definitions, statements and proofs. No protocol of its own: the reduction, its counts, its joints
and its theorems are those of Cb/G6/Carried.lean, taken as they stand.

The short sumcheck's verifier completes each message and then is the verifier of the long block
`Y.psc Ex` on the completed transcript. The completion changes messages alone: the completed
transcript has the short transcript's own challenges (`carryS_rho`). So whatever is known on which
round of the long block draws which coordinate of its output statement holds of the short block,
round for round.

Main names:
  `toShort`, `shortB`: a `Binds` on the long rounds read on the short rounds, round for round.
  `cShort_rho`, `carryS_rho`: the completed transcript has the short transcript's challenges.
  `psc_carries`: `Carries` (Cb/G6/Rider/Carrier.lean) of the long block: coordinate t of the reader
    is coordinate pl t of the output statement's point, drawn in the round of variable pl t.
  `short_carries`: from any `Carries` of the long block at its own counts, `Carries` of the short
    block at its own counts, with the same coordinates and the same reader. No premise on the pick F
    of the powers that are left out (at a pick that is not lawful the short verifier rejects, and
    these statements hold vacuously: Cb/G6/Carried.lean).
  `short_rider`: the rule at `KnowAt`, between the sumcheck's own two joints, each with the rider.
  `short_rider_in`: the safe form of `short_rider`: the source comes in inside the relation A0 that
    rides along and does not come out.
  `short_rider_good`: the rule at `GoodAt`, with the honest side of Cb/G6/Carried.lean, under
    `HFixs.OK` in addition.
  `short_hollow`: an empty use.
  `psc_carries_sel`: `psc_carries` for any naming sel of the rounds of the variables.
  `short_passes`, `shortC_passes`: both short blocks hand the state on.
  `v0_carries`, `v0C_carries`: `short_carries` and `shortC_carries` at the letters `V₀`, `V₀C` of
    Cb/G6/Pick.lean.
  `toShort0`, `shortBC`, `carryC_rho`, `core_carries_sel`, `shortC_carries`: the same for the block
    without the round of values (`shortRC`, Cb/G6/Core.lean), whose output statement is `Y.Mid`.

Limits: for a free letter `V : ShortK Y Ex` (Cb/G6/Letter.lean) no `Carries` can be had: the record
lays no law on what `V.R` puts out. [An argument in words; no theorem here.] The statements here are
of the filled letters. A0 is a free letter. `Y.baseIn A0` and `Y.baseOut A0` hand A0 out as it came
in; a source that stands in A0 at this block makes the statement with the rider empty
(`short_hollow`). The file speaks of one sumcheck. It does not say anything on a line step, a level
of a product tree or a lookup over short sumchecks; their `Carries` would go by the rules of
Cb/G6/Rider/Carrier.lean from `short_carries`. It fixes neither the pick F nor an order of the
variables. The two sentences that a use of the rule should prove are proved at no block of this
library: neither `short_carries` nor `shortC_carries` has a test of its own.

Terms: lean/GLOSSARY.md.
-/
import Cb.G6.Pick
import Cb.G6.Rider.KnowAt

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks TWhole Johnson.L5.Layers Johnson.L5.Door

/-! ## 1. A `Binds` on the long rounds, read on the short rounds -/

section Foot
variable {E : Type} [Field E]

/-- A short round has the long round's challenges, so what a long round binds the short round binds.
The rounds of t behind them are left as they are. -/
def toShort : (l : List (PFmt E)) → (t : Shape) → Binds ℕ E (pRounds l ++ t) →
    Binds ℕ E (sRounds l ++ t)
  | [], _, b => b
  | _ :: l, t, (o, b) => (o, toShort l t b)

theorem toShort_vars : ∀ (l : List (PFmt E)) (t : Shape) (b : Binds ℕ E (pRounds l ++ t)),
    (toShort l t b).vars = b.vars
  | [], _, _ => rfl
  | _ :: l, t, (Option.none, b) => toShort_vars l t b
  | _ :: l, t, (some (k, _), b) => congrArg (k :: ·) (toShort_vars l t b)

theorem toShort_inj : ∀ (l : List (PFmt E)) (t : Shape) (b : Binds ℕ E (pRounds l ++ t)),
    b.Inj → (toShort l t b).Inj
  | [], _, _, h => h
  | _ :: l, t, (Option.none, b), h => toShort_inj l t b h
  | _ :: l, t, (some _, b), h => ⟨h.1, toShort_inj l t b h.2⟩

theorem toShort_pt : ∀ (l : List (PFmt E)) (t : Shape) (b : Binds ℕ E (pRounds l ++ t))
    (ρ : Rho (sRounds l ++ t)) (z : ℕ → E), (toShort l t b).pt ρ z = b.pt (rhoL l t ρ) z
  | [], _, _, _, _ => rfl
  | _ :: l, t, (Option.none, b), (_, ρ), z => toShort_pt l t b ρ z
  | _ :: l, t, (some _, b), (_, ρ), _ => toShort_pt l t b ρ _

omit [Field E] in
theorem errTo_self : ∀ (s : Shape) (ε : Err s), errTo s s ε = ε
  | [], _ => rfl
  | _ :: s, (e, ε) => congrArg (fun x => (e, x)) (errTo_self s ε)

omit [Field E] in
theorem errTo_le : ∀ (s s' : Shape) (a b : Err s'), Err.le a b →
    Err.le (errTo s s' a) (errTo s s' b)
  | [], _, _, _, _ => trivial
  | _ :: s, [], _, _, _ => ⟨Nat.le_refl 0, errTo_le s [] () () trivial⟩
  | _ :: s, _ :: s', (_, a), (_, b), h => ⟨h.1, errTo_le s s' a b h.2⟩

theorem toShort_err (d : ℕ → ℕ) : ∀ (l : List (PFmt E)) (t : Shape)
    (b : Binds ℕ E (pRounds l ++ t)),
    (toShort l t b).err d = errTo (sRounds l ++ t) (pRounds l ++ t) (b.err d)
  | [], t, b => (errTo_self t (b.err d)).symm
  | _ :: l, t, (Option.none, b) => congrArg (fun x => (0, x)) (toShort_err d l t b)
  | _ :: l, t, (some (k, _), b) => congrArg (fun x => (d k, x)) (toShort_err d l t b)

/-- The completed transcript has the short transcript's own challenges. -/
theorem cShort_rho : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E) (t : Shape)
    (τ : Tr (sRounds l ++ t)), ((cShort l d F σ t).tr τ).rho = rhoL l t τ.rho
  | [], _, _, _, t, τ => congrArg Tr.rho (Carry.tr_refl t τ)
  | f :: l, d, F, σ, t, (m, c, τ) =>
    congrArg (fun x => (c, x))
      (cShort_rho l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t τ)

end Foot

/-! ## 2. The long block and the short block carry the same coordinates -/

section Short
variable {E : Type} [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec)

/-- A `Binds` on the long block's rounds, read on the short block's rounds, round for round. -/
def shortB (β : Binds ℕ E (Y.psc Ex).shape) : Binds ℕ E (shapeS Y) :=
  ((show Binds ℕ E (pRound0 E :: (pRounds Y.fmt ++ [pRoundV E Y.A])) from β).1,
    toShort Y.fmt [pRoundV E Y.A]
      (show Binds ℕ E (pRound0 E :: (pRounds Y.fmt ++ [pRoundV E Y.A])) from β).2)

theorem shortB_vars (β : Binds ℕ E (Y.psc Ex).shape) : (shortB Y Ex β).vars = β.vars :=
  match (show Binds ℕ E (pRound0 E :: (pRounds Y.fmt ++ [pRoundV E Y.A])) from β) with
  | (Option.none, b) => toShort_vars Y.fmt _ b
  | (some (k, _), b) => congrArg (k :: ·) (toShort_vars Y.fmt _ b)

theorem shortB_inj (β : Binds ℕ E (Y.psc Ex).shape) (h : β.Inj) : (shortB Y Ex β).Inj :=
  match (show Binds ℕ E (pRound0 E :: (pRounds Y.fmt ++ [pRoundV E Y.A])) from β), h with
  | (Option.none, b), h => toShort_inj Y.fmt _ b h
  | (some _, b), h => ⟨h.1, toShort_inj Y.fmt _ b h.2⟩

theorem shortB_pt (β : Binds ℕ E (Y.psc Ex).shape) (ρ : Rho (shapeS Y)) (z : ℕ → E) :
    (shortB Y Ex β).pt ρ z = β.pt (rhoS Y Ex ρ) z :=
  match (show Binds ℕ E (pRound0 E :: (pRounds Y.fmt ++ [pRoundV E Y.A])) from β), ρ with
  | (Option.none, b), (_, ρ) => toShort_pt Y.fmt _ b ρ z
  | (some _, b), (_, ρ) => toShort_pt Y.fmt _ b ρ _

theorem shortB_err (d : ℕ → ℕ) (β : Binds ℕ E (Y.psc Ex).shape) :
    (shortB Y Ex β).err d = errTo (shapeS Y) (Y.psc Ex).shape (β.err d) :=
  match (show Binds ℕ E (pRound0 E :: (pRounds Y.fmt ++ [pRoundV E Y.A])) from β) with
  | (Option.none, b) => congrArg (fun x => (0, x)) (toShort_err d Y.fmt _ b)
  | (some (k, _), b) => congrArg (fun x => (d k, x)) (toShort_err d Y.fmt _ b)

/-- The completed transcript of the short block has the short transcript's own challenges. -/
theorem carryS_rho (x : E × Y.St) (G : HFixs (Y.vars x.2)) (τ : Tr (shapeS Y)) :
    ((carryS Y x G Ex).tr τ).rho = rhoS Y Ex τ.rho :=
  match τ with
  | (m, ε, τ) =>
    congrArg (fun r => (ε, r)) (cShort_rho Y.fmt (Y.dat x.2) G (m.2 + ε * x.1) [pRoundV E Y.A] τ)

/-- The long block: coordinate t < g of the reader is coordinate pl t of the point in the output
statement, and it is the challenge of the round of variable pl t. The places are different, in range
and of degree at least 1. -/
theorem psc_carries (hI : Y.ValInj) (g : ℕ) (pl : ℕ → ℕ)
    (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t') (hlt : ∀ t < g, pl t < Y.fmt.length)
    (hn : ∀ t < g, ∀ φ, Y.fmt[pl t]? = some φ → 1 ≤ φ.n) :
    Carries (Y.psc Ex) (pscBinds Y Ex (selPl g pl)) (Y.err Ex) (fun t => t < g)
      fun o t => ptAt Y.fmt o.pt (pl t) where
  inj := inj_pscBinds Y Ex _ hI
  mem := fun t ht => by
    rw [vars_pscBinds, mem_vars_bindsV]
    exact ⟨pl t, hlt t ht, by rw [Nat.zero_add]; exact selPl_apply hpl ht⟩
  rd := fun x y τ o z h t ht => by
    rw [pt_pscBinds, pt_bindsV (selPl g pl) (fun _ _ _ => selPl_inj) Y.fmt 0 _ z (pl t) t (hlt t ht)
      (by rw [Nat.zero_add]; exact selPl_apply hpl ht), (psc_out_pt Y Ex x y τ o h).2]
  le := psc_rider_err_le Y Ex g pl hn

variable (F : ∀ st, HFixs (Y.vars st))

/-- The short block carries what the long block carries: the same coordinates, the same reader, each
drawn in the short round of the same variable; the counts are each block's own. No premise on F. -/
theorem short_carries {β : Binds ℕ E (Y.psc Ex).shape} {T : ℕ → Prop} {r : Y.Out → ℕ → E}
    (C : Carries (Y.psc Ex) β (Y.err Ex) T r) :
    Carries (shortR Y F Ex) (shortB Y Ex β) (shortE Y Ex) T r where
  inj := shortB_inj Y Ex β C.inj
  mem := fun k hk => by
    show k ∈ Binds.vars (s := shapeS Y) (shortB Y Ex β)
    rw [shortB_vars]
    exact C.mem k hk
  rd := fun x y τ o z h k hk => by
    have h' : (Y.psc Ex).out x y ((carryS Y x (F x.2) Ex).tr τ) = some o := h
    have e := C.rd x y _ o z h' k hk
    rw [carryS_rho] at e
    rw [← e]
    exact congrFun (shortB_pt Y Ex β τ.rho z) k
  le := by
    show Err.le (s := shapeS Y) (Binds.err (fun _ => 1) (s := shapeS Y) (shortB Y Ex β))
      (shortE Y Ex)
    rw [shortB_err]
    exact errTo_le _ _ _ _ C.le

/-! ## 3. The rule at the short block -/

/-- The rule at the sumcheck with short messages, at `KnowAt`: reduction, extractor and counts are
those of `short_knowAt` (Cb/G6/Carried.lean), which is used as a black box. Source: every array of
the family is 0 at every vertex of the cube of dimension g. Target: its multilinear extension is 0
at the coordinates pl 0, .., pl (g - 1) of the sumcheck's point. No premise on F. Warning: A0 is
free; where A0, or the sum claim, gives the source, this says nothing (`short_hollow`,
`knowAt_hollow_own`). -/
theorem short_rider (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (M Wp Kc ι : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) (g : ℕ) (pl : ℕ → ℕ)
    (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t') (hlt : ∀ t < g, pl t < Y.fmt.length)
    (hn : ∀ t < g, ∀ φ, Y.fmt[pl t]? = some φ → 1 ≤ φ.n) (f : ι → Y.St → M → ℕ → E) :
    KnowAt (shortR Y F Ex) (withRider (Y.baseIn A0 fun w => msg w.1) fun m a => OnCube g f a.1.2 m)
      (withRider (Y.baseOut A0 fun w => msg w.1) fun m o => AtPoint g pl f Y.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (shortE Y Ex) :=
  knowAt_cubes (short_knowAt Y F Ex hV hD hI M Wp Kc A0 msg)
    (short_carries Y Ex F (psc_carries Y Ex hI g pl hpl hlt hn)) (fun _ : ι => g) (fun _ t => t)
    (fun _ => ⟨fun _ _ _ _ e => e, fun _ ht => ht⟩) (fun i m a => f i a.1.2 m)
    (fun i m o => f i o.1.st m) fun i m a τ o ho X _ => by
      show f i o.1.st m X = f i a.1.2 m X
      rw [psc_st Y Ex a.1 a.2 _ o.1 (red_out ho)]

/-- The safe form of `short_rider`. The source comes in inside the relation A0 that rides along, and
does not come out: the output joint rides over A0 alone and has the target. It is still an empty use
if A0 itself, or the sum claim, gives the source (`knowAt_hollow_own`). -/
theorem short_rider_in (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (M Wp Kc ι : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) (g : ℕ) (pl : ℕ → ℕ)
    (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t') (hlt : ∀ t < g, pl t < Y.fmt.length)
    (hn : ∀ t < g, ∀ φ, Y.fmt[pl t]? = some φ → 1 ≤ φ.n) (f : ι → Y.St → M → ℕ → E) :
    KnowAt (shortR Y F Ex) (Y.baseIn (withRider A0 fun m s => OnCube g f s.1 m) fun w => msg w.1)
      (withRider (Y.baseOut A0 fun w => msg w.1) fun m o => AtPoint g pl f Y.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (shortE Y Ex) :=
  have h := short_rider Y Ex F hV hD hI M Wp Kc ι A0 msg g pl hpl hlt hn f
  ⟨h.point, h.isLocal, h.onOut, fun m a ha =>
    Doomed.mono _ _ (fun _ hτ b w hb hw =>
      ⟨⟨(hτ b w hb hw).1.1, (hτ b w hb hw).2⟩, (hτ b w hb hw).1.2⟩) (h.know m a ha)⟩

/-- The rule at `GoodAt`, with the honest side and the numbers of Cb/G6/Carried.lean (`shortH`),
under `HFixs.OK` in addition. Warning: A0 is free, as in `short_rider`. -/
theorem short_rider_good (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (hV : Y.VarsOK) (hD : Y.DegOK)
    (hI : Y.ValInj) (M Wp Kc ι : Type) (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E)
    (g : ℕ) (pl : ℕ → ℕ) (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t')
    (hlt : ∀ t < g, pl t < Y.fmt.length) (hn : ∀ t < g, ∀ φ, Y.fmt[pl t]? = some φ → 1 ≤ φ.n)
    (f : ι → Y.St → M → ℕ → E) :
    GoodAt (shortR Y F Ex) (shortHon Y F Ex fun w : M × Wp => msg w.1)
      (withRider (Y.baseIn A0 fun w => msg w.1) fun m a => OnCube g f a.1.2 m)
      (withRider (Y.baseOut A0 fun w => msg w.1) fun m o => AtPoint g pl f Y.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (shortN Y F Ex Kc) :=
  goodAt_cubes ((shortH Y F Ex hF).good hV hD hI M Wp Kc A0 msg)
    (short_carries Y Ex F (psc_carries Y Ex hI g pl hpl hlt hn)) (fun _ : ι => g) (fun _ t => t)
    (fun _ => ⟨fun _ _ _ _ e => e, fun _ ht => ht⟩) (fun i m a => f i a.1.2 m)
    (fun i m o => f i o.1.st m) fun i m a τ o ho X _ => by
      show f i o.1.st m X = f i a.1.2 m X
      rw [psc_st Y Ex a.1 a.2 _ o.1 (red_out ho)]

/-- An empty use. With the source inside the relation that rides along on both sides, the very
conclusion of `short_rider` follows from `short_knowAt` alone, for any places pl (they need not be
different, nor in range): the output joint still holds the source. -/
theorem short_hollow (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (M Wp Kc ι : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) (g : ℕ) (pl : ℕ → ℕ)
    (f : ι → Y.St → M → ℕ → E) :
    KnowAt (shortR Y F Ex)
      (withRider (Y.baseIn (withRider A0 fun m s => OnCube g f s.1 m) fun w => msg w.1)
        fun m a => OnCube g f a.1.2 m)
      (withRider (Y.baseOut (withRider A0 fun m s => OnCube g f s.1 m) fun w => msg w.1)
        fun m o => AtPoint g pl f Y.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (shortE Y Ex) :=
  knowAt_hollow_own
    (short_knowAt Y F Ex hV hD hI M Wp Kc (withRider A0 fun m s => OnCube g f s.1 m) msg) _ _
    fun _ _ _ h => h.1.2

/-! ## 4. Any naming of the rounds; the state is handed on; the letters of Cb/G6/Pick.lean -/

/-- The list 1 | 0 of any naming sel lies below the long block's own counts, if each named variable
has degree at least 1. -/
theorem pscBinds_err_le (sel : ℕ → Option ℕ)
    (hn : ∀ j φ k, Y.fmt[j]? = some φ → sel j = some k → 1 ≤ φ.n) :
    Err.le ((pscBinds Y Ex sel).err fun _ => 1) (Y.err Ex) := by
  have e1 : (pscBinds Y Ex sel).err (fun _ => 1) =
      Err.app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
        (Binds.err (fun _ => 1)
          ((none, bindsV sel 0 Y.fmt) : Binds ℕ E (pRound0 E :: pRounds Y.fmt)))
        (Binds.err (fun _ => 1) ((none, ()) : Binds ℕ E [pRoundV E Y.A])) :=
    Binds.err_app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape) (fun _ => 1) _ _
  rw [e1]
  refine Iop.Err.le_app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape) (a' := Y.errC Ex)
    (b' := (0, ())) ⟨Nat.zero_le _, ?_⟩ ⟨Nat.le_refl _, trivial⟩
  refine err_bindsV_le _ Y.fmt 0 fun j φ k hφ hk => ?_
  rw [Nat.zero_add] at hk
  exact hn j φ k hφ hk

/-- The long block, for any naming sel of the rounds of the variables: sel j = some k says that the
round of variable j draws coordinate k. T says of which coordinates the statement speaks, pl k is
the variable whose round draws k. No coordinate is named twice; each named variable has degree at
least 1. -/
theorem psc_carries_sel (hI : Y.ValInj) (sel : ℕ → Option ℕ)
    (hsel : ∀ i i' k, sel i = some k → sel i' = some k → i = i') (T : ℕ → Prop) (pl : ℕ → ℕ)
    (hT : ∀ k, T k → pl k < Y.fmt.length ∧ sel (pl k) = some k)
    (hn : ∀ j φ k, Y.fmt[j]? = some φ → sel j = some k → 1 ≤ φ.n) :
    Carries (Y.psc Ex) (pscBinds Y Ex sel) (Y.err Ex) T fun o k => ptAt Y.fmt o.pt (pl k) where
  inj := inj_pscBinds Y Ex _ hI
  mem := fun k hk => by
    rw [vars_pscBinds, mem_vars_bindsV]
    exact ⟨pl k, (hT k hk).1, by rw [Nat.zero_add]; exact (hT k hk).2⟩
  rd := fun x y τ o z h k hk => by
    rw [pt_pscBinds, pt_bindsV sel hsel Y.fmt 0 _ z (pl k) k (hT k hk).1
      (by rw [Nat.zero_add]; exact (hT k hk).2), (psc_out_pt Y Ex x y τ o h).2]
  le := pscBinds_err_le Y Ex sel hn

/-- The short block hands the state on. -/
theorem short_passes : (shortR Y F Ex).Passes Prod.snd PscPar.Out.st :=
  fun x y _ o h => psc_st Y Ex x y _ o h

/-- The short block without the round of values hands the state on. -/
theorem shortC_passes : (shortRC Y F Ex).Passes Prod.snd PscPar.Mid.st :=
  fun x _ _ z h => Y.outC_st x _ z h

/-- `short_carries` at the letter `V₀` of Cb/G6/Pick.lean. -/
theorem v0_carries {β : Binds ℕ E (Y.psc Ex).shape} {T : ℕ → Prop} {r : Y.Out → ℕ → E}
    (C : Carries (Y.psc Ex) β (Y.err Ex) T r) :
    Carries (V₀ Y Ex).R (shortB Y Ex β) (V₀ Y Ex).ε T r :=
  short_carries Y Ex (F₀ Y) C

end Short

/-! ## 5. The block without the round of values -/

section Foot0
variable {E : Type} [Field E]

/-- `toShort` without further rounds behind. -/
def toShort0 : (l : List (PFmt E)) → Binds ℕ E (pRounds l) → Binds ℕ E (sRounds l)
  | [], b => b
  | _ :: l, (o, b) => (o, toShort0 l b)

theorem toShort0_vars : ∀ (l : List (PFmt E)) (b : Binds ℕ E (pRounds l)),
    (toShort0 l b).vars = b.vars
  | [], _ => rfl
  | _ :: l, (Option.none, b) => toShort0_vars l b
  | _ :: l, (some (k, _), b) => congrArg (k :: ·) (toShort0_vars l b)

theorem toShort0_inj : ∀ (l : List (PFmt E)) (b : Binds ℕ E (pRounds l)),
    b.Inj → (toShort0 l b).Inj
  | [], _, h => h
  | _ :: l, (Option.none, b), h => toShort0_inj l b h
  | _ :: l, (some _, b), h => ⟨h.1, toShort0_inj l b h.2⟩

theorem toShort0_pt : ∀ (l : List (PFmt E)) (b : Binds ℕ E (pRounds l)) (ρ : Rho (sRounds l))
    (z : ℕ → E), (toShort0 l b).pt ρ z = b.pt (rhoL0 l ρ) z
  | [], _, _, _ => rfl
  | _ :: l, (Option.none, b), (_, ρ), z => toShort0_pt l b ρ z
  | _ :: l, (some _, b), (_, ρ), _ => toShort0_pt l b ρ _

theorem toShort0_err (d : ℕ → ℕ) : ∀ (l : List (PFmt E)) (b : Binds ℕ E (pRounds l)),
    (toShort0 l b).err d = errTo (sRounds l) (pRounds l) (b.err d)
  | [], _ => rfl
  | _ :: l, (Option.none, b) => congrArg (fun x => (0, x)) (toShort0_err d l b)
  | _ :: l, (some (k, _), b) => congrArg (fun x => (d k, x)) (toShort0_err d l b)

theorem cShort0_rho : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E)
    (τ : Tr (sRounds l)), ((cShort0 l d F σ).tr τ).rho = rhoL0 l τ.rho
  | [], _, _, _, _ => rfl
  | f :: l, d, F, σ, (m, c, τ) =>
    congrArg (fun x => (c, x))
      (cShort0_rho l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) τ)

end Foot0

section Core
variable {E : Type} [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec)

/-- A `Binds` on the rounds of `Y.core Ex`, read on the short rounds, round for round. -/
def shortBC (β : Binds ℕ E Y.shapeC) : Binds ℕ E (shapeSC Y) := (β.1, toShort0 Y.fmt β.2)

theorem shortBC_vars (β : Binds ℕ E Y.shapeC) : (shortBC Y β).vars = β.vars :=
  match β with
  | (Option.none, b) => toShort0_vars Y.fmt b
  | (some (k, _), b) => congrArg (k :: ·) (toShort0_vars Y.fmt b)

theorem shortBC_inj (β : Binds ℕ E Y.shapeC) (h : β.Inj) : (shortBC Y β).Inj :=
  match β, h with
  | (Option.none, b), h => toShort0_inj Y.fmt b h
  | (some _, b), h => ⟨h.1, toShort0_inj Y.fmt b h.2⟩

theorem shortBC_pt (β : Binds ℕ E Y.shapeC) (ρ : Rho (shapeSC Y)) (z : ℕ → E) :
    (shortBC Y β).pt ρ z = β.pt (rhoSC Y ρ) z :=
  match β, ρ with
  | (Option.none, b), (_, ρ) => toShort0_pt Y.fmt b ρ z
  | (some _, b), (_, ρ) => toShort0_pt Y.fmt b ρ _

theorem shortBC_err (d : ℕ → ℕ) (β : Binds ℕ E Y.shapeC) :
    (shortBC Y β).err d = errTo (shapeSC Y) Y.shapeC (β.err d) :=
  match β with
  | (Option.none, b) => congrArg (fun x => (0, x)) (toShort0_err d Y.fmt b)
  | (some (k, _), b) => congrArg (fun x => (d k, x)) (toShort0_err d Y.fmt b)

theorem carryC_rho (x : E × Y.St) (G : HFixs (Y.vars x.2)) (τ : Tr (shapeSC Y)) :
    ((carryC Y x G).tr τ).rho = rhoSC Y τ.rho :=
  match τ with
  | (m, ε, τ) => congrArg (fun r => (ε, r)) (cShort0_rho Y.fmt (Y.dat x.2) G (m.2 + ε * x.1) τ)

/-- The long block without the round of values, for any naming sel of the rounds of the variables;
the letters are those of `psc_carries_sel`; the reader is on `Y.Mid`. -/
theorem core_carries_sel (hI : Y.ValInj) (sel : ℕ → Option ℕ)
    (hsel : ∀ i i' k, sel i = some k → sel i' = some k → i = i') (T : ℕ → Prop) (pl : ℕ → ℕ)
    (hT : ∀ k, T k → pl k < Y.fmt.length ∧ sel (pl k) = some k)
    (hn : ∀ j φ k, Y.fmt[j]? = some φ → sel j = some k → 1 ≤ φ.n) :
    Carries (Y.core Ex) ((none, bindsV sel 0 Y.fmt) : Binds ℕ E (pRound0 E :: pRounds Y.fmt))
      (Y.errC Ex) T fun z k => ptAt Y.fmt z.pt (pl k) where
  inj := inj_bindsV sel Y.fmt 0 hI
  mem := fun k hk => by
    show k ∈ (bindsV sel 0 Y.fmt).vars
    rw [mem_vars_bindsV]
    exact ⟨pl k, (hT k hk).1, by rw [Nat.zero_add]; exact (hT k hk).2⟩
  rd := fun x _ τ o z h k hk => by
    have hp : o.pt = pG Y.fmt τ.rho.2 := by
      have h' : Y.outC x τ = some o := h
      unfold PscPar.outC at h'
      split at h'
      · obtain rfl := Option.some.inj h'
        rfl
      · exact absurd h' (by simp)
    show (bindsV sel 0 Y.fmt).pt τ.rho.2 z k = _
    rw [pt_bindsV sel hsel Y.fmt 0 _ z (pl k) k (hT k hk).1
      (by rw [Nat.zero_add]; exact (hT k hk).2), hp]
  le := ⟨Nat.zero_le _, err_bindsV_le _ Y.fmt 0 fun j φ k hφ hk => by
    rw [Nat.zero_add] at hk
    exact hn j φ k hφ hk⟩

variable (F : ∀ st, HFixs (Y.vars st))

/-- The short block without the round of values carries what the long one carries. No premise on F.
-/
theorem shortC_carries {β : Binds ℕ E Y.shapeC} {T : ℕ → Prop} {r : Y.Mid → ℕ → E}
    (C : Carries (Y.core Ex) β (Y.errC Ex) T r) :
    Carries (shortRC Y F Ex) (shortBC Y β) (shortEC Y Ex) T r where
  inj := shortBC_inj Y β C.inj
  mem := fun k hk => by
    show k ∈ Binds.vars (s := shapeSC Y) (shortBC Y β)
    rw [shortBC_vars]
    exact C.mem k hk
  rd := fun x y τ o z h k hk => by
    have h' : (Y.core Ex).out x y ((carryC Y x (F x.2)).tr τ) = some o := h
    exact (congrFun (shortBC_pt Y β τ.rho z) k).trans
      ((congrArg (fun ρ => β.pt ρ z k) (carryC_rho Y x (F x.2) τ).symm).trans
        (C.rd x y _ o z h' k hk))
  le := by
    show Err.le (s := shapeSC Y) (Binds.err (fun _ => 1) (s := shapeSC Y) (shortBC Y β))
      (shortEC Y Ex)
    rw [shortBC_err]
    exact errTo_le _ _ _ _ C.le

/-- `shortC_carries` at the letter `V₀C` of Cb/G6/Pick.lean. -/
theorem v0C_carries {β : Binds ℕ E Y.shapeC} {T : ℕ → Prop} {r : Y.Mid → ℕ → E}
    (C : Carries (Y.core Ex) β (Y.errC Ex) T r) :
    Carries (V₀C Y Ex).R (shortBC Y β) (V₀C Y Ex).ε T r :=
  shortC_carries Y Ex (F₀ Y) C

end Core

end Cb.Rider

#print axioms Cb.Rider.psc_carries
#print axioms Cb.Rider.short_carries
#print axioms Cb.Rider.short_rider
#print axioms Cb.Rider.short_rider_in
#print axioms Cb.Rider.short_rider_good
#print axioms Cb.Rider.short_hollow
#print axioms Cb.Rider.psc_carries_sel
#print axioms Cb.Rider.short_passes
#print axioms Cb.Rider.shortC_passes
#print axioms Cb.Rider.v0_carries
#print axioms Cb.Rider.core_carries_sel
#print axioms Cb.Rider.shortC_carries
#print axioms Cb.Rider.v0C_carries
