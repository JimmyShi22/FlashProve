-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Reads/HearStarts.lean: WITH WHICH FORM EACH OF FIVE SUMCHECKS OF K4's HEAR WAS
BEGUN: of slots and constants alone: SO THEIR OWN CLAIMS NAME NO ENTRY. Statements and proofs. It
pays five of the ten premises of `front_covered` and `back_covered`
(Johnson/Road/K4/Reads/Covered.lean).

`Ret x Φ`: wherever the plain function x returns, the value that it returns has Φ. Rules:
`Ret.pure`, `Ret.bind` (what the first returns may be used for the second), `Ret.skip` (it is not
used).
The masked sumcheck's functions (OnBytes/K/Kc/Flat.lean, QuietLink.lean) hand the start form on:
`ret_pscBegin`, `ret_pscRound`, `ret_roundIn`, `ret_pscEnds`, `ret_pscRow`, `ret_levelRounds`,
`ret_tscLoop`, `ret_wsForkRounds`. So: `ret_levelIn`: a layer's claim names what its start form C
names; `ret_tscIn`: a token sumcheck begins with a slot; `ret_flatForkEnd`: the merge begins with
`wsForkStart`, a sum of slots.
`hear_starts`: WHEREVER `hearFl` RETURNS o: for every Q: `EntsIn Q` of o.H.wpl.row, o.H.tV.p.start,
o.hd.row, the second gated layer's row, and the merge's start form: they name no entry at all.

Not here: the batched sumcheck's claim (its start form does name reads), the two end forms, and the
lookup's own two (K3's files'). One direction, from a return. THE SAME WALK STANDS FOR THE
ROUTINES OF THE PROGRAM `verify-on-bytes` (`Gives`, `levelIn_rows`, `tscIn_rows`:
OnBytes/Tie/Pv/Led/LedRowsLevel.lean); on the plain functions nothing of the kind is shown here.

`levelIn_tape`, NormsTape.lean and StackTape.lean walk the same returns for the tape; this file says
another thing of them (which entries a start form names) and stands on Flat.lean alone. Nothing on
soundness.
-/
import Johnson.Road.K4.Reads.RowsEnts
import OnBytes.Desc.First.K4.Plain
import OnBytes.Desc.First.FlGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Reads

open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc
open OnBytes.Desc.First.Grow (bind_some some_triple)

variable {α β : Type}

/-! ### What a plain function returns -/

/-- Wherever x returns, the value that it returns has Φ. -/
def Ret (x : Fl α) (Φ : α → Prop) : Prop :=
  ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → Φ a

theorem Ret.pure {a : α} {Φ : α → Prop} (h : Φ a) : Ret (Pure.pure a : Fl α) Φ :=
  fun _ _ _ _ _ e => (some_triple.mp e).1 ▸ h

theorem Ret.bind {x : Fl α} {f : α → Fl β} {Φ : α → Prop} {Ψ : β → Prop} (hx : Ret x Φ)
    (hf : ∀ a, Φ a → Ret (f a) Ψ) : Ret (x >>= f) Ψ := fun F t b G u e => by
  obtain ⟨a, G1, u1, h1, h2⟩ := bind_some.mp e
  exact hf a (hx F t a G1 u1 h1) G1 u1 b G u h2

theorem Ret.skip {x : Fl α} {f : α → Fl β} {Ψ : β → Prop} (hf : ∀ a, Ret (f a) Ψ) :
    Ret (x >>= f) Ψ :=
  Ret.bind (Φ := fun _ => True) (fun _ _ _ _ _ _ => trivial) fun a _ => hf a

/-! ### The masked sumcheck hands its start form on -/

theorem ret_pscBegin (C : Aff) : Ret (Fl.pscBegin C) fun p => p.start = C := by
  unfold Fl.pscBegin
  refine Ret.skip fun _ => Ret.skip fun _ => Ret.pure rfl

theorem ret_pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    Ret (Fl.pscRound p w draw) fun x => x.2.start = p.start := by
  unfold Fl.pscRound
  refine Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ =>
    Ret.pure rfl

theorem ret_roundIn (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    Ret (Fl.roundIn form p z d) fun x => x.2.start = p.start := by
  unfold Fl.roundIn
  exact Ret.skip fun _ => Ret.skip fun _ => ret_pscRound _ _ _

theorem ret_pscEnds (p : Psc) (d n : Nat) :
    Ret (Fl.pscEnds p d n) fun x => x.2.start = p.start := by
  unfold Fl.pscEnds
  refine Ret.skip fun _ => Ret.bind (ret_pscRound _ _ _) fun x hx => ?_
  obtain ⟨beta, q⟩ := x
  refine Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ =>
    Ret.pure hx

theorem ret_pscRow (p : Psc) (S0 : E) (kept : Aff) :
    Ret (Fl.pscRow p S0 kept) fun x => x.1 = p.rowForm S0 kept := by
  unfold Fl.pscRow
  exact Ret.skip fun _ => Ret.skip fun _ => Ret.pure rfl

theorem ret_levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p : Psc),
    Ret (Fl.levelRounds mu rho order r p) fun x => x.2.start = p.start
  | [], r, p => by
    unfold Fl.levelRounds
    exact Ret.pure rfl
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine Ret.skip fun _ => Ret.bind (ret_roundIn _ _ _ _) fun x hx => ?_
    obtain ⟨c, q⟩ := x
    exact fun F t a G u e => (ret_levelRounds mu rho order _ q F t a G u e).trans hx

/-- **A layer's claim names what its start form names.** -/
theorem ret_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Ret (Fl.levelIn mu rho C order) fun L =>
      ∀ Q : ℕ → ℕ → ℕ → Prop, EntsIn Q C → EntsIn Q L.row := by
  unfold Fl.levelIn
  refine Ret.skip fun _ => Ret.bind (ret_pscBegin C) fun p hp => ?_
  refine Ret.bind (ret_levelRounds _ _ _ _ p) fun x hx => ?_
  obtain ⟨r, p1⟩ := x
  refine Ret.bind (ret_pscEnds p1 2 2) fun x hx2 => ?_
  obtain ⟨sL, p2⟩ := x
  refine Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ =>
    Ret.bind (ret_pscRow p2 _ _) fun x hx3 => ?_
  obtain ⟨row, p3⟩ := x
  refine Ret.pure fun Q hC => ?_
  have e : p2.start = C := (hx2.trans hx).trans hp
  show EntsIn Q row
  rw [show row = _ from hx3]
  exact entsIn_rowForm _ _ (e ▸ hC) entsIn_empty

theorem ret_tscLoop : ∀ (zs : List E) (r : Array E) (p : Psc),
    Ret (Fl.tscLoop zs r p) fun x => x.2.start = p.start
  | [], r, p => by
    unfold Fl.tscLoop
    exact Ret.pure rfl
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine Ret.bind (ret_roundIn _ _ _ _) fun x hx => ?_
    obtain ⟨c, q⟩ := x
    exact fun F t a G u e => (ret_tscLoop zs _ q F t a G u e).trans hx

/-- **A token sumcheck begins with a slot.** -/
theorem ret_tscIn (P : Array E) (lt n d : Nat) :
    Ret (Fl.tscIn P lt n d) fun o => ∀ Q : ℕ → ℕ → ℕ → Prop, EntsIn Q o.p.start := by
  unfold Fl.tscIn Fl.tscRounds
  refine Ret.bind (Φ := fun o : Tsc => ∃ j, o.p.start = Aff.slot j) ?_ fun o ho => ?_
  · refine Ret.skip fun _ => Ret.skip fun sCl => Ret.bind (ret_pscBegin _) fun p hp => ?_
    refine Ret.bind (ret_tscLoop _ _ p) fun x hx => ?_
    obtain ⟨r, q⟩ := x
    exact Ret.pure ⟨sCl, hx.trans hp⟩
  · refine Ret.bind (ret_pscEnds o.p d n) fun x hx => ?_
    obtain ⟨sEnd, q⟩ := x
    obtain ⟨j, hj⟩ := ho
    refine Ret.pure fun Q => ?_
    show EntsIn Q q.start
    rw [show q.start = _ from hx, hj]
    exact entsIn_slot j

theorem ret_wsForkRounds : ∀ (n : Nat) (rm : Array E) (p : Psc),
    Ret (Fl.wsForkRounds n rm p) fun x => x.2.start = p.start
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    exact Ret.pure rfl
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine Ret.bind (ret_roundIn _ _ _ _) fun x hx => ?_
    obtain ⟨c, q⟩ := x
    exact fun F t a G u e => (ret_wsForkRounds n _ q F t a G u e).trans hx

theorem entsIn_wsForkStart {Q : ℕ → ℕ → ℕ → Prop} (sv : Array Nat) (rho : Array E) :
    EntsIn Q (wsForkStart sv rho) := by
  unfold wsForkStart
  rw [← Array.foldl_toList]
  exact entsIn_foldl _ (fun _ _ hf => entsIn_addMul _ hf (entsIn_slot _)) _ _ entsIn_empty

/-- **The merge begins with a sum of slots.** -/
theorem ret_flatForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    Ret (flatForkEnd lay cl sv) fun o =>
      ∀ Q : ℕ → ℕ → ℕ → Prop, EntsIn Q o.toWsMerged.p.start := by
  unfold flatForkEnd Fl.wsForkMerge
  refine Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ => ?_
  refine Ret.bind (Φ := fun x : WsMerged × Array E =>
    ∀ Q : ℕ → ℕ → ℕ → Prop, EntsIn Q x.1.p.start) ?_ fun x hx => ?_
  · refine Ret.skip fun rho => Ret.bind (ret_pscBegin _) fun p hp => ?_
    refine Ret.bind (ret_wsForkRounds _ _ p) fun x hx => ?_
    obtain ⟨rm, p1⟩ := x
    refine Ret.bind (ret_pscEnds p1 1 1) fun x hx2 => ?_
    obtain ⟨sFv, p2⟩ := x
    refine Ret.skip fun _ => Ret.pure fun Q => ?_
    show EntsIn Q p2.start
    rw [show p2.start = _ from (hx2.trans hx).trans hp]
    exact entsIn_wsForkStart _ _
  · obtain ⟨o, rho⟩ := x
    exact Ret.pure hx

/-! ### HEAR -/

theorem entsIn_normsStart {Q : ℕ → ℕ → ℕ → Prop} (y : Lay) (sW : Nat) (gp rhoI PV : Array E) :
    EntsIn Q (normsStart y sW gp rhoI PV).1 := by
  unfold normsStart
  exact entsIn_foldl _ (fun _ _ hf =>
    entsIn_foldl _ (fun _ _ hg => entsIn_addMul _ hg (entsIn_slot _)) _ _ hf) _ _
    (entsIn_ofConst _)

/-- What is kept of the norms' messages. -/
def NormsOk (H : Heard) : Prop :=
  ∀ Q : ℕ → ℕ → ℕ → Prop, EntsIn Q H.wpl.row ∧ EntsIn Q H.tV.p.start

theorem ret_hearNorms (P : Pub) (g : Nat) (fo : Forest.Heard) :
    Ret (hearNorms engFl P g fo) NormsOk := by
  unfold hearNorms
  repeat' first
    | refine Ret.bind (ret_levelIn _ _ _ _) fun wpl hw => ?_
    | refine Ret.bind (ret_tscIn _ _ _ _) fun tV ht => ?_
    | refine Ret.skip fun _ => ?_
    | split
  all_goals exact Ret.pure fun Q => ⟨hw Q (entsIn_foldl _ (fun _ _ hf =>
    entsIn_foldl _ (fun _ _ hg => entsIn_addMul _ hg (entsIn_slot _)) _ _ hf) _ _
    (entsIn_ofConst _)), ht Q⟩

theorem ret_hearTerms (P : Pub) (H : Heard) (hH : NormsOk H) :
    Ret (hearTerms engFl P H) NormsOk := by
  unfold hearTerms
  refine Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun x => ?_
  obtain ⟨row, p⟩ := x
  exact Ret.pure hH

theorem ret_hearGated (P : Pub) (H : Heard) (K : HeardStack) :
    Ret (hearGated engFl P H K) fun x =>
      ∀ Q : ℕ → ℕ → ℕ → Prop, EntsIn Q x.1.row ∧ EntsIn Q x.2.row := by
  unfold hearGated
  refine Ret.bind (ret_levelIn _ _ _ _) fun hd h1 => ?_
  refine Ret.skip fun _ => Ret.skip fun _ => Ret.bind (ret_levelIn _ _ _ _) fun hd2 h2 => ?_
  refine Ret.pure fun Q => ⟨h1 Q (entsIn_slot _), h2 Q ?_⟩
  exact entsIn_foldl _ (fun _ _ hf => entsIn_addMul _ hf (entsIn_slot _)) _ _ (entsIn_ofConst _)

/-- What is kept of HEAR's return. -/
def StartsOk (o : Own) : Prop :=
  ∀ Q : ℕ → ℕ → ℕ → Prop, EntsIn Q o.H.wpl.row ∧ EntsIn Q o.H.tV.p.start ∧ EntsIn Q o.hd.row ∧
    (∀ x, o.hd2 = some x → EntsIn Q x.row) ∧ EntsIn Q o.wo.toWsMerged.p.start

theorem ret_hear (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) :
    Ret (hear engFl P hp g fo) StartsOk := by
  unfold hear
  iterate 3 refine Ret.skip fun _ => ?_
  refine Ret.bind (ret_hearNorms P g fo) fun H0 h0 => ?_
  refine Ret.bind (ret_hearTerms P H0 h0) fun H hH => ?_
  refine Ret.skip fun _ => Ret.skip fun x => ?_
  obtain ⟨tab, laid, nU3⟩ := x
  refine Ret.skip fun _ => Ret.skip fun K => Ret.bind (ret_hearGated P H K) fun x hx => ?_
  obtain ⟨hd, hd2⟩ := x
  repeat' first
    | refine Ret.bind (ret_flatForkEnd _ _ _) fun wo hwo => ?_
    | refine Ret.skip fun _ => ?_
    | split
  all_goals
    refine Ret.pure fun Q => ⟨(hH Q).1, (hH Q).2, (hx Q).1, fun x e => ?_, hwo Q⟩
    obtain rfl := Option.some.inj e
    exact (hx Q).2

/-- **WHEREVER HEAR RETURNS, FIVE OF ITS SUMCHECKS' FORMS NAME NO ENTRY.** -/
theorem hear_starts {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, G, u)) : StartsOk o :=
  ret_hear P hp g fo F t o G u h

end OnBytes.Desc.First.K4.Reads
