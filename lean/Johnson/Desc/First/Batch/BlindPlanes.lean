-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/BlindPlanes.lean: THE LOOKUP's RUN "planes" IS BLIND TO THE ADDING
(Johnson/Desc/First/Batch/ObjectsLaw.lean: Blind; Johnson/Desc/First/Batch/BlindFl.lean: Away). It
fills slots of the ledger (the leaves' hiding coefficients) and marks a debt. No Mathlib.
  `hid`: the three arrays that a filling of slots writes, laid anew; `addAll_hid`: laying them and
      adding claims commute. `addAll_quiet`: an adding leaves the number of slots and these three.
  `hideRun_away`: the filling of a run of slots is Away. `Away.ofFoldlM`: a fold of Away steps.
  `planesProg_away` · `planesCalls_is` · `planesCalls_blind`: under ONE premise: the caller's
      readers are not turned by an adding (`Unturned`).
Limits: under one premise on the caller's readers. A law on two programs' commuting. Nothing on
soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.BlindFl
import Johnson.Desc.First.Look.LookPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)

/-! ## the arrays that a filling writes -/

/-- The ledger with the marks of filled slots, what was shown and the factors laid anew. -/
def hid (F : Fork) (g : Array Bool) (v m : Array E) : Fork := { F with gotF := g, vp := v, mf := m }

theorem kapTake_hid (F : Fork) (g : Array Bool) (v m : Array E) (c : Nat) :
    (hid F g v m).kapTake c = (F.kapTake c).map fun x => (x.1, hid x.2 g v m) := by
  cases h1 : F.doorShutF <;> cases h2 : F.kapMapF.isEmpty <;> cases h3 : F.thetaDrawnF <;>
    cases h4 : (decide (c < F.planClaimsF) && F.kapMapF.size == F.planClaimsF &&
      !F.kapMapF.getD c true) <;>
    (simp [Fork.kapTake, Fork.kapAt, hid, h1, h2, h3, h4] <;> rfl)

theorem kap_hid (F : Fork) (g : Array Bool) (v m : Array E) :
    (hid F g v m).kap = F.kap.map fun x => (x.1, hid x.2 g v m) := by
  unfold Fork.kap
  rw [show (hid F g v m).nClaim = F.nClaim from rfl, kapTake_hid]
  cases F.kapTake F.nClaim <;> rfl

theorem push_hid (F : Fork) (g : Array Bool) (v m : Array E) (w : E) (a : Aff) :
    (hid F g v m).push w a = (F.push w a).map (hid · g v m) := by
  cases h1 : F.doorShutF <;> cases h2 : a.ents.foldlM (Fork.pushEnt w) F.trees <;>
    cases h3 : a.slots.foldlM (Fork.pushSlot w F.ns) F.LS <;>
    (simp [Fork.push, hid, h1, h2, h3] <;> rfl)

theorem pushRuns_hid (F : Fork) (g : Array Bool) (v m : Array E) (k : E) (runs : Array Run2) :
    (hid F g v m).pushRuns k runs = (F.pushRuns k runs).map (hid · g v m) := by
  cases h : runs.foldlM (pushRun k) F.trees <;>
    (simp [Fork.pushRuns, hid, h] <;> rfl)

theorem addWith_hid (k : Option E) (G : Fork) (cl : Claim) (g : Array Bool) (v m : Array E) :
    addWith k (hid G g v m) cl = (addWith k G cl).map (hid · g v m) := by
  cases k with
  | none => rfl
  | some k =>
    simp only [addWith, Option.bind]
    rw [push_hid]
    cases G.push k cl.form with
    | none => rfl
    | some P => exact pushRuns_hid P g v m k cl.runs

theorem addClaim_hid (F : Fork) (cl : Claim) (g : Array Bool) (v m : Array E) :
    addClaim (hid F g v m) cl = (addClaim F cl).map (hid · g v m) := by
  rw [addClaim_eq, addClaim_eq, kap_hid]
  cases F.kap with
  | none => rfl
  | some x => exact addWith_hid (weightOf F x cl) x.2 cl g v m

theorem addAll_hid (g : Array Bool) (v m : Array E) : ∀ (cs : List Claim) (F : Fork),
    addAll (hid F g v m) cs = (addAll F cs).map (hid · g v m) := by
  intro cs
  induction cs with
  | nil => intro F; rfl
  | cons c l ih =>
    intro F
    unfold addAll
    rw [List.foldlM_cons, List.foldlM_cons, addClaim_hid]
    cases addClaim F c with
    | none => rfl
    | some G => exact ih G

/-! ## an adding leaves the number of slots and these three arrays -/

/-- What a filling of slots reads and writes. -/
def quiet (F : Fork) : Nat × Array Bool × Array E × Array E := (F.ns, F.gotF, F.vp, F.mf)

theorem kapTake_quiet (F : Fork) (c : Nat) (x : E × Fork) (h : F.kapTake c = some x) :
    quiet x.2 = quiet F := by
  unfold Fork.kapTake at h
  split at h
  · simp at h
  · split at h
    · obtain ⟨k, _, hk⟩ := map_some h
      rw [← hk]
    · split at h
      · obtain ⟨k, _, hk⟩ := map_some h
        rw [← hk]
        rfl
      · simp at h

theorem kap_quiet (F : Fork) (x : E × Fork) (h : F.kap = some x) : quiet x.2 = quiet F := by
  unfold Fork.kap at h
  obtain ⟨y, hy, hx⟩ := map_some h
  rw [← hx]
  exact kapTake_quiet F F.nClaim y hy

theorem push_quiet (F G : Fork) (w : E) (a : Aff) (h : F.push w a = some G) :
    quiet G = quiet F := by
  unfold Fork.push at h
  split at h
  · simp at h
  · simp only at h
    split at h
    · injection h with h'
      rw [← h']
      rfl
    · simp at h

theorem pushRuns_quiet (F G : Fork) (k : E) (runs : Array Run2)
    (h : F.pushRuns k runs = some G) : quiet G = quiet F := by
  unfold Fork.pushRuns at h
  obtain ⟨tr, _, hG⟩ := map_some h
  rw [← hG]
  rfl

theorem addClaim_quiet (F G : Fork) (cl : Claim) (h : addClaim F cl = some G) :
    quiet G = quiet F := by
  unfold addClaim at h
  obtain ⟨x, hx, h1⟩ := bind_some h
  obtain ⟨k, _, h2⟩ := bind_some h1
  obtain ⟨P, hP, h3⟩ := bind_some h2
  rw [pushRuns_quiet P G k cl.runs h3, push_quiet x.2 P k cl.form hP, kap_quiet F x hx]

theorem addAll_quiet : ∀ (cs : List Claim) (F G : Fork), addAll F cs = some G →
    quiet G = quiet F := by
  intro cs
  induction cs with
  | nil =>
    intro F G h
    simp [addAll, pure] at h
    rw [h]
  | cons c l ih =>
    intro F G h
    unfold addAll at h
    rw [List.foldlM_cons] at h
    obtain ⟨H, hH, hl⟩ := bind_some h
    rw [ih H G hl, addClaim_quiet F H c hH]

/-! ## the filling of slots -/

/-- One slot filled, by what it reads. -/
theorem hide_eq (F : Fork) (j : Nat) (y f : E) :
    F.hide j y f =
      if decide (j < F.ns) && F.gotF.size == F.ns && !F.gotF.getD j true then
        some (hid F (F.gotF.set! j true) (F.vp.set! j y) (F.mf.set! j f))
      else none := rfl

/-- One slot filled, and the adding. -/
theorem hide_moves (F G : Fork) (cs : List Claim) (j : Nat) (y f : E) (h : addAll F cs = some G) :
    match F.hide j y f with
    | none => G.hide j y f = none
    | some F' => ∃ G', G.hide j y f = some G' ∧ addAll F' cs = some G' := by
  have hq := addAll_quiet cs F G h
  simp only [quiet, Prod.mk.injEq] at hq
  obtain ⟨h1, h2, h3, h4⟩ := hq
  rw [hide_eq, hide_eq, h1, h2, h3, h4]
  cases (decide (j < F.ns) && F.gotF.size == F.ns && !F.gotF.getD j true) with
  | false => simp
  | true =>
    simp only [if_true]
    exact ⟨_, rfl, by rw [addAll_hid, h]; rfl⟩

theorem hide_keeps (F F' : Fork) (cs : List Claim) (j : Nat) (y f : E)
    (h : F.hide j y f = some F') : (addAll F' cs).isSome = (addAll F cs).isSome := by
  rw [hide_eq] at h
  cases hc : (decide (j < F.ns) && F.gotF.size == F.ns && !F.gotF.getD j true) with
  | false =>
    rw [hc] at h
    simp at h
  | true =>
    rw [hc] at h
    simp only [if_true] at h
    injection h with h'
    rw [← h', addAll_hid]
    cases addAll F cs <;> rfl

/-- A run of slots filled, as a fold over a list. -/
theorem hideSteps_moves (f : E) (cs : List Claim) : ∀ (v : List E) (j : Nat) (F G : Fork),
    addAll F cs = some G →
    match v.foldlM (Fork.hideStep f) (j, F) with
    | none => v.foldlM (Fork.hideStep f) (j, G) = none
    | some x => ∃ G', v.foldlM (Fork.hideStep f) (j, G) = some (x.1, G') ∧
        addAll x.2 cs = some G' := by
  intro v
  induction v with
  | nil =>
    intro j F G h
    exact ⟨G, rfl, h⟩
  | cons y l ih =>
    intro j F G h
    have h1 := hide_moves F G cs j y f h
    simp only [List.foldlM_cons, Fork.hideStep]
    cases hF : F.hide j y f with
    | none =>
      simp only [hF] at h1
      simp [h1]
    | some F' =>
      simp only [hF] at h1
      obtain ⟨G', hG, hadd⟩ := h1
      simp only [hG, Option.map, bind, Option.bind]
      exact ih (j + 1) F' G' hadd

theorem hideSteps_keeps (f : E) (cs : List Claim) : ∀ (v : List E) (j : Nat) (F : Fork)
    (x : Nat × Fork), v.foldlM (Fork.hideStep f) (j, F) = some x →
    (addAll x.2 cs).isSome = (addAll F cs).isSome := by
  intro v
  induction v with
  | nil =>
    intro j F x h
    simp [pure] at h
    rw [← h]
  | cons y l ih =>
    intro j F x h
    simp only [List.foldlM_cons, Fork.hideStep] at h
    cases hF : F.hide j y f with
    | none => simp [hF] at h
    | some F' =>
      simp only [hF, Option.map, bind, Option.bind] at h
      rw [ih (j + 1) F' x h, hide_keeps F F' cs j y f hF]

theorem hideRun_list (F : Fork) (first : Nat) (v : Array E) (f : E) :
    F.hideRun first v f = (v.toList.foldlM (Fork.hideStep f) (first, F)).map (·.2) := by
  unfold Fork.hideRun
  rw [← Array.foldlM_toList]
  cases v.toList.foldlM (Fork.hideStep f) (first, F) <;> rfl

/-- **The filling of a run of slots is Away.** -/
theorem hideRun_away (first : Nat) (v : Array E) (f : E) :
    Away (Fl.change (·.hideRun first v f)) where
  moves := by
    intro F G cs tp h
    have h1 := hideSteps_moves f cs v.toList first F G h
    unfold Fl.change
    simp only [hideRun_list]
    cases hx : v.toList.foldlM (Fork.hideStep f) (first, F) with
    | none =>
      simp only [hx] at h1
      simp [h1]
    | some x =>
      simp only [hx] at h1
      obtain ⟨G', hG, hadd⟩ := h1
      simp only [hG, Option.map]
      exact ⟨G', rfl, hadd⟩
  keeps := by
    intro F tp x cs h
    unfold Fl.change at h
    simp only [hideRun_list] at h
    cases hx : v.toList.foldlM (Fork.hideStep f) (first, F) with
    | none => simp [hx] at h
    | some y =>
      simp only [hx, Option.map] at h
      injection h with h'
      rw [← h']
      exact hideSteps_keeps f cs v.toList first F y hx

/-- A fold of Away steps is Away. -/
theorem Away.ofFoldlM {α β : Type} (f : β → α → Fl β) (hf : ∀ b a, Away (f b a)) :
    ∀ (l : List α) (b : β), Away (l.foldlM f b) := by
  intro l
  induction l with
  | nil => intro b; exact Away.ofPure b
  | cons a l ih =>
    intro b
    rw [List.foldlM_cons]
    exact Away.ofBind _ _ (hf b a) fun b' => ih b'

/-! ## "planes" -/

theorem pscRow_away (p : Psc) (S0 : E) (kept : Aff) : Away (Fl.pscRow p S0 kept) :=
  Away.ofBind _ _ (Away.ofMust _) fun _ =>
    Away.ofBind _ _ (hideRun_away _ _ _) fun _ => Away.ofPure _

theorem planesAtF_away (g : Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Fl Aff)
    (hb : ∀ e col, Away (bit e col)) : Away (First.Look.planesAtF g lm e bit) :=
  Away.ofFoldlM _ (fun _ col => Away.ofBind _ _ (hb e col) fun _ => Away.ofPure _) _ _

theorem leavesRowOwn_away (p : Psc) (S0 : E) (kept : Aff) :
    Away (First.Look.leavesRowOwn p S0 kept) :=
  Away.ofBind _ _ (Away.ofMust _) fun _ =>
    Away.ofBind _ _ (hideRun_away _ _ _) fun _ => Away.ofPure _

theorem planeClaimsOwn_away (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Fl Aff)
    (pin : Nat → Fl Aff) (hb : ∀ e col, Away (bit e col)) (hp : ∀ col, Away (pin col)) :
    Away (First.Look.planeClaimsOwn g lm bit pin) :=
  Away.ofBind _ _ (Away.ofMust _) fun _ =>
    Away.ofBind _ _ (planesAtF_away g lm 0 bit hb) fun _ =>
      Away.ofBind _ _ (planesAtF_away g lm 1 bit hb) fun _ =>
        Away.ofBind _ _
          (Away.ofFoldlM _ (fun _ col => Away.ofBind _ _ (hp col) fun _ => Away.ofPure _) _ _)
          fun _ => Away.ofBind _ _ (leavesRowOwn_away _ _ _) fun _ => Away.ofPure _

theorem planeClaimsF_away (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Fl Aff)
    (pin : Nat → Fl Aff) (hb : ∀ e col, Away (bit e col)) (hp : ∀ col, Away (pin col)) :
    Away (First.Look.planeClaimsF g lm bit pin) :=
  Away.ofBind _ _ (Away.ofMust _) fun _ =>
    Away.ofBind _ _ (planesAtF_away g lm 0 bit hb) fun _ =>
      Away.ofBind _ _ (planesAtF_away g lm 1 bit hb) fun _ =>
        Away.ofBind _ _
          (Away.ofFoldlM _ (fun _ col => Away.ofBind _ _ (hp col) fun _ => Away.ofPure _) _ _)
          fun _ => Away.ofBind _ _ (pscRow_away _ _ _) fun _ => Away.ofPure _

/-- The program of "planes". -/
def planesProg (lm : Nat) (g : Forest.Heard)
    (r : (Nat → Nat → Option Aff) × (Nat → Option Aff)) : Fl (Array Aff) := do
  let fs ← First.Look.planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col))
    fun col => Fl.need (r.2 col)
  First.Look.planesAddedF g
  pure fs

theorem planesProg_away (lm : Nat) (g : Forest.Heard)
    (r : (Nat → Nat → Option Aff) × (Nat → Option Aff)) : Away (planesProg lm g r) :=
  Away.ofBind _ _
    (planeClaimsOwn_away g lm _ _ (fun _ _ => Away.ofNeed _) fun _ => Away.ofNeed _) fun _ =>
      Away.ofBind _ _ (Away.ofPaid _) fun _ => Away.ofPure _

/-- "planes" at the calls' seat, in flRun's form. readers: the calling kind's. -/
def planesCalls (lm : Nat) (readers : K3.Readers S) : Fn S :=
  flRun "K3 planes: no sub-proof is open"
    (fun s => named "K3 planes: nothing was heard" s.lookHeard?)
    "K3 planes: they are made once" (fun g F => K3.unpaid F g.owedPlanes)
    (fun s => named "K3 planes: the caller's readers" (readers s))
    "K3 planes: the matrix, the caller's forms or the leaves' claim" (planesProg lm)
    (fun fs => fs.toList.map fun a => ({ form := a } : Claim))

/-- It is K3's own run. -/
theorem planesCalls_is (lm : Nat) (readers : K3.Readers S) :
    K3.planesRun (K3.seatCalls fun a => ({ form := a } : Claim)) lm readers =
      planesCalls lm readers := rfl

/-- **K3's "planes" at the calls is Blind to the real adding**, if an adding does not turn the
caller's readers. -/
theorem planesCalls_blind (lm : Nat) (readers : K3.Readers S) (hr : Unturned readers) :
    Blind (addsOf atS atS_ok) (planesCalls lm readers) :=
  flRun_blind _ _ _ _ _ _ _ _
    (fun t p _ G _ _ => by rw [(set_heard t { p with F := G }).1])
    (fun t p cs G hp hG => by rw [hr t p cs G hp hG])
    (fun g F G h => by unfold K3.unpaid; rw [h])
    (fun g r => planesProg_away lm g r)

end VerifiableInference.Desc.K9
