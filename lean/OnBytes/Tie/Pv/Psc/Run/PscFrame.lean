-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscFrame.lean: a relation between two states of a sub-proof that says that
filled slots are kept, and the class of routines that keep them.

Main names:
  `SlotsKept F G`: if F's three arrays on slots are sized, so are G's, ns is the same, and a slot
    that is filled in F is filled in G with the same shown scalar and the same factor.
    `SlotsKept.refl`, `SlotsKept.trans`, `SlotsKept.same`, `Filled.kept`.
  `world_kept`: the value under a filled slot in the world of Fork.worldOf is the same at G as at F.
  `kept_hideRun`, `kept_hide`, `kept_push`, `kept_kapTake`, `kept_kap`, `kept_lin`,
    `kept_batchBy`: Fork's own steps.
  `KeepsSlots x`: wherever the routine x succeeds from F and leaves G, SlotsKept F G.
    `KeepsSlots.bind`, `ks_change`, `ks_take`, and the tactic `ks`.
  Instances: the calls of SubM in OnBytes/Model/Hide.lean but SubM.slots, and the routines of
    OnBytes/Model/Psc.lean and OnBytes/Model/Tsc.lean.
Limits: SubM.change and SubM.take keep the slots only if their function does. SubM.slots does not:
Fork.slots sets the arrays up anew. The routines of the other files of OnBytes/Model/ are not
treated here. Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscHide
import OnBytes.Tie.Pv.Psc.Run.PscKit

set_option autoImplicit false

namespace OnBytes.Model.Road

/-- Filled slots are kept from F to G: see the head. -/
def SlotsKept (F G : Fork) : Prop :=
  Sized F → Sized G ∧ G.ns = F.ns ∧ ∀ j, F.gotF.getD j false = true →
    G.gotF.getD j false = true ∧ G.vp.getD j zeroE = F.vp.getD j zeroE ∧
      G.mf.getD j zeroE = F.mf.getD j zeroE

theorem SlotsKept.refl (F : Fork) : SlotsKept F F := fun h => ⟨h, rfl, fun _ g => ⟨g, rfl, rfl⟩⟩

theorem SlotsKept.trans {F G H : Fork} (a : SlotsKept F G) (b : SlotsKept G H) : SlotsKept F H := by
  intro h
  obtain ⟨s1, n1, k1⟩ := a h
  obtain ⟨s2, n2, k2⟩ := b s1
  refine ⟨s2, n2.trans n1, fun j g => ?_⟩
  obtain ⟨g1, v1, m1⟩ := k1 j g
  obtain ⟨g2, v2, m2⟩ := k2 j g1
  exact ⟨g2, v2.trans v1, m2.trans m1⟩

/-- A step that writes none of ns, vp, mf, gotF. -/
theorem SlotsKept.same {F G : Fork} (n : G.ns = F.ns) (v : G.vp = F.vp) (m : G.mf = F.mf)
    (g : G.gotF = F.gotF) : SlotsKept F G := fun h =>
  ⟨⟨by rw [v, n]; exact h.vp, by rw [m, n]; exact h.mf, by rw [g, n]; exact h.got⟩, n,
    fun _ k => ⟨by rw [g]; exact k, by rw [v], by rw [m]⟩⟩

theorem getD_free {a : Array Bool} {j : Nat} (h : a.getD j true = false) :
    a.getD j false = false := by
  rw [Array.getD_eq_getD_getElem?] at h ⊢
  cases e : a[j]? with
  | none => simp [e] at h
  | some b => simpa [e] using h

/-- A run of hidden values fills free slots alone. -/
theorem Filled.kept {F G : Fork} {first : Nat} {l : List E} {factor : E}
    (a : Filled F G first l factor) : SlotsKept F G := by
  intro _
  refine ⟨a.sized, a.ns, fun j g => ?_⟩
  by_cases hj : j < first ∨ first + l.length ≤ j
  · obtain ⟨o1, o2, o3⟩ := a.other j hj
    exact ⟨by rw [o3]; exact g, o1, o2⟩
  · have h1 : first ≤ j := by omega
    have h2 : j - first < l.length := by omega
    obtain ⟨_, _, _, b4⟩ := a.here (j - first) h2
    rw [show first + (j - first) = j by omega] at b4
    rw [getD_free b4] at g
    cases g

/-- The hidden value under a filled slot does not change. -/
theorem world_kept {K : Type} [CommRing K] (ρ : Reading K) {F G : Fork} (a : SlotsKept F G) (hs :
    Sized F)
    (mask : Nat → K) (entry entry' : Nat → Nat → Nat → K) (j : Nat) (g :
        F.gotF.getD j false = true) :
    (G.worldOf ρ mask entry).slot j = (F.worldOf ρ mask entry').slot j := by
  obtain ⟨_, _, k⟩ := a hs
  obtain ⟨_, v, m⟩ := k j g
  show ρ.val (G.vp.getD j zeroE) - ρ.val (G.mf.getD j zeroE) * mask j =
    ρ.val (F.vp.getD j zeroE) - ρ.val (F.mf.getD j zeroE) * mask j
  rw [v, m]

/-! ## Fork's own steps -/

theorem kept_hideRun (F G : Fork) (first : Nat) (v : Array E) (factor : E)
    (h : F.hideRun first v factor = some G) : SlotsKept F G := fun hs =>
  (hideRun_ok F G first v factor h hs).kept hs

theorem kept_hide (F G : Fork) (j : Nat) (s f : E) (h : F.hide j s f = some G) : SlotsKept F G := by
  have : F.hideRun j #[s] f = some G := by
    unfold Fork.hideRun
    simp [Fork.hideStep, h]
  exact kept_hideRun F G j #[s] f this

theorem kept_push (F G : Fork) (w : E) (a : Aff) (h : F.push w a = some G) : SlotsKept F G := by
  unfold Fork.push at h
  split at h
  · cases h
  · simp only [] at h
    split at h
    · rw [← Option.some.inj h]; exact SlotsKept.same rfl rfl rfl rfl
    · cases h

theorem kept_kapTake (F G : Fork) (c : Nat) (k : E) (h : F.kapTake c = some (k, G)) :
    SlotsKept F G := by
  unfold Fork.kapTake at h
  split at h
  · cases h
  · split at h
    · cases e : F.kapAt c with
      | none => rw [e] at h; cases h
      | some y => rw [e] at h; cases h; exact SlotsKept.refl _
    · split at h
      · cases e : F.kapAt c with
        | none => rw [e] at h; cases h
        | some y => rw [e] at h; cases h; exact SlotsKept.same rfl rfl rfl rfl
      · cases h

theorem kept_kap (F G : Fork) (k : E) (h : F.kap = some (k, G)) : SlotsKept F G := by
  unfold Fork.kap at h
  cases e : F.kapTake F.nClaim with
  | none => rw [e] at h; cases h
  | some y =>
    obtain ⟨k1, H⟩ := y
    rw [e] at h
    cases h
    exact (kept_kapTake F H _ k1 e).trans (SlotsKept.same rfl rfl rfl rfl)

theorem kept_lin (F G : Fork) (f : Aff) (h : F.lin f = some G) : SlotsKept F G := by
  unfold Fork.lin at h
  cases e : F.kap with
  | none => rw [e] at h; cases h
  | some y =>
    obtain ⟨k1, H⟩ := y
    rw [e] at h
    exact (kept_kap F H k1 e).trans (kept_push H G k1 f h)

theorem kept_batchBy (F G : Fork) (d : E) (h : F.batchBy d = some G) : SlotsKept F G := by
  unfold Fork.batchBy at h
  split at h
  · cases h
  · cases h; exact SlotsKept.same rfl rfl rfl rfl

/-! ## The class -/

/-- Wherever the routine succeeds, the slots are kept. -/
class KeepsSlots {α : Type} (x : SubM α) : Prop where
  out : ∀ F c a G c', x F c = .ok ((a, G), c') → SlotsKept F G

instance ks_pure {α : Type} (a : α) : KeepsSlots (pure a : SubM α) :=
  ⟨fun F c x G c' h => by
    obtain ⟨_, e, _⟩ := (pure_ok _ _ _ _ _ _).1 h
    rw [e]
    exact SlotsKept.refl _⟩

theorem KeepsSlots.bind {α β : Type} {x : SubM α} {f : α → SubM β} (hx : KeepsSlots x)
    (hf : ∀ a, KeepsSlots (f a)) : KeepsSlots (x >>= f) :=
  ⟨fun F c b G c' h => by
    obtain ⟨a, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 h
    exact (hx.out _ _ _ _ _ h1).trans ((hf a).out _ _ _ _ _ h2)⟩

instance ks_lift {α : Type} (b : Blk α) : KeepsSlots (StateT.lift b : SubM α) :=
  ⟨fun F c a G c' h => by
    obtain ⟨_, e⟩ := (liftY_ok _ _ _ _ _ _).1 h
    rw [e]
    exact SlotsKept.refl _⟩

instance ks_ask {α : Type} (f : Fork → Option α) : KeepsSlots (SubM.ask f) :=
  ⟨fun F c a G c' h => by
    unfold SubM.ask at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some y => rw [e] at h; cases h; exact SlotsKept.refl _⟩

theorem ks_change (f : Fork → Option Fork) (hf : ∀ F G, f F = some G → SlotsKept F G) :
    KeepsSlots (SubM.change f) :=
  ⟨fun F _ _ G _ h => hf F G ((change_ok _ _ _ _ _ _).1 h).1⟩

theorem ks_take {α : Type} (f : Fork → Option (α × Fork))
    (hf : ∀ F a G, f F = some (a, G) → SlotsKept F G) : KeepsSlots (SubM.take f) :=
  ⟨fun F _ a G _ h => hf F a G ((take_ok _ _ _ _ _ _).1 h).1⟩

/-- Instances first, then bind, match and if by cases. -/
macro "ks" : tactic =>
  `(tactic| repeat' first
      | infer_instance
      | intro _
      | apply KeepsSlots.bind
      | split
      | dsimp only)

/-! ## The calls of SubM in OnBytes/Model/Hide.lean (all but SubM.slots) -/

instance : ∀ b, KeepsSlots (SubM.must b) := fun _ => by unfold SubM.must; ks
instance : ∀ b, KeepsSlots (SubM.test b) := fun _ => by unfold SubM.test; ks
instance {α : Type} : ∀ x : Option α, KeepsSlots (SubM.get x) := fun _ => by unfold SubM.get; ks
instance : ∀ n, KeepsSlots (SubM.read n) := fun _ => by unfold SubM.read; ks
instance : KeepsSlots SubM.readSum := by unfold SubM.readSum; ks
instance : ∀ r, KeepsSlots (SubM.answer r) := fun _ => by unfold SubM.answer; ks
instance : ∀ r, KeepsSlots (SubM.answerNotZero r) := fun _ => by unfold SubM.answerNotZero; ks
instance : ∀ r n, KeepsSlots (SubM.point r n) := fun _ _ => by unfold SubM.point; ks
instance : ∀ n, KeepsSlots (SubM.batch n) := fun _ => by unfold SubM.batch; ks
instance : KeepsSlots SubM.batchOpen := by unfold SubM.batchOpen; ks
instance : ∀ n, KeepsSlots (SubM.batchRows n) := fun _ => by unfold SubM.batchRows; ks
instance : ∀ r, KeepsSlots (SubM.empty r) := fun _ => by unfold SubM.empty; ks
instance : ∀ a b, KeepsSlots (SubM.trits a b) := fun _ _ => by unfold SubM.trits; ks
instance : KeepsSlots SubM.slot := by unfold SubM.slot; ks
instance : ∀ j, KeepsSlots (SubM.shown j) := fun _ => by unfold SubM.shown; ks
instance : ∀ a, KeepsSlots (SubM.publicPart a) := fun _ => by unfold SubM.publicPart; ks
instance : KeepsSlots SubM.claims := by unfold SubM.claims; ks
instance : KeepsSlots SubM.allTaken := by unfold SubM.allTaken; ks
instance : ∀ u, KeepsSlots (SubM.settle u) := fun _ => by unfold SubM.settle; ks
instance : ∀ t w, KeepsSlots (SubM.rootTaken t w) := fun _ _ =>
  ks_change _ fun _ _ h => by cases h; exact SlotsKept.same rfl rfl rfl rfl
instance : ∀ n, KeepsSlots (SubM.takeSlots n) := fun _ =>
  ks_take _ fun _ _ _ h => by cases h; exact SlotsKept.same rfl rfl rfl rfl
instance : ∀ j s f, KeepsSlots (SubM.hide j s f) := fun j s f => ks_change _ fun F G h => kept_hide
    F G j s f h
instance ks_hideRun : ∀ (j : Nat) (v : Array E) (f : E), KeepsSlots (SubM.change (·.hideRun j v f))
    :=
  fun j v f => ks_change _ fun F G h => kept_hideRun F G j v f h
instance : ∀ d, KeepsSlots (SubM.batchBy d) := fun d => ks_change _ fun F G h => kept_batchBy F G d
    h
instance : KeepsSlots SubM.kap := ks_take _ fun F k G h => kept_kap F G k h
instance : ∀ w a, KeepsSlots (SubM.push w a) := fun w a => ks_change _ fun F G h => kept_push F G w
    a h
instance : ∀ f, KeepsSlots (SubM.lin f) := fun f => ks_change _ fun F G h => kept_lin F G f h
instance : ∀ n, KeepsSlots (SubM.setPlanClaims n) := fun _ =>
  ks_change _ fun _ _ h => by cases h; exact SlotsKept.same rfl rfl rfl rfl
instance : ∀ w, KeepsSlots (SubM.owe w) := fun _ =>
  ks_take _ fun _ _ _ h => by cases h; exact SlotsKept.same rfl rfl rfl rfl
instance : ∀ i, KeepsSlots (SubM.paid i) := fun _ =>
  ks_change _ fun _ _ h => by cases h; exact SlotsKept.same rfl rfl rfl rfl
instance : ∀ n, KeepsSlots (SubM.claimsIn n) := fun _ => by unfold SubM.claimsIn; ks

/-! ## OnBytes/Model/Psc.lean and OnBytes/Model/Tsc.lean -/

instance : ∀ t, KeepsSlots (pscBeginAt t) := fun _ => by unfold pscBeginAt; ks
instance : ∀ C, KeepsSlots (pscBegin C) := fun _ => by unfold pscBegin; ks
instance : ∀ p w d, KeepsSlots (pscRound p w d) := fun _ _ _ => by unfold pscRound; ks
instance : ∀ f p z d, KeepsSlots (roundIn f p z d) := fun _ _ _ _ => by unfold roundIn; ks
instance : ∀ p d n, KeepsSlots (pscEnds p d n) := fun _ _ _ => by unfold pscEnds; ks
instance : ∀ p s k, KeepsSlots (pscRow p s k) := fun _ _ _ => by unfold pscRow; ks
instance ks_levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p : Psc),
    KeepsSlots (levelRounds mu rho order r p)
  | [], _, _ => by unfold levelRounds; ks
  | _ :: order, _, _ => by
    unfold levelRounds
    have := ks_levelRounds mu rho order
    ks
instance : ∀ mu rho C order, KeepsSlots (levelIn mu rho C order) := fun _ _ _ _ => by
  unfold levelIn; ks
instance : ∀ o, KeepsSlots (layerObject o) := fun _ => by unfold layerObject; ks
instance ks_tscLoop : ∀ (zs : List E) (r : Array E) (p : Psc), KeepsSlots (tscLoop zs r p)
  | [], _, _ => by unfold tscLoop; ks
  | _ :: zs, _, _ => by
    unfold tscLoop
    have := ks_tscLoop zs
    ks
instance : ∀ P lt, KeepsSlots (tscRounds P lt) := fun _ _ => by unfold tscRounds; ks
instance ks_tscIn : ∀ P lt s d, KeepsSlots (tscIn P lt s d) := fun _ _ _ _ => by unfold tscIn; ks

#print axioms world_kept
#print axioms ks_tscIn
#print axioms Filled.kept

end OnBytes.Model.Road
