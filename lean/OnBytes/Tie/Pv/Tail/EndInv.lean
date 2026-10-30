-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndInv.lean: the lookup's claims, which objectsF (OnBytes/Model/Tail.lean) adds
before its ties and reads, keep three things of the sub-proof's state: that there is one coefficient
for each slot, the number of claims in the plan, and the batching element.

Definitions, statements and proofs.
Main names:
  `Inv F G`: if F has one coefficient for each slot, then so has G, and G has F's number of claims
    in the plan and F's batching element. `Inv.refl`, `Inv.trans`.
  `Pres x`: wherever the routine x returns, `Inv` holds from the state before to the state after.
    `Pres.pure`, `Pres.bind`, `Pres.lift`, `Pres.ask`, `Pres.get`, `Pres.loop`, `Pres.loopArr`,
    `Pres.lin`, `Pres.t2Lin`, `Pres.paid`, `Pres.pscRow`.
  `pres_objects`, `pres_linJoin9`, `pres_linBits9`: the three routines.
  `objectsF_keeps`: if objectsF returns G from F and F has one coefficient for each slot, then G has
    one too, and G has F's number of claims in the plan and F's batching element.
  `objectsF_spread_from`: objectsF_spread with the plan's number of claims and the batching element
    read off the state before objectsF.
Limits: nothing on what the lookup's claims add to the one equation.
-/
import OnBytes.Tie.Pv.Tail.EndSpread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

/-- What is kept. -/
def Inv (F G : Fork) : Prop :=
  F.LS.size = F.ns → G.LS.size = G.ns ∧ G.planClaimsF = F.planClaimsF ∧ G.theta = F.theta

theorem Inv.refl (F : Fork) : Inv F F := fun h => ⟨h, rfl, rfl⟩

theorem Inv.trans {F G H : Fork} (a : Inv F G) (b : Inv G H) : Inv F H := fun h => by
  obtain ⟨h1, h2, h3⟩ := a h
  obtain ⟨k1, k2, k3⟩ := b h1
  exact ⟨k1, k2.trans h2, k3.trans h3⟩

/-- Wherever the routine returns, `Inv` holds. -/
def Pres {α : Type} (x : SubM α) : Prop :=
  ∀ F c a G c', x F c = .ok ((a, G), c') → Inv F G

theorem Pres.pure {α : Type} (a : α) : Pres (pure a : SubM α) := fun F _ _ _ _ h => by
  obtain ⟨_, rfl, _⟩ := (pure_ok _ _ _ _ _ _).1 h
  exact Inv.refl _

theorem Pres.bind {α β : Type} {x : SubM α} {f : α → SubM β} (hx : Pres x)
    (hf : ∀ a, Pres (f a)) : Pres (x >>= f) := fun F c b G c' h => by
  obtain ⟨a, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 h
  exact (hx F c a F1 c1 h1).trans (hf a F1 c1 b G c' h2)

theorem Pres.lift {α : Type} (b : Blk α) : Pres (liftM b : SubM α) := fun F _ _ _ _ h => by
  obtain ⟨_, rfl⟩ := (lift_ok _ _ _ _ _ _).1 h
  exact Inv.refl _

theorem Pres.ask {α : Type} (f : Fork → Option α) : Pres (SubM.ask f) := fun F _ _ _ _ h => by
  obtain ⟨_, rfl, _⟩ := (ask_ok _ _ _ _ _ _).1 h
  exact Inv.refl _

theorem Pres.get {α : Type} (x : Option α) : Pres (SubM.get x) := fun F _ _ _ _ h => by
  obtain ⟨_, rfl, _⟩ := (get_ok _ _ _ _ _ _).1 h
  exact Inv.refl _

theorem Pres.loop {α β : Type} (f : α → β → SubM (ForInStep β)) (hf : ∀ a b, Pres (f a b)) :
    ∀ (l : List α) (b : β), Pres (forIn l b f)
  | [], b => by
      rw [List.forIn_nil]
      exact Pres.pure b
  | a :: l, b => by
      rw [List.forIn_cons]
      refine Pres.bind (hf a b) fun r => ?_
      cases r with
      | done b1 => exact Pres.pure b1
      | yield b1 => exact Pres.loop f hf l b1

theorem Pres.loopArr {α β : Type} (f : α → β → SubM (ForInStep β)) (hf : ∀ a b, Pres (f a b))
    (as : Array α) (b : β) : Pres (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact Pres.loop f hf as.toList b

/-- A change of the state. -/
theorem Pres.change (f : Fork → Option Fork) (hf : ∀ F G, f F = some G → Inv F G) :
    Pres (SubM.change f) := fun F c a G c' h => by
  simp only [SubM.change] at h
  cases hq : f F with
  | none => simp [hq, liftOption_none] at h
  | some H =>
    simp only [hq, Option.map_some, liftOption_some, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨_, rfl⟩, _⟩ := h
    exact hf F H hq

/-! ## The steps that add a claim, mark a claim as added, or fill slots -/

theorem Pres.t2Lin (a : Aff) (runs : Array Run2) : Pres (t2Lin a runs) :=
  fun F c _ G c' h hs => by
    obtain ⟨_, _, _, e4, _, e6, _⟩ :=
      t2Lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ a runs F G c c' hs h
    exact ⟨e6, t2Lin_plan a runs F G c c' hs h, e4⟩

/-- Fork.lin keeps the plan's number of claims. -/
theorem lin_plan (F G : Fork) (f : Aff) (hs : F.LS.size = F.ns) (h : F.lin f = some G) :
    G.planClaimsF = F.planClaimsF := by
  unfold Fork.lin at h
  cases hk : F.kap with
  | none => simp [hk] at h
  | some x =>
    obtain ⟨k, F1⟩ := x
    rw [hk] at h
    have h2 : F1.push k f = some G := by simpa using h
    obtain ⟨_, hF1, _, _⟩ := Fork.kap_spec F F1 k hk
    have hs1 : F1.LS.size = F1.ns := by rw [hF1]; exact hs
    obtain ⟨_, hG, _, _⟩ :=
      Fork.push_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F1 G k f hs1 h2
    rw [hG, hF1]

theorem Pres.lin (f : Aff) : Pres (SubM.lin f) := fun F c _ G c' h hs => by
  obtain ⟨h1, _⟩ := (SubM.lin_run f F G c c').1 h
  obtain ⟨_, _, e3, _, e5, _⟩ :=
    Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h1
  exact ⟨e5, lin_plan F G f hs h1, e3⟩

theorem Pres.paid (i : Nat) : Pres (SubM.paid i) :=
  Pres.change _ fun F G h => by
    obtain rfl := Option.some.inj h
    exact fun hs => ⟨hs, rfl, rfl⟩

theorem hide_inv {F G : Fork} {j : Nat} {y f : E} (h : F.hide j y f = some G) : Inv F G := by
  unfold Fork.hide at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  exact fun hs => ⟨hs, rfl, rfl⟩

theorem hideSteps_inv (factor : E) : ∀ (l : List E) (first : Nat) (F : Fork) (x : Nat × Fork),
    l.foldlM (Fork.hideStep factor) (first, F) = some x → Inv F x.2
  | [], first, F, x, h => by
    have hx : (first, F) = x := by simpa using h
    subst hx
    exact Inv.refl F
  | y :: l, first, F, x, h => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.hideStep factor (first, F) y with
    | none => simp [hq] at h
    | some s =>
      rw [hq] at h
      have h2 : l.foldlM (Fork.hideStep factor) s = some x := by simpa using h
      simp only [Fork.hideStep] at hq
      cases hh : F.hide first y factor with
      | none => simp [hh] at hq
      | some H =>
        rw [hh] at hq
        obtain rfl : (first + 1, H) = s := by simpa using hq
        exact (hide_inv hh).trans (hideSteps_inv factor l _ _ _ h2)

theorem hideRun_inv {F G : Fork} {first : Nat} {v : Array E} {factor : E}
    (h : F.hideRun first v factor = some G) : Inv F G := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    exact hideSteps_inv factor _ _ _ _ hx
  · simp at h

theorem Pres.pscRow (p : Psc) (S0 : E) (kept : Aff) : Pres (pscRow p S0 kept) := by
  unfold OnBytes.Model.pscRow
  exact Pres.bind (Pres.lift _) fun _ =>
    Pres.bind (Pres.change _ fun _ _ h => hideRun_inv h) fun _ => Pres.pure _

/-! ## The three routines -/

theorem Pres.foldlM {α β : Type} (f : β → α → SubM β) (hf : ∀ b a, Pres (f b a)) :
    ∀ (l : List α) (b : β), Pres (l.foldlM f b)
  | [], b => by
      rw [List.foldlM_nil]
      exact Pres.pure b
  | a :: l, b => by
      rw [List.foldlM_cons]
      exact Pres.bind (hf b a) fun b1 => Pres.foldlM f hf l b1

theorem pres_objects (g : Forest.Heard) : Pres (Forest.objects g) := by
  unfold Forest.objects
  refine Pres.bind ?_ fun _ => Pres.paid _
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact Pres.foldlM _ (fun _ a => Pres.lin a) _ _

/-- One step of a walk through a routine's text. -/
macro "pres_step" : tactic => `(tactic| first
  | exact Pres.pure _ | exact Pres.get _ | exact Pres.ask _ | exact Pres.lift _
  | exact Pres.t2Lin _ _ | exact Pres.paid _ | exact Pres.lin _
  | refine Pres.bind ?_ ?_ | refine Pres.loop _ ?_ _ _ | refine Pres.loopArr _ ?_ _ _
  | dsimp only | split | intro _)

theorem pres_linJoin9 (tl : HTailF2) : Pres tl.linJoin9 := by
  unfold HTailF2.linJoin9 Forest.paddingLaid
  repeat' pres_step

theorem pres_linBits9 (tl : HTailF2) : Pres tl.linBits9 := by
  unfold HTailF2.linBits9
  refine Pres.bind (Pres.get _) fun g => ?_
  refine Pres.bind (Pres.pscRow _ _ _) fun x => ?_
  refine Pres.bind (Pres.t2Lin _ _) fun _ => ?_
  refine Pres.bind (Pres.t2Lin _ _) fun _ => ?_
  refine Pres.bind (Pres.t2Lin _ _) fun _ => ?_
  exact Pres.bind (Pres.paid _) fun _ => Pres.pure _

/-! ## objectsF -/

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- If objectsF returns G from a state F with one coefficient for each slot, then G has one too, and
G has F's number of claims in the plan and F's batching element. -/
theorem objectsF_keeps (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (hs : F.LS.size = F.ns) :
    G.LS.size = G.ns ∧ G.planClaimsF = F.planClaimsF ∧ G.theta = F.theta := by
  obtain ⟨g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, tl1, F1, c1, _, hFo, hJ, hB, hWt, _, _, _, _,
    himp⟩ := objectsF_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ tl tl' funs F G c c' h
  obtain ⟨eF, _, _, _⟩ := weightsF_spec tlb tl1 Fc F1 cc c1 hWt
  obtain ⟨k1, k2, k3⟩ := ((pres_objects g F c _ Fa ca hFo).trans
    ((pres_linJoin9 tl Fa ca tla Fb cb hJ).trans (pres_linBits9 tla Fb cb tlb Fc cc hB))) hs
  subst eF
  obtain ⟨_, hk, _, _⟩ := himp k1
  exact ⟨hk.sized, hk.plan.trans k2, hk.theta.trans k3⟩

/-- objectsF_spread (OnBytes/Tie/Pv/Tail/EndSpread.lean) from the state before objectsF: the number
of claims in the plan and the batching element are those of F, and the one premise on a state is
that F has one coefficient for each slot. -/
theorem objectsF_spread_from (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (hfit : Fits tl) (hs : F.LS.size = F.ns)
    (A : Nat → Nat → Nat → K) (hV : RawRows W tl G funs (ρ.val F.theta) A) :
    Rising (rowsTail ρ tl funs F.planClaimsF) ∧
    (∀ r ∈ rowsTail ρ tl funs F.planClaimsF,
      F.planClaimsF ≤ r.1 ∧ r.1 < F.planClaimsF + topOf tl funs) ∧
    ∃ g Fa ca tla Fb cb tlb Fc cc,
      tl.heard = some g ∧ Forest.objects g F c = .ok (((), Fa), ca) ∧
      tl.linJoin9 Fa ca = .ok ((tla, Fb), cb) ∧ tla.linBits9 Fb cb = .ok ((tlb, Fc), cc) ∧
      c' = cc ∧ Kept Fc G ∧ G.nClaim = Fc.nClaim + tl.NM + (readsList tl funs).length ∧
      G.total ρ W = Fc.total ρ W +
        batchOf (ρ.val F.theta) A (rowsTail ρ tl funs F.planClaimsF) := by
  obtain ⟨_, ePC, eθ⟩ := objectsF_keeps tl tl' funs F G c c' h hs
  rw [← eθ] at hV
  obtain ⟨hr, hb, g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, hg, hFo, hJ, hB, himp⟩ :=
    objectsF_spread ρ W tl tl' funs F G c c' h hfit A hV
  obtain ⟨k1, _, _⟩ := ((pres_objects g F c _ Fa ca hFo).trans
    ((pres_linJoin9 tl Fa ca tla Fb cb hJ).trans (pres_linBits9 tla Fb cb tlb Fc cc hB))) hs
  obtain ⟨e1, hk, hn, ht⟩ := himp k1
  rw [ePC] at hr hb ht
  rw [eθ] at ht
  exact ⟨hr, hb, g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, hg, hFo, hJ, hB, e1, hk, hn, ht⟩

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.pres_objects
#print axioms OnBytes.Tie.Pv.Tail.Port.pres_linJoin9
#print axioms OnBytes.Tie.Pv.Tail.Port.pres_linBits9
#print axioms OnBytes.Tie.Pv.Tail.Port.objectsF_keeps
#print axioms OnBytes.Tie.Pv.Tail.Port.objectsF_spread_from
