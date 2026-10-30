-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedWalkPlanes.lean: the three claims of a lookup that read the planes of its
counts, as a written list.

Forest.planeLins (OnBytes/Model/Look.lean) makes three forms by a routine (Forest.planeClaims), adds
them as claims and marks them as added. The routine asks its caller for forms column by column.
Where the caller's answers are values that must be there, the three forms are a function of these
values. This file writes that function and shows that the routine returns it.

Main names.
  Rules for a routine that adds nothing and whose value is given by a function: walks_val_pure,
    walks_val_bind, walks_val_then (then a routine whose list may read the value), walks_must_val,
    walks_val_foldlM (a fold over a list).
  planesAtO, planeFormsO: the planes' value at a point, and the three forms, as functions.
  walks_planesAt, walks_planeClaims: the routines return them and add nothing.
  walks_planeLins: Forest.planeLins adds just the three forms.
  planesL v fo, walks_claimsPlanes: the list for a layer sub-proof (claimsPlanes,
    OnBytes/Model/Layer.lean).

What this file does not claim. What the three forms say. Nothing where a routine does not return.


-/
import OnBytes.Model.Layer
import OnBytes.Tie.Pv.Led.LedWalkSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

/-! ## Routines whose value is given by a function -/

theorem walks_val_pure {α : Type} (a : α) :
    Walks (pure a : Model.SubM α) (fun b => some a = some b) (some []) := walks_pure a rfl

theorem walks_val_bind {α β : Type} {r : Model.SubM α} {k : α → Model.SubM β} {o : Option α}
    {o' : α → Option β} (hr : Walks r (fun a => o = some a) (some []))
    (hk : ∀ a, Walks (k a) (fun b => o' a = some b) (some [])) :
    Walks (r >>= k) (fun b => o.bind o' = some b) (some []) := by
  intro F G c c' y h
  obtain ⟨x, F1, c1, h1, h2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
  obtain ⟨q, la, e, wa⟩ := hr F F1 c c1 x h1
  obtain rfl : [] = la := Option.some.inj e
  obtain ⟨p, lb, e2, wb⟩ := hk x F1 G c1 c' y h2
  obtain rfl : [] = lb := Option.some.inj e2
  exact ⟨by rw [q]; exact p, [], rfl, by simpa using wa.trans wb⟩

/-- A routine whose value is given, and then a routine whose list may read the value. -/
theorem walks_val_then {α β : Type} {r : Model.SubM α} {k : α → Model.SubM β} {o : Option α}
    {P : β → Prop} {l : α → Option (List Model.Aff)}
    (hr : Walks r (fun a => o = some a) (some [])) (hk : ∀ a, Walks (k a) P (l a)) :
    Walks (r >>= k) P (o.bind l) := by
  intro F G c c' y h
  obtain ⟨x, F1, c1, h1, h2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
  obtain ⟨q, la, e, wa⟩ := hr F F1 c c1 x h1
  obtain rfl : [] = la := Option.some.inj e
  obtain ⟨p, lb, e2, wb⟩ := hk x F1 G c1 c' y h2
  exact ⟨p, lb, by rw [q]; exact e2, by simpa using wa.trans wb⟩

/-- A condition: where the routine returns, it holds. -/
theorem walks_must_val (b : Bool) :
    Walks (Model.SubM.must b) (fun _ => b = true) (some []) :=
  walks_still fun F G c c' a hr => by
    obtain ⟨hb, e⟩ := (PscRun.must_ok b F c _).1 hr
    simp only [Prod.mk.injEq] at e
    exact ⟨e.1.2, hb⟩

/-- A fold over a list. -/
theorem walks_val_foldlM {α β : Type} (f : β → α → Model.SubM β) (g : β → α → Option β)
    (h : ∀ b a, Walks (f b a) (fun y => g b a = some y) (some [])) :
    ∀ (l : List α) (b : β), Walks (l.foldlM f b) (fun y => l.foldlM g b = some y) (some [])
  | [], b => by
    rw [List.foldlM_nil]
    exact walks_pure b rfl
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact walks_mono (walks_val_bind (h b a) fun b' => walks_val_foldlM f g h l b') fun y hy => by
      rw [List.foldlM_cons]
      exact hy

/-! ## The three forms -/

/-- The value of the planes at the point zb e, as a form. -/
def planesAtO (g : Model.Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Option Model.Aff) :
    Option Model.Aff :=
  (List.range (g.shape.NC * 2 ^ (g.shape.kT + 5 - lm))).foldlM
    (fun (f : Model.Aff) col => (bit e col).bind fun x =>
      some (Model.Aff.addMul f x
        (mulE ((Model.eqTab ((g.zb e).extract g.shape.kT (g.shape.kT + g.shape.cK))).getD
            (col / 2 ^ (g.shape.kT + 5 - lm)) zeroE)
          ((Model.eqTab ((g.zb e).extract 0 (g.shape.kT + 5 - lm))).getD
            (col % 2 ^ (g.shape.kT + 5 - lm)) zeroE))))
    (Model.Aff.ofConst zeroE)

theorem walks_planesAt (g : Model.Forest.Heard) (lm e : Nat)
    (bit : Nat → Nat → Option Model.Aff) :
    Walks (Model.Forest.planesAt g lm e fun e x => Model.SubM.get (bit e x))
      (fun a => planesAtO g lm e bit = some a) (some []) := by
  unfold Model.Forest.planesAt planesAtO
  exact walks_val_foldlM _ _ (fun f col => walks_val_bind (walks_get _) fun x => walks_val_pure _)
    _ _

/-- The sum of the counts, less the number of keys that are not padding, as a form. -/
def countO (g : Model.Forest.Heard) (lm : Nat) (pin : Nat → Option Model.Aff) :
    Option Model.Aff :=
  (List.range (g.shape.NC * 2 ^ (g.shape.kT + 5 - lm))).foldlM
    (fun (f : Model.Aff) col => (pin col).bind fun x => some (f + x))
    (Model.Aff.ofConst (negE (ofF (2 ^ g.shape.v - g.shape.padding).toUInt64)))

/-- The three forms. -/
def planeFormsO (g : Model.Forest.Heard) (lm : Nat) (bit : Nat → Nat → Option Model.Aff)
    (pin : Nat → Option Model.Aff) : Option (Array Model.Aff) :=
  (planesAtO g lm 0 bit).bind fun at0 => (planesAtO g lm 1 bit).bind fun at1 =>
    (countO g lm pin).bind fun count =>
      some #[g.leaves.rowForm oneE (Model.Aff.scale at0 g.leavesA),
        Model.Aff.slot g.sBit - at1, count]

theorem walks_planeClaims (g : Model.Forest.Heard) (lm : Nat)
    (bit : Nat → Nat → Option Model.Aff) (pin : Nat → Option Model.Aff) :
    Walks (Model.Forest.planeClaims g lm (fun e x => Model.SubM.get (bit e x))
        fun x => Model.SubM.get (pin x))
      (fun rows => planeFormsO g lm bit pin = some rows) (some []) := by
  unfold Model.Forest.planeClaims planeFormsO
  refine walks_after (walks_must _) fun _ _ => ?_
  refine walks_val_bind (walks_planesAt g lm 0 bit) fun at0 => ?_
  refine walks_val_bind (walks_planesAt g lm 1 bit) fun at1 => ?_
  refine walks_val_bind (o := countO g lm pin)
    (walks_val_foldlM _ _ (fun f col => walks_val_bind (walks_get _) fun x => walks_val_pure _)
      _ _) fun count => ?_
  refine walks_after (walks_pscRow g.leaves oneE _) fun x hx => ?_
  obtain ⟨row, p'⟩ := x
  obtain rfl : row = g.leaves.rowForm oneE (Model.Aff.scale at0 g.leavesA) := hx
  exact walks_val_pure _

/-- Forest.planeLins adds just the three forms. -/
theorem walks_planeLins (g : Model.Forest.Heard) (lm : Nat)
    (bit : Nat → Nat → Option Model.Aff) (pin : Nat → Option Model.Aff) :
    Walks (Model.Forest.planeLins g lm (fun e x => Model.SubM.get (bit e x))
        fun x => Model.SubM.get (pin x))
      (fun _ => True) ((planeFormsO g lm bit pin).bind fun rows => some rows.toList) := by
  unfold Model.Forest.planeLins
  exact walks_val_then (walks_planeClaims g lm bit pin) fun rows =>
    walks_before (walks_forM_lin rows) fun _ _ => walks_planesAdded g

/-! ## A layer sub-proof -/

/-- An entry of a table on the reads, if its column is one of the planes' matrix. -/
def planeCol (v : Model.Layer.Env) (t x : Nat) : Option Model.Aff :=
  if x < v.y.kbm then v.U3at t x else none

/-- The three claims of a layer sub-proof's lookup that read the planes. -/
def planesL (v : Model.Layer.Env) (fo : Model.Forest.Heard) : Option (List Model.Aff) :=
  (v.tabAt "b-bits-0").bind fun tB0 => (v.tabAt "b-bits-1").bind fun tB1 =>
    (v.tabAt "b-pin").bind fun tP =>
      (planeFormsO fo v.y.h.lmb (fun e x => planeCol v (if e == 0 then tB0 else tB1) x)
        (planeCol v tP)).bind fun rows => some rows.toList

theorem walks_claimsPlanes (v : Model.Layer.Env) (fo : Model.Forest.Heard) :
    Walks (Model.Layer.claimsPlanes v fo) (fun _ => True) (planesL v fo) := by
  unfold Model.Layer.claimsPlanes planesL
  refine walks_get_bind _ fun tB0 => walks_get_bind _ fun tB1 => walks_get_bind _ fun tP => ?_
  exact walks_planeLins fo v.y.h.lmb _ _

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.walks_val_foldlM
#print axioms OnBytes.Road.Rows.walks_planeLins
#print axioms OnBytes.Road.Rows.walks_claimsPlanes
