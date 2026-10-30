-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedRowsLook.lean: the claims that a lookup of the shipped Lean verifier leaves
name no entry of a virtual row.

Forest.pad (OnBytes/Model/Look.lean) reads a lookup's messages and keeps its own claims (rows), the
state of the leaves' sumcheck (leaves) and the form in which the key side ends (cEnd). All of them
are made of slots and constants. This file follows them through the routine.

Main names.
  Bare f: the form f names no entry of a virtual row: RowsIn Q f for every Q (LedRowsOf.lean).
  gives_roundsIn: rounds in a row keep a sumcheck's start form.
  gives_tieStep, gives_tie, gives_level: the parts of the lookup.
  gives_pad: what Forest.pad returns has bare rows, a bare start form of the leaves' sumcheck and a
    bare cEnd.

Gives: LedRowsLevel.lean.

What this file does not claim. Nothing where the routine does not return. Nothing on the claims that
a caller makes of what the lookup kept (the join; the claims on the planes).


-/
import OnBytes.Tie.Pv.Led.LedRowsLevel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open OnBytes.Model

/-- The form names no entry of a virtual row. -/
def Bare (f : Aff) : Prop := ∀ Q : Nat → Nat → Prop, RowsIn Q f

theorem bare_ofConst (v : E) : Bare (Aff.ofConst v) := fun _ => rowsIn_ofConst v

theorem bare_slot (j : Nat) : Bare (Aff.slot j) := fun _ => rowsIn_slot j

theorem bare_addMul {a b : Aff} (k : E) (ha : Bare a) (hb : Bare b) : Bare (Aff.addMul a b k) :=
  fun Q => rowsIn_addMul k (ha Q) (hb Q)

theorem bare_add {a b : Aff} (ha : Bare a) (hb : Bare b) : Bare (a + b) :=
  fun Q => rowsIn_add (ha Q) (hb Q)

theorem bare_scale {a : Aff} (k : E) (ha : Bare a) : Bare (Aff.scale a k) :=
  fun Q => rowsIn_scale k (ha Q)

theorem bare_rowForm (p : Psc) (S0 : E) (hs : Bare p.start) : Bare (p.rowForm S0 {}) :=
  fun Q => rowsIn_rowForm p S0 (hs Q) rowsIn_empty

theorem bare_foldl {α : Type} (step : Aff → α → Aff) (hs : ∀ f x, Bare f → Bare (step f x)) :
    ∀ (l : List α) (f : Aff), Bare f → Bare (l.foldl step f)
  | [], _, h => h
  | x :: l, f, h => bare_foldl step hs l (step f x) (hs f x h)

/-- All members of an array of forms are bare. -/
def BareAll (a : Array Aff) : Prop := ∀ f ∈ a.toList, Bare f

theorem bareAll_push {a : Array Aff} {f : Aff} (ha : BareAll a) (hf : Bare f) :
    BareAll (a.push f) := fun x hx => by
  rw [Array.toList_push, List.mem_append] at hx
  rcases hx with hx | hx
  · exact ha x hx
  · rw [List.mem_singleton.1 hx]
    exact hf

theorem bareAll_empty : BareAll #[] := fun x hx => by simp at hx

/-- A fold of a routine over a list, with a property of the carried value. -/
theorem gives_foldlM {α β : Type} (f : β → α → SubM β) (P : β → Prop)
    (h : ∀ b a, P b → Gives (f b a) P) : ∀ (l : List α) (b : β), P b → Gives (l.foldlM f b) P
  | [], b, hb => by
    rw [List.foldlM_nil]
    exact gives_pure b hb
  | a :: l, b, hb => by
    rw [List.foldlM_cons]
    exact gives_bind (h b a hb) fun b' hb' => gives_foldlM f P h l b' hb'

theorem gives_roundsIn (form : RoundForm) (p : Psc) (zs : List (E × Nat)) :
    Gives (roundsIn form p zs) fun x => x.2.start = p.start := by
  unfold roundsIn
  refine gives_foldlM _ (fun s : Array E × Psc => s.2.start = p.start) (fun s z hs => ?_) _ _ rfl
  refine gives_bind (gives_roundIn form s.2 z.1 z.2) fun x hx => ?_
  obtain ⟨r, q⟩ := x
  exact gives_pure _ (hx.trans hs)

theorem gives_tieStep (a : E) (s : Forest.TieStep) (j : Nat) (hs : BareAll s.rows) :
    Gives (Forest.tieStep a s j) fun t => BareAll t.rows := by
  unfold Forest.tieStep
  refine gives_bind (gives_pscBegin _) fun p0 h0 => gives_bind (gives_pscEnds p0 _ _) fun x hx => ?_
  obtain ⟨first, p⟩ := x
  dsimp only
  have hb : Bare p.start := by
    have e2 : p.start = _ := hx.trans h0
    rw [e2]
    split
    · exact bare_ofConst _
    · exact bare_slot _
  refine gives_bind (gives_true _) fun vP _ => gives_bind (gives_true _) fun vG _ => ?_
  split
  · refine gives_bind (gives_true _) fun _ _ => gives_bind (gives_true _) fun y _ =>
      gives_bind (gives_pscRow p _ {}) fun d hd => ?_
    refine gives_pure _ (bareAll_push hs ?_)
    rw [hd]
    exact bare_rowForm p _ hb
  · refine gives_bind (gives_true _) fun y _ => gives_bind (gives_pscRow p _ {}) fun d hd => ?_
    refine gives_pure _ (bareAll_push hs ?_)
    rw [hd]
    exact bare_rowForm p _ hb

theorem gives_tie (a : E) : Gives (Forest.tie a) fun t => BareAll t.rows ∧ Bare t.cT := by
  unfold Forest.tie
  refine gives_bind (gives_foldlM _ (fun s : Forest.TieStep => BareAll s.rows)
    (fun s j hs => gives_tieStep a s j hs) _ _ bareAll_empty) fun s hs => ?_
  refine gives_bind (gives_true _) fun pt _ => gives_pure _ ⟨hs, ?_⟩
  exact bare_foldl _ (fun f j hf => bare_addMul _ hf (bare_slot _)) _ _ (bare_ofConst _)

theorem bare_handDown (o : Level) : Bare o.handDown.2 := by
  unfold Level.handDown
  exact bare_add (bare_scale _ (bare_slot _)) (bare_scale _ (bare_slot _))

theorem gives_level (s : Forest.Descent) (mu : Nat) (order : List Nat) (hr : BareAll s.rows)
    (hf : Bare s.form) :
    Gives (Forest.level s mu order) fun t => BareAll t.rows ∧ Bare t.form := by
  unfold Forest.level
  refine gives_bind (gives_levelIn mu s.rho s.form order) fun o ho => ?_
  obtain ⟨p, S0, e, hp⟩ := ho
  refine gives_pure _ ⟨bareAll_push hr ?_, bare_handDown o⟩
  rw [e]
  exact bare_rowForm p S0 (hp ▸ hf)

/-- What a lookup keeps is made of slots and constants. -/
theorem gives_pad (calls : Array Call) (pub : Array Nat) (lid : Nat) :
    Gives (Forest.pad calls pub lid) fun g =>
      BareAll g.rows ∧ Bare g.leaves.start ∧ Bare g.cEnd := by
  unfold Forest.pad
  refine gives_bind (gives_true _) fun h0 _ => gives_bind (gives_true _) fun _ _ => ?_
  dsimp only
  refine gives_bind (gives_true _) fun slot0 _ => gives_bind (gives_true _) fun o1 _ =>
    gives_bind (gives_true _) fun o2 _ => gives_bind (gives_true _) fun o3 _ =>
      gives_bind (gives_true _) fun dr _ => ?_
  obtain ⟨theta, alpha, a⟩ := dr
  dsimp only
  refine gives_bind (gives_tie a) fun t ht => ?_
  refine gives_bind (gives_foldlM _
    (fun s : Forest.Descent => BareAll s.rows ∧ Bare s.form)
    (fun s mu hs => gives_level s mu _ hs.1 hs.2) _ _ ⟨ht.1, bare_slot _⟩) fun keys hk => ?_
  refine gives_bind (gives_foldlM _
    (fun s : Forest.Descent => BareAll s.rows ∧ Bare s.form)
    (fun s l hs => gives_level s _ _ hs.1 hs.2) _ _ ⟨hk.1, ht.2⟩) fun table htb => ?_
  refine gives_bind (gives_true _) fun _ _ => gives_bind (gives_pscBegin table.form)
    fun lv0 hl0 => gives_bind (gives_roundsIn _ lv0 _) fun x hx => ?_
  obtain ⟨zb0, leaves⟩ := x
  dsimp only
  refine gives_bind (gives_true _) fun r5 _ => gives_bind (gives_pscBegin _) fun b0 hb0 =>
    gives_bind (gives_roundsIn _ b0 _) fun y hy => ?_
  obtain ⟨zb1, bits1⟩ := y
  dsimp only
  refine gives_bind (gives_pscEnds bits1 2 1) fun z hz => ?_
  obtain ⟨sBit, bits⟩ := z
  dsimp only
  refine gives_bind (gives_true _) fun vBit _ => gives_bind (gives_pscRow bits _ {})
    fun w hw => ?_
  obtain ⟨bitsRow, bits'⟩ := w
  dsimp only
  refine gives_bind (gives_true _) fun sl _ => gives_bind (gives_true _) fun _ _ =>
    gives_bind (gives_true _) fun _ _ => gives_bind (gives_true _) fun _ _ => ?_
  refine gives_pure _ ⟨bareAll_push htb.1 ?_, ?_, hk.2⟩
  · have e : bitsRow = bits.rowForm _ {} := hw
    rw [e]
    refine bare_rowForm bits _ ?_
    have e2 : bits.start = Aff.ofConst zeroE := hz.trans (hy.trans hb0)
    rw [e2]
    exact bare_ofConst _
  · have e3 : leaves.start = table.form := hx.trans hl0
    show Bare leaves.start
    rw [e3]
    exact htb.2

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.gives_tie
#print axioms OnBytes.Road.Rows.gives_pad
