-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Read.lean: a form over hidden values (Model.Aff) at a ledger, read by
its values: the public value (each hidden value replaced by what was shown) and the hidden value in
a world of mask entries. What it means that a form reads as a claim of the course over the field (a
mask form and a value), and that this lasts to every later ledger.

Main names:
  pubV F a, hidV W home F a: the two values (Aff.value of OnBytes/Model/HideLaws.lean at two
    worlds).
  pubV_eq, hidV_eq: they are valOf, and valOf - <mfOf, mask entries> (Statement.lean).
  AllShown F a: every slot that the form names is filled.
  Reads W home F a m v: the form's slots are filled, its public value is v, and its hidden value is
    v - <m, mask entries>. Reads.later, Reads.const, Reads.slot, Reads.addMul, Reads.scale,
    Reads.add.
  public_reads: what Fork.publicPart returns.
  forms_ext: two mask forms with the same value in every world are the same function on the entries.
    split_ext: "mask form - target" the same in every world: so are the two parts.

Limits. W is one world of mask entries; the last two theorems are where all worlds are used.

-/
import Johnson.Desc.First.Look.KeyLaw.Statement
import Johnson.Desc.First.Look.KeyLaw.Kit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World)
open OnBytes.PscRun (took Later Sized Filled)
open Lk6.PortSim (rdMF)

/-- The reading in the field. -/
abbrev rho : Reading GE := Reading.gl

theorem rho_val (x : E) : rho.val x = readE x := rfl

/-- The world in which a hidden value is what was shown for it. -/
def pubW (F : Fork) : World GE := ⟨fun j => readE (F.vp.getD j zeroE), fun _ _ _ => 0⟩

variable (W : PscF.World) (home : ℕ → Slot)

/-- The world in which the hidden value under slot j is vp j - mf j * (the mask entry of slot j). -/
def hidW (F : Fork) : World GE := F.worldOf rho (fun j => W.mask (home j)) fun _ _ _ => 0

def pubV (F : Fork) (a : Aff) : GE := a.value rho (pubW F)
def hidV (F : Fork) (a : Aff) : GE := a.value rho (hidW W home F)

theorem ents_zero (s : ℕ → GE) (l : List Model.Ent) :
    (l.map (Model.Ent.value rho ⟨s, fun _ _ _ => 0⟩)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp [Model.Ent.value]

theorem pubV_eq (F : Fork) (a : Aff) : pubV F a = valOf F a := by
  unfold pubV valOf Aff.value pubW
  rw [ents_zero, zero_add, add_comm]
  rfl

theorem hid_sum (F : Fork) : ∀ l : List (ℕ × E),
    (l.map (Model.slotValue rho (hidW W home F))).sum =
      (l.map fun t => readE t.2 * readE (F.vp.getD t.1 zeroE)).sum -
        W.form (l.map fun t => (home t.1, readE t.2 * readE (F.mf.getD t.1 zeroE)))
  | [] => by simp [PscF.World.form]
  | x :: l => by
    rw [List.map_cons, List.sum_cons, hid_sum F l, List.map_cons, List.sum_cons, List.map_cons,
      PscF.World.form_cons]
    show readE x.2 * (readE (F.vp.getD x.1 zeroE) - readE (F.mf.getD x.1 zeroE) * W.mask (home x.1))
      + _ = _
    ring

theorem hidV_eq (F : Fork) (a : Aff) : hidV W home F a = valOf F a - W.form (mfOf F home a) := by
  unfold hidV valOf mfOf Aff.value
  have e : (a.ents.toList.map (Model.Ent.value rho (hidW W home F))).sum = 0 := ents_zero _ _
  rw [e, zero_add, hid_sum]
  show _ + readE a.const = _
  ring

/-- Every slot that the form names is there and filled. -/
def AllShown (F : Fork) (a : Aff) : Prop := ∀ x ∈ a.slots.toList, x.1 < F.ns ∧ Filled F x.1

theorem value_congr (a : Aff) (W1 W2 : World GE) (he : W1.entry = W2.entry)
    (hs : ∀ x ∈ a.slots.toList, W1.slot x.1 = W2.slot x.1) : a.value rho W1 = a.value rho W2 := by
  unfold Aff.value
  have e1 : a.ents.toList.map (Model.Ent.value rho W1) = a.ents.toList.map (Model.Ent.value rho W2)
      :=
    List.map_congr_left fun x _ => by simp only [Model.Ent.value, he]
  have e2 : a.slots.toList.map (Model.slotValue rho W1) =
      a.slots.toList.map (Model.slotValue rho W2) :=
    List.map_congr_left fun x hx => by simp only [Model.slotValue, hs x hx]
  rw [e1, e2]

variable {W home}

theorem AllShown.later {F H : Fork} {a : Aff} (h : AllShown F a) (l : Later F H) : AllShown H a :=
  fun x hx => ⟨by rw [l.ns]; exact (h x hx).1, (l.keep _ (h x hx).2).1⟩

theorem pubV_later {F H : Fork} {a : Aff} (h : AllShown F a) (l : Later F H) :
    pubV H a = pubV F a :=
  value_congr a _ _ rfl fun x hx => by
    show readE _ = readE _
    rw [(l.keep _ (h x hx).2).2.1]

theorem hidV_later {F H : Fork} {a : Aff} (h : AllShown F a) (l : Later F H) :
    hidV W home H a = hidV W home F a :=
  value_congr a _ _ rfl fun x hx => by
    show readE _ - readE _ * _ = readE _ - readE _ * _
    rw [(l.keep _ (h x hx).2).2.1, (l.keep _ (h x hx).2).2.2]

/-- The form names no entry of a virtual row. -/
def NoEnt (a : Aff) : Prop := a.ents.toList = []

theorem noEnt_const (c : E) : NoEnt (Aff.ofConst c) := rfl
theorem noEnt_slot (j : ℕ) : NoEnt (Aff.slot j) := rfl
theorem noEnt_empty : NoEnt {} := rfl

theorem NoEnt.addMul {a b : Aff} (ha : NoEnt a) (hb : NoEnt b) (k : E) :
    NoEnt (Aff.addMul a b k) := by
  show (b.ents.foldl (fun l x => l.push { x with coef := mulE x.coef k }) a.ents).toList = []
  rw [Model.foldl_push_toList, ha, hb]
  rfl

theorem NoEnt.sub {a b : Aff} (ha : NoEnt a) (hb : NoEnt b) : NoEnt (a - b) := ha.addMul hb _

theorem NoEnt.addSlots {a : Aff} (ha : NoEnt a) (first : ℕ) (form : Array E) :
    NoEnt (Model.addSlots a first form) := by
  unfold Model.addSlots
  rw [← Array.foldl_toList]
  generalize form.toList = l
  induction l generalizing a first with
  | nil => exact ha
  | cons x l ih => exact ih (ha.addMul (noEnt_slot first) x) (first + 1)

theorem NoEnt.rowForm {p : Psc} (hp : NoEnt p.start) (S0 : E) : NoEnt (p.rowForm S0 {}) :=
  (((noEnt_const _).addSlots _ _).addMul ((noEnt_const _).sub hp) _).addMul noEnt_empty _

variable (W home)

/-- **The form reads as the claim (m, v).** -/
structure Reads (F : Fork) (a : Aff) (m : PscF.MaskForm) (v : GE) : Prop where
  ne : NoEnt a
  shown : AllShown F a
  pub : pubV F a = v
  hid : hidV W home F a = v - W.form m

variable {W home}

theorem Reads.later {F H : Fork} {a : Aff} {m : PscF.MaskForm} {v : GE} (h : Reads W home F a m v)
    (l : Later F H) : Reads W home H a m v :=
  ⟨h.ne, h.shown.later l, (pubV_later h.shown l).trans h.pub, (hidV_later h.shown l).trans h.hid⟩

theorem Reads.const (F : Fork) (c : E) : Reads W home F (Aff.ofConst c) [] (readE c) :=
  ⟨rfl, fun x hx => by simp [Aff.ofConst] at hx, Aff.value_ofConst _ _ _, by
    show (Aff.ofConst c).value rho _ = _
    rw [Aff.value_ofConst, PscF.World.form_nil, sub_zero]
    rfl⟩

theorem Reads.slot {F : Fork} {j : ℕ} (h1 : j < F.ns) (h2 : Filled F j) :
    Reads W home F (Aff.slot j) [(home j, readE (F.mf.getD j zeroE))]
      (readE (F.vp.getD j zeroE)) :=
  ⟨rfl, fun x hx => by
      have : x = (j, oneE) := by simpa [Aff.slot] using hx
      subst this
      exact ⟨h1, h2⟩, Aff.value_slot _ _ _, by
    show (Aff.slot j).value rho _ = _
    rw [Aff.value_slot, PscF.World.form_cons, PscF.World.form_nil, add_zero]
    rfl⟩

theorem slots_addMul (a b : Aff) (k : E) : (Aff.addMul a b k).slots.toList =
    a.slots.toList ++ b.slots.toList.map fun x => (x.1, mulE x.2 k) := by
  show (b.slots.foldl (fun l x => l.push (x.1, mulE x.2 k)) a.slots).toList = _
  exact Model.foldl_push_toList _ _ _

theorem AllShown.addMul {F : Fork} {a b : Aff} (ha : AllShown F a) (hb : AllShown F b) (k : E) :
    AllShown F (Aff.addMul a b k) := fun x hx => by
  rw [slots_addMul, List.mem_append] at hx
  rcases hx with hx | hx
  · exact ha x hx
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hb y hy

theorem Reads.addMul {F : Fork} {a b : Aff} {m m' : PscF.MaskForm} {v v' : GE}
    (ha : Reads W home F a m v) (hb : Reads W home F b m' v') (k : E) :
    Reads W home F (Aff.addMul a b k) (m ++ PscF.scaleForm (readE k) m') (v + readE k * v') :=
  ⟨ha.ne.addMul hb.ne k, ha.shown.addMul hb.shown k, by
    show (Aff.addMul a b k).value rho _ = _
    rw [Aff.value_addMul]
    show pubV F a + readE k * pubV F b = _
    rw [ha.pub, hb.pub], by
    show (Aff.addMul a b k).value rho _ = _
    rw [Aff.value_addMul]
    show hidV W home F a + readE k * hidV W home F b = _
    rw [ha.hid, hb.hid, PscF.World.form_append, PscF.World.form_scale]
    ring⟩

/-- The same claim under another mask form with the same value, and an equal value. -/
theorem Reads.congr {F : Fork} {a : Aff} {m m' : PscF.MaskForm} {v v' : GE}
    (h : Reads W home F a m v) (hm : W.form m' = W.form m) (hv : v' = v) :
    Reads W home F a m' v' := by
  subst hv
  exact ⟨h.ne, h.shown, h.pub, by rw [h.hid, hm]⟩

theorem Reads.empty (F : Fork) : Reads W home F {} [] 0 :=
  ⟨rfl, fun x hx => by simp at hx, Aff.value_empty _ _, by
    show ({} : Aff).value rho _ = _
    rw [Aff.value_empty]
    simp [PscF.World.form]⟩

theorem Reads.scale {F : Fork} {a : Aff} {m : PscF.MaskForm} {v : GE}
    (ha : Reads W home F a m v) (k : E) :
    Reads W home F (Aff.scale a k) (PscF.scaleForm (readE k) m) (readE k * v) :=
  ((Reads.empty F).addMul ha k).congr (by rw [List.nil_append]) (by rw [zero_add])

theorem Reads.add {F : Fork} {a b : Aff} {m m' : PscF.MaskForm} {v v' : GE}
    (ha : Reads W home F a m v) (hb : Reads W home F b m' v') :
    Reads W home F (a + b) (m ++ m') (v + v') :=
  (ha.addMul hb oneE).congr (by
    rw [PscF.World.form_append, PscF.World.form_append, PscF.World.form_scale, readE_one, one_mul])
    (by rw [readE_one, one_mul])

/-- What the loop of Fork.publicPart returns. -/
theorem public_loop (F : Fork) : ∀ (l : List (ℕ × E)) (v τ : E),
    l.foldlM (fun (v : E) (x : ℕ × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y)) v =
      some τ →
    (∀ x ∈ l, x.1 < F.ns ∧ Filled F x.1) ∧
      readE τ = readE v + (l.map fun t => readE t.2 * readE (F.vp.getD t.1 zeroE)).sum
  | [], v, τ, h => by
    have h' : some v = some τ := h
    cases h'
    exact ⟨fun x hx => (by cases hx), (by simp)⟩
  | x :: l, v, τ, h => by
    rw [List.foldlM_cons] at h
    cases hs : F.shown x.1 with
    | none => rw [hs] at h; cases h
    | some y =>
      rw [hs] at h
      obtain ⟨h1, h2⟩ := public_loop F l _ τ h
      obtain ⟨a1, a2, rfl⟩ := (PscRun.shown_iff F x.1 y).1 hs
      refine ⟨fun z hz => ?_, ?_⟩
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨a1, a2⟩
        · exact h1 z hz
      · rw [h2, readE_add, readE_mul, List.map_cons, List.sum_cons]
        ring

theorem public_reads {F : Fork} {a : Aff} {τ : E} (h : F.publicPart a = some τ) :
    AllShown F a ∧ readE τ = pubV F a := by
  unfold Fork.publicPart at h
  rw [← Array.foldlM_toList] at h
  obtain ⟨h1, h2⟩ := public_loop F _ _ _ h
  exact ⟨h1, by rw [h2, pubV_eq]; rfl⟩

/-! ## All worlds -/

/-- The world that is 1 at the mask entries that stand at j, and 0 elsewhere. -/
def unitW {J : Type} [DecidableEq J] (sl : Slot → J) (j : J) : PscF.World :=
  ⟨fun s => if j = sl s then 1 else 0⟩

theorem form_unit {J : Type} [DecidableEq J] (sl : Slot → J) (j : J) : ∀ m : PscF.MaskForm,
    (unitW sl j).form m = rdMF sl m j
  | [] => rfl
  | t :: m => by
    rw [PscF.World.form_cons, Lk6.PortSim.rdMF_cons, form_unit sl j m]
    congr 1
    show t.2 * (if j = sl t.1 then 1 else 0) = Lk6.Parts.one (sl t.1) t.2 j
    unfold Lk6.Parts.one
    split <;> simp

/-- Two mask forms with the same value in every world are one function on the entries. -/
theorem forms_ext {J : Type} [DecidableEq J] (sl : Slot → J) {m m' : PscF.MaskForm}
    (h : ∀ W : PscF.World, W.form m = W.form m') : rdMF sl m = rdMF sl m' :=
  funext fun j => by rw [← form_unit, ← form_unit, h]

/-- From "form - value" in every world to the form and the value. -/
theorem split_ext {m m' : PscF.MaskForm} {v v' : GE}
    (h : ∀ W : PscF.World, W.form m - v = W.form m' - v') :
    v = v' ∧ ∀ W : PscF.World, W.form m = W.form m' := by
  have z : ∀ l : PscF.MaskForm, (⟨fun _ => 0⟩ : PscF.World).form l = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons t l ih => rw [PscF.World.form_cons, ih]; simp
  have h0 := h ⟨fun _ => 0⟩
  rw [z, z] at h0
  have hv : v = v' := by linear_combination -h0
  exact ⟨hv, fun W => by have := h W; rw [hv] at this; linear_combination this⟩

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.hidV_eq
#print axioms VerifiableInference.Desc.K3.KeyLaw.Reads.addMul
#print axioms VerifiableInference.Desc.K3.KeyLaw.public_reads
#print axioms VerifiableInference.Desc.K3.KeyLaw.forms_ext
#print axioms VerifiableInference.Desc.K3.KeyLaw.split_ext
