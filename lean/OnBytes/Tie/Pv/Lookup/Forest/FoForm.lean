-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean.
The words in which a stretch of the byte-level lookup routine is compared with the flat function.

A form of the byte-level verifier (Aff) names hidden values by their slots. What stands under a slot
is kept in the state of the sub-proof (Fork) and is read only at the end, so a statement on a form's
value must hold in every later state.

* `Later F G`: G has at least F's slots taken and as many slots in all, and every slot that is
  FILLED in F stays filled in G and keeps what stands under it (what was shown, the factor of the
  mask entry). A slot that is taken and still free may be filled later: a sumcheck's claim fills the
  slots of its hiding polynomial, which were taken rounds before. `Later.refl`, `Later.trans`,
  `took_later`.
* `FilledA F a` (OnBytes/Tie/Pv/Lookup/Forest/FoEv.lean): every slot that the form a names is filled
  in F. `value_later`, `publicPart_later`: such a form keeps its value and its public part in every
  later state.
* `FormIs ρ F C tg inc`: in every later state the public part of the form C, if it is given, reads
  tg, and for every mask row the value of C is tg less the sparse form inc at the mask row.
* `RowIs ρ F row r`: in every later state, for every mask row, the value of the claim row is the
  value of the flat function's row r: its form at the mask row less its target.
* `FormIs.later`, `RowIs.later`: both pass to later states.
* `Closed ρ l`: the calls of l leave no message open.
* `worldAt ρ G mk en μ`, `ValIs ρ F mk en ok a cf c`: for a form that also names entries of virtual
  rows. The caller says at which place each mask entry stands (mk), what each entry of a virtual row
  is as a function of the entries (en: a virtual row is a combination of rows), and which entries
  are lawful (ok; `zeroOk`: the place that is no cell reads 0); then in every later state, at all
  lawful entries μ, the value of the form a is the sparse form cf at μ plus c. `valIs_of`,
  `ValIs.later`.
* `RowVal ρ F mk en ok row u r`: the claim row is u times the flat function's row r. Two of the
  byte-level claims are written with the other sign, so whoever adds claims up must see u.
* `OnMasks cf`, `evalL_muOf`, `evalL_scale`, `FormIs.valIs`, `RowIs.rowVal`: a form or claim on mask
  entries alone, carried into these words.
* `hideRun_later`: filling a run of slots, in a state whose arrays have the right sizes, leads to a
  later state (on `hideRun_ok` of OnBytes/Tie/Pv/Psc/PscFork.lean).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

/-- G is a later state than F: what stands under the slots that are filled in F is kept. -/
structure Later (F G : Fork) : Prop where
  next : F.next ≤ G.next
  ns : G.ns = F.ns
  keep : ∀ j, Filled F j → Filled G j ∧ G.vp.getD j zeroE = F.vp.getD j zeroE ∧
    G.mf.getD j zeroE = F.mf.getD j zeroE

theorem Later.refl (F : Fork) : Later F F := ⟨le_refl _, rfl, fun _ h => ⟨h, rfl, rfl⟩⟩

theorem Later.trans {F G H : Fork} (h1 : Later F G) (h2 : Later G H) : Later F H :=
  ⟨le_trans h1.next h2.next, h2.ns.trans h1.ns, fun j hj =>
    ⟨(h2.keep j (h1.keep j hj).1).1, (h2.keep j (h1.keep j hj).1).2.1.trans (h1.keep j hj).2.1,
      (h2.keep j (h1.keep j hj).1).2.2.trans (h1.keep j hj).2.2⟩⟩

theorem took_later (F : Fork) (n : ℕ) : Later F (took F n) :=
  ⟨Nat.le_add_right _ _, rfl, fun _ h => ⟨h, rfl, rfl⟩⟩

theorem shown_later {F G : Fork} (h : Later F G) (j : ℕ) (hj : j < F.ns ∧ Filled F j) :
    G.shown j = F.shown j := by
  unfold Fork.shown
  have hF : F.gotF.getD j false = true := hj.2
  have hG : G.gotF.getD j false = true := (h.keep j hj.2).1
  rw [h.ns, hF, hG, (h.keep j hj.2).2.1]

theorem foldlM_congr_mem {α σ : Type} (f g : σ → α → Option σ) : ∀ (l : List α) (s : σ),
    (∀ x ∈ l, ∀ s, f s x = g s x) → l.foldlM f s = l.foldlM g s
  | [], _, _ => rfl
  | a :: l, s, h => by
    rw [List.foldlM_cons, List.foldlM_cons, h a List.mem_cons_self s]
    cases g s a with
    | none => rfl
    | some s' => exact foldlM_congr_mem f g l s' fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem publicPart_later {F G : Fork} (h : Later F G) (a : Aff) (ha : FilledA F a) :
    G.publicPart a = F.publicPart a := by
  unfold Fork.publicPart
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact foldlM_congr_mem _ _ _ _ fun x hx s => by rw [shown_later h x.1 (ha x hx)]

/-- Filling a run of slots leads to a later state. -/
theorem hideRun_later {F G : Fork} {first : ℕ} {v : Array OnBytes.E} {f : OnBytes.E} (hF : Sized F)
    (h : F.hideRun first v f = some G) : Later F G := by
  obtain ⟨hS, _, hin, hout⟩ := hideRun_ok F G first v f hF h
  refine ⟨le_of_eq hS.next.symm, hS.ns, fun j hj => ?_⟩
  have ho : j < first ∨ first + v.size ≤ j := by
    by_contra hc
    have h1 : first ≤ j := by omega
    have h2 : j - first < v.size := by omega
    have := (hin (j - first) h2).2.1
    rw [show first + (j - first) = j by omega] at this
    exact this hj
  exact ⟨(hout j ho).2.2.2 hj, (hout j ho).1, (hout j ho).2.1⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem value_later {F G : Fork} (h : Later F G) (a : Aff) (ha : FilledA F a) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) :
    a.value ρ (G.worldOf ρ mask entry) = a.value ρ (F.worldOf ρ mask entry) := by
  unfold Aff.value
  congr 2
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  unfold slotValue Fork.worldOf
  simp only
  rw [(h.keep x.1 (ha x hx).2).2.1, (h.keep x.1 (ha x hx).2).2.2]

/-- The form C has the public part tg, and its value is tg less the sparse form inc at the mask
row. -/
def FormIs (F : Fork) (C : Aff) (tg : K) (inc : List (Pl × K)) : Prop :=
  ∀ G, Later F G →
    (∀ x, G.publicPart C = some x → ρ.val x = tg) ∧
    ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
      C.value ρ (G.worldOf ρ mask entry) = tg - evalL (muOf mask) inc

/-- The claim row is the flat function's row r. -/
def RowIs (F : Fork) (row : Aff) (r : SRow Pl K) : Prop :=
  ∀ G, Later F G → ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
    row.value ρ (G.worldOf ρ mask entry) = rowRes (muOf mask) r

/-- A form whose slots are filled is compared once, in the state in which it is made. -/
theorem formIs_of {F : Fork} {C : Aff} {tg : K} {inc : List (Pl × K)} (hC : FilledA F C)
    (h1 : ∀ x, F.publicPart C = some x → ρ.val x = tg)
    (h2 : ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
      C.value ρ (F.worldOf ρ mask entry) = tg - evalL (muOf mask) inc) : FormIs ρ F C tg inc :=
  fun G hG => ⟨fun x hx => h1 x (by rw [← publicPart_later hG C hC]; exact hx),
    fun mask entry => by rw [value_later ρ hG C hC]; exact h2 mask entry⟩

theorem rowIs_of {F : Fork} {row : Aff} {r : SRow Pl K} (hC : FilledA F row)
    (h : ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
      row.value ρ (F.worldOf ρ mask entry) = rowRes (muOf mask) r) : RowIs ρ F row r :=
  fun G hG mask entry => by rw [value_later ρ hG row hC]; exact h mask entry

theorem FormIs.later {F G : Fork} {C : Aff} {tg : K} {inc : List (Pl × K)}
    (h : FormIs ρ F C tg inc) (hG : Later F G) : FormIs ρ G C tg inc :=
  fun H hH => h H (hG.trans hH)

theorem RowIs.later {F G : Fork} {row : Aff} {r : SRow Pl K} (h : RowIs ρ F row r)
    (hG : Later F G) : RowIs ρ G row r :=
  fun H hH => h H (hG.trans hH)

/-- The world at the entries μ: mask entry j stands at the place mk j; entry i of virtual row r of
array t is en μ t r i, any function of the entries (a virtual row is a combination of rows). -/
def worldAt {P : Type} (G : Fork) (mk : ℕ → P) (en : (P → K) → ℕ → ℕ → ℕ → K) (μ : P → K) :
    World K :=
  G.worldOf ρ (fun j => μ (mk j)) (en μ)

/-- The form a, which may name entries of virtual rows, is the sparse form cf plus the constant c.
-/
def ValIs {P : Type} (F : Fork) (mk : ℕ → P) (en : (P → K) → ℕ → ℕ → ℕ → K) (ok : (P → K) → Prop)
    (a : Aff) (cf : List (P × K)) (c : K) : Prop :=
  ∀ G, Later F G → ∀ μ : P → K, ok μ → a.value ρ (worldAt ρ G mk en μ) = evalL μ cf + c

/-- The claim row is u times the flat function's row r (meant: u = 1 or -1; two of the byte-level
claims are written with the other sign). -/
def RowVal {P : Type} (F : Fork) (mk : ℕ → P) (en : (P → K) → ℕ → ℕ → ℕ → K) (ok : (P → K) → Prop)
    (row : Aff) (u : K) (r : SRow P K) : Prop :=
  ∀ G, Later F G → ∀ μ : P → K, ok μ → row.value ρ (worldAt ρ G mk en μ) = u * rowRes μ r

/-- The entries at which the flat function's rows are read: the place that is no cell reads 0. -/
def zeroOk (μ : Pl → K) : Prop := μ Pl.zero = 0

theorem valIs_of {P : Type} {F : Fork} {mk : ℕ → P} {en : (P → K) → ℕ → ℕ → ℕ → K}
    {ok : (P → K) → Prop} {a : Aff} {cf : List (P × K)} {c : K} (ha : FilledA F a)
    (h : ∀ μ : P → K, ok μ → a.value ρ (worldAt ρ F mk en μ) = evalL μ cf + c) :
    ValIs ρ F mk en ok a cf c :=
  fun G hG μ hμ => by
    unfold worldAt
    rw [value_later ρ hG a ha]
    exact h μ hμ

theorem ValIs.later {P : Type} {F G : Fork} {mk : ℕ → P} {en : (P → K) → ℕ → ℕ → ℕ → K}
    {ok : (P → K) → Prop} {a : Aff} {cf : List (P × K)} {c : K} (h : ValIs ρ F mk en ok a cf c)
    (hG : Later F G) : ValIs ρ G mk en ok a cf c :=
  fun H hH => h H (hG.trans hH)

theorem RowVal.later {P : Type} {F G : Fork} {mk : ℕ → P} {en : (P → K) → ℕ → ℕ → ℕ → K}
    {ok : (P → K) → Prop} {row : Aff} {u : K} {r : SRow P K} (h : RowVal ρ F mk en ok row u r)
    (hG : Later F G) : RowVal ρ G mk en ok row u r :=
  fun H hH => h H (hG.trans hH)

/-- The sparse form names mask entries alone. -/
def OnMasks (cf : List (Pl × K)) : Prop := ∀ pc ∈ cf, ∃ j, pc.1 = Pl.mask j

omit [CommRing K] in
theorem OnMasks.nil : OnMasks ([] : List (Pl × K)) := fun _ h => absurd h List.not_mem_nil

/-- On mask entries alone the two ways of reading a sparse form agree. -/
theorem evalL_muOf {cf : List (Pl × K)} (h : OnMasks cf) (μ : Pl → K) :
    evalL (muOf fun j => μ (.mask j)) cf = evalL μ cf := by
  unfold evalL
  refine congrArg List.sum (List.map_congr_left fun pc hpc => ?_)
  obtain ⟨j, hj⟩ := h pc hpc
  rw [hj]
  rfl

theorem evalL_scale {P : Type} (μ : P → K) (u : K) (cf : List (P × K)) :
    evalL μ (scale u cf) = u * evalL μ cf := by
  unfold evalL scale
  rw [List.map_map, ← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun pc _ => mul_assoc u pc.2 (μ pc.1))

/-- A form on mask entries alone, in the words for forms that may name entries of virtual rows. -/
theorem FormIs.valIs {F : Fork} {C : Aff} {tg : K} {inc : List (Pl × K)} (h : FormIs ρ F C tg inc)
    (hm : OnMasks inc) (en : (Pl → K) → ℕ → ℕ → ℕ → K) (ok : (Pl → K) → Prop) :
    ValIs ρ F Pl.mask en ok C (scale (-1) inc) tg :=
  fun G hG μ _ => by
    unfold worldAt
    rw [(h G hG).2, evalL_muOf hm, evalL_scale]
    ring

/-- A claim on mask entries alone, likewise. -/
theorem RowIs.rowVal {F : Fork} {row : Aff} {r : SRow Pl K} (h : RowIs ρ F row r)
    (hm : OnMasks r.cf) (en : (Pl → K) → ℕ → ℕ → ℕ → K) (ok : (Pl → K) → Prop) :
    RowVal ρ F Pl.mask en ok row 1 r :=
  fun G hG μ _ => by
    unfold worldAt
    rw [h G hG, one_mul]
    unfold rowRes
    rw [evalL_muOf hm]

/-- The calls leave no message open. -/
def Closed (l : List Ev) : Prop := openAfter ρ [] l = []

theorem Closed.nil : Closed ρ [] := rfl

theorem Closed.append {l₁ l₂ : List Ev} (h1 : Closed ρ l₁) (h2 : Closed ρ l₂) :
    Closed ρ (l₁ ++ l₂) := by
  unfold Closed
  rw [openAfter_append, h1, h2]

theorem flEv_app {l₁ l₂ : List Ev} (h1 : Closed ρ l₁) :
    flEv ρ (l₁ ++ l₂) = flEv ρ l₁ ++ flEv ρ l₂ := flEv_append ρ l₁ l₂ h1

end
end Fo
