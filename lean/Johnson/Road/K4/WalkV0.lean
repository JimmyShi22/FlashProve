-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/WalkV0.lean: THE ORDER OF THE WEIGHT CLAIMS: the number that the verifier gives to
the first weight claim of a panel is the number of the pieces of the panels in front of it in the
library's list.

The verifier's two functions that append a panel (plain and tri, OnBytes/Model/LayerPanels.lean)
give a panel with weights the next free number and move that number on: by the panel's rows, or by
1 for a panel with the selector. Every list of panels is made by these two alone. So the numbers
are running sums. The library's second side has, for a weight panel, one piece a row, or one piece
for a panel with the selector (cntB, Cb/Pv/Lay/At/InnerGeo.lean): the same steps.

Main names:
  `incV`: by how much a panel moves the next free number on.
  `WalkL n l n'`: from n, each panel of l that has a first weight claim has the running number, and
    the walk ends at n'.
  `Walked`: a state of the verifier's list is walked from 0 to its own next free number.
  `plain_walked`, `tri_walked`, `panelA_walked`, `panelsA_walked`, `panelT_walked`,
    `panelsT_walked`: each function keeps that.
  `walk_off`: a walked list whose members move the number as the members of a list of the
    library's panels without repeats count: the numbers are offIn
    (Johnson/Road/K4/NumPieces.lean), and the walk ends at the sum.
  `incV_fields`: under EndFields (Johnson/Road/K4/EndFields.lean) a panel moves the number by cntB.
  `placed_v0`: each weight panel of the placed list has b.v0 = some (v0Of D pn), and the verifier's
    number of weight claims is nWK D.
Limits. EndFields of every pair is a premise of placed_v0. An identity on public numbers: nothing on
what a claim says, on a world, on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.EndFields
import Johnson.Road.K4.NumPieces
import Johnson.Road.K4.StackRowB3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading)
open OnBytes.Model.Layer (Lay SBlk Panels PanelEnv plain tri panelA panelsA panelT panelsT
  placePanels)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan pans)
open Cb.Pv.Lay.At (cntB)

/-- By how much a panel moves the next free number on. -/
def incV (b : SBlk) : ℕ :=
  match b.v0 with
  | some _ => if b.tri then 1 else b.ni
  | none => 0

/-- From n, each panel that has a first weight claim has the running number; the walk ends at
n'. -/
def WalkL : ℕ → List SBlk → ℕ → Prop
  | n, [], n' => n = n'
  | n, b :: l, n' => (∀ v0, b.v0 = some v0 → v0 = n) ∧ WalkL (n + incV b) l n'

theorem walk_append : ∀ {l1 l2 : List SBlk} {n m n' : ℕ}, WalkL n l1 m → WalkL m l2 n' →
    WalkL n (l1 ++ l2) n'
  | [], _, _, _, _, h1, h2 => by
    have e : _ = _ := h1
    rw [e]
    exact h2
  | _ :: _, _, _, _, _, h1, h2 => ⟨h1.1, walk_append h1.2 h2⟩

/-- A state of the verifier's list is walked from 0 to its own next free number. -/
def Walked (s : Panels) : Prop := WalkL 0 s.bl.toList s.nextV

theorem walked_push {s : Panels} {b : SBlk} {n' : ℕ} (h : Walked s)
    (h1 : ∀ v0, b.v0 = some v0 → v0 = s.nextV) (h2 : s.nextV + incV b = n') :
    Walked { bl := s.bl.push b, nextV := n' } := by
  unfold Walked
  rw [Array.toList_push]
  exact walk_append h ⟨h1, h2⟩

theorem plain_walked {y : Lay} {ec : E} {claim : ℕ} {moeSet : Bool} {ny : ℕ}
    {A B : Option (ℕ → ℕ → Option OnBytes.Model.Aff)} {wt : ℕ → E} {virt : Option ℕ} {s : Panels}
    (h : Walked s) : Walked (plain y ec claim moeSet ny A B wt virt s) := by
  cases B with
  | none => exact walked_push h (fun _ e => (Option.some.inj e).symm) rfl
  | some B => exact walked_push h (fun _ e => nomatch e) rfl

theorem tri_walked {y : Lay} {ec : E} {claim nk : ℕ} {sl : Array E}
    {xx : Array OnBytes.Model.Aff} {virt : Option ℕ} {wt : E} {s : Panels} (h : Walked s) :
    Walked (tri y ec claim nk sl xx virt wt s) :=
  walked_push h (fun _ e => (Option.some.inj e).symm) rfl

theorem panelA_walked {p : PanelEnv} {ec : E} {el : Array E} {sn : String} {s : Panels}
    (h : Walked s) : Walked (panelA p ec el sn s) := by
  unfold panelA
  dsimp only
  split_ifs <;> first | exact plain_walked h | exact h

/-- A fold keeps what each step keeps. -/
theorem foldl_keeps {α σ : Type} {Q : σ → Prop} {f : σ → α → σ} (hf : ∀ s a, Q s → Q (f s a)) :
    ∀ (l : List α) (s : σ), Q s → Q (l.foldl f s)
  | [], _, h => h
  | a :: l, s, h => foldl_keeps hf l (f s a) (hf s a h)

/-- The same for a fold that may refuse. -/
theorem foldlM_keeps {α σ : Type} {Q : σ → Prop} {f : σ → α → Option σ}
    (hf : ∀ s a s', f s a = some s' → Q s → Q s') :
    ∀ (l : List α) (s s' : σ), l.foldlM f s = some s' → Q s → Q s'
  | [], s, s', h, hs => by
    rw [List.foldlM_nil] at h
    cases h
    exact hs
  | a :: l, s, s', h, hs => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := bind_some h
    exact foldlM_keeps hf l s1 s' h2 (hf s a s1 h1 hs)

theorem panelsA_walked {p : PanelEnv} {s : Panels} (h : Walked s) : Walked (panelsA p s) := by
  unfold panelsA
  exact foldl_keeps (fun s _ hs => foldl_keeps (fun _ _ hs' => panelA_walked hs') _ s hs) _ s h

theorem walked_pure {x s' : Panels} (h : (pure x : Option Panels) = some s') (hx : Walked x) :
    Walked s' := by
  cases h
  exact hx

theorem walked_bind {α : Type} {o : Option α} {g : α → Panels} {s' : Panels}
    (h : (do let a ← o; pure (g a)) = some s') (hg : ∀ a, Walked (g a)) : Walked s' := by
  obtain ⟨a, -, e⟩ := bind_some h
  exact walked_pure e (hg a)

theorem panelT_walked {p : PanelEnv} {ec : E} {el : Array E} {sn : String} {s s' : Panels}
    (h : panelT p ec el sn s = some s') (hs : Walked s) : Walked s' := by
  unfold panelT at h
  dsimp only at h
  split_ifs at h <;>
    first
      | exact walked_bind h fun _ => plain_walked hs
      | exact walked_pure h (plain_walked hs)
      | exact walked_pure h hs
      | (refine foldlM_keeps (fun s1 lm s2 e h1 => ?_) _ s s' h hs
         try dsimp only at e
         first
           | exact walked_pure e (tri_walked h1)
           | exact walked_bind e fun _ => tri_walked h1)

theorem panelsT_walked {p : PanelEnv} {TS : List ℕ} {s s' : Panels}
    (h : panelsT p TS s = some s') (hs : Walked s) : Walked s' := by
  unfold panelsT at h
  exact foldlM_keeps (fun s1 _ s2 e h1 =>
    foldlM_keeps (fun _ _ _ e' h' => panelT_walked e' h') _ s1 s2 e h1) _ s s' h hs

/-- The placing turns neither the numbers nor the steps. -/
theorem walk_placed : ∀ {l' l : List SBlk} {n n' : ℕ},
    List.Forall₂ (fun b' b : SBlk => ∃ o, b' = { b with off := o }) l' l → WalkL n l n' →
    WalkL n l' n'
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ⟨_, e⟩ t, h => by
    subst e
    exact ⟨h.1, walk_placed t h.2⟩

/-- **The numbers are running sums over the library's list.** -/
theorem walk_off (c : Pan → ℕ) : ∀ {bs : List SBlk} {ps : List Pan} {n n' : ℕ}, ps.Nodup →
    List.Forall₂ (fun b pn => incV b = c pn) bs ps → WalkL n bs n' →
    List.Forall₂ (fun b pn => ∀ v0, b.v0 = some v0 → v0 = n + offIn c ps pn) bs ps ∧
      n' = n + (ps.map c).sum
  | _, _, n, n', _, .nil, h => by
    have e : n = n' := h
    exact ⟨.nil, by rw [e]; rfl⟩
  | b :: bs, q :: ps, n, n', hn, .cons e t, h => by
    obtain ⟨hq, hn'⟩ := List.nodup_cons.mp hn
    obtain ⟨r1, r2⟩ := walk_off c hn' t h.2
    refine ⟨.cons (fun v0 hv => ?_) ((f2_mem_right r1).imp fun b' pn k v0 hv => ?_), ?_⟩
    · rw [h.1 v0 hv]
      show n = n + (if q = q then 0 else c q + offIn c ps q)
      rw [if_pos rfl, Nat.add_zero]
    · have hne : ¬ q = pn := fun e' => hq (e' ▸ k.1)
      rw [k.2 v0 hv, e]
      show n + c q + offIn c ps pn = n + (if q = pn then 0 else c q + offIn c ps pn)
      rw [if_neg hne, Nat.add_assoc]
    · rw [r2, e, List.map_cons, List.sum_cons, Nat.add_assoc]

variable {K : Type} [Field K] [scl : Scl] {ρ : Reading K}

/-- Under EndFields a panel moves the number by the number of its pieces on the second side. -/
theorem incV_fields {y : Lay} {sh : Array E} {D : Dim} {z : ℕ → K} {b : SBlk} {pn : Pan}
    (En : EndFields ρ y sh D z b pn) : incV b = cntB D pn := by
  unfold incV cntB
  cases hw : pn.weight with
  | false =>
    rw [En.v0n hw]
    rfl
  | true =>
    obtain ⟨v0, e⟩ := En.v0w hw
    rw [e, En.tri]
    cases h3 : pn.three with
    | true => rfl
    | false =>
      show b.ni = pn.nr D
      exact En.ni h3

/-- **The order of the weight claims.** -/
theorem placed_v0 {y : Lay} {sh : Array E} {D : Dim} {z : ℕ → K} {p : PanelEnv} {TS : List ℕ}
    {pans' : Panels} (hp : panelsT p TS (panelsA p {}) = some pans')
    (FE : List.Forall₂ (fun b pn => EndFields ρ y sh D z b pn) (placePanels pans'.bl).1.toList
      (pans D)) :
    List.Forall₂ (fun (b : SBlk) (pn : Pan) => pn.weight = true → b.v0 = some (v0Of D pn))
      (placePanels pans'.bl).1.toList (pans D) ∧ pans'.nextV = nWK D := by
  have w0 : Walked ({} : Panels) := rfl
  have w1 : Walked pans' := panelsT_walked hp (panelsA_walked w0)
  have w2 := walk_placed (placed_f2 pans'.bl) w1
  obtain ⟨r1, r2⟩ := walk_off (cntB D) (Cb.Pv.Lay.End.Sig.pans_nodup D)
    (FE.imp fun _ _ En => incV_fields En) w2
  refine ⟨(f2_and FE r1).imp fun b pn k hw => ?_, ?_⟩
  · obtain ⟨v0, e⟩ := k.1.v0w hw
    rw [e, k.2 v0 e, Nat.zero_add]
    rfl
  · rw [r2, Nat.zero_add]
    rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.panelsT_walked
#print axioms OnBytes.Road.K4.walk_off
#print axioms OnBytes.Road.K4.placed_v0
