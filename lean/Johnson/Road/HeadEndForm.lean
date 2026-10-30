-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/HeadEndForm.lean: the hidden value at the end of the lookup's key side, in what the
output head's check hears.

The lookup's routine (Forest.pad in OnBytes/Model/Look.lean) walks down the product tree of the
keys, level by level. Each level is a sumcheck that ends in two hidden values, under two slots,
and hands down to the next level the form (1 - tau) vL + tau vR. What the last level hands down is
kept as cEnd; the claim on the calls' key vectors sets it against the calls' forms. This file
shows that shape of cEnd, and that its two slots are taken before the slots of the sums of limb
products, which the head's routine hear (OnBytes/Model/HeadHeard.lean) takes after the lookup.

How. The tree has at least ten levels, because Forest.shape refuses a smaller depth (shape_depth).
Every level leaves a form of that shape on the last two slots that were taken (level_ok), so the
last one does (levels_end). No later routine lowers the number of the next free slot.

Main theorems: shape_depth, level_ok, levels_keep, levels_end, levels_grow, roundsIn_grows, pad_end,
mergedPoint_stay, hear_end.

What is not claimed. Every theorem begins "if the routine succeeds": none says that it does. Nothing
is said about what a slot holds, or about what a verifier's acceptance shows. The program does not
import this file.
-/
import Johnson.Road.HeadSlots
import Johnson.Road.FormsKeysCap

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Fork SubM Aff)

/-- Forest.shape returns no tree of a depth below ten. -/
theorem shape_depth {calls : Array Model.Call} {lid : ℕ} {fo : Model.Forest.Shape}
    (h : Model.Forest.shape calls lid = .ok fo) : 10 ≤ fo.dT := by
  unfold Model.Forest.shape at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨e2, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r, -, h⟩ := ok_of_bind h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨-, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  exact Nat.not_lt.mp e2

/-- The form of the walk's state is what a level hands down, on the last two slots that were taken
before the state F. -/
def HandedDown (s : Model.Forest.Descent) (F : Fork) : Prop :=
  ∃ (sL : ℕ) (tau : E),
    s.form = Aff.scale (Aff.slot sL) (subE oneE tau) + Aff.scale (Aff.slot (sL + 1)) tau ∧
      F.next = sL + 2

/-- One level: it takes slots, and leaves such a form. -/
theorem level_ok {s s' : Model.Forest.Descent} {mu : ℕ} {order : List ℕ} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.Forest.level s mu order) F C s' G D) : HandedDown s' G ∧ F.next ≤ G.next := by
  unfold Model.Forest.level at h
  obtain ⟨o, F1, C1, h1, h2⟩ := bind_ok h
  obtain ⟨e1, e2, e3⟩ := levelIn_ok h1
  have h2' : Ok (pure { rows := s.rows.push o.row, rho := o.handDown.1, form := o.handDown.2 } :
      SubM Model.Forest.Descent) F1 C1 s' G D := h2
  obtain ⟨rfl, rfl, -⟩ := pure_ok h2'
  refine ⟨⟨o.sL, o.tau, ?_, e3⟩, by omega⟩
  show Aff.scale (Aff.slot o.sL) (subE oneE o.tau) + Aff.scale (Aff.slot o.sR) o.tau = _
  rw [e2]

/-- Further levels keep the shape. -/
theorem levels_keep (ord : ℕ → List ℕ) : ∀ (l : List ℕ) (s : Model.Forest.Descent) (F : Fork)
    (C : Ctx) (s' : Model.Forest.Descent) (G : Fork) (D : Ctx), HandedDown s F →
    Ok (l.foldlM (fun s mu => Model.Forest.level s mu (ord mu)) s) F C s' G D → HandedDown s' G
  | [], s, F, C, s', G, D, P, h => by
    rw [List.foldlM_nil] at h
    obtain ⟨rfl, rfl, -⟩ := pure_ok h
    exact P
  | x :: l, s, F, C, s', G, D, _, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, F1, C1, h1, h2⟩ := bind_ok h
    exact levels_keep ord l s1 F1 C1 s' G D (level_ok h1).1 h2

/-- After at least one level the form is what the last level hands down. -/
theorem levels_end {ord : ℕ → List ℕ} {l : List ℕ} {s s' : Model.Forest.Descent} {F G : Fork}
    {C D : Ctx} (h : Ok (l.foldlM (fun s mu => Model.Forest.level s mu (ord mu)) s) F C s' G D)
    (hl : l ≠ []) : HandedDown s' G := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x l =>
    rw [List.foldlM_cons] at h
    obtain ⟨s1, F1, C1, h1, h2⟩ := bind_ok h
    exact levels_keep ord l s1 F1 C1 s' G D (level_ok h1).1 h2

/-- Levels do not lower the number of the next free slot. -/
theorem levels_grow (ord : ℕ → List ℕ) (f : ℕ → ℕ) : ∀ (l : List ℕ) (s : Model.Forest.Descent)
    (F : Fork) (C : Ctx) (s' : Model.Forest.Descent) (G : Fork) (D : Ctx),
    Ok (l.foldlM (fun s x => Model.Forest.level s (f x) (ord x)) s) F C s' G D → F.next ≤ G.next
  | [], s, F, C, s', G, D, h => by
    rw [List.foldlM_nil] at h
    obtain ⟨-, rfl, -⟩ := pure_ok h
    exact Nat.le_refl _
  | x :: l, s, F, C, s', G, D, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, F1, C1, h1, h2⟩ := bind_ok h
    exact Nat.le_trans (level_ok h1).2 (levels_grow ord f l s1 F1 C1 s' G D h2)

/-- Rounds in a row do not lower it either. -/
theorem roundsLoop_grows (form : Model.RoundForm) : ∀ (zs : List (E × ℕ))
    (s : Array E × Model.Psc) (F : Fork) (C : Ctx) (s' : Array E × Model.Psc) (G : Fork) (D : Ctx),
    Ok (zs.foldlM (fun (s : Array E × Model.Psc) z => do
      let (r, q) ← Model.roundIn form s.2 z.1 z.2
      pure (s.1.push r, q)) s) F C s' G D → F.next ≤ G.next
  | [], s, F, C, s', G, D, h => by
    rw [List.foldlM_nil] at h
    obtain ⟨-, rfl, -⟩ := pure_ok h
    exact Nat.le_refl _
  | z :: zs, s, F, C, s', G, D, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, F1, C1, h1, h2⟩ := bind_ok h
    obtain ⟨⟨r, q⟩, F2, C2, h3, h4⟩ := bind_ok h1
    have e1 := roundIn_ok h3
    obtain ⟨-, e2, -⟩ := pure_ok h4
    have e3 := roundsLoop_grows form zs s1 F1 C1 s' G D h2
    rw [e2] at e3
    omega

/-- Rounds of one form give no slot back. -/
theorem roundsIn_grows {form : Model.RoundForm} {p : Model.Psc} {zs : List (E × ℕ)}
    {x : Array E × Model.Psc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.roundsIn form p zs) F C x G D) : F.next ≤ G.next :=
  roundsLoop_grows form zs (#[], p) F C x G D h

/-- A list of the numbers below a positive number is not empty. -/
theorem range_ne_nil {n : ℕ} (h : 0 < n) : List.range n ≠ [] := by
  intro e
  have k := congrArg List.length e
  simp at k
  omega

/-- **The lookup's routine**: the hidden value at the end of the key side is (1 - tau) times one
slot plus tau times the next, and both slots have been taken when the routine ends. -/
theorem pad_end {calls : Array Model.Call} {pub : Array ℕ} {lid : ℕ} {F G : Fork} {C D : Ctx}
    {g : Model.Forest.Heard} (h : Ok (Model.Forest.pad calls pub lid) F C g G D) :
    ∃ (sL : ℕ) (tau : E),
      g.cEnd = Aff.scale (Aff.slot sL) (subE oneE tau) + Aff.scale (Aff.slot (sL + 1)) tau ∧
        sL + 2 ≤ G.next := by
  unfold Model.Forest.pad at h
  obtain ⟨h0, _, _, k, h⟩ := bind_ok h
  obtain ⟨e0, -, -⟩ := subGet_ok k
  obtain ⟨_, _, _, -, h⟩ := bind_ok h
  obtain ⟨slot0, _, _, -, h⟩ := bind_ok h
  obtain ⟨o1, _, _, -, h⟩ := bind_ok h
  obtain ⟨o2, _, _, -, h⟩ := bind_ok h
  obtain ⟨o3, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨theta, alpha, a⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨t, _, _, -, h⟩ := bind_ok h
  obtain ⟨keys, Fk, Ck, kk, h⟩ := bind_ok h
  obtain ⟨table, Ft, Ct, kt, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨leaves, F5, C5, k5, h⟩ := bind_ok h
  obtain ⟨⟨zb0, leaves'⟩, F6, C6, k6, h⟩ := bind_ok h
  obtain ⟨r5, F7, C7, k7, h⟩ := bind_ok h
  obtain ⟨bits, F8, C8, k8, h⟩ := bind_ok h
  obtain ⟨⟨zb1, bits'⟩, F9, C9, k9, h⟩ := bind_ok h
  obtain ⟨⟨sBit, bits''⟩, F10, C10, k10, h⟩ := bind_ok h
  obtain ⟨vBit, F11, C11, k11, h⟩ := bind_ok h
  obtain ⟨⟨bitsRow, p'⟩, F12, C12, k12, h⟩ := bind_ok h
  obtain ⟨s, F13, C13, k13, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨rfl, rfl, -⟩ := pure_ok h
  have hd := shape_depth (ok_of_toOption e0)
  obtain ⟨sL, tau, f1, f2⟩ := levels_end kk (range_ne_nil (by
    show 0 < h0.dT + h0.rK
    omega))
  have g1 := levels_grow _ _ _ _ _ _ _ _ _ kt
  have g5 := (pscBegin_ok k5).2
  have g6 := roundsIn_grows k6
  have g7 := congrArg Fork.next (lift_stay k7)
  have g8 := (pscBegin_ok k8).2
  have g9 := roundsIn_grows k9
  obtain ⟨g10, g10'⟩ : F9.next ≤ sBit ∧ F10.next = sBit + 1 := pscEnds_ok k10
  have g11 := congrArg Fork.next (ask_stay k11)
  have g12 := pscRow_ok k12
  have g13 := congrArg Fork.next (ask_stay k13)
  exact ⟨sL, tau, f1, by omega⟩

/-- The routine that merges the calls' points leaves the state. -/
theorem mergedPoint_stay {h : Model.Head.Shape} {g1 : Model.Forest.Heard} {Zl : Array E}
    {F G : Fork} {C D : Ctx} (hm : Ok (Model.Head.mergedPoint h g1) F C Zl G D) : G = F := by
  unfold Model.Head.mergedPoint at hm
  obtain ⟨Z, F1, C1, h1, h2⟩ := bind_ok hm
  obtain ⟨u, F2, C2, h3, h4⟩ := bind_ok h2
  obtain ⟨-, e3, -⟩ := pure_ok h4
  have e1 := ((ok_lift _ _ _ _ _ _).1 h1).2
  have e2 := ((ok_lift _ _ _ _ _ _).1 h3).2
  rw [e3, e2, e1]

/-- **What hear returns**: the hidden value at the end of the lookup's key side is (1 - tau) times
one slot plus tau times the next, and both lie before the slots of the sums of limb products. -/
theorem hear_end {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard} {F G : Fork} {C D : Ctx}
    (hx : Ok (Model.Head.hear h L hp cov plain) F C x G D) :
    ∃ (sL : ℕ) (tau : E),
      x.g1.cEnd = Aff.scale (Aff.slot sL) (subE oneE tau) + Aff.scale (Aff.slot (sL + 1)) tau ∧
        sL + 1 < x.sW := by
  obtain ⟨yTok, F1, C1, F2, C2, g1, F3, C3, Zl, F4, C4, PV, F5, C5, sW, gp, wpl, F6, C6, sPv, omV,
    tV, F7, C7, qN, qH, tN, F8, C8, tH, rs, F9, C9, _, _, k3, k4, k5, k6, _, _, _, _, _, _, ex⟩ :=
    hear_steps hx
  obtain ⟨sL, tau, e1, e2⟩ := pad_end k3
  have m4 := congrArg Fork.next (mergedPoint_stay k4)
  have m5 := congrArg Fork.next (lift_stay k5)
  obtain ⟨s1, _, _, _⟩ := hearSquares_ok k6
  subst ex
  refine ⟨sL, tau, e1, ?_⟩
  show sL + 1 < sW
  omega

#print axioms shape_depth
#print axioms pad_end
#print axioms hear_end

end OnBytes.Road.Hd
