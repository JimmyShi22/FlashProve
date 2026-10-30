-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/JoinTable.lean
(kind K9's soundness lemma): THEOREM: THE ROW OF THREE PIECES
ON THE ROAD OF MOVES (Law/JoinMoves.lean: inMoves) BETWEEN THE ITEMS OF THE TABLE OF JOINTS: forms
of the listed runs; totalB; total; each with the open rows (the fields as
typed: the form of the four fields, Sound/FormsQ.lean).
  afterOf, after_iff   a row of quiet moves as one function on records: THE TABLE's LETTER "after"
                (the runs behind the batching, one after the other); a yes of the row is its return.
  tabAt_quiet, data_quiet   along a row of quiet moves that keep the door and the book, the
                accessor's tables and the data are the same.
  relT3         the relations at the four boundaries, in the table's letters.
  join_table    **THE ROW AT THESE RELATIONS**, from JoinAsks at tabOf := the table's one accessor
                and ms1 := the moves of a list of steps.
HYPOTHESES NEW HERE: hbook2 (each quiet move behind the batching keeps the book) - htin (the public
test totalIn says yes of whatever these moves return from a state with on1) - hs2 (at a state with
on2 K9's part is there) - hitems (Law/AtTable.lean).
Not claimed: any of them at a segment of the protocol.

-/
import Johnson.Desc.First.Batch.Law.JoinMoves
import Johnson.Desc.First.Batch.Law.TableTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (onJ relJ JoinAsks)
open _root_.Run (ckP)

/-- A row of quiet moves as one function on records. -/
def afterOf : List (Move S) → S → Except String S
  | [], s => .ok s
  | .quiet h :: l, s => (h s).bind (afterOf l)
  | .add _ :: _, _ => .error "a move that adds"

/-- A yes of a row of quiet moves is that function's return. -/
theorem after_iff : ∀ (ms : List (Move S)), (∀ m ∈ ms, ∃ h, m = .quiet h) → ∀ s t,
    MovesYes atS ms s t [] ↔ afterOf ms s = .ok t
  | [], _, s, t => by
    constructor
    · rintro ⟨rfl, _⟩
      rfl
    · intro h
      exact ⟨(Except.ok.inj h).symm, rfl⟩
  | m :: l, hq, s, t => by
    obtain ⟨h, rfl⟩ := hq m List.mem_cons_self
    have ih := after_iff l fun q hq' => hq q (List.mem_cons_of_mem _ hq')
    constructor
    · rintro ⟨u, c, c', h1, h2, e⟩
      have e1 : c = [] := h1.2
      have e2 : c' = [] := by
        rw [e1] at e
        exact e.symm
      rw [e2] at h2
      show (h s).bind (afterOf l) = .ok t
      rw [h1.1]
      exact (ih u t).1 h2
    · intro h0
      obtain ⟨u, hu, h2⟩ := ok_bind (show (h s).bind (afterOf l) = .ok t from h0)
      exact ⟨u, [], [], ⟨hu, rfl⟩, (ih u t).2 h2, rfl⟩

/-- Along a row of moves that keep the door and the book the accessor's tables are the same. -/
theorem tabAt_quiet (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (ms : List (Move S))
    (hkd : ∀ m ∈ ms, MoveDoor atS m) (hbk : ∀ m ∈ ms, MoveBook m) (s t : S) (c : List Claim)
    (hs : (atS.get? s).isSome = true) (hy : MovesYes atS ms s t c) :
    tabAt own rd t = tabAt own rd s ∧ KeepsDoor atS s t := by
  have hk := moves_door atS (fun s a h => by
    obtain ⟨a', e0, _, e2, e3⟩ := atS_reads s a h
    exact ⟨a', e0, e2, e3⟩) ms hkd s t c hy
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨a', ha', _, d1⟩ := hk a ha
  refine ⟨tabAt_same own rd s t a a' ha ha' ?_ (moves_book ms hbk s t c hy), hk⟩
  rw [d1]
  exact SameBits.refl _

variable {α W Cl : Type} {F : Frame}

/-- The relations at the four boundaries, in the table's letters. -/
def relT3 (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (items : List (ℕ × String)) (after : S → Except String S) (N : ℕ)
    (ctx : S × F.E.Str → W → Prop) (j : ℕ) : ℕ → S × F.E.Str → W → Prop := fun i a w =>
  if i = j then
    (∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w)) ∧
      GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)
  else if i = j + 1 then
    (totalBQ after own a.1 (rdW w) ∧ GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) ∧
      ctx a w
  else if i = j + 2 then
    (totalQ own a.1 (rdW w) ∧ GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) ∧ ctx a w
  else GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1) ∧ ctx a w

/-- **The row of three pieces at the table's letters.** -/
theorem join_table (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (l : List (Step S (α × Option Pub9) GQ)) (ms₂ : List (Termed S (α × Option Pub9) GQ))
    (d N j : ℕ) (b₁ b₂ b₃ : Block S Cl) (pb pq pe : Piece (ckP .two) F S Cl W)
    (on0 on1 on2 on3 : S × F.E.Str → Prop) (ctx : S × F.E.Str → W → Prop)
    (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (H : JoinAsks φ Ok Fu p pw (movesOf l) ms₂ d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3
      (fun a w => tabAt own (rdW w) a.1) ctx)
    (hs2 : ∀ c, on2 c → (atS.get? c.1).isSome = true)
    (hbook₂ : ∀ m ∈ ms₂.map (·.move), MoveBook m)
    (htin : ∀ a t, on1 a → MovesYes atS (ms₂.map (·.move)) a.1 t [] →
      K9.totalIn own t = true)
    (hitems : ∀ a w, on0 a → ∀ e ∈ items, ∃ (b : K9.Part) (R : K9.Read)
      (r : TermedRun S (α × Option Pub9) GQ) (vals : α × Option Pub9 → Bound GQ → List GQ),
      atS.get? a.1 = some b ∧ r ∈ runsOf l ∧
      (∀ n y, r.tm n (fixed9 φ a.1) y = numbered n (vals (fixed9 φ a.1) y)) ∧
      Rd.forms e.1 e.2 a.1 = some R ∧ K9.formsIn Rd own e.1 e.2 a.1 = true ∧
      vals (fixed9 φ a.1) (dataQ own b (rdW w)) =
        R.forms.map fun f => f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w)))) :
    EachGoodIn (onJ on0 on1 on2 on3 j)
      (relT3 Rd own rdW items (afterOf (ms₂.map (·.move))) N ctx j) j [pb, pq, pe] := by
  obtain ⟨g1, g2, g3, _⟩ := inMoves α W Cl F φ Ok Fu p pw (movesOf l) ms₂ d N j b₁ b₂ b₃ pb pq pe
    on0 on1 on2 on3 (fun a w => tabAt own (rdW w) a.1) ctx H
  have part1 := H.hs1
  have part2 := hs2
  have hkd₂ : ∀ m ∈ ms₂.map (·.move), MoveDoor atS m := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact H.hkd q (List.mem_append_right _ hq)
  have hq₂ : ∀ m ∈ ms₂.map (·.move), ∃ h, m = .quiet h := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact H.quiet q hq
  have o0 : onJ on0 on1 on2 on3 j j = on0 := by
    funext a
    simp [onJ]
  have o1 : onJ on0 on1 on2 on3 j (j + 1) = on1 := by
    funext a
    simp [onJ]
  have o2 : onJ on0 on1 on2 on3 j (j + 1 + 1) = on2 := by
    funext a
    unfold onJ
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  have r0 : ∀ a w, relJ (O9 φ Ok Fu) (movesOf l) ms₂ N (fun a w => tabAt own (rdW w) a.1) ctx j j
      a w = ((∃ y, boundAt atS (fun a w => tabAt own (rdW w) a.1) ctx a w y ∧
        ∀ x ∈ termsOf ((O9 (K := GQ) φ Ok Fu).fixed a.1) y (movesOf l ++ ms₂) 0, x.2 = 0) ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) := fun a w => by
    simp [relJ]
  have r1 : ∀ a w, relJ (O9 φ Ok Fu) (movesOf l) ms₂ N (fun a w => tabAt own (rdW w) a.1) ctx j
      (j + 1) a w = (((∃ t, MovesYes atS (ms₂.map (·.move)) a.1 t [] ∧
          oneK atS Reading.gl t t (dataAt atS a.1 (tabAt own (rdW w) a.1)) = 0) ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) ∧ ctx a w) := fun a w => by
    simp [relJ]
  have r2 : ∀ a w, relJ (O9 φ Ok Fu) (movesOf l) ms₂ N (fun a w => tabAt own (rdW w) a.1) ctx j
      (j + 1 + 1) a w = ((oneK atS Reading.gl a.1 a.1
          (dataAt atS a.1 (tabAt own (rdW w) a.1)) = 0 ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) ∧ ctx a w) := fun a w => by
    unfold relJ
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  have r3 : ∀ a w, relJ (O9 φ Ok Fu) (movesOf l) ms₂ N (fun a w => tabAt own (rdW w) a.1) ctx j
      (j + 1 + 1 + 1) a w =
      (GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1) ∧ ctx a w) := fun a w => by
    unfold relJ
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have t0 : ∀ a w, relT3 Rd own rdW items (afterOf (ms₂.map (·.move))) N ctx j j a w =
      ((∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w)) ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) := fun a w => by
    simp [relT3]
  have t1 : ∀ a w, relT3 Rd own rdW items (afterOf (ms₂.map (·.move))) N ctx j (j + 1) a w =
      ((totalBQ (afterOf (ms₂.map (·.move))) own a.1 (rdW w) ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) ∧ ctx a w) := fun a w => by
    simp [relT3]
  have t2 : ∀ a w, relT3 Rd own rdW items (afterOf (ms₂.map (·.move))) N ctx j (j + 1 + 1) a w =
      ((totalQ own a.1 (rdW w) ∧ GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1)) ∧
        ctx a w) := fun a w => by
    unfold relT3
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  have t3 : ∀ a w, relT3 Rd own rdW items (afterOf (ms₂.map (·.move))) N ctx j (j + 1 + 1 + 1) a
      w = (GroupHoldsAt atS Reading.gl N a.1 (tabAt own (rdW w) a.1) ∧ ctx a w) := fun a w => by
    unfold relT3
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- along the quiet moves the data at the accessor's tables are the same
  have hdata : ∀ (a : S × F.E.Str) (w : W) (t : S), on1 a →
      MovesYes atS (ms₂.map (·.move)) a.1 t [] →
      dataAt atS t (tabAt own (rdW w) t) = dataAt atS a.1 (tabAt own (rdW w) a.1) := by
    intro a w t ha hy
    obtain ⟨e1, e2⟩ := tabAt_quiet own (rdW w) _ hkd₂ hbook₂ a.1 t [] (part1 a ha) hy
    rw [e1]
    exact dataAt_door atS a.1 t e2 (part1 a ha) _
  refine ⟨goodIn_mono pb _ _ _ _ _ _ g1 (fun a w ha h => ?_) (fun b w hb h => ?_),
    goodIn_mono pq _ _ _ _ _ _ g2 (fun a w ha h => ?_) (fun b w _ h => ?_),
    goodIn_mono pe _ _ _ _ _ _ g3 (fun a w ha h => ?_) (fun b w _ h => ?_), trivial⟩
  · rw [r0] at h
    rw [t0]
    rw [o0] at ha
    obtain ⟨⟨y, ⟨_, hy⟩, hz⟩, hG⟩ := h
    refine ⟨fun e he => ?_, hG⟩
    obtain ⟨b, R, r, vals, hb, hr, hp, hR, hin, hv⟩ := hitems a w ha e he
    have ey : y = dataQ own b (rdW w) := hy.trans (data_at own (rdW w) a.1 b hb)
    rw [ey, termsOf_append] at hz
    exact forms_of_front Rd own e.1 e.2 a.1 (rdW w) b R (fixed9 φ a.1) l r vals hr hp hb hR hin hv
      fun x hx => hz x (List.mem_append_left _ hx)
  · rw [t1] at h
    rw [r1]
    rw [o1] at hb
    obtain ⟨⟨⟨t, ht, _, hq⟩, hG⟩, hc⟩ := h
    have hy := (after_iff _ hq₂ b.1 t).2 ht
    refine ⟨⟨⟨t, hy, ?_⟩, hG⟩, hc⟩
    rw [← hdata b w t hb hy]
    exact ((total_iff own (rdW w) t).1 hq).2
  · rw [r1] at h
    rw [t1]
    rw [o1] at ha
    obtain ⟨⟨⟨t, hy, h0⟩, hG⟩, hc⟩ := h
    refine ⟨⟨⟨t, (after_iff _ hq₂ a.1 t).1 hy, htin a t ha hy, ?_⟩, hG⟩, hc⟩
    rw [← hdata a w t ha hy] at h0
    obtain ⟨_, e2⟩ := tabAt_quiet own (rdW w) _ hkd₂ hbook₂ a.1 t [] (part1 a ha) hy
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (part1 a ha)
    obtain ⟨x', hx', _⟩ := e2 x hx
    exact (total_iff own (rdW w) t).2 ⟨by simp [hx'], h0⟩
  · rw [t2] at h
    rw [r2]
    exact ⟨⟨((total_iff own (rdW w) b.1).1 h.1.1).2, h.1.2⟩, h.2⟩
  · rw [r2] at h
    rw [t2]
    rw [o2] at ha
    exact ⟨⟨(total_iff own (rdW w) a.1).2 ⟨part2 a ha, h.1.1⟩, h.1.2⟩, h.2⟩
  · rw [t3] at h
    rw [r3]
    exact h

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.after_iff
#print axioms VerifiableInference.Desc.K9L.join_table
