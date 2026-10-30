-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Room.lean: the ledger's room: what the block in front of the kind K5 has
to hand on, as one record, and that the kind's own hearing hands the like on behind itself.

Definitions, statements and proofs.
Main names:
  `Room F ns nx k`: the ledger has ns slots; its next free number is nx; its three arrays on slots
    have their length (`Sized`); the k slots from nx on are there and free (`Free`,
    Johnson/Desc/Part/MaskedSumLaw.lean).
  `Room.less`, `Room.cast`.
  `take_room`, `sum_room`, `takes_room`, `units_room`: from the verb's return itself: room for the
    verb's slots and k more in front gives room k behind, at the same ns, the next free number moved
    on by the verb's slots.
  `slotsOf_append`.
  `room_behind`: where `hear` x (F, rs, lead) returns (h, G, rs', lead') and F has room for slotsOf
    (script x) + k, G has room k at nx + slotsOf (script x).
  `room_pays`: `Room` gives `Sized` F, that the stretch's slots are free, F.ns = ns, and numsPlan x
    F.next = numsPlan x nx.
Used: plain records, pure functions and lemmas on them alone; no routine in a context:
`take_spec`, `sum_spec`, `close_spec`, `batch_spec`, `hear_ran`, `row_write`, `hideRun_ok`,
`filled_free`, `free_sub`, `free_next`, `hiding_length`, `script_eq`, `tailStages`, `numsPlan`.
Limits: that the block in front of the kind hands `Room` on is not shown in this file or in what it
imports. Nothing on what lies under a slot. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5Returns
import Johnson.Desc.First.Att.K05Numbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Free)

/-- **The ledger's room.** -/
structure Room (F : Fork) (ns nx k : Nat) : Prop where
  ns : F.ns = ns
  next : F.next = nx
  sized : Sized F
  free : Free F nx k

theorem Room.less {F : Fork} {ns nx k k' : Nat} (R : Room F ns nx k) (h : k' ≤ k) : Room F ns nx k' :=
  ⟨R.ns, R.next, R.sized, free_sub R.free (Nat.le_refl _) (by omega)⟩

theorem Room.cast {F : Fork} {ns nx nx' k : Nat} (R : Room F ns nx k) (h : nx = nx') : Room F ns nx' k := h ▸ R

/-- n scalars are taken. -/
theorem take_room {n k j lead lead' ns nx : Nat} {F G : Fork} {rs rs' : List Fmt.RoundView}
    (h : take n (F, rs, lead) = some (j, G, rs', lead')) (R : Room F ns nx (n + k)) :
    Room G ns (nx + n) k := by
  obtain ⟨rfl, rfl, hz, hf⟩ := R
  obtain ⟨_, _, _, r, rest, v, _, _, hl, hG⟩ := take_spec h
  have fill := hideRun_ok _ _ _ _ _ hG ⟨hz.vp, hz.mf, hz.got⟩
  rw [List.toList_toArray] at fill
  exact ⟨fill.ns, fill.next, fill.sized,
    filled_free fill (free_next (free_sub hf (by omega) (by omega))) (Or.inr (by rw [hl]))⟩

/-- A sumcheck is heard. -/
theorem sum_room {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {k lead lead' ns nx : Nat}
    {F G : Fork} {rs rs' : List Fmt.RoundView} (h : sum C (.sum vs e) (F, rs, lead) = some (hh, G, rs', lead'))
    (R : Room F ns nx ((Stage.sum vs e).slots + k)) : Room G ns (nx + (Stage.sum vs e).slots) k := by
  obtain ⟨rfl, rfl, hz, hf⟩ := R
  have hf' : Free F F.next (MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + e.n + k) := hf
  obtain ⟨_, _, G1, f, a1, a2⟩ := sum_spec h
  obtain ⟨hsh, T, Rd, b1, b2, b3, b4⟩ := MaskedSum.hear_spec a1
  obtain ⟨r0, used, rv, front, c1, c2, c3, c4, c5⟩ := MaskedSum.readAll_spec b2
  have hall : (⟨lead, vs, some e⟩ : MaskedSum.Call).all = vs ++ [.point zeroE (e.dY + 1)] := rfl
  rw [hall] at b3 b4
  rw [c5.2.1] at b4
  have F1 := hideRun_ok _ _ _ _ _ b4 ⟨hz.vp, hz.mf, hz.got⟩
  rw [List.toList_toArray] at F1
  have F2 := hideRun_ok _ _ _ _ _ (row_write a2) F1.sized
  rw [Array.toList_replicate] at F2
  have hlen : (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length =
      MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) := by
    have hz1 : (hh.vars.zip hh.r).map (·.1) = vs ++ [.point zeroE (e.dY + 1)] := by
      rw [b3]
      exact List.map_fst_zip (by rw [List.length_map, c4.length.2])
    rw [← hz1]
    refine hiding_length _ (fun h0 => ?_) fun x hx => ?_
    · rw [h0] at hz1
      simp at hz1
    · have hm : x.1 ∈ vs ++ [Var.point zeroE (e.dY + 1)] := by
        rw [← hz1]
        exact List.mem_map_of_mem hx
      rcases List.mem_append.1 hm with h1 | h1
      · simp only [MaskedSum.shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsh
        have := (hsh.1 _ h1).1
        omega
      · rw [List.mem_singleton.1 h1]
        show 1 ≤ e.dY + 1
        omega
  have hfirst : hh.first = F.next := by rw [b3]
  refine ⟨by rw [F2.ns, F1.ns], ?_, F2.sized, ?_⟩
  · rw [F2.next, F1.next]
    show F.next + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + e.n = _
    show _ = F.next + (MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + e.n)
    omega
  · show Free G (F.next + (MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + e.n)) k
    refine filled_free F2 (filled_free F1 (free_next (free_sub hf' (by omega) (by omega)))
      (Or.inr (by rw [c5.2.1]; omega))) (Or.inr ?_)
    rw [List.length_replicate, hlen, hfirst]
    omega

theorem slotsOf_append : ∀ a b : List Stage, slotsOf (a ++ b) = slotsOf a + slotsOf b
  | [], _ => (Nat.zero_add _).symm
  | s :: a, b => by
    show s.slots + slotsOf (a ++ b) = s.slots + slotsOf a + slotsOf b
    rw [slotsOf_append a b, Nat.add_assoc]

/-- The plane messages' scalars are taken. -/
theorem takes_room {k ns : Nat} : ∀ (n : Nat) (js : List Nat) (s s' : St) (nx : Nat), TakesRan 3 n js s s' →
    Room s.1 ns nx (slotsOf (List.replicate n (.scalars 3)) + k) →
    Room s'.1 ns (nx + slotsOf (List.replicate n (.scalars 3))) k
  | 0, [], _, _, _, h, R => by
    have e : _ = _ := h
    rw [e]
    simpa [slotsOf] using R
  | n + 1, _ :: js, ⟨F, rs, lead⟩, s', nx, ⟨⟨F1, rs1, l1⟩, h1, h2⟩, R => by
    have e : slotsOf (List.replicate (n + 1) (Stage.scalars 3)) =
        3 + slotsOf (List.replicate n (Stage.scalars 3)) := rfl
    rw [e] at R ⊢
    have R1 := take_room (k := slotsOf (List.replicate n (Stage.scalars 3)) + k) h1
      (by rw [← Nat.add_assoc]; exact R)
    have R2 := takes_room n js _ s' _ h2 R1
    rw [← Nat.add_assoc]
    exact R2
  | 0, _ :: _, _, _, _, h, _ => h.elim
  | _ + 1, [], _, _, _, h, _ => h.elim

/-- The units of the scores are heard. -/
theorem units_room {k ns : Nat} : ∀ (us : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (s s' : St)
    (nx : Nat), UnitsRan us os s s' →
    Room s.1 ns nx (slotsOf (us.flatMap fun u => [.scalars 7, products u.1 u.2]) + k) →
    Room s'.1 ns (nx + slotsOf (us.flatMap fun u => [.scalars 7, products u.1 u.2])) k
  | [], [], _, _, _, h, R => by
    have e : _ = _ := h
    rw [e]
    simpa [slotsOf] using R
  | u :: us, _ :: os, ⟨F, rs, lead⟩, s', nx, ⟨s2, ⟨⟨F1, rs1, l1⟩, h1, h2⟩, h3⟩, R => by
    obtain ⟨F2, rs2, l2⟩ := s2
    have e : slotsOf ((u :: us).flatMap fun u => [Stage.scalars 7, products u.1 u.2]) =
        7 + ((products u.1 u.2).slots + slotsOf (us.flatMap fun u => [Stage.scalars 7, products u.1 u.2])) := rfl
    rw [e] at R ⊢
    have R1 := take_room
      (k := (products u.1 u.2).slots + slotsOf (us.flatMap fun u => [Stage.scalars 7, products u.1 u.2]) + k) h1
      (by rw [← Nat.add_assoc]; exact R)
    have R2 := sum_room (k := slotsOf (us.flatMap fun u => [Stage.scalars 7, products u.1 u.2]) + k) h2
      (by rw [← Nat.add_assoc]; exact R1)
    have R3 := units_room us os _ s' _ h3 R2
    rw [← Nat.add_assoc, ← Nat.add_assoc]
    exact R3
  | [], _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, h, _ => h.elim

/-- **The kind's hearing hands the ledger's room on.** -/
theorem room_behind {x : Params.AttentionRounds} {F G : Fork} {rs rs' : List Fmt.RoundView} {lead lead' k ns nx : Nat}
    {h : Heard} (hh : hear x (F, rs, lead) = some (h, G, rs', lead'))
    (R : Room F ns nx (slotsOf (script x) + k)) : Room G ns (nx + slotsOf (script x)) k := by
  obtain ⟨sa, sb, ⟨F1, r1, l1⟩, ⟨F2, r2, l2⟩, ⟨F3, r3, l3⟩, ⟨F4, r4, l4⟩, ⟨F5, r5, l5⟩, ⟨F6, r6, l6⟩, ⟨F7, r7, l7⟩,
    ⟨F8, r8, l8⟩, ⟨F9, r9, l9⟩, ⟨F10, r10, l10⟩, ⟨F11, r11, l11⟩, ⟨F12, r12, l12⟩, ⟨F13, r13, l13⟩,
    ⟨F14, r14, l14⟩, ⟨F15, r15, l15⟩, pt, ha, hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h10, h11, h12, h13, h14,
    h15, h16⟩ := (hear_ran hh).ran
  obtain ⟨Fb, rb, lb⟩ := sb
  have e5 := (batch_spec h5).1
  have e9 := (close_spec h9).1
  have e11 := (batch_spec h11).1
  have e13 := (batch_spec h13).1
  have e15 := (batch_spec h15).1
  subst e5 e9 e11 e13 e15
  rw [script_eq, slotsOf_append, slotsOf_append] at R ⊢
  have et : slotsOf (tailStages x) = 5 + (x.lt + (2 + ((products x.e x.pairs).slots + (2 +
      ((products x.valueM x.pairs).slots + ((products x.valueD x.pairs).slots + (x.pairs +
      ((products x.attained x.pairs).slots + ((keyStage x).slots + (products x.bits x.pairs).slots))))))))) := by
    simp only [tailStages, slotsOf, Stage.slots, Nat.zero_add, Nat.add_zero]
  rw [et] at R ⊢
  have Ra := takes_room _ _ _ sa _ ha (by rw [← Nat.add_assoc]; exact R)
  have Rb := units_room _ _ _ _ _ hb (by rw [← Nat.add_assoc]; exact Ra)
  have R1 := take_room h1 (by rw [← Nat.add_assoc]; exact Rb)
  have R2 := take_room h2 (by rw [← Nat.add_assoc]; exact R1)
  have R3 := take_room h3 (by rw [← Nat.add_assoc]; exact R2)
  have R4 : Room _ ns (_ + (products x.e x.pairs).slots) _ := sum_room h4 (by rw [← Nat.add_assoc]; exact R3)
  have R6 := take_room h6 (by rw [← Nat.add_assoc]; exact R4)
  have R7 : Room _ ns (_ + (products x.valueM x.pairs).slots) _ :=
    sum_room h7 (by rw [← Nat.add_assoc]; exact R6)
  have R8 : Room _ ns (_ + (products x.valueD x.pairs).slots) _ :=
    sum_room h8 (by rw [← Nat.add_assoc]; exact R7)
  have R10 := take_room h10 (by rw [← Nat.add_assoc]; exact R8)
  have R12 : Room _ ns (_ + (products x.attained x.pairs).slots) _ :=
    sum_room h12 (by rw [← Nat.add_assoc]; exact R10)
  have R14 : Room _ ns (_ + (keyStage x).slots) _ := sum_room h14 (by rw [← Nat.add_assoc]; exact R12)
  have R16 : Room G ns (_ + (products x.bits x.pairs).slots) k := sum_room h16 R14
  exact R16.cast (by omega)

/-- **What the statements on the kind take of the ledger in front, from `Room`**: the arrays'
lengths; the stretch's slots are free; the two numbers on which the closed parameters hang. -/
theorem room_pays {F : Fork} {ns nx k : Nat} (x : Params.AttentionRounds) (R : Room F ns nx (slotsOf (script x) + k)) :
    Sized F ∧ Free F F.next (slotsOf (script x)) ∧ F.ns = ns ∧ numsPlan x F.next = numsPlan x nx :=
  ⟨R.sized, by rw [R.next]; exact (R.less (Nat.le_add_right _ _)).free, R.ns, by rw [R.next]⟩

end VerifiableInference.Desc.First.Att.P
