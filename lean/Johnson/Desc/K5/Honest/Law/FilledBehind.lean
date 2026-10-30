-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/FilledBehind.lean: CONDITIONAL: the ledger's marks "this slot is filled"
(the field gotF of Fork, OnBytes/Model/Hide.lean) BEHIND THE VERIFIER's HEARING OF AN ATTENTION
SEGMENT's OWN ROUNDS (kind K5; hear, Johnson/Desc/First/Att/K5AttentionKind.lean), SLOT BY SLOT, as a function
of the marks in front and of two numbers. Over the library alone: no prover's text is read. A
definition, and statements with their proofs.

Why. Whoever writes the kind's step as one update on a shape of the state without field elements has
to say what the list of marks is behind the step. The library has: below the next free number in
front nothing turns (`hear_below`, Johnson/Desc/First/Att/K05HearBelow.lean); what is free above the
stretch stays free (`room_behind`, Att/K05Room.lean). That EVERY slot of the stretch is filled, and
that above it NO mark turns, is shown here.

Main names:
  `Stretch`, `Stretch.refl`, `Stretch.trans`   the relation between a ledger in front and one behind
  `take_stretch`, `sum_stretch`, `takes_stretch`, `units_stretch`   step by step
  `hear_stretch`     the whole hearing
  `filled_behind`    **the next free number, the number of marks and each mark behind**
  `stretch_bites`    a control: the relation can fail

EVERY STATEMENT ON THE HEARING IS CONDITIONAL on: the hearing (or its step) returns; the three
arrays on slots of the ledger in front have their length (`Sized`,
OnBytes/Tie/Pv/Psc/Run/PscHide.lean). `filled_behind` also on: the stretch's slots are there and
free in front (`Free`, Johnson/Desc/Part/MaskedSumLaw.lean).
Limits. One direction, from a return. Marks alone: nothing is said of what lies under a slot.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05HearBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Free)
open VerifiableInference.Desc.First.Att.P

/-! ## The relation -/

/-- **Of the marks "this slot is filled", G against F**: G's next free number is not
below F's; every slot from F's next free number up to G's is filled in G; from G's next free number
on the marks are F's. It is a definition. -/
structure Stretch (F G : Fork) : Prop where
  le : F.next ≤ G.next
  full : ∀ j, F.next ≤ j → j < G.next → G.gotF.getD j false = true
  above : ∀ j, G.next ≤ j → ∀ d, G.gotF.getD j d = F.gotF.getD j d

theorem Stretch.refl (F : Fork) : Stretch F F := by
  exact ⟨Nat.le_refl _, fun j h1 h2 => absurd h2 (Nat.not_lt.2 h1), fun _ _ _ => rfl⟩

/-- Two stretches in a row, where the second writes nothing below its own beginning. -/
theorem Stretch.trans {F G H : Fork} (a : Stretch F G) (b : Stretch G H) (bl : Below G H) :
    Stretch F H := by
  refine ⟨Nat.le_trans a.le b.le, fun j h1 h2 => ?_, fun j h1 d => ?_⟩
  · rcases Nat.lt_or_ge j G.next with h3 | h3
    · rw [(bl.2.2 j h3).2.2 false]
      exact a.full j h1 h3
    · exact b.full j h3 h2
  · rw [b.above j h1 d]
    exact a.above j (Nat.le_trans b.le h1) d

/-! ## Step by step -/

/-- n scalars are taken. -/
theorem take_stretch {n j lead lead' : Nat} {F G : Fork} {rs rs' : List Fmt.RoundView}
    (h : take n (F, rs, lead) = some (j, G, rs', lead')) (hz : Sized F) : Stretch F G := by
  obtain ⟨_, _, _, r, rest, v, _, _, hl, hG⟩ := take_spec h
  have fill := hideRun_ok _ _ _ _ _ hG ⟨hz.vp, hz.mf, hz.got⟩
  rw [List.toList_toArray] at fill
  have hn : G.next = F.next + n := fill.next
  refine ⟨by rw [hn]; exact Nat.le_add_right _ _, fun i h1 h2 => ?_, fun i h1 d => ?_⟩
  · rw [hn] at h2
    have e := (fill.here (i - F.next) (by rw [hl]; omega)).2.2.1
    rwa [show F.next + (i - F.next) = i by omega] at e
  · rw [hn] at h1
    exact (fill.other i (Or.inr (by rw [hl]; exact h1))).2.2 d

/-- A sumcheck is heard, and its hiding polynomial's coefficients are put under their slots. -/
theorem sum_stretch {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {lead lead' : Nat}
    {F G : Fork} {rs rs' : List Fmt.RoundView}
    (h : sum C (.sum vs e) (F, rs, lead) = some (hh, G, rs', lead')) (hz : Sized F) :
    Stretch F G := by
  obtain ⟨_, _, G1, f, a1, a2⟩ := sum_spec h
  obtain ⟨hsh, T, Rd, b1, b2, b3, b4⟩ := MaskedSum.hear_spec a1
  obtain ⟨r0, used, rv, front, c1, c2, c3, c4, c5⟩ := MaskedSum.readAll_spec b2
  have hall : (⟨lead, vs, some e⟩ : MaskedSum.Call).all = vs ++ [.point zeroE (e.dY + 1)] := rfl
  rw [hall] at b3 b4
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
      · simp only [MaskedSum.shapeOk, Bool.and_eq_true, List.all_eq_true,
          decide_eq_true_eq] at hsh
        have := (hsh.1 _ h1).1
        omega
      · rw [List.mem_singleton.1 h1]
        show 1 ≤ e.dY + 1
        omega
  have hfirst : hh.first = F.next := by rw [b3]
  have hn : G.next = F.next + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) +
      Rd.values.length := by
    rw [F2.next, F1.next]
  refine ⟨by rw [hn]; omega, fun i h1 h2 => ?_, fun i h1 d => ?_⟩
  · rw [hn] at h2
    rcases Nat.lt_or_ge i (F.next + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)])) with
      h3 | h3
    · have e1 := (F2.here (i - F.next) (by rw [List.length_replicate, hlen]; omega)).2.2.1
      rwa [hfirst, show F.next + (i - F.next) = i by omega] at e1
    · rw [(F2.other i (Or.inr (by rw [List.length_replicate, hlen, hfirst]; exact h3))).2.2 false]
      have e1 := (F1.here (i - (F.next + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)])))
        (by omega)).2.2.1
      rwa [show F.next + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) +
        (i - (F.next + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]))) = i by omega] at e1
  · rw [hn] at h1
    rw [(F2.other i (Or.inr (by rw [List.length_replicate, hlen, hfirst]; omega))).2.2 d]
    exact (F1.other i (Or.inr h1)).2.2 d

/-- The plane messages' scalars are taken (`TakesRan`, Johnson/Desc/First/Att/K5Shape.lean). -/
theorem takes_stretch : ∀ (n : Nat) (js : List Nat) (s s' : St), TakesRan 3 n js s s' →
    Sized s.1 → Stretch s.1 s'.1
  | 0, [], _, _, h, _ => by
    have e : _ = _ := h
    rw [e]
    exact Stretch.refl _
  | n + 1, _ :: js, ⟨F, rs, lead⟩, s', ⟨⟨F1, rs1, l1⟩, h1, h2⟩, hz => by
    obtain ⟨z1, _⟩ := take_below h1 hz
    exact (take_stretch h1 hz).trans (takes_stretch n js _ s' h2 z1)
      (takes_below n js _ s' h2 z1).2
  | 0, _ :: _, _, _, h, _ => h.elim
  | _ + 1, [], _, _, h, _ => h.elim

/-- The units of the scores are heard (`UnitsRan`, Att/K5Shape.lean). -/
theorem units_stretch : ∀ (us : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (s s' : St),
    UnitsRan us os s s' → Sized s.1 → Stretch s.1 s'.1
  | [], [], _, _, h, _ => by
    have e : _ = _ := h
    rw [e]
    exact Stretch.refl _
  | u :: us, _ :: os, ⟨F, rs, lead⟩, s', ⟨s2, ⟨⟨F1, rs1, l1⟩, h1, h2⟩, h3⟩, hz => by
    obtain ⟨F2, rs2, l2⟩ := s2
    obtain ⟨z1, _⟩ := take_below h1 hz
    obtain ⟨z2, b2⟩ := sum_below h2 z1
    exact ((take_stretch h1 hz).trans (sum_stretch h2 z1) b2).trans
      (units_stretch us os _ s' h3 z2) (units_below us os _ s' h3 z2).2
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

/-! ## The whole hearing -/

/-- **Behind the hearing of an attention segment's own rounds every slot from the next free number
in front up to the next free number behind is filled, and from there on the marks are as in front.**
CONDITIONAL on: the hearing returns; the three arrays on slots of the ledger in front have their
length. -/
theorem hear_stretch {x : Params.AttentionRounds} {F G : Fork} {rs rs' : List Fmt.RoundView}
    {lead lead' : Nat} {h : Heard} (hh : hear x (F, rs, lead) = some (h, G, rs', lead'))
    (hz : Sized F) : Stretch F G := by
  obtain ⟨sa, sb, ⟨F1, r1, l1⟩, ⟨F2, r2, l2⟩, ⟨F3, r3, l3⟩, ⟨F4, r4, l4⟩, ⟨F5, r5, l5⟩,
    ⟨F6, r6, l6⟩, ⟨F7, r7, l7⟩, ⟨F8, r8, l8⟩, ⟨F9, r9, l9⟩, ⟨F10, r10, l10⟩, ⟨F11, r11, l11⟩,
    ⟨F12, r12, l12⟩, ⟨F13, r13, l13⟩, ⟨F14, r14, l14⟩, ⟨F15, r15, l15⟩, pt, ha, hb, h1, h2, h3,
    h4, h5, h6, h7, h8, h9, _, h10, h11, h12, h13, h14, h15, h16⟩ := (hear_ran hh).ran
  obtain ⟨Fb, rb, lb⟩ := sb
  have e5 := (batch_spec h5).1
  have e9 := (close_spec h9).1
  have e11 := (batch_spec h11).1
  have e13 := (batch_spec h13).1
  have e15 := (batch_spec h15).1
  subst e5 e9 e11 e13 e15
  obtain ⟨za, _⟩ := takes_below _ _ _ sa ha hz
  obtain ⟨zb, bb⟩ := units_below _ _ _ _ hb za
  obtain ⟨z1, b1⟩ := take_below h1 zb
  obtain ⟨z2, b2⟩ := take_below h2 z1
  obtain ⟨z3, b3⟩ := take_below h3 z2
  obtain ⟨z4, b4⟩ := sum_below h4 z3
  obtain ⟨z6, b6⟩ := take_below h6 z4
  obtain ⟨z7, b7⟩ := sum_below h7 z6
  obtain ⟨z8, b8⟩ := sum_below h8 z7
  obtain ⟨z10, b10⟩ := take_below h10 z8
  obtain ⟨z12, b12⟩ := sum_below h12 z10
  obtain ⟨z14, b14⟩ := sum_below h14 z12
  obtain ⟨_, b16⟩ := sum_below h16 z14
  exact ((((((((((((takes_stretch _ _ _ sa ha hz).trans (units_stretch _ _ _ _ hb za) bb).trans
    (take_stretch h1 zb) b1).trans (take_stretch h2 z1) b2).trans (take_stretch h3 z2) b3).trans
    (sum_stretch h4 z3) b4).trans (take_stretch h6 z4) b6).trans (sum_stretch h7 z6) b7).trans
    (sum_stretch h8 z7) b8).trans (take_stretch h10 z8) b10).trans (sum_stretch h12 z10) b12).trans
    (sum_stretch h14 z12) b14).trans (sum_stretch h16 z14) b16

/-- **THE MARKS BEHIND THE HEARING, SLOT BY SLOT, AS A FUNCTION OF THE MARKS IN FRONT AND OF TWO
NUMBERS**: F.next: the next free number in front; N: the slots that the plan's stages take. The next
free number moves by N; there are as many marks as in front; the mark at slot j is true on the
stretch and as in front elsewhere. CONDITIONAL on: the hearing returns; the arrays' lengths; the
stretch's slots are there and free in front. -/
theorem filled_behind {x : Params.AttentionRounds} {F G : Fork} {rs rs' : List Fmt.RoundView}
    {lead lead' : Nat} {h : Heard} (hh : hear x (F, rs, lead) = some (h, G, rs', lead'))
    (hz : Sized F) (hfree : Free F F.next (slotsOf (script x))) :
    G.next = F.next + slotsOf (script x) ∧ G.gotF.size = F.gotF.size ∧
      ∀ j d, G.gotF.getD j d =
        if F.next ≤ j ∧ j < F.next + slotsOf (script x) then true else F.gotF.getD j d := by
  have R : Room F F.ns F.next (slotsOf (script x) + 0) := ⟨rfl, rfl, hz, hfree⟩
  have RG := room_behind hh R
  obtain ⟨zG, bl⟩ := hear_below hh hz
  have St := hear_stretch hh hz
  have hn : G.next = F.next + slotsOf (script x) := RG.next
  refine ⟨hn, by rw [zG.got, hz.got, RG.ns], fun j d => ?_⟩
  by_cases hj : F.next ≤ j ∧ j < F.next + slotsOf (script x)
  · rw [if_pos hj]
    have e := St.full j hj.1 (by rw [hn]; exact hj.2)
    have hs : j < G.gotF.size := by
      rw [zG.got, RG.ns]
      exact Nat.lt_of_lt_of_le hj.2 hfree.2.1
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs] at e ⊢
    exact e
  · rw [if_neg hj]
    rcases Nat.lt_or_ge j F.next with h1 | h1
    · exact (bl.2.2 j h1).2.2 d
    · exact St.above j (by rw [hn]; omega) d

/-- A control: a ledger with a free slot on the stretch is no `Stretch`. -/
theorem stretch_bites {F G : Fork} {j : Nat} (h1 : F.next ≤ j) (h2 : j < G.next)
    (hd : G.gotF.getD j false = false) : ¬ Stretch F G := by
  intro S
  rw [S.full j h1 h2] at hd
  cases hd

end H2K5.Honest

#print axioms H2K5.Honest.Stretch.refl
#print axioms H2K5.Honest.Stretch.trans
#print axioms H2K5.Honest.take_stretch
#print axioms H2K5.Honest.sum_stretch
#print axioms H2K5.Honest.takes_stretch
#print axioms H2K5.Honest.units_stretch
#print axioms H2K5.Honest.hear_stretch
#print axioms H2K5.Honest.filled_behind
#print axioms H2K5.Honest.stretch_bites
