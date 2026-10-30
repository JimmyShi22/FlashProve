-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/NamesMarks.lean: the honest side of the kind "lookup" (K3).
Conditional: from the hearing's return, on any rounds, at any face: which forms name slots that the
verifier's own list `K3.fromKeys` (Johnson/Desc/First/Look/K3Key.lean) marks. Every row, the form
that the leaves' sumcheck was given, and the leads of the claims on the planes name unmarked slots
alone; every part's key form names marked slots alone. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md: see there hearing, form, slot, row, sumcheck, key tree, tie, leaves
and planes. In this file: a mark is an entry of a list of Boolean values, one for each slot; it is
neither the mark of a state nor the frame's. lo is the ledger's count in front of the lookup, and M
the list of marks so far.

What is shown.
  `Names P a`: every slot that the form a names has the property P; with lemmas for the makers of
    forms. It has, but for the bound letters, the text of the library's `Kinds.Head.Law.SlotsAt`
    (Johnson/Desc/Kinds/Law/PlanesFormsInT.lean; the tie: `names_eq_slotsAt`,
    Honest/K3/Law/TiesSealedForms.lean [not in this library]), of the library's
    `OnBytes.Desc.First.K4.Slots.SlotsIn` (Johnson/Road/K4/Slots/SlotsIn.lean) and of `SlotsIn`
    (Honest/K3/Law/StageFacts.lean); `In lo hi` (Honest/K3/Parts/NamesOwn.lean) is `Names` at a
    range: `in_eq_names` (Honest/K3/Law/Ties.lean [not in this library]).
  `Is b lo M j`: slot j stands from lo on, inside the list M of marks, and bears the mark b.
  `whole_step`: the basic fact: a masked sumcheck heard whole takes its own slots, then those of its
    end values; its row names its own slots and those of the form that it was given.
  `level_step`, `fold_off`, `tree_marks`, `tieV_marks`, `partsV_marks`, `keysV_marks`: the hearing's
    pieces, each with the stretch of marks that it appends.
  `heard_marks`, `hearV_is`, `hearV_marks`: what was heard.
  `planesV_is`, `planesV_marks`: the leads of the three claims on the planes.
Further definitions: `AllNames` (of all rows), `CarriedOff`, `TieM` (what a run of levels, and the
tie, carry), `lev`, `marksK`, `marksT` (stretches of marks), `markAt` (a slot's mark in the
verifier's list).

Hypotheses that remain, in the last five.
  `h`, `hh`: the hearing returns (`messagesV`; `hearV`).
  `hok`: (in `heard_marks`) the face passes its own test.
  `hp`: (in the last two) `planesV` returns.
In the pieces: `hN`: the ledger's count is lo + M.length. `hC`, `hs`: the form, or what is carried,
names unmarked slots alone. `hw`, `e`: the routine returns. `hT`: the stretch of marks has its
length. `hv`: 1 ≤ v. In the lemmas on `Names`: `ha`, `hb`, `hs`, `hk`, `hy`, `hr`: `Names` (or
`AllNames`) of what goes in; `hg`: (in `names_foldl`) the step g keeps `Names`; `ho`, `hL`, `hR`: P
at the slots that come in; `h`: (in `names_mono`) P gives Q; (in `names_slot`) P at j; (in
`names_joinForm`) P at every plane's slot.

How the proof goes. No closed form of a slot's number is used. Along the walk a list M of marks is
carried, one for each slot taken so far, with the ledger's count at lo + M.length; "names slots with
the mark b" is stable under appending; each piece appends its own stretch; at the end M is the text
of `fromKeys`, stretch by stretch.

Users. Honest/K3/Shape/Closed.lean and Honest/K3/Parts/NamesMarksGuards.lean [not in this library]
import this file.

Limits. All statements are implications. It says which slots are named, not with which coefficient.
An instance: Honest/K3/Parts/NamesMarksGuards.lean [not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.NamesOwn
import Johnson.Desc.ProofFile.Honest.K3.RowOwnedLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Fork Aff orderDefault)
open OnBytes.Desc.First.K4 (hideRun_core)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (ownSlots)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV messagesV planesV Hr sumV openV tieV
  partsV keysV drawV noVar leafVars bitsCall fromKeys)
open VerifiableInference.Desc.First.ProdV (LevelOut level turn Carried stepDown level_spec levelVars
  levelEnds)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Forward (joinForm)

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run
local notation "no" => VerifiableInference.Desc.K3.own

/-! ## 1 Forms that name slots with a property alone -/

/-- Every slot that the form names has the property P. -/
def Names (P : Nat → Prop) (a : Aff) : Prop := ∀ x ∈ a.slots.toList, P x.1

theorem names_mono {P Q : Nat → Prop} (h : ∀ j, P j → Q j) {a : Aff} (ha : Names P a) : Names Q a :=
  fun x hx => h _ (ha x hx)

theorem names_ofConst (P : Nat → Prop) (v : E) : Names P (Aff.ofConst v) := by
  intro x hx
  simp [Aff.ofConst] at hx

theorem names_empty (P : Nat → Prop) : Names P {} := by
  intro x hx
  simp at hx

theorem names_slot {P : Nat → Prop} {j : Nat} (h : P j) : Names P (Aff.slot j) := by
  intro x hx
  have e : x = (j, oneE) := by simpa [Aff.slot] using hx
  rw [e]
  exact h

theorem names_addMul {P : Nat → Prop} {a b : Aff} (ha : Names P a) (hb : Names P b) (k : E) :
    Names P (Aff.addMul a b k) := by
  intro x hx
  have hx' : x ∈ (b.slots.foldl (fun l y => l.push (y.1, mulE y.2 k)) a.slots).toList := hx
  rw [OnBytes.Model.foldl_push_toList (fun y : Nat × E => (y.1, mulE y.2 k))] at hx'
  rcases List.mem_append.1 hx' with h | h
  · exact ha x h
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
    exact hb y hy

theorem names_scale {P : Nat → Prop} {a : Aff} (ha : Names P a) (k : E) :
    Names P (Aff.scale a k) := names_addMul (names_empty P) ha k

theorem names_add {P : Nat → Prop} {a b : Aff} (ha : Names P a) (hb : Names P b) :
    Names P (a + b) := names_addMul ha hb oneE

theorem names_sub {P : Nat → Prop} {a b : Aff} (ha : Names P a) (hb : Names P b) :
    Names P (a - b) := names_addMul ha hb (subE zeroE oneE)

theorem names_onFold {P : Nat → Prop} : ∀ (u : List E) (first : Nat) (f : Aff), Names P f →
    (∀ i, i < u.length → P (first + i)) →
    Names P (u.foldl (fun (s : Nat × Aff) x => (s.1 + 1, Aff.addMul s.2 (Aff.slot s.1) x))
      (first, f)).2
  | [], _, _, hf, _ => hf
  | x :: u, first, f, hf, h => by
    rw [List.foldl_cons]
    refine names_onFold u (first + 1) _
      (names_addMul hf (names_slot (h 0 (Nat.succ_pos _))) x) fun i hi => ?_
    have q := h (i + 1) (Nat.succ_lt_succ hi)
    rwa [show first + (i + 1) = first + 1 + i by omega] at q

/-- A row names its sumcheck's own slots, and those of the form that the sumcheck was given and of
the kept term. Conditional on these having the property. -/
theorem names_rowAff {P : Nat → Prop} (h : MaskedSum.Heard) (S0 : E) {kept : Aff}
    (hs : Names P h.start) (hk : Names P kept)
    (ho : ∀ i, i < (MaskedSum.hidingAt (h.vars.zip h.r)).1.length → P (h.first + i)) :
    Names P (MaskedSum.rowAff h S0 kept) := by
  unfold MaskedSum.rowAff
  exact names_addMul (names_addMul (names_onFold _ _ _ (names_ofConst P _) ho)
    (names_sub (names_ofConst P _) hs) _) hk _

theorem names_stepDown {P : Nat → Prop} (o : LevelOut) (hL : P o.sL) (hR : P o.sR) :
    Names P (stepDown o).2 :=
  names_add (names_scale (names_slot hL) _) (names_scale (names_slot hR) _)

theorem names_foldl {P : Nat → Prop} (g : Aff → Nat → Aff)
    (hg : ∀ c j, Names P c → Names P (g c j)) :
    ∀ (l : List Nat) (c : Aff), Names P c → Names P (l.foldl g c)
  | [], _, hc => hc
  | j :: l, c, hc => names_foldl g hg l _ (hg c j hc)

theorem names_joinForm {P : Nat → Prop} (f : LFace) (sG : Array Nat) (rho : Array E)
    (h : ∀ j, j < f.planes → P (sG.getD j 0)) : Names P (joinForm f sG rho) := by
  unfold joinForm
  refine names_foldl _ (fun c j hc => ?_) _ _ (names_ofConst P _)
  by_cases hj : j < f.planes
  · simp only [if_pos hj]
    exact names_addMul hc (names_slot (h j hj)) _
  · simp only [if_neg hj]
    exact names_add hc (names_ofConst P _)

/-- All rows of an array. -/
def AllNames (P : Nat → Prop) (rows : Array Aff) : Prop := ∀ y ∈ rows.toList, Names P y

theorem allNames_mono {P Q : Nat → Prop} (h : ∀ j, P j → Q j) {rows : Array Aff}
    (hr : AllNames P rows) : AllNames Q rows := fun y hy => names_mono h (hr y hy)

theorem allNames_push {P : Nat → Prop} {rows : Array Aff} {y : Aff} (h : AllNames P rows)
    (hy : Names P y) : AllNames P (rows.push y) := by
  intro z hz
  rw [Array.toList_push] at hz
  rcases List.mem_append.1 hz with h1 | h1
  · exact h z h1
  · obtain rfl : z = y := by simpa using h1
    exact hy

/-! ## 2 Marks -/

/-- Slot j stands from lo on, inside the list M of marks, and bears the mark b. -/
def Is (b : Bool) (lo : Nat) (M : List Bool) (j : Nat) : Prop := lo ≤ j ∧ M[j - lo]? = some b

theorem no_length (n : Nat) : (no n).length = n := by
  unfold VerifiableInference.Desc.K3.own
  exact List.length_replicate

theorem no_get {n i : Nat} (h : i < n) : (no n)[i]? = some false := by
  unfold VerifiableInference.Desc.K3.own
  simp [h]

/-- Appending keeps a mark. -/
theorem is_append {b : Bool} {lo : Nat} {M : List Bool} (T : List Bool) {j : Nat}
    (h : Is b lo M j) : Is b lo (M ++ T) j := by
  refine ⟨h.1, ?_⟩
  obtain ⟨hl, _⟩ := List.getElem?_eq_some_iff.1 h.2
  rw [List.getElem?_append_left hl]
  exact h.2

/-- A mark of the appended stretch. -/
theorem is_new {b : Bool} {lo : Nat} {M T : List Bool} {i : Nat} (h : T[i]? = some b) :
    Is b lo (M ++ T) (lo + M.length + i) := by
  refine ⟨by omega, ?_⟩
  rw [show lo + M.length + i - lo = M.length + i by omega,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact h

theorem grow (M : List Bool) (a b : Nat) : (M ++ no a) ++ no b = M ++ no (a + b) := by
  rw [List.append_assoc, no_add]

/-- Unmarked slots stay unmarked where more unmarked ones are appended. -/
theorem is_no_mono {b : Bool} {lo : Nat} {M : List Bool} {a a' j : Nat} (h : Is b lo (M ++ no a) j)
    (ha : a ≤ a') : Is b lo (M ++ no a') j := by
  have e : M ++ no a' = (M ++ no a) ++ no (a' - a) := by
    rw [grow, Nat.add_sub_cancel' ha]
  rw [e]
  exact is_append _ h

/-! ## 3 The masked sumcheck heard whole -/

/-- **A masked sumcheck heard whole**: it takes its own slots, then its end values'; here T is any
marks for the end values. Its row names unmarked slots alone, where the form that it was given does.
Conditional on its return, on the ledger's count standing behind M, and on that form. -/
theorem whole_step {lo : Nat} {M : List Bool} {C : Aff} {k : MaskedSum.Call}
    {endTerm : List E → List E → E} {F G : Fork} {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff}
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) (hN : F.next = lo + M.length)
    (hC : Names (Is false lo M) C) (T : List Bool) (hT : T.length = k.endsN) :
    G.next = lo + (M ++ (no (ownSlots k.all) ++ T)).length ∧
      Names (Is false lo (M ++ (no (ownSlots k.all) ++ T))) f ∧
      h.sEnd = lo + M.length + ownSlots k.all := by
  obtain ⟨_, G1, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  obtain ⟨a1, a2, a3, a4, a5⟩ := hear_names hh
  have b2 := (hideRun_core (MaskedSum.row_write hr)).next
  refine ⟨?_, ?_, by omega⟩
  · rw [List.length_append, List.length_append, no_length, hT]
    omega
  · rw [MaskedSum.row_spec hr]
    refine names_rowAff h _ (by rw [a1]; exact names_mono (fun _ => is_append _) hC)
      (names_empty _) fun i hi => ?_
    rw [a2, hN]
    refine is_new ?_
    rw [List.getElem?_append_left (by rw [no_length]; omega)]
    exact no_get (by omega)

/-- A mark of an end value. -/
theorem is_end {lo : Nat} {M T : List Bool} {n i : Nat} {b : Bool} (h : T[i]? = some b) :
    Is b lo (M ++ (no n ++ T)) (lo + M.length + n + i) := by
  rw [Nat.add_assoc]
  refine is_new ?_
  rw [List.getElem?_append_right (by rw [no_length]; omega), no_length, Nat.add_sub_cancel_left]
  exact h

/-- The same with unmarked end values: the stretch that is appended has all the slots that the
sumcheck takes, its own and those of its end values. Conditional on the same. -/
theorem sumV_off {lo : Nat} {M : List Bool} {C : Aff} {k : MaskedSum.Call}
    {endTerm : List E → List E → E} {F G : Fork} {rs rest : List Fmt.RoundView}
    {x : MaskedSum.Heard × Aff} (e : sumV C k endTerm F rs = some (x, G, rest))
    (hN : F.next = lo + M.length) (hC : Names (Is false lo M) C) :
    G.next = lo + (M ++ no (ownSlots k.all + k.endsN)).length ∧
      Names (Is false lo (M ++ no (ownSlots k.all + k.endsN))) x.2 ∧
      ∀ i, i < k.endsN → Is false lo (M ++ no (ownSlots k.all + k.endsN)) (x.1.sEnd + i) := by
  obtain ⟨a, b, c⟩ := whole_step (sumV_whole e) hN hC (no k.endsN) (no_length _)
  rw [no_add] at a b
  refine ⟨a, b, fun i hi => ?_⟩
  rw [c, ← no_add]
  exact is_end (no_get hi)

/-! ## 4 The product levels -/

/-- A level that returns has an order with as many entries as the level has variables. Conditional
on its return. -/
theorem level_len {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest)) :
    order.length = m := by
  obtain ⟨hd, line, s, hw, _, _, _, _, _⟩ := level_spec h
  have hw' : MaskedSum.whole C ⟨0, levelVars m z order, some levelEnds⟩
      VerifiableInference.Desc.First.ProdV.endProd F (rs.take (m + 3)) = some (hd, o.row, G) := hw
  have a := (whole_seg hw').1
  have b := (level_seg h).2.1
  rw [List.length_take, levelVars, List.length_map] at a
  omega

/-- A level's sumcheck takes 2 n + 3 slots of its own, where n is the number of entries of its
order. -/
theorem own_levelVars (m : Nat) (z : Array E) (order : List Nat) :
    ownSlots (⟨0, levelVars m z order, some levelEnds⟩ : MaskedSum.Call).all =
      2 * order.length + 3 := by
  simp only [MaskedSum.Call.all, levelEnds, levelVars, ownSlots_eq, List.map_append, List.map_map,
    Function.comp_def, MaskedSum.Var.d, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, sum_map_const]
  omega

/-- **One level**: 2 m + 3 slots of its own, unmarked; then its two end values, with any marks T.
Conditional on its return, on the ledger's count standing behind M, and on the form that it is given
naming unmarked slots alone. -/
theorem level_step {lo : Nat} {M : List Bool} {m : Nat} {z : Array E} {order : List Nat} {C : Aff}
    {F G : Fork} {rs rest : List Fmt.RoundView} {o : LevelOut}
    (h : level m z order C F rs = some (o, G, rest)) (hN : F.next = lo + M.length)
    (hC : Names (Is false lo M) C) (T : List Bool) (hT : T.length = 2) :
    G.next = lo + (M ++ (no (2 * m + 3) ++ T)).length ∧
      Names (Is false lo (M ++ (no (2 * m + 3) ++ T))) o.row ∧
      o.sL = lo + M.length + (2 * m + 3) ∧ o.sR = lo + M.length + (2 * m + 3) + 1 := by
  have hl := level_len h
  obtain ⟨hd, line, s, hw, _, _, _, hL, hR⟩ := level_spec h
  have hw' : MaskedSum.whole C ⟨0, levelVars m z order, some levelEnds⟩
      VerifiableInference.Desc.First.ProdV.endProd F (rs.take (m + 3)) = some (hd, o.row, G) := hw
  obtain ⟨a, b, c⟩ := whole_step hw' hN hC T hT
  rw [own_levelVars, hl] at a b c
  exact ⟨a, b, hL.trans c, by rw [hR, c]⟩

/-- What a run of levels carries: rows and form name unmarked slots alone. -/
def CarriedOff (lo : Nat) (M : List Bool) (c : Carried) : Prop :=
  AllNames (Is false lo M) c.rows ∧ Names (Is false lo M) c.form

/-- One turn, its end values unmarked. Conditional on its return and on what it is given. -/
theorem turn_off {lo : Nat} {M : List Bool} {order : List Nat} {s s' : Carried} {m : Nat}
    {F G : Fork} {rs rest : List Fmt.RoundView} (h : turn order s m F rs = some (s', G, rest))
    (hN : F.next = lo + M.length) (hs : CarriedOff lo M s) :
    G.next = lo + (M ++ no (2 * m + 5)).length ∧ CarriedOff lo (M ++ no (2 * m + 5)) s' := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, _⟩ := e
  subst e1 e2
  obtain ⟨a, b, cL, cR⟩ := level_step hx hN hs.2 (no 2) (no_length 2)
  have eM : no (2 * m + 3) ++ no 2 = no (2 * m + 5) := no_add _ _
  have hL : Is false lo (M ++ (no (2 * m + 3) ++ no 2)) o.sL := by
    rw [cL, ← Nat.add_zero (lo + M.length + (2 * m + 3))]
    exact is_end (no_get (by omega))
  have hR : Is false lo (M ++ (no (2 * m + 3) ++ no 2)) o.sR := by
    rw [cR]
    exact is_end (no_get (by omega))
  rw [eM] at a b hL hR
  exact ⟨a, allNames_push (allNames_mono (fun _ => is_append _) hs.1) b, names_stepDown o hL hR⟩

/-- A fold of turns, all end values unmarked. Conditional on its return and on what it is given. -/
theorem fold_off {lo : Nat} (m0 : Nat) (orders : Nat → List Nat) : ∀ (l : List Nat) (M : List Bool)
    (x y : Carried × Fork × List Fmt.RoundView),
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y →
    x.2.1.next = lo + M.length → CarriedOff lo M x.1 →
    y.2.1.next = lo + (M ++ l.flatMap fun i => no (2 * (m0 + i) + 5)).length ∧
      CarriedOff lo (M ++ l.flatMap fun i => no (2 * (m0 + i) + 5)) y.1
  | [], M, x, y, h, hN, hx => by
    obtain rfl : x = y := Option.some.inj h
    rw [List.flatMap_nil, List.append_nil]
    exact ⟨hN, hx⟩
  | i :: l, M, x, y, h, hN, hx => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    obtain ⟨a, b⟩ := turn_off hz hN hx
    have r := fold_off m0 orders l _ (s', G, rest) y h a b
    rw [List.append_assoc] at r
    rw [List.flatMap_cons]
    exact r

/-- The marks of a key tree's level number k, in a tree of v levels. -/
def lev (v k : Nat) : List Bool :=
  if k + 1 == v then no (2 * k + 3) ++ [true, true] else no (2 * k + 5)

/-- **A part's key tree**: its rows name unmarked slots alone; the form that it leaves names marked
slots alone: the two end values of its last level. Conditional on its return, on a level at least,
and on what it is given. -/
theorem tree_marks {lo : Nat} {M : List Bool} {v : Nat} {orders : Nat → List Nat} {s s' : Carried}
    {F G : Fork} {rs rest : List Fmt.RoundView} (h : vRun 0 v orders s F rs = some (s', G, rest))
    (hv : 1 ≤ v) (hN : F.next = lo + M.length) (hs : CarriedOff lo M s) :
    G.next = lo + (M ++ (List.range v).flatMap (lev v)).length ∧
      AllNames (Is false lo (M ++ (List.range v).flatMap (lev v))) s'.rows ∧
      Names (Is true lo (M ++ (List.range v).flatMap (lev v))) s'.form := by
  obtain ⟨n, rfl⟩ : ∃ n, v = n + 1 := ⟨v - 1, by omega⟩
  have h' : (List.range (n + 1)).foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (0 + i)) x.1 (0 + i) x.2.1 x.2.2) (s, F, rs) = some (s', G, rest) := h
  rw [List.range_succ, List.foldlM_append] at h'
  obtain ⟨z, hz, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨a, b⟩ := fold_off (lo := lo) 0 orders (List.range n) M (s, F, rs) z hz hN hs
  have eF : ((List.range n).flatMap fun i => no (2 * (0 + i) + 5)) =
      (List.range n).flatMap (lev (n + 1)) := by
    refine List.flatMap_congr fun k hk => ?_
    have hk' := List.mem_range.1 hk
    have hne : (k + 1 == n + 1) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    unfold lev
    rw [hne, Nat.zero_add]
    rfl
  rw [eF] at a b
  have eL : lev (n + 1) n = no (2 * n + 3) ++ [true, true] := by
    unfold lev
    rw [beq_self_eq_true]
    rfl
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    eL, ← List.append_assoc]
  rw [List.foldlM_cons] at h'
  obtain ⟨w, hw, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain rfl : w = (s', G, rest) := Option.some.inj h'
  rw [Nat.zero_add] at hw
  unfold turn at hw
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 hw
  obtain ⟨o, G', rest'⟩ := x
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, _⟩ := e
  subst e1 e2
  obtain ⟨c, d, cL, cR⟩ := level_step hx a b.2 [true, true] rfl
  refine ⟨c, allNames_push (allNames_mono (fun _ => is_append _) b.1) d, names_stepDown o ?_ ?_⟩
  · rw [cL, ← Nat.add_zero (lo + _ + (2 * n + 3))]
    exact is_end rfl
  · rw [cR]
    exact is_end rfl

/-! ## 5 The lookup's own pieces -/

/-- What the tie's fold carries. Here sZ is the slot of the key side's root. -/
def TieM (lo : Nat) (M : List Bool) (sZ : Nat) (s : Array Aff × Nat × Array Nat) (F : Fork) :
    Prop :=
  1 ≤ s.2.2.size ∧ F.next = lo + (M ++ no (7 + 6 * (s.2.2.size - 1))).length ∧
    AllNames (Is false lo (M ++ no (7 + 6 * (s.2.2.size - 1)))) s.1 ∧
    Is false lo (M ++ no (7 + 6 * (s.2.2.size - 1))) s.2.1 ∧
    (∀ j ∈ s.2.2.toList, Is false lo (M ++ no (7 + 6 * (s.2.2.size - 1))) j) ∧
    Is false lo (M ++ no (7 + 6 * (s.2.2.size - 1))) sZ

/-- **The tie**: 7 + 6 (w - 2) slots, all unmarked. Conditional on its return and on the ledger's
count standing behind M. -/
theorem tieV_marks {lo : Nat} {M : List Bool} {w : Nat} {a : E} {F G : Fork} {rs rest : List Fmt.RoundView}
    {rows : Array Aff} {sZ : Nat} {sG : Array Nat}
    (h : tieV w a F rs = some ((rows, sZ, sG), G, rest)) (hN : F.next = lo + M.length) :
    G.next = lo + (M ++ no (7 + 6 * (w - 2))).length ∧
      AllNames (Is false lo (M ++ no (7 + 6 * (w - 2)))) rows ∧
      Is false lo (M ++ no (7 + 6 * (w - 2))) sZ ∧
      (∀ j ∈ sG.toList, Is false lo (M ++ no (7 + 6 * (w - 2))) j) ∧ sG.size = w - 2 + 2 := by
  unfold tieV at h
  obtain ⟨x, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨s, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨hg, hG, _⟩ := pure_spec h
  obtain ⟨a1, a2, a3⟩ := sumV_off e1 hN (names_ofConst _ _)
  have a1' : F1.next = lo + (M ++ no 7).length := a1
  have a2' : Names (Is false lo (M ++ no 7)) x.2 := a2
  have a3' : ∀ i, i < 3 → Is false lo (M ++ no 7) (x.1.sEnd + i) := a3
  have P0 : TieM lo M x.1.sEnd (#[x.2], x.1.sEnd + 1, #[x.1.sEnd + 2]) F1 := by
    refine ⟨Nat.le_refl 1, a1', ?_, a3' 1 (by omega), ?_, a3' 0 (by omega)⟩
    · intro y hy
      obtain rfl : y = x.2 := by simpa using hy
      exact a2'
    · intro j hj
      obtain rfl : j = x.1.sEnd + 2 := by simpa using hj
      exact a3' 2 (by omega)
  have step := foldlM_keeps (TieM lo M x.1.sEnd)
    (by
      intro s _ F' rs' s' G' rest' hs hp
      obtain ⟨y, F3, r3, e3, hs⟩ := bindHr_some hs
      obtain ⟨q1, q2, _⟩ := pure_spec hs
      obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hp
      obtain ⟨b1, b2, b3⟩ := sumV_off e3 p1 (names_slot p3)
      have eM : (M ++ no (7 + 6 * (s.2.2.size - 1))) ++ no 6 =
          M ++ no (7 + 6 * ((s.2.2.push (y.1.sEnd + 1)).size - 1)) := by
        rw [grow, Array.size_push]
        congr 2
        omega
      have b1' : F3.next = lo + ((M ++ no (7 + 6 * (s.2.2.size - 1))) ++ no 6).length := b1
      have b2' : Names (Is false lo ((M ++ no (7 + 6 * (s.2.2.size - 1))) ++ no 6)) y.2 := b2
      have b3' : ∀ i, i < 2 →
          Is false lo ((M ++ no (7 + 6 * (s.2.2.size - 1))) ++ no 6) (y.1.sEnd + i) := b3
      rw [q1, q2]
      unfold TieM
      dsimp only
      rw [← eM]
      refine ⟨by rw [Array.size_push]; omega, b1',
        allNames_push (allNames_mono (fun _ => is_append _) p2) b2', b3' 0 (by omega), ?_,
        is_append _ p5⟩
      intro j hj
      rcases mem_push hj with h1 | h1
      · exact is_append _ (p4 j h1)
      · rw [h1]
        exact b3' 1 (by omega))
    _ _ _ _ _ _ _ e2 P0
  have hsz : s.2.2.size = 1 + (List.range (w - 2)).length :=
    foldlM_count (fun (s : Array Aff × Nat × Array Nat) => s.2.2.size)
      (by
        intro s _ F' rs' s' G' rest' hs
        obtain ⟨y, F3, r3, e3, hs⟩ := bindHr_some hs
        obtain ⟨q1, _, _⟩ := pure_spec hs
        rw [q1]
        simp)
      _ _ _ _ _ _ _ e2
  rw [List.length_range] at hsz
  obtain ⟨_, t1, t2, t3, t4, t5⟩ := step
  have en : s.2.2.size - 1 = w - 2 := by omega
  rw [en] at t1 t2 t3 t4 t5
  simp only [Prod.mk.injEq] at hg
  obtain ⟨g1, g2, g3⟩ := hg
  subst g1 g2 g3
  rw [hG]
  refine ⟨t1, t2, t5, ?_, by rw [Array.size_push, hsz]; omega⟩
  intro j hj
  rcases mem_push hj with h1 | h1
  · exact t4 j h1
  · rw [h1]
    exact t3

/-- **From the product of the parts' roots to each**: 5 n slots, all unmarked; n + 1 roots.
Conditional on its return and on what it is given. -/
theorem partsV_marks {lo : Nat} : ∀ (n : Nat) (M : List Bool) (rows : Array Aff) (C : Aff)
    (F : Fork) (rs : List Fmt.RoundView) (rows' : Array Aff) (roots : List Aff) (G : Fork)
    (rest : List Fmt.RoundView),
    partsV n rows C F rs = some ((rows', roots), G, rest) → F.next = lo + M.length →
    AllNames (Is false lo M) rows → Names (Is false lo M) C →
    G.next = lo + (M ++ no (5 * n)).length ∧ AllNames (Is false lo (M ++ no (5 * n))) rows' ∧
      (∀ y ∈ roots, Names (Is false lo (M ++ no (5 * n))) y) ∧ roots.length = n + 1
  | 0, M, rows, C, F, rs, rows', roots, G, rest, h, hN, hr, hC => by
    unfold partsV at h
    obtain ⟨a, b, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2 b
    have e : M ++ no (5 * 0) = M := by
      show M ++ List.replicate 0 false = M
      simp
    rw [e]
    refine ⟨hN, hr, fun y hy => ?_, rfl⟩
    obtain rfl : y = C := by simpa using hy
    exact hC
  | n + 1, M, rows, C, F, rs, rows', roots, G, rest, h, hN, hr, hC => by
    unfold partsV at h
    obtain ⟨w, F1, r1, e1, h⟩ := bindHr_some h
    obtain ⟨x, F2, r2, e2, h⟩ := bindHr_some h
    obtain ⟨a, b, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2
    rw [b]
    obtain ⟨b1, b2, b3⟩ := sumV_off e1 hN hC
    have b1' : F1.next = lo + (M ++ no 5).length := b1
    have b2' : Names (Is false lo (M ++ no 5)) w.2 := b2
    have b3' : ∀ i, i < 2 → Is false lo (M ++ no 5) (w.1.sEnd + i) := b3
    obtain ⟨c1, c2, c3, c4⟩ := partsV_marks n (M ++ no 5) _ _ F1 r1 x.1 x.2 F2 r2 e2 b1'
      (allNames_push (allNames_mono (fun _ => is_append _) hr) b2')
      (names_slot (b3' 1 (by omega)))
    have eM : (M ++ no 5) ++ no (5 * n) = M ++ no (5 * (n + 1)) := by
      rw [grow]
      congr 2
      omega
    rw [eM] at c1 c2 c3
    refine ⟨c1, c2, fun y hy => ?_, by rw [List.length_cons, c4]⟩
    rcases List.mem_cons.1 hy with h1 | h1
    · rw [h1, ← eM]
      exact names_slot (is_append _ (b3' 0 (by omega)))
    · exact c3 y h1

/-- **The parts' key trees**: the rows name unmarked slots alone, every part's key form marked ones
alone. Conditional on its return; a root for each part; a level at least in each; and on what it is
given. -/
theorem keysV_marks {lo : Nat} (f : LFace) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff)
    (M : List Bool) (rows : Array Aff) (F : Fork) (rs : List Fmt.RoundView) (rows' : Array Aff)
    (keys : List (Array E × Aff)) (G : Fork) (rest : List Fmt.RoundView),
    keysV f xs Cs rows F rs = some ((rows', keys), G, rest) → xs.length = Cs.length →
    (∀ x ∈ xs, 1 ≤ x.1) → F.next = lo + M.length → AllNames (Is false lo M) rows →
    (∀ C ∈ Cs, Names (Is false lo M) C) →
    G.next = lo + (M ++ xs.flatMap fun x => (List.range x.1).flatMap (lev x.1)).length ∧
      AllNames (Is false lo (M ++ xs.flatMap fun x => (List.range x.1).flatMap (lev x.1))) rows' ∧
      ∀ y ∈ keys,
        Names (Is true lo (M ++ xs.flatMap fun x => (List.range x.1).flatMap (lev x.1))) y.2
  | [], _, M, rows, F, rs, rows', keys, G, rest, h, _, _, hN, hr, _ => by
    unfold keysV at h
    obtain ⟨a, b, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2 b
    rw [List.flatMap_nil, List.append_nil]
    exact ⟨hN, hr, fun y hy => by simp at hy⟩
  | _ :: _, [], _, _, _, _, _, _, _, _, _, hl, _, _, _, _ => by simp at hl
  | x :: xs, C :: Cs, M, rows, F, rs, rows', keys, G, rest, h, hl, hv, hN, hr, hC => by
    unfold keysV at h
    obtain ⟨k, F1, r1, e1, h⟩ := bindHr_some h
    obtain ⟨y, F2, r2, e2, h⟩ := bindHr_some h
    obtain ⟨a, b, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2
    rw [b]
    have e1' : vRun 0 x.1 (f.orders x.2) { rows := rows, point := #[], form := C } F rs =
        some (k, F1, r1) := e1
    obtain ⟨k1, k2, k3⟩ := tree_marks e1' (hv x (by simp)) hN ⟨hr, hC C (by simp)⟩
    obtain ⟨c1, c2, c3⟩ := keysV_marks f xs Cs _ k.rows F1 r1 y.1 y.2 F2 r2 e2
      (by simpa using hl) (fun z hz => hv z (List.mem_cons_of_mem _ hz)) k1 k2
      (fun D hD => names_mono (fun _ => is_append _) (hC D (List.mem_cons_of_mem _ hD)))
    rw [List.append_assoc] at c1 c2 c3
    rw [List.flatMap_cons]
    refine ⟨c1, c2, fun z hz => ?_⟩
    rcases List.mem_cons.1 hz with h1 | h1
    · rw [h1, ← List.append_assoc]
      exact names_mono (fun _ => is_append _) k3
    · exact c3 z h1

/-! ## 6 What was heard -/

theorem owe_next {what : String} {F G : Fork} {rs rest : List Fmt.RoundView} {n : Nat}
    (h : Hr.owe what F rs = some (n, G, rest)) : G.next = F.next := by
  have h' : some ((F.owe what).1, (F.owe what).2, rs) = some (n, G, rest) := h
  cases h'
  rfl

theorem drawV_same {F G : Fork} {rs rest : List Fmt.RoundView} {a : E}
    (e : drawV F rs = some (a, G, rest)) : G = F := by
  unfold drawV at e
  split at e
  · rename_i x G' rest' hx
    split at e
    · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
      exact drawsV_same hx
    · exact nomatch e
  · exact nomatch e

/-- Stretches of unmarked slots, one behind the other, are one. -/
theorem no_flatMap (g : Nat → Nat) : ∀ l : List Nat,
    (l.flatMap fun i => no (g i)) = no ((l.map g).sum)
  | [] => rfl
  | i :: l => by rw [List.flatMap_cons, no_flatMap g l, no_add, List.map_cons, List.sum_cons]

/-- The marks behind the parts' key trees, as the walk sets them. -/
def marksK (f : LFace) : List Bool :=
  (([] ++ no (7 + 6 * (f.planes - 2))) ++ no (5 * (f.parts.length - 1))) ++
    f.parts.zipIdx.flatMap fun x => (List.range x.1).flatMap (lev x.1)

/-- The marks behind the table side's levels. -/
def marksT (f : LFace) : List Bool :=
  marksK f ++ (List.range f.d).flatMap fun i => no (2 * (f.mu + i) + 5)

/-- **The verifier's own list, as the walk sets it.** -/
theorem fromKeys_walk (f : LFace) :
    (marksT f ++ no (1 + f.mu + 2 * f.d)) ++ no (1 + 2 * (f.mu + f.d) + 2 + 1) = fromKeys f := by
  unfold fromKeys marksT marksK
  rw [List.nil_append, no_add, no_flatMap (fun i => 2 * (f.mu + i) + 5),
    flatMap_zipIdx_fst (fun v => (List.range v).flatMap (lev v)) f.parts 0, List.append_assoc,
    List.append_assoc, no_add, no_add]
  exact congrArg₂ (· ++ ·) rfl (congrArg VerifiableInference.Desc.K3.own (by omega))

/-- **Of what was heard**, from the return. Here lo is the ledger's count in front. Every row
and the form that the leaves' sumcheck was given name slots that the verifier's list leaves
unmarked; every part's key form names marked slots alone; the leaves' own slots and the bits' end
slot are unmarked. Conditional on the return of `messagesV` and on the face's own test. -/
theorem heard_marks {f : LFace} {F G : Fork} {rs rest : List Fmt.RoundView} {g : HeardV}
    (hok : f.ok = true) (h : messagesV f F rs = some (g, G, rest)) :
    AllNames (Is false F.next (fromKeys f)) g.rows ∧
      (∀ y ∈ g.keys, Names (Is true F.next (fromKeys f)) y.2) ∧
      Names (Is false F.next (fromKeys f)) g.leaves.start ∧
      (∀ i, i < 1 + f.mu + 2 * f.d → Is false F.next (fromKeys f) (g.leaves.first + i)) ∧
      Is false F.next (fromKeys f) g.sBit ∧
      (MaskedSum.hidingAt (g.leaves.vars.zip g.leaves.r)).1.length ≤ 1 + f.mu + 2 * f.d := by
  have hok' := hok
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true'] at hok'
  have hne : f.parts.isEmpty = false := hok'.1.1.1.1.2
  have hv1 : ∀ v ∈ f.parts, 1 ≤ v := hok'.1.1.1.2
  have hlen : 1 ≤ f.parts.length := by
    cases hp : f.parts with
    | nil => rw [hp] at hne; exact nomatch hne
    | cons _ _ => simp
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3, h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4, h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5, h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6, h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7, h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8, h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9, h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10, h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11, h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12, h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13, h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14, h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15, h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16, h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17, h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18, h⟩ := bindHr_some h
  obtain ⟨hg, _, _⟩ := pure_spec h
  have q5 : F5 = F4 := by
    by_cases hsft : f.shifted = true
    · rw [if_pos hsft] at e5
      exact drawV_same e5
    · rw [if_neg hsft] at e5
      exact (pure_spec e5).2.1
  have n6 : F6.next = F.next + ([] : List Bool).length := by
    rw [drawV_same e6, q5, owe_next e4, owe_next e3, owe_next e2, (slot_spec e1).2]
    rfl
  obtain ⟨t1, t2, t3, t4, t5⟩ := tieV_marks e7 n6
  obtain ⟨p1, p2, p3, p4⟩ := partsV_marks _ _ _ _ _ _ _ _ _ _ e8 t1 t2 (names_slot t3)
  rw [← drawsV_same e9] at p1
  obtain ⟨k1, k2, k3⟩ := keysV_marks f _ _ _ _ _ _ _ _ _ _ e10
    (by rw [List.length_zipIdx, p4]; omega)
    (fun x hx => hv1 x.1 (by
      have := List.mem_map_of_mem (f := Prod.fst) hx
      rwa [List.zipIdx_map_fst] at this)) p1 p2 p3
  rw [← (must_spec e11).2] at k1
  have hsG : ∀ j, j < f.planes → Is false F.next (marksK f) (sG.getD j 0) := by
    intro j hj
    have h2 := two_le_planes_of_ok f hok
    have hlt : j < sG.size := by omega
    have hm : sG.getD j 0 ∈ sG.toList := by simp [Array.getD, hlt]
    exact is_append _ (is_append _ (t4 _ hm))
  have e12' : (List.range f.d).foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orderDefault (f.mu + i)) x.1 (f.mu + i) x.2.1 x.2.2)
      ({ rows := rows3, point := jo.reverse, form := joinForm f sG jo.reverse }, F11, r11) =
      some (table, F12, r12) := e12
  have k1' : F11.next = F.next + (marksK f).length := k1
  have k2' : AllNames (Is false F.next (marksK f)) rows3 := k2
  obtain ⟨q1, q2, q3⟩ := fold_off (lo := F.next) f.mu orderDefault _ (marksK f) _ _ e12' k1'
    ⟨k2', names_joinForm f sG _ hsG⟩
  have q1' : F12.next = F.next + (marksT f).length := q1
  have q2' : AllNames (Is false F.next (marksT f)) table.rows := q2
  have q3' : Names (Is false F.next (marksT f)) table.form := q3
  rw [← (must_spec e13).2] at q1'
  obtain ⟨l1, l2, l3, l4, l5⟩ := hear_names (openV_hear e14)
  have o14 : ownSlots ({ lead := 0, vs := leafVars f table.point, ends := none } :
      MaskedSum.Call).all = 1 + f.mu + 2 * f.d := own_leafVars f _
  have n15 : F15.next = F.next + (marksT f ++ no (1 + f.mu + 2 * f.d)).length := by
    rw [drawsV_same e15, l4, l3, o14, q1', List.length_append, no_length]
    show _ + 0 = _
    omega
  obtain ⟨b1, b2, b3⟩ := sumV_off e16 n15 (names_ofConst _ _)
  have s15 := (drawsV_spec e15).2.2.2
  have ob : ownSlots (bitsCall ze.reverse.toList).all + (bitsCall ze.reverse.toList).endsN =
      1 + 2 * (f.mu + f.d) + 2 + 1 := by
    rw [own_bits]
    have : ze.reverse.toList.length = f.mu + f.d := by simp [s15]
    rw [this]
    rfl
  rw [ob, fromKeys_walk] at b2 b3
  have up1 : ∀ {b : Bool} {j : Nat}, Is b F.next (marksT f) j → Is b F.next (fromKeys f) j := by
    intro b j hj
    rw [← fromKeys_walk]
    exact is_append _ (is_append _ hj)
  subst hg
  have k3' : ∀ y ∈ keys, Names (Is true F.next (marksK f)) y.2 := k3
  refine ⟨allNames_push (allNames_mono (fun _ => up1) q2') b2,
    fun y hy => names_mono (fun _ hj => up1 (is_append _ hj)) (k3' y hy), ?_, fun i hi => ?_,
    b3 0 (Nat.succ_pos 0), by rw [← o14]; exact l5⟩
  · show Names _ leaves.start
    rw [l1]
    exact names_mono (fun _ => up1) q3'
  · show Is false F.next (fromKeys f) (leaves.first + i)
    rw [l2, q1', ← fromKeys_walk]
    exact is_append _ (is_new (no_get hi))

/-- The mark that the verifier's list bears at slot j; here lo is the ledger's count in front of the
lookup. -/
def markAt (f : LFace) (lo j : Nat) : Bool := (fromKeys f).getD (j - lo) false

theorem markAt_of_is {f : LFace} {lo j : Nat} {b : Bool} (h : Is b lo (fromKeys f) j) :
    markAt f lo j = b := by
  unfold markAt
  rw [List.getD_eq_getElem?_getD, h.2]
  rfl

/-- **Behind `hearV`: every row names unmarked slots alone; every part's key form names marked ones
alone.** `markAt` says "unmarked" of every slot outside the list too: that the named slots lie
inside it is what `hearV_is` says. Conditional on the return of `hearV`. An instance:
Honest/K3/Parts/NamesMarksGuards.lean [not in this library] (by evaluation). -/
theorem hearV_marks {f : LFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (hh : hearV f F rs = some (g, G)) :
    (∀ a ∈ g.rows.toList, ∀ x ∈ a.slots.toList, markAt f F.next x.1 = false) ∧
      (∀ y ∈ g.keys, ∀ x ∈ y.2.slots.toList, markAt f F.next x.1 = true) ∧
      (∀ x ∈ g.leaves.start.slots.toList, markAt f F.next x.1 = false) ∧
      (∀ i, i < 1 + f.mu + 2 * f.d → markAt f F.next (g.leaves.first + i) = false) ∧
      markAt f F.next g.sBit = false := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  obtain ⟨a, b, c, d, e, _⟩ := heard_marks hok hm
  exact ⟨fun r hr x hx => markAt_of_is (a r hr x hx), fun y hy x hx => markAt_of_is (b y hy x hx),
    fun x hx => markAt_of_is (c x hx), fun i hi => markAt_of_is (d i hi), markAt_of_is e⟩

/-- **Behind `hearV`, in the stronger form**: every named slot lies from the ledger's first
count on, inside the verifier's list, and bears the mark. Conditional on the return of `hearV`.
An instance: Honest/K3/Parts/NamesMarksGuards.lean [not in this library] (by evaluation). -/
theorem hearV_is {f : LFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (hh : hearV f F rs = some (g, G)) :
    AllNames (Is false F.next (fromKeys f)) g.rows ∧
      (∀ y ∈ g.keys, Names (Is true F.next (fromKeys f)) y.2) ∧
      Names (Is false F.next (fromKeys f)) g.leaves.start ∧
      (∀ i, i < 1 + f.mu + 2 * f.d → Is false F.next (fromKeys f) (g.leaves.first + i)) ∧
      Is false F.next (fromKeys f) g.sBit := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  obtain ⟨a, b, c, d, e, _⟩ := heard_marks hok hm
  exact ⟨a, b, c, d, e⟩

/-- **The leads of the three claims on the planes, in the stronger form.** Conditional on the return
of `hearV` and that of `planesV`. An instance: Honest/K3/Parts/NamesMarksGuards.lean
[not in this library] (by evaluation). -/
theorem planesV_is {f : LFace} {F G F' G' : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    {cl : List PlaneClaim} (hh : hearV f F rs = some (g, G))
    (hp : planesV f g F' = some (cl, G')) :
    ∀ c ∈ cl, Names (Is false F.next (fromKeys f)) c.lead := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  obtain ⟨_, _, c3, c4, c5, hlen⟩ := heard_marks hok hm
  unfold planesV at hp
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hp
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, _⟩ := e
  subst e1
  have hy' : MaskedSum.row g.leaves oneE {} F' = some (y.1, y.2) := hy
  have r1 : Names (Is false F.next (fromKeys f)) y.1 := by
    rw [MaskedSum.row_spec hy']
    exact names_rowAff _ _ c3 (names_empty _) fun i hi => c4 i (by omega)
  intro c hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact r1
  · exact names_slot c5
  · exact names_ofConst _ _

/-- **The leads of the three claims on the planes name unmarked slots alone.** `markAt` says
"unmarked" of every slot outside the list too: that the named slots lie inside it is what
`planesV_is` says. Conditional on the return of `hearV` and that of `planesV`. An instance:
Honest/K3/Parts/NamesMarksGuards.lean [not in this library] (by evaluation). -/
theorem planesV_marks {f : LFace} {F G F' G' : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    {cl : List PlaneClaim} (hh : hearV f F rs = some (g, G))
    (hp : planesV f g F' = some (cl, G')) :
    ∀ c ∈ cl, ∀ x ∈ c.lead.slots.toList, markAt f F.next x.1 = false :=
  fun c hc x hx => markAt_of_is (planesV_is hh hp c hc x hx)

#print axioms ProofFile.Honest.K3.Parts.names_mono
#print axioms ProofFile.Honest.K3.Parts.names_ofConst
#print axioms ProofFile.Honest.K3.Parts.names_empty
#print axioms ProofFile.Honest.K3.Parts.names_slot
#print axioms ProofFile.Honest.K3.Parts.names_addMul
#print axioms ProofFile.Honest.K3.Parts.names_scale
#print axioms ProofFile.Honest.K3.Parts.names_add
#print axioms ProofFile.Honest.K3.Parts.names_sub
#print axioms ProofFile.Honest.K3.Parts.names_onFold
#print axioms ProofFile.Honest.K3.Parts.names_rowAff
#print axioms ProofFile.Honest.K3.Parts.names_stepDown
#print axioms ProofFile.Honest.K3.Parts.names_foldl
#print axioms ProofFile.Honest.K3.Parts.names_joinForm
#print axioms ProofFile.Honest.K3.Parts.allNames_mono
#print axioms ProofFile.Honest.K3.Parts.allNames_push
#print axioms ProofFile.Honest.K3.Parts.no_length
#print axioms ProofFile.Honest.K3.Parts.no_get
#print axioms ProofFile.Honest.K3.Parts.is_append
#print axioms ProofFile.Honest.K3.Parts.is_new
#print axioms ProofFile.Honest.K3.Parts.grow
#print axioms ProofFile.Honest.K3.Parts.is_no_mono
#print axioms ProofFile.Honest.K3.Parts.whole_step
#print axioms ProofFile.Honest.K3.Parts.is_end
#print axioms ProofFile.Honest.K3.Parts.sumV_off
#print axioms ProofFile.Honest.K3.Parts.level_len
#print axioms ProofFile.Honest.K3.Parts.own_levelVars
#print axioms ProofFile.Honest.K3.Parts.level_step
#print axioms ProofFile.Honest.K3.Parts.turn_off
#print axioms ProofFile.Honest.K3.Parts.fold_off
#print axioms ProofFile.Honest.K3.Parts.tree_marks
#print axioms ProofFile.Honest.K3.Parts.tieV_marks
#print axioms ProofFile.Honest.K3.Parts.partsV_marks
#print axioms ProofFile.Honest.K3.Parts.keysV_marks
#print axioms ProofFile.Honest.K3.Parts.owe_next
#print axioms ProofFile.Honest.K3.Parts.drawV_same
#print axioms ProofFile.Honest.K3.Parts.no_flatMap
#print axioms ProofFile.Honest.K3.Parts.fromKeys_walk
#print axioms ProofFile.Honest.K3.Parts.heard_marks
#print axioms ProofFile.Honest.K3.Parts.markAt_of_is
#print axioms ProofFile.Honest.K3.Parts.hearV_marks
#print axioms ProofFile.Honest.K3.Parts.hearV_is
#print axioms ProofFile.Honest.K3.Parts.planesV_is
#print axioms ProofFile.Honest.K3.Parts.planesV_marks

end ProofFile.Honest.K3.Parts
