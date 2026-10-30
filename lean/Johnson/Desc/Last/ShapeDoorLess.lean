-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorLess.lean: THE DOOR OF THE LAST CHAIN AT `fillZ` FROM LESS: of the eight
tests on the first chain's end (Johnson/Desc/Last/ShapeDoor.lean) two are paid: "the open rows name
messages of the statement alone" follows from "tidy"; "the mask has come" follows from the start's
yes where the shape sends the masks ahead. Definitions, statements and proofs. WHAT IS LEFT IS PAID
NOWHERE.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`named_is_member`**, `named_is_there`: in a statement in order (`OnBytes.Means.InOrder`) every
    message that an open row of a group names is a member of that group, so its number is below the
    count of the statement's messages: by `RowIn`, `placeOk_iff` and `GroupOk.there`
    (Johnson/Desc/Means/Says.lean, Lays.lean).
  `firstSixClauses h`, `firstSixB h`: the six that are left: tidy; the book fits; one pending row
    with lawful weights; two members; one sample row each; an open row. `firstDoorB_of_six`: with a
    mask's number handed they give `firstDoorB h`.
  **`DoorOwedLess p fs On₂ start₃`**: first: the six, inside On₂ where start₃ says yes; shared and
    start: as in `DoorOwed`; ahead: `p.S.masksAhead = true` (at what the planner has sized:
    `masksAhead_of_linSized`, Johnson/Desc/Last/ShapeMask.lean). **`doorOwed_of_less`**: the four
    give `DoorOwed`. `door_fillZ_less`: so the door.

Every "there is": e in `DoorOwedLess.start`: tied by `ended d = some e`.
Limits. Those of ShapeDoor.lean: a reduction; no member; On₂ := False pays first and shared for
nothing. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoor
import Johnson.Desc.Third.Law.Mask

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.Sound (bookFitsB)
open OnBytes.Means (InOrder RowIn GroupOk placeOk_iff)
open _root_.Desc.K14 (St)

/-! ## 1 The names -/

/-- **In a statement in order every message that an open row of a group names is a member of that
group.** -/
theorem named_is_member {S : Statement} (h : InOrder S) {g : Nat} {G : Group}
    (hG : S.groups[g]? = some G) {r : OnBytes.Row} (hr : r ∈ G.rows.toList) {o : Nat}
    (ho : o ∈ r.oracles) : o ∈ G.members.toList := by
  have R : RowIn S G r := h.rows g G hG r hr
  unfold OnBytes.Row.oracles at ho
  simp only [List.mem_append, Array.toList_map, List.mem_map] at ho
  rcases ho with ((⟨t, ht, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨w, hw, rfl⟩) | ⟨f, hf, rfl⟩
  · exact ((placeOk_iff _ _ _ _ _ _).1 (R.terms t ht)).1
  · exact ((placeOk_iff _ _ _ _ _ _).1 (R.units u hu)).1
  · exact ((placeOk_iff _ _ _ _ _ _).1 (R.runs w hw).2.2).1
  · exact ((placeOk_iff _ _ _ _ _ _).1 (R.forms f hf).1).1

/-- So it is one of the statement's. -/
theorem named_is_there {S : Statement} (h : InOrder S) {g : Nat} {G : Group}
    (hG : S.groups[g]? = some G) {r : OnBytes.Row} (hr : r ∈ G.rows.toList) {o : Nat}
    (ho : o ∈ r.oracles) : o < S.oracles.size :=
  (h.groups g G hG).there o (named_is_member h hG hr ho)

/-! ## 2 Six of the eight -/

/-- **The six tests on the first chain's end that are left**, each with its name. -/
def firstSixClauses (h : Handed) : List (String × Bool) :=
  [("the first chain's last statement is tidy", Means.tidy4B h.st),
   ("the first chain's book fits", bookFitsB h.book),
   ("one pending row, and its row weights are lawful",
      match h.pending with
      | [r] => r.g.all (·.ok)
      | _ => false),
   ("the own group that was handed has two members",
      match h.st.groups[h.own]? with
      | some G => G.members.size == 2
      | none => false),
   ("each of the two has one sample row",
      match h.st.groups[h.own]? with
      | some G => G.members.toList.all fun i =>
          match h.st.oracles[i]? with
          | some x => x.sampleRows.size == 1
          | none => false
      | none => false),
   ("the own group has an open row",
      match h.st.groups[h.own]? with
      | some G => !G.rows.isEmpty
      | none => false)]

def firstSixB (h : Handed) : Bool := (firstSixClauses h).all (·.2)

/-- With a mask's number handed, the six give the eight. -/
theorem firstDoorB_of_six {h : Handed} (h6 : firstSixB h = true) (hm : h.mask.isSome = true) :
    firstDoorB h = true := by
  simp only [firstSixB, firstSixClauses, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at h6
  obtain ⟨a1, a2, a3, a4, a5, a7⟩ := h6
  simp only [firstDoorB, firstDoorClauses, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  refine ⟨a1, a2, a3, a4, a5, ?_, a7, hm⟩
  cases hG : h.st.groups[h.own]? with
  | none =>
    rw [hG] at a7
    cases a7
  | some G =>
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact fun r hr o ho => named_is_there (Means.tidy4B_iff.1 a1).inOrder hG hr ho

/-! ## 3 The door from less -/

variable {P S₁ Str : Type} (p : P₁₄) (R : List Fmt.DeclaredRound) (fs : P × S₁ → First.S)

/-- **What is left owed at the door.** -/
structure DoorOwedLess (On₂ : ((P × S₁) × St) × Str → Prop) (start₃ : P → S₁ → St → Option S₃) :
    Prop where
  /-- inside the shared chain's last promise, where the start says yes: the six say yes -/
  first : ∀ b s, On₂ b → start₃ b.1.1.1 b.1.1.2 b.1.2 = some s →
    ∀ f, firstOfS (fs b.1.1) = some f → firstSixB f = true
  shared : ∀ b s, On₂ b → start₃ b.1.1.1 b.1.1.2 b.1.2 = some s →
    ∀ e, _root_.Desc.K14.ended b.1.2 = some e → sharedDoorB p (sharedOfEnd e) = true
  start : ∀ pub s₁ d s, start₃ pub s₁ d = some s →
    ∃ e, _root_.Desc.K14.ended d = some e ∧ startAtEnds p pub (fs (pub, s₁)) e = .ok s
  /-- the plan's shape sends the masks ahead -/
  ahead : p.S.masksAhead = true

variable {p R fs}

/-- **The four give the three.** -/
theorem doorOwed_of_less {On₂ : ((P × S₁) × St) × Str → Prop} {start₃ : P → S₁ → St → Option S₃}
    (H : DoorOwedLess p fs On₂ start₃) : DoorOwed p fs On₂ start₃ where
  first := fun b s hb hs f hf => by
    obtain ⟨e, _, h₀⟩ := H.start _ _ _ _ hs
    unfold startAtEnds start₃F at h₀
    have hf' : firstOfS (fs (b.1.1.1, b.1.1.2)) = some f := hf
    rw [hf'] at h₀
    exact firstDoorB_of_six (H.first b s hb hs f hf)
      ((start_mask_ahead _ _ _ _ _ _ _ _ _ _ _ h₀).trans H.ahead)
  shared := H.shared
  start := H.start

/-- **THE DOOR AT `fillZ`, FROM LESS.** -/
theorem door_fillZ_less {On₂ : ((P × S₁) × St) × Str → Prop} {start₃ : P → S₁ → St → Option S₃}
    (H : DoorOwedLess p fs On₂ start₃) (b : ((P × S₁) × St) × Str) (s : S₃) (hb : On₂ b)
    (hs : start₃ b.1.1.1 b.1.1.2 b.1.2 = some s) :
    (fillZ p R fs).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true :=
  door_fillZ (doorOwed_of_less H) b s hb hs

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.named_is_member
#print axioms VerifiableInference.Desc.Last.named_is_there
#print axioms VerifiableInference.Desc.Last.firstDoorB_of_six
#print axioms VerifiableInference.Desc.Last.doorOwed_of_less
#print axioms VerifiableInference.Desc.Last.door_fillZ_less
