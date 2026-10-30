-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/SeatsNamedKey.lean: the test `P5J.seatsNamedC` (Johnson/P5J/SeatsNamedC.lean) at
the numbering and the numbers off one list of seats (`P5T.arrOf ps`, `P5T.numOfPlan ps`) is a test
on the seats' keys. The list of keys without repeats, which both functions make anew at every call,
falls out. And the test reads the public data through the view of their shape
alone.

Row or tool. General laws, at every list of seats, all numbers, every layout and every X. No written
value is named; nothing is evaluated.

Why. `namedOnce arr N k n` counts the seats x of segment k's group with `arr x = n`. At `arrOf ps`
and `numOfPlan ps l m` both sides are places in one list without repeats: that of the key of the
seat at x, and that of the key (0, l, m). Two members of such a list have one place only if they are
one.

What is here.
  `groupsFound ps N`: a test: every seat of the 25 segments' groups is a seat of the list.
  `keyHeldOnce ps N k key`: just one seat of segment k's group holds the key.
  `namedOnce_key`: `namedOnce (arrOf ps) N k (numOfPlan ps l m) = keyHeldOnce ps N k (0, l, m)`,
    where the group's seats are found.
  `seatsKeyV V layout ps N`: the text of `seatsNamedC` with `keyHeldOnce`, read off a view.
  `seatsNamedC_view`: under `groupsFound`, and where attention is there and there are twelve groups
    of layers: `seatsNamedC X (sizesOf X) layout (numOfPlan ps) (arrOf ps) N = seatsKeyV (xShapeOf
    X) layout ps N`.
  `group_same`, `seatsNamedC_same`: the test reads the numbers through their field `sent` alone.

Limits. As at `seatsNamedC`: a segment whose tail is empty adds no entry. Nothing on soundness.


-/
import Johnson.HB.LLHARD.TailAtView
import Johnson.P5J.SeatsNamedC
import Johnson.P5T.NumOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc (arrayOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (namedOnce)
open VerifiableInference.PlanWritten (XShape xShapeOf)
open Meaning (nameOf labAt ownerK ownerA sizesOf viewTail viewEntry viewTail_at viewEntry_at
  all_range_same)
open P5T (PSeat keyOf arrOf numOfPlan arrOf_of_find)

/-- Every seat of the 25 segments' groups is a seat of the list. -/
def groupsFound (ps : List PSeat) (N : Numbers) : Bool :=
  (List.range 25).all fun k => (N.group k).all fun x =>
    (ps.find? fun p => p.j == x.1 && p.t == x.2).isSome

/-- Just one seat of segment k's group holds the key. -/
def keyHeldOnce (ps : List PSeat) (N : Numbers) (k : ℕ) (key : ℕ × ℕ × ℕ) : Bool :=
  ((N.group k).filter fun x =>
    (ps.find? fun p => p.j == x.1 && p.t == x.2).any fun p => keyOf p == key).length == 1

/-- **The list of keys falls out.** -/
theorem namedOnce_key (ps : List PSeat) (N : Numbers) (k l m : ℕ)
    (hG : ∀ x ∈ N.group k, (ps.find? fun p => p.j == x.1 && p.t == x.2).isSome = true) :
    namedOnce (arrOf ps) N k (numOfPlan ps l m) = keyHeldOnce ps N k (0, l, m) := by
  unfold namedOnce keyHeldOnce
  have e : ((N.group k).filter fun x => arrOf ps x.1 x.2 == numOfPlan ps l m) =
      (N.group k).filter fun x =>
        (ps.find? fun p => p.j == x.1 && p.t == x.2).any fun p => keyOf p == (0, l, m) := by
    refine List.filter_congr fun x hx => ?_
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (hG x hx)
    rw [arrOf_of_find ps x.1 x.2 p hp, hp, Option.any_some]
    have hm : keyOf p ∈ (ps.map keyOf).eraseDups :=
      List.mem_eraseDups.2 (List.mem_map.2 ⟨p, List.mem_of_find?_eq_some hp, rfl⟩)
    unfold numOfPlan
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact List.idxOf_inj hm
  rw [e]

/-- **The test's text with the keys, read off a view.** -/
def seatsKeyV (V : XShape) (layout : ReqLayout) (ps : List PSeat) (N : Numbers) : Bool :=
  (List.range 25).all fun k => (List.range (viewTail V k).1).all fun a =>
    match arrayOf layout (ownerK (viewEntry V k a).1) (nameOf (ownerA (viewEntry V k a).1)) with
    | none => false
    | some A => keyHeldOnce ps N k (0, ownerK (viewEntry V k a).1, A.message)

/-- **The test, off the view and the keys.** -/
theorem seatsNamedC_view {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (layout : ReqLayout) {ps : List PSeat} {N : Numbers} (hG : groupsFound ps N = true) :
    seatsNamedC X (sizesOf X) layout (numOfPlan ps) (arrOf ps) N =
      seatsKeyV (xShapeOf X) layout ps N := by
  unfold seatsNamedC seatsKeyV
  refine all_range_same fun k hk => ?_
  have hGk : ∀ x ∈ N.group k, (ps.find? fun p => p.j == x.1 && p.t == x.2).isSome = true :=
    List.all_eq_true.1 (List.all_eq_true.1 hG k (List.mem_range.2 hk))
  have e1 : (viewTail (xShapeOf X) k).1 = (sizesOf X k).NM := by
    rw [viewTail_at h4 hN hk]
    rfl
  rw [e1]
  refine all_range_same fun a _ => ?_
  rw [viewEntry_at h4 hN hk a]
  cases arrayOf layout (ownerK (labAt X k a)) (nameOf (ownerA (labAt X k a))) with
  | none => rfl
  | some A => exact namedOnce_key ps N k _ _ hGk

/-- The groups hang on the field `sent` alone. -/
theorem group_same {N N' : Numbers} (h : N.sent = N'.sent) (k : ℕ) : N.group k = N'.group k := by
  unfold Numbers.group
  rw [h]

theorem seatsNamedC_same {X : Verify.Public} {s : ℕ → Cb.Pv.Tail.Size} {layout : ReqLayout}
    {num arr : ℕ → ℕ → ℕ} {N N' : Numbers} (h : N.sent = N'.sent) :
    seatsNamedC X s layout num arr N = seatsNamedC X s layout num arr N' := by
  unfold seatsNamedC namedOnce
  simp only [group_same h]

end P5J

#print axioms P5J.namedOnce_key
#print axioms P5J.seatsNamedC_view
#print axioms P5J.group_same
#print axioms P5J.seatsNamedC_same
