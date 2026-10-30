-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlanKeyB.lean: THE CLOSED FACTS ON THE PLAN THAT `hF_of_door`
(HFOfDoor.lean) STILL ASKS BESIDE HFDoorB.lean's TESTS, AS TESTS WITH CODE, EACH WITH ITS LAW: «the
seat's tree is the first tree of the frame's list with the listed tree's key» (so the reading by key
is Strs.col there: `PlanAt`'s fourth clause; hforc) and «below the base» (so the strings stay: hy |
hyF). Definitions and theorems. No text already in the library turns.

  `seatKeyB all key Lp o seat`: the plan's list places o in a tree tp, and the first tree of `all`
    with the key tp has the number seat.1. `reads_of_keyB`: then K2.orcY all key Y tp x = Y.col
    seat.1 x at every x: `planAt_of_B`'s premise hr.
  `planAt_of_Bs`: **planPubB · seatKeyB ⊢ PlanAt G t Lp (K2.orcY all key Y) Y o seat a**: PlanAt
    whole from two tests.
  `freshTree all key Lp fresh`: the fresh mask's tree, as a term with code. `freshKeyB`: it is
    there. `fresh_reads`: then hforc at tree := freshTree ….
  `belowB base js`, `belowB_says`: every number of the list is below the base.
Limits. Tests and their laws. No test has been evaluated here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HFDoorB
import Johnson.Desc.First.Link.Law.StaysAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound

/-- The seat's tree is the first tree of the list with the listed tree's key. -/
def seatKeyB (all : List LeftT) (key : ℕ → ℕ) (Lp : VerifiableInference.Desc.K12.Door.Laid)
    (o : ℕ) (seat : ℕ × ℕ) : Bool :=
  match Lp.places[o]? with
  | some q => decide (((all.find? fun L => key L.no == q.1).map (·.no)) = some seat.1)
  | none => false

theorem reads_of_keyB {all : List LeftT} {key : ℕ → ℕ}
    {Lp : VerifiableInference.Desc.K12.Door.Laid} {o : ℕ} {seat : ℕ × ℕ}
    (h : seatKeyB all key Lp o seat = true) (Y : Strs) (tp : ℕ)
    (hq : Lp.places[o]? = some (tp, seat.2)) (x : ℕ) :
    First.K2.orcY all key Y tp x = Y.col seat.1 x := by
  unfold seatKeyB at h
  simp only [hq, decide_eq_true_eq] at h
  obtain ⟨L, h1, h2⟩ := Option.map_eq_some_iff.1 h
  rw [orcY_at h1, h2]

/-- **PlanAt, WHOLE, FROM TWO TESTS.** -/
theorem planAt_of_Bs {Xi : Type} {G : FileDescription Xi} {t : First.S}
    {Lp : VerifiableInference.Desc.K12.Door.Laid} {o : ℕ} {seat : ℕ × ℕ} {a : ℕ}
    {all : List LeftT} {key : ℕ → ℕ} (h1 : planPubB G t Lp o seat a = true)
    (h2 : seatKeyB all key Lp o seat = true) (Y : Strs) :
    PlanAt G t Lp (First.K2.orcY all key Y) Y o seat a :=
  planAt_of_B h1 _ Y fun tp hq x _ => reads_of_keyB h2 Y tp hq x

/-- The fresh mask's tree: the first tree of the list with the key of the tree in which the plan's
list places the fresh mask; 0 where there is none. -/
def freshTree (all : List LeftT) (key : ℕ → ℕ) (Lp : VerifiableInference.Desc.K12.Door.Laid)
    (fresh : ℕ) : ℕ :=
  (((Lp.places[fresh]?).bind fun q => all.find? fun L => key L.no == q.1).map (·.no)).getD 0

def freshKeyB (all : List LeftT) (key : ℕ → ℕ) (Lp : VerifiableInference.Desc.K12.Door.Laid)
    (fresh : ℕ) : Bool :=
  ((Lp.places[fresh]?).bind fun q => all.find? fun L => key L.no == q.1).isSome

theorem fresh_reads {all : List LeftT} {key : ℕ → ℕ}
    {Lp : VerifiableInference.Desc.K12.Door.Laid} {fresh : ℕ}
    (h : freshKeyB all key Lp fresh = true) (Y : Strs) (tpF tnF : ℕ)
    (hq : Lp.places[fresh]? = some (tpF, tnF)) (x : ℕ) :
    First.K2.orcY all key Y tpF x = Y.col (freshTree all key Lp fresh) x := by
  unfold freshKeyB at h
  rw [hq, Option.bind_some] at h
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.1 h
  have e : freshTree all key Lp fresh = L.no := by
    unfold freshTree
    rw [hq, Option.bind_some, hL]
    rfl
  rw [e]
  exact orcY_at hL Y x

def belowB (base : ℕ) (js : List ℕ) : Bool := js.all fun j => decide (j < base)

theorem belowB_says {base : ℕ} {js : List ℕ} (h : belowB base js = true) (j : ℕ) (hj : j ∈ js) :
    j < base := of_decide_eq_true (List.all_eq_true.1 h j hj)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.reads_of_keyB
#print axioms VerifiableInference.Desc.LinkJoin.planAt_of_Bs
#print axioms VerifiableInference.Desc.LinkJoin.fresh_reads
#print axioms VerifiableInference.Desc.LinkJoin.belowB_says
