-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Slots/RunsSpare.lean: K4's TWO LISTINGS OF CLAIMS, FROM A LEDGER WITH ARRAYS OF THE
RIGHT SIZES, TURN NEITHER THE MARK NOR THE SHOWN VALUE NOR THE FACTOR OF A SLOT OUTSIDE THREE
WINDOWS; AND WHERE TWO OF THE THREE WINDOWS LIE. The twin, for `formsFrontWith` and
`formsBack` (OnBytes/Desc/First/K4/Plain.lean), of HearSpares.lean's statement on the hearing. A
definition, statements and proofs, off `formsFrontWith_some`, `formsBack_some`
(OnBytes/Desc/First/K4/ClaimsLaws.lean), `hearNorms_calls`, `hearTerms_keeps`, `hear_parts` and
`hear_of_flat`, `mergeHear_inv` (Johnson/Top/H0/MergeLaw/Flat.lean, Hear.lean).

  `InWin p j`: slot j lies in the window of the sumcheck p: p.first ≤ j < p.first + the number of
    members of `p.walk.1`.
  `win_same`: laying a sumcheck's window turns nothing outside it, and not the ledger's next.
  **`formsFront_same`**: from a ledger F with arrays of the right sizes to G: G has them; G.next =
    F.next; outside the windows of the row products' token sumcheck and of the lookup's leaves'
    sumcheck each slot holds in G what it holds in F (`SameAt`).
  **`formsBack_same`**: the same, outside the merge's window.
  **`hear_wins`**: where the hearing returns (o, G, u) from F, F with arrays of the right sizes: the
    window of the row products' token sumcheck and the merge's window lie from F.next on and below
    G.next.
  `merge_next`, **`hear_next`** (from such a ledger): the merge begins at the ledger's next and
    takes 2 lk + 3 slots: so behind the hearing G.next = (the merge's first slot) + 2 lk + 3, lk the
    layout's column bits.
  `formsFront_past`, `formsBack_past`: so, if the windows lie below the ledger's next, every slot
    from that next on holds behind the listing what it held in front.

Limits. ONE DIRECTION, FROM A RETURN. WHERE THE LOOKUP's LEAVES' WINDOW LIES IS NOT SAID HERE: it is
a premise of `formsFront_past` (the lookup's files' to say). On the listings alone: that the
block's runs "front" and "back" lay just these ledgers is `front_ok`, `back_ok`'s
(Johnson/Desc/First/K4/BlockLaws.lean), not called here. Adding the forms to the one equation leaves
the slots (`linsLoop_slots`): not called here. Nothing on soundness.
-/
import Johnson.Road.K4.Slots.HearSpares
import Johnson.Top.H0.MergeLaw.Flat
import OnBytes.Desc.First.K4.ClaimsLaws
import OnBytes.Desc.First.K4.NormsCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.PscRun (Sized Filled Later hideRun_keeps)
open OnBytes.Psc (Weight)
open OnBytes.Desc.First.Grow (Grows)
open VerifiableInference.Desc.First.MergeLaw (hear_of_flat mergeHear_inv)

/-- Slot j lies in the window of the sumcheck p. -/
def InWin (p : Psc) (j : ℕ) : Prop := p.first ≤ j ∧ j < p.first + p.walk.1.length

/-- Laying a sumcheck's window turns nothing outside it. -/
theorem win_same {p : Psc} {F G : Fork} (hF : Sized F)
    (h : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G) :
    Sized G ∧ G.next = F.next ∧ ∀ j, ¬ InWin p j → SameAt F G j := by
  obtain ⟨s, n, q⟩ := run_same hF h
  refine ⟨s, n, fun j hj => q j ?_⟩
  rw [Array.size_replicate]
  unfold InWin at hj
  omega

/-- **The listing in front.** -/
theorem formsFront_same {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F G : Fork} {fs : Array Aff}
    (hF : Sized F) (h : formsFrontWith rows P g o F = some (fs, G)) :
    Sized G ∧ G.next = F.next ∧
      ∀ j, ¬ InWin o.H.tV.p j → ¬ InWin o.H.fo.leaves j → SameAt F G j := by
  obtain ⟨_, _, _, F1, F2, _, _, _, _, r1, r2, e⟩ := formsFrontWith_some h
  obtain ⟨s1, n1, q1⟩ := win_same hF r1
  obtain ⟨s2, n2, q2⟩ := win_same s1 r2
  have k : Sized G ∧ G.next = F2.next ∧ ∀ j, SameAt F2 G j := by
    rw [e]
    split
    · exact ⟨s2, rfl, fun _ => ⟨Iff.rfl, rfl, rfl⟩⟩
    · exact ⟨s2, rfl, fun _ => ⟨Iff.rfl, rfl, rfl⟩⟩
  exact ⟨k.1, k.2.1.trans (n2.trans n1), fun j h1 h2 =>
    ((q1 j h1).trans (q2 j h2)).trans (k.2.2 j)⟩

/-- **The listing behind.** -/
theorem formsBack_same {o : Own} {F G : Fork} {fs : Array Aff} (hF : Sized F)
    (h : formsBack o F = some (fs, G)) :
    Sized G ∧ G.next = F.next ∧ ∀ j, ¬ InWin o.wo.toWsMerged.p j → SameAt F G j := by
  obtain ⟨F1, _, r1, e⟩ := formsBack_some h
  obtain ⟨s1, n1, q1⟩ := win_same hF r1
  rw [e]
  exact ⟨s1, n1, fun j hj => (q1 j hj).trans ⟨Iff.rfl, rfl, rfl⟩⟩

/-- **Where two of the three windows lie**, behind a hearing from a ledger with arrays of the right
sizes. -/
theorem hear_wins {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork}
    {t u : Tape} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    (F.next ≤ o.H.tV.p.first ∧ o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ G.next) ∧
      (F.next ≤ o.wo.toWsMerged.p.first ∧
        o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ G.next) := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, hN, hT, hS, hG, _, hM,
    _, _, hE⟩ := hear_parts h
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, p1, p2, p3, _, cW,
    bW, rhoI, pI, cL, cP, bP, cT, _⟩ := hearNorms_calls hN
  have L1 : Later F F1 := Grows.later p1
  have L2 : Later F1 F2 := Grows.later p2
  have L3 : Later F2 F3 := Grows.later p3
  have L4 : Later F3 F4 := Grows.later cW
  have L5 : Later F4 F5 := Grows.later bW
  have L6 : Later F5 F6 := Grows.later pI
  have L7 : Later F6 F7 := Grows.later cL
  have L8 : Later F7 F8 := Grows.later cP
  have L9 : Later F8 F9 := Grows.later bP
  have L09 : Later F F9 :=
    L1.trans (L2.trans (L3.trans (L4.trans (L5.trans (L6.trans (L7.trans (L8.trans L9)))))))
  obtain ⟨_, f9, a1, a2⟩ := tsc_win (L09.sized hF) cT
  have M2 : Later G1 G2 := Grows.later hT
  have M3 : Later G2 G3 := Grows.later hS
  have M4 : Later G3 G4 := Grows.later hG
  have M5 : G4.next ≤ G5.next := by
    unfold mergeFront at hM
    by_cases hg : (g == 0) = true
    · rw [if_pos hg] at hM
      exact (Grows.later hM : Later G4 G5).next
    · rw [if_neg hg] at hM
      rw [hM.2.1]
  have M6 : Later G5 G := Grows.later hE
  have eV : o.H.tV = H1.tV := (hearTerms_keeps hT).2.2.2.2.2.2.2.2.2.2
  obtain ⟨_, _, _, _, beta, v, _, _, _, _, qs, _, _, _, _, _, _, _, _, _, _, _, hh, _, _, hvars,
    hfirst, _⟩ := mergeHear_inv (hear_of_flat hE)
  have h3 : ∀ w ∈ List.replicate P.wsLay.lk (Weight.plain 3), w.d = 3 := fun w hw => by
    obtain rfl := List.eq_of_mem_replicate hw
    rfl
  have hw := win_three o.wo.toWsMerged.p _ 1 h3 hvars
  rw [List.length_replicate] at hw
  have b1 : G5.next + 1 + 2 * P.wsLay.lk + 2 ≤ G.next := (hideRun_keeps hh).next
  have n09 := L09.next
  have n9 := f9.next
  have n2 := M2.next
  have n3 := M3.next
  have n4 := M4.next
  have n6 := M6.next
  rw [eV]
  exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- From a ledger with arrays of the right sizes the merge begins at the ledger's next and takes
2 lk + 3 slots. (`flatForkEnd_slots`, Johnson/Road/K4/HearSlotsEnd.lean, says this
and more.) -/
theorem merge_next {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (hF : Sized F) (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    wo.toWsMerged.p.first = F.next ∧ G.next = F.next + (2 * lay.lk + 3) := by
  obtain ⟨_, _, _, _, beta, v, _, _, _, _, qs, _, _, _, _, _, _, _, _, _, _, _, hh, _, _, _,
    hfirst, _⟩ := mergeHear_inv (hear_of_flat h)
  obtain ⟨_, n, _⟩ :=
    run_same (show Sized ({ F with next := F.next + 1 + 2 * lay.lk + 2 } : Fork) from hF) hh
  have n' : G.next = F.next + 1 + 2 * lay.lk + 2 := n
  exact ⟨hfirst, by omega⟩

/-- **The ledger's next behind the hearing**, from a ledger with arrays of the right sizes. -/
theorem hear_next {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork}
    {t u : Tape} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    G.next = o.wo.toWsMerged.p.first + (2 * P.wsLay.lk + 3) := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, hN, hT, hS, hG, _, hM,
    _, _, hE⟩ := hear_parts h
  obtain ⟨s1, _⟩ := Spares.fresh hN hF
  obtain ⟨s2, _⟩ := Spares.fresh hT s1
  obtain ⟨s3, _⟩ := Spares.fresh hS s2
  obtain ⟨s4, _⟩ := Spares.fresh hG s3
  obtain ⟨s5, _, _⟩ := front_fills s4 hM
  obtain ⟨a, b⟩ := merge_next s5 hE
  rw [a, b]

/-- From the ledger's next on, the listing in front turns nothing, if its two windows lie below. -/
theorem formsFront_past {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F G : Fork} {fs : Array Aff}
    (hF : Sized F) (h : formsFrontWith rows P g o F = some (fs, G))
    (w1 : o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ F.next)
    (w2 : o.H.fo.leaves.first + o.H.fo.leaves.walk.1.length ≤ F.next) :
    Sized G ∧ G.next = F.next ∧ ∀ j, F.next ≤ j → SameAt F G j := by
  obtain ⟨s, n, q⟩ := formsFront_same hF h
  refine ⟨s, n, fun j hj => q j ?_ ?_⟩
  · unfold InWin
    omega
  · unfold InWin
    omega

/-- From the ledger's next on, the listing behind turns nothing, if the merge's window lies
below. -/
theorem formsBack_past {o : Own} {F G : Fork} {fs : Array Aff} (hF : Sized F)
    (h : formsBack o F = some (fs, G))
    (w : o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ F.next) :
    Sized G ∧ G.next = F.next ∧ ∀ j, F.next ≤ j → SameAt F G j := by
  obtain ⟨s, n, q⟩ := formsBack_same hF h
  refine ⟨s, n, fun j hj => q j ?_⟩
  unfold InWin
  omega

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.formsFront_same
#print axioms OnBytes.Desc.First.K4.Slots.formsBack_same
#print axioms OnBytes.Desc.First.K4.Slots.hear_wins
#print axioms OnBytes.Desc.First.K4.Slots.hear_next
#print axioms OnBytes.Desc.First.K4.Slots.formsFront_past
#print axioms OnBytes.Desc.First.K4.Slots.formsBack_past
