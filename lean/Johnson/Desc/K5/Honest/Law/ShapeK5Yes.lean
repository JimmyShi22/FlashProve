-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ShapeK5Yes.lean: THE ONE BOOL OF THE KIND "AN ATTENTION SEGMENT's OWN
ROUNDS" (`k5G`, Johnson/Desc/K5/Honest/Law/ShapeK5.lean) CAN SAY YES, AND AT A STATE's SHAPE IT SAYS
JUST WHAT THE LIBRARY's `ReadyO` SAYS OF THE STATE. Over the library and the shapes alone.
Statements with their proofs.

Why. The two laws of Law/ShapeK5.lean take the Bool's yes as a premise, and its controls all end in
a no. Where the Bool said yes nowhere the two laws would hold of nothing.

Main names:
  `k5G_yes`      the Bool says yes at a shape that is typed by hand, for every plan's numbers
  `freeB_of`     the test with code on the ledger's shape, from the two premises of the library's
                 laws
  `G_of_readyO`, `k5G_iff`   **k5G p.own (k5Sh s) = true ↔ ReadyO p s**

Conditional on: `freeB_of`: the arrays' lengths; the slots are there and free. `G_of_readyO`:
`ReadyO`. The two others: on nothing.
Limits. `k5G_yes` speaks of a made-up shape: it is the shape of no state that is shown to be
reached, and of no state at all by this file. `k5G_iff` carries the question "is it ever yes" to
`ReadyO` (Johnson/Desc/First/Att/K05SeatAccepts.lean); it does not answer it. On that question:
Johnson/Desc/ProofFile/Honest/K5/Law/Ready.lean (`readyO_of_thr`: from the first chain's thread in
front of the kind's member, under a hypothesis on the public input) and Law/ReadyToy.lean (an
evaluation at a made-up plan).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ShapeK5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Free)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.First.Shape (AttOwnSh attOwnSh LedSh ledSh freeB sizedB)

/-- **THE BOOL SAYS YES AT A SHAPE**, for every plan's numbers x: a made-up shape: no mark; no count
of rows; the lookup has laid; a ledger with just the N slots that the rounds take, all free, the
next free number 0, and nothing else; an attention link in which nothing is laid. So the Bool is not
false everywhere. The shape is typed by hand: it is the shape of no state that is shown to be
reached. -/
theorem k5G_yes (x : Params.AttentionRounds) :
    k5G x
      { marked := false, rowsOwed := none, look := true
        led := some (LedSh.mk (slotsOf (script x)) (slotsOf (script x)) (slotsOf (script x))
          (List.replicate (slotsOf (script x)) false) [] 0 [] 0 0 0 false [] false)
        att := some { planes := false, scores := false, heard5 := none } } = true := by
  simp [k5G, noneWaitsB, freeB, sizedB, LedSh.mk, LedSh.next, LedSh.ns, LedSh.shown, LedSh.factors,
    LedSh.got]

/-- The test with code on the ledger's shape, from the two premises of the library's laws. -/
theorem freeB_of {F : Fork} {n : Nat} (hz : Sized F) (hfree : Free F F.next n) :
    freeB (ledSh F) (ledSh F).next n = true := by
  have e1 : sizedB (ledSh F) = true := by
    simp only [sizedB, ledSh, LedSh.mk, LedSh.shown, LedSh.ns, LedSh.factors, LedSh.got,
      Bool.and_eq_true, beq_iff_eq, Array.length_toList]
    exact ⟨⟨hz.vp, hz.mf⟩, hz.got⟩
  have e2 : F.next + n ≤ F.ns := hfree.2.1
  have e3 : ((F.gotF.toList.drop F.next).take n).all (!·) = true := by
    rw [List.all_eq_true]
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hb
    have hi' : i < n ∧ F.next + i < F.gotF.size := by
      simp only [List.length_take, List.length_drop, Array.length_toList] at hi
      omega
    have k := hfree.2.2 (F.next + i) (Nat.le_add_right _ _) (by omega)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi'.2] at k
    simp only [List.getElem_take, List.getElem_drop, Array.getElem_toList]
    simpa using k
  unfold freeB
  rw [e1]
  show (true && Decidable.decide (F.next + n ≤ F.ns) &&
    ((F.gotF.toList.drop F.next).take n).all (!·)) = true
  rw [e3, decide_eq_true e2]
  rfl

/-- **Where the state is ready the Bool says yes** (`ReadyO`,
Johnson/Desc/First/Att/K05SeatAccepts.lean). -/
theorem G_of_readyO (p : Par) {s : First.S} (R : ReadyO p s) : k5G p.own (k5Sh s) = true := by
  obtain ⟨a, g, ha, hg, h5, hz, hfree⟩ := R.open_
  rw [k5Sh_att ha]
  have e1 : s.failed.isSome = false := by rw [R.clean]; rfl
  have e2 : noneWaitsB s.rowsOwed = true := R.none_
  have e3 : a.g.isSome = true := by rw [hg]; rfl
  have e4 : (attOwnSh a).heard5.isNone = true := by
    show (a.heard5.map _).isNone = true
    rw [h5]
    rfl
  simp only [k5G, e1, e2, e3, e4, freeB_of hz hfree, Bool.not_false, Bool.and_self]

/-- **THE BOOL AT A STATE's SHAPE SAYS JUST WHAT THE LIBRARY's `ReadyO` SAYS OF THE STATE.** -/
theorem k5G_iff (p : Par) (s : First.S) : k5G p.own (k5Sh s) = true ↔ ReadyO p s := by
  exact ⟨readyO_of_G p, G_of_readyO p⟩

end H2K5.Honest

#print axioms H2K5.Honest.k5G_yes
#print axioms H2K5.Honest.freeB_of
#print axioms H2K5.Honest.G_of_readyO
#print axioms H2K5.Honest.k5G_iff
