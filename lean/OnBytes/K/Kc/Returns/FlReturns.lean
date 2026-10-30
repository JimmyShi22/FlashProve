--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Kc/Returns/FlReturns.lean: the flat hearing functions return, first part: the steps. The
other direction of every "taken apart where it returns" lemma on OnBytes/K/Kc/Flat.lean: on a tape
of the right shape, from a ledger with room, a function returns. Definitions, statements and proofs.
Functions Fork -> Tape -> Option; no routine in a context.

Every test that these functions make, function by function, read off the text, and what it reads:
  recv, recvN   the open message still holds the elements that are asked for.       [number sent]
  closeN        the round's name; its number of never-0 draws; nothing left in the message;
                n elements drawn.                                          [three words; numbers]
  closeOne      the same, with just one element drawn.                     [three words; numbers]
  closeRows     the name of the round that batches rows; no never-0 draw; the round's number of
                rows; one element drawn.                                   [three words; numbers]
  batchOn       rows is not 0.                                                    [public number]
  claimsIn      must (v.size == n): holds behind recvN. hideRun: the n slots are there and free.
                                                                                         [ledger]
  pscBegin      publicPart C: every slot that C names is there and filled.               [ledger]
  pscRound      the two tests of the round's weight: its sizes fit; it is held. At an equality
                weight the first is "d is at least 2", and the second, which computes on the
                coordinate z (a drawn value at most callers), holds at every z
                (weightHeld_equality). must (sent.size + 1 == w.d).        [public; number sent]
  roundIn       must (!p.ended); the form admits the degree (.eq2 always does).
                                                                              [the record's flag]
  pscEnds       must (!p.ended, 1 <= degreeInY, 1 <= n); must (v.size == n); hideRun.
                                                                           [flag; public; ledger]
  pscRow        must (!p.rowMade, p.started, some variable, as many challenges as variables);
                hideRun at the sumcheck's own slots.                              [flags; ledger]
No test reads a sent value. Of drawn values the test that a weight is held alone reads one, and it
holds at all. The word "never-0 draws" is a number in the tape's round: that such a draw is not 0 no
flat function tests (Flat.lean's own head).

Main names:
  bindR, pureR, mustR, needR, askR, changeR, onTapeR, takeSlotsR: how returns compose.
  recvN_mk, closeOne_mk, closeN_mk, closeRows_mk, emptyOn_mk: the tape's steps on a written-out
    round.
  hideRun_free, publicPart_some: the ledger's steps.
  `Room F n`: the ledger's arrays have their size, n more slots fit, every slot from F.next on is
    free.
  `Mid p F n`: a sumcheck in course: its flags, its slots taken and still free, room for n more.
  `Ended p G e n k`: behind its end values.
  takeHide, claimsInR, batchR, pointR, pscBeginR, pscRoundR, roundInR, pscEndsR, pscRowR.

Sources. recvLoop_mk, closeOne_mk, emptyOn_mk and the way of the proofs of pscBeginR, pscRoundR,
pscEndsR: after Johnson/Top/H/P1Tie/FlatMk.lean. hide_free, hideSteps_free, hideRun_free: copied
from Johnson/Desc/First/ProdV/Returns.lean [not in this library]; publicLoop_some, publicPart_some:
from Johnson/Desc/First/ProdV/NonEmptyRun.lean [not in this library]. Lemmas taken:
OnBytes/Tie/Pv/Psc/PscFork.lean hide_ok, hideRun_ok, Sized, Filled, Same;
OnBytes/Tie/Pv/Psc/PscLater.lean shown_iff; OnBytes/Tie/Pv/Psc/PscHeld.lean fits_equality,
weightHeld_equality; OnBytes/G4/RunLaws.lean hidingWalk_length; OnBytes/Chain/Lists.lean zipT_eq.

Limits. It says "returns", not "returns what": what the returned value and ledger are, beyond what
is needed to go on, the lemmas "from a return" say. Equality weights alone in this file. The
statements hold of every tape of the right shape: whether a prover is honest does not enter.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.Flat
import OnBytes.Tie.Pv.Psc.PscLater
import OnBytes.Tie.Pv.Psc.PscHeld
import OnBytes.G4.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Ret
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun

variable {α β : Type}

/-! ## 0. How returns compose -/

theorem bindR {x : Fl α} {f : α → Fl β} {F G : Fork} {t u : Tape} {a : α}
    {r : Option (β × Fork × Tape)} (h : x F t = some (a, G, u)) (h' : f a G u = r) :
    (x >>= f) F t = r := by
  show Fl.andThen x f F t = r
  unfold Fl.andThen
  rw [h]
  exact h'

theorem pureR (a : α) (F : Fork) (t : Tape) : (pure a : Fl α) F t = some (a, F, t) := rfl

theorem mustR {b : Bool} (h : b = true) (F : Fork) (t : Tape) :
    Fl.must b F t = some ((), F, t) := by
  unfold Fl.must
  rw [if_pos h]

theorem needR {x : Option α} {a : α} (h : x = some a) (F : Fork) (t : Tape) :
    Fl.need x F t = some (a, F, t) := by
  unfold Fl.need
  rw [h]
  rfl

theorem askR {f : Fork → Option α} {F : Fork} {a : α} (h : f F = some a) (t : Tape) :
    Fl.ask f F t = some (a, F, t) := by
  unfold Fl.ask
  rw [h]
  rfl

theorem changeR {f : Fork → Option Fork} {F G : Fork} (h : f F = some G) (t : Tape) :
    Fl.change f F t = some ((), G, t) := by
  unfold Fl.change
  rw [h]
  rfl

theorem onTapeR {g : Tape → Option (α × Tape)} {t u : Tape} {a : α} (h : g t = some (a, u))
    (F : Fork) : Fl.onTape g F t = some (a, F, u) := by
  unfold Fl.onTape
  rw [h]
  rfl

theorem takeSlotsR (n : Nat) (F : Fork) (t : Tape) :
    Fl.takeSlots n F t = some (F.next, { F with next := F.next + n }, t) := rfl

/-! ## 1. The tape's steps on a written-out round -/

theorem recvLoop_mk (nm : Option String) (z w : Nat) (d : List E) (t : Tape) :
    ∀ (xs : List E) (a : Array E) (s : List E),
    recvLoop xs.length a (⟨nm, z, w, xs ++ s, d⟩ :: t) =
      some ((a.toList ++ xs).toArray, ⟨nm, z, w, s, d⟩ :: t)
  | [], a, s => by
    show some (a, (⟨nm, z, w, s, d⟩ : FlatRound) :: t) =
      some ((a.toList ++ []).toArray, ⟨nm, z, w, s, d⟩ :: t)
    simp
  | x :: xs, a, s => by
    show recvLoop xs.length (a.push x) (⟨nm, z, w, xs ++ s, d⟩ :: t) = _
    rw [recvLoop_mk nm z w d t xs (a.push x) s]
    simp

/-- The first elements of the open message are taken; s is left. -/
theorem recvN_mk (nm : Option String) (z w : Nat) (d : List E) (t : Tape) (xs s : List E) :
    recvN xs.length (⟨nm, z, w, xs ++ s, d⟩ :: t) = some (xs.toArray, ⟨nm, z, w, s, d⟩ :: t) := by
  have h := recvLoop_mk nm z w d t xs (Array.emptyWithCapacity xs.length) s
  unfold recvN
  rw [h]
  rfl

theorem readR (nm : Option String) (z w : Nat) (d : List E) (t : Tape) (xs s : List E) (n : Nat)
    (hn : n = xs.length) (F : Fork) :
    Fl.read n F (⟨nm, z, w, xs ++ s, d⟩ :: t) = some (xs.toArray, F, ⟨nm, z, w, s, d⟩ :: t) := by
  subst hn
  exact onTapeR (recvN_mk nm z w d t xs s) F

theorem closeOne_mk (name : String) (nz w : Nat) (x : E) (t : Tape) :
    closeOne name nz (⟨some name, nz, w, [], [x]⟩ :: t) = some (x, t) := by
  simp [closeOne]

theorem closeN_mk (name : String) (nz w n : Nat) (d : List E) (t : Tape) (h : d.length = n) :
    closeN name nz n (⟨some name, nz, w, [], d⟩ :: t) = some (d, t) := by
  simp [closeN, h]

theorem closeRows_mk (rows : Nat) (x : E) (t : Tape) :
    closeRows rows (⟨some Model.RoundName.batSigma.name, 0, rows, [], [x]⟩ :: t) = some (x, t) := by
  simp [closeRows]

theorem emptyOn_mk (name : String) (w : Nat) (t : Tape) :
    Fl.emptyOn name (⟨some name, 0, w, [], []⟩ :: t) = some ((), t) := by
  simp [Fl.emptyOn, closeN]

/-! ## 2. The ledger's steps -/

theorem hide_free {F : Fork} {j : Nat} (y f : E) (hF : Sized F) (hj : j < F.ns)
    (hfree : ¬ Filled F j) : ∃ G, F.hide j y f = some G := by
  have hs : F.gotF.size = F.ns := hF.2.2
  have hg : F.gotF.getD j true = false := by
    have h1 : F.gotF.getD j false = false := by
      cases hq : F.gotF.getD j false with
      | false => rfl
      | true => exact absurd hq hfree
    have hj' : j < F.gotF.size := by rw [hs]; exact hj
    have e : F.gotF.getD j false = F.gotF.getD j true := by
      simp [Array.getD_eq_getD_getElem?, hj']
    rw [← e]
    exact h1
  unfold Fork.hide
  rw [if_pos (by simp [hj, hs, hg])]
  exact ⟨_, rfl⟩

theorem hideSteps_free (f : E) : ∀ (l : List E) (first : Nat) (F : Fork), Sized F →
    (∀ i, i < l.length → first + i < F.ns ∧ ¬ Filled F (first + i)) →
    ∃ x, l.foldlM (Fork.hideStep f) (first, F) = some x
  | [], first, F, _, _ => ⟨(first, F), rfl⟩
  | y :: l, first, F, hF, h => by
    obtain ⟨h0, h1⟩ := h 0 (by simp)
    rw [Nat.add_zero] at h0 h1
    obtain ⟨G, hG⟩ := hide_free y f hF h0 h1
    obtain ⟨_, _, a3, a4, _, _, _, a7⟩ := hide_ok F G first y f hF hG
    have hstep : Fork.hideStep f (first, F) y = some (first + 1, G) := by
      show (F.hide first y f).map _ = _
      rw [hG]
      rfl
    rw [List.foldlM_cons, hstep]
    refine hideSteps_free f l (first + 1) G a4 fun i hi => ?_
    obtain ⟨b0, b1⟩ := h (i + 1) (by simpa using hi)
    have e : first + 1 + i = first + (i + 1) := by omega
    rw [e]
    refine ⟨by rw [a3.ns]; exact b0, fun hf => b1 ?_⟩
    exact ((a7 (first + (i + 1)) (by omega)).2.2).1 hf

/-- Putting values under free slots returns. -/
theorem hideRun_free {F : Fork} (first : Nat) (v : Array E) (f : E) (hF : Sized F)
    (h : ∀ i, i < v.size → first + i < F.ns ∧ ¬ Filled F (first + i)) :
    ∃ G, F.hideRun first v f = some G := by
  obtain ⟨x, hx⟩ := hideSteps_free f v.toList first F hF (by simpa using h)
  unfold Fork.hideRun
  rw [← Array.foldlM_toList, hx]
  exact ⟨_, rfl⟩

theorem publicLoop_some (F : Fork) : ∀ (l : List (Nat × E)) (v : E),
    (∀ x ∈ l, x.1 < F.ns ∧ Filled F x.1) →
    ∃ t, l.foldlM (fun (v : E) (x : Nat × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y)) v =
      some t
  | [], v, _ => ⟨v, rfl⟩
  | x :: l, v, h => by
    have hs : F.shown x.1 = some (F.vp.getD x.1 zeroE) :=
      (shown_iff F _ _).2 ⟨(h x (by simp)).1, (h x (by simp)).2, rfl⟩
    rw [List.foldlM_cons, hs]
    exact publicLoop_some F l _ fun y hy => h y (by simp [hy])

/-- The public part of a form on slots that are there and filled. -/
theorem publicPart_some (F : Fork) (C : Aff)
    (h : ∀ x ∈ C.slots.toList, x.1 < F.ns ∧ Filled F x.1) : ∃ t, F.publicPart C = some t := by
  unfold Fork.publicPart
  rw [← Array.foldlM_toList]
  exact publicLoop_some F _ _ h

/-- Counting slots as taken turns neither the arrays' sizes nor what is filled. -/
theorem sized_next {F : Fork} {m : Nat} (h : Sized F) : Sized ({ F with next := m } : Fork) :=
  ⟨h.1, h.2.1, h.2.2⟩

theorem filled_next {F : Fork} {m j : Nat} :
    Filled ({ F with next := m } : Fork) j ↔ Filled F j := by
  unfold Filled
  exact Iff.rfl

/-- A ledger with room for n more slots. -/
structure Room (F : Fork) (n : Nat) : Prop where
  sized : Sized F
  fits : F.next + n ≤ F.ns
  free : ∀ j, F.next ≤ j → ¬ Filled F j

theorem Room.mono {F : Fork} {n m : Nat} (h : Room F n) (hm : m ≤ n) : Room F m :=
  ⟨h.sized, by have := h.fits; omega, h.free⟩

/-- n slots are taken and filled: it returns, room for the rest is left, the n slots are filled, and
what lies below is as it was. -/
theorem takeHide {F : Fork} {n k : Nat} (h : Room F (n + k)) (v : Array E) (hv : v.size = n)
    (f : E) :
    ∃ G, ({ F with next := F.next + n } : Fork).hideRun F.next v f = some G ∧ Room G k ∧
      G.next = F.next + n ∧ G.ns = F.ns ∧ (∀ i, i < n → Filled G (F.next + i)) ∧
      ∀ j, j < F.next → (Filled G j ↔ Filled F j) := by
  have hS : Sized ({ F with next := F.next + n } : Fork) := h.sized
  obtain ⟨G, hG⟩ := hideRun_free (F := { F with next := F.next + n }) F.next v f hS (by
    intro i hi
    have := h.fits
    exact ⟨by show F.next + i < F.ns; omega, h.free _ (by omega)⟩)
  obtain ⟨a1, a2, a3, a4⟩ := hideRun_ok _ G F.next v f hS hG
  have hn : G.next = F.next + n := a1.next
  have hns : G.ns = F.ns := a1.ns
  refine ⟨G, hG, ⟨a2, by rw [hn, hns]; have := h.fits; omega, fun j hj hf => ?_⟩, hn, hns,
    fun i hi => (a3 i (by omega)).2.2.1, fun j hj => (a4 j (Or.inl hj)).2.2⟩
  rw [hn] at hj
  exact h.free j (by omega) ((a4 j (Or.inr (by omega))).2.2.1 hf)

/-! ## 3. Outside a sumcheck -/

/-- **n hidden values.** The open message begins with them; s is left of it. -/
theorem claimsInR {F : Fork} {n k : Nat} (h : Room F (n + k)) (nm : Option String) (z w : Nat)
    (xs s d : List E) (t : Tape) (hx : xs.length = n) :
    ∃ G, Fl.claimsIn n F (⟨nm, z, w, xs ++ s, d⟩ :: t) = some (F.next, G, ⟨nm, z, w, s, d⟩ :: t) ∧
      Room G k ∧ G.next = F.next + n ∧ G.ns = F.ns ∧ (∀ i, i < n → Filled G (F.next + i)) ∧
      ∀ j, j < F.next → (Filled G j ↔ Filled F j) := by
  obtain ⟨G, hG, r1, r2, r3, r4, r5⟩ := takeHide h xs.toArray (by simpa using hx) oneE
  refine ⟨G, ?_, r1, r2, r3, r4, r5⟩
  unfold Fl.claimsIn
  refine bindR (readR nm z w d t xs s n hx.symm F) ?_
  refine bindR (mustR (by show (xs.toArray.size == n) = true; simp [hx]) _ _) ?_
  refine bindR (takeSlotsR n F _) ?_
  refine bindR (changeR hG _) ?_
  rfl

/-- **The round that batches rows.** -/
theorem batchR (rows : Nat) (hr : rows ≠ 0) (x : E) (F : Fork) (t : Tape) :
    Fl.batch rows F (⟨some Model.RoundName.batSigma.name, 0, rows, [], [x]⟩ :: t) =
      some (Model.powers x rows, F, t) := by
  refine onTapeR ?_ F
  unfold Fl.batchOn
  rw [if_pos (by simpa using hr), closeRows_mk]
  rfl

/-- **A point of n drawn elements.** -/
theorem pointR (r : Model.RoundName) (n w : Nat) (d : List E) (hd : d.length = n) (F : Fork)
    (t : Tape) : Fl.point r n F (⟨some r.name, 0, w, [], d⟩ :: t) = some (d.toArray, F, t) := by
  refine onTapeR ?_ F
  unfold Fl.pointOn
  rw [closeN_mk _ 0 w n d t hd]
  rfl

/-- **One drawn element.** -/
theorem answerR (r : Model.RoundName) (w : Nat) (x : E) (F : Fork) (t : Tape) :
    Fl.answer r F (⟨some r.name, 0, w, [], [x]⟩ :: t) = some (x, F, t) :=
  onTapeR (closeOne_mk _ 0 w x t) F

/-! ## 4. The masked sumcheck's steps -/

/-- The record behind a round. -/
def stepQ (p : Psc) (w : OnBytes.Psc.Weight) (sent : List E) (r : E) : Psc :=
  { p with claim := OnBytes.Psc.polyAt (w.complete sent p.claim) r, vars := p.vars.push w,
           r := p.r.push r }

/- The record's other fields stay. Stated as rewriting lemmas: left to itself the unifier compares p
with
stepQ p .. field by field and loses itself in the field's arithmetic at "claim". -/
theorem stepQ_ended (p : Psc) (w : OnBytes.Psc.Weight) (sent : List E) (r : E) :
    (stepQ p w sent r).ended = p.ended := by
  unfold stepQ
  rfl

theorem stepQ_rowMade (p : Psc) (w : OnBytes.Psc.Weight) (sent : List E) (r : E) :
    (stepQ p w sent r).rowMade = p.rowMade := by
  unfold stepQ
  rfl

theorem stepQ_started (p : Psc) (w : OnBytes.Psc.Weight) (sent : List E) (r : E) :
    (stepQ p w sent r).started = p.started := by
  unfold stepQ
  rfl

theorem stepQ_first (p : Psc) (w : OnBytes.Psc.Weight) (sent : List E) (r : E) :
    (stepQ p w sent r).first = p.first := by
  unfold stepQ
  rfl

/-- The slots that a sumcheck with these variables has taken. -/
def taken (p : Psc) : Nat := 1 + (p.vars.toList.map fun w => w.d - 1).sum

theorem taken_step (p : Psc) (w : OnBytes.Psc.Weight) (sent : List E) (r : E) :
    taken (stepQ p w sent r) = taken p + (w.d - 1) := by
  unfold taken stepQ
  simp
  omega

/-- A sumcheck in course, with room for n more slots. -/
structure Mid (p : Psc) (F : Fork) (n : Nat) : Prop where
  notEnded : p.ended = false
  noRow : p.rowMade = false
  started : p.started = true
  sizes : p.r.size = p.vars.size
  pos : ∀ w ∈ p.vars.toList, 1 ≤ w.d
  sized : Sized F
  next : F.next = p.first + taken p
  fits : F.next + n ≤ F.ns
  free : ∀ j, p.first ≤ j → ¬ Filled F j

/-- **The beginning.** -/
theorem pscBeginR {F : Fork} {n : Nat} (h : Room F (1 + n)) {C : Aff} {T : E}
    (hT : F.publicPart C = some T) (mu eps : E) (w : Nat) (t : Tape) :
    ∃ p, Fl.pscBegin C F (⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: t) =
        some (p, { F with next := F.next + 1 }, t) ∧
      Mid p { F with next := F.next + 1 } n ∧ p.first = F.next := by
  have h1 : Fl.pscBeginAt T F (⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: t) =
      some ({ target := T, first := F.next, eps := eps, claim := addE mu (mulE eps T) },
        { F with next := F.next + 1 }, t) := by
    unfold Fl.pscBeginAt
    refine bindR (takeSlotsR 1 F _) ?_
    refine bindR (a := mu) (G := { F with next := F.next + 1 })
      (u := ⟨some Model.RoundName.pscEpsilon.name, 0, w, [], [eps]⟩ :: t) rfl ?_
    refine bindR (answerR .pscEpsilon w eps _ t) ?_
    rfl
  refine ⟨{ target := T, first := F.next, eps := eps, claim := addE mu (mulE eps T), start := C,
            started := true }, ?_, ⟨rfl, rfl, rfl, rfl, by simp, h.sized, rfl, ?_, h.free⟩, rfl⟩
  · unfold Fl.pscBegin
    refine bindR (askR hT _) ?_
    refine bindR h1 ?_
    rfl
  · show F.next + 1 + n ≤ F.ns
    have := h.fits
    omega

/-- **One round at an equality weight**, closed under a name. -/
theorem pscRoundR (p : Psc) (z : E) (d : Nat) (hd : 2 ≤ d) (name : String) (nz w : Nat)
    (sent : List E) (x : E) (t : Tape) (F : Fork) (hs : sent.length + 1 = d) :
    Fl.pscRound p (OnBytes.Psc.Weight.equality z d) (closeOne name nz) F
        (⟨some name, nz, w, sent, [x]⟩ :: t) =
      some ((x, stepQ p (OnBytes.Psc.Weight.equality z d) sent x),
        { F with next := F.next + (d - 1) }, t) := by
  have hread := readR (some name) nz w [x] t sent [] (d - 1) (by omega) F
  rw [List.append_nil] at hread
  unfold Fl.pscRound
  refine bindR (mustR (by
    rw [Bool.and_eq_true]
    exact ⟨(fits_equality z d).mpr hd, weightHeld_equality z d⟩) _ _) ?_
  refine bindR hread ?_
  refine bindR (mustR (by show (sent.toArray.size + 1 == d) = true; simp [hs]) _ _) ?_
  refine bindR (onTapeR (closeOne_mk name nz w x t) F) ?_
  refine bindR (takeSlotsR (d - 1) F t) ?_
  rfl

theorem mid_step {p : Psc} {F : Fork} {n d : Nat} (h : Mid p F (d - 1 + n)) (hd : 2 ≤ d) (z : E)
    (sent : List E) (x : E) :
    Mid (stepQ p (OnBytes.Psc.Weight.equality z d) sent x) { F with next := F.next + (d - 1) }
      n := by
  refine ⟨by rw [stepQ_ended]; exact h.notEnded, by rw [stepQ_rowMade]; exact h.noRow,
    by rw [stepQ_started]; exact h.started, ?_, ?_, sized_next h.sized, ?_, ?_,
    fun j hj hf => h.free j (by rw [stepQ_first] at hj; exact hj) (filled_next.mp hf)⟩
  · show (p.r.push x).size = (p.vars.push _).size
    rw [Array.size_push, Array.size_push, h.sizes]
  · intro w hw
    have hw' : w ∈ p.vars.toList ++ [OnBytes.Psc.Weight.equality z d] := by
      simpa [stepQ] using hw
    rcases List.mem_append.mp hw' with h1 | h1
    · exact h.pos w h1
    · rw [List.mem_singleton] at h1
      rw [h1]
      show 1 ≤ d
      omega
  · rw [stepQ_first]
    show F.next + (d - 1) = p.first + taken (stepQ p _ sent x)
    rw [taken_step, h.next]
    show p.first + taken p + (d - 1) = p.first + (taken p + (d - 1))
    omega
  · show F.next + (d - 1) + n ≤ F.ns
    have := h.fits
    omega

/-- **One round of the form eq2.** -/
theorem roundInR {p : Psc} {F : Fork} {n : Nat} (h : Mid p F (2 + n)) (z : E) (w : Nat)
    (sent : List E) (x : E) (t : Tape) (hs : sent.length = 2) :
    Fl.roundIn .eq2 p z 0 F (⟨some Model.RoundName.pscRound.name, 0, w, sent, [x]⟩ :: t) =
        some ((x, stepQ p (OnBytes.Psc.Weight.equality z 3) sent x),
          { F with next := F.next + 2 }, t) ∧
      Mid (stepQ p (OnBytes.Psc.Weight.equality z 3) sent x) { F with next := F.next + 2 } n := by
  refine ⟨?_, mid_step (d := 3) h (by omega) z sent x⟩
  unfold Fl.roundIn
  refine bindR (mustR (by rw [h.notEnded]; rfl) _ _) ?_
  refine bindR (needR (a := OnBytes.Psc.Weight.equality z 3) rfl _ _) ?_
  exact pscRoundR p z 3 (by omega) _ 0 w sent x t F (by omega)

/-- Behind the end values: e is their first slot, n their number, k the room that is left. -/
structure Ended (p : Psc) (G : Fork) (e n k : Nat) : Prop where
  noRow : p.rowMade = false
  started : p.started = true
  sizes : p.r.size = p.vars.size
  some : p.vars.toList ≠ []
  pos : ∀ w ∈ p.vars.toList, 1 ≤ w.d
  sized : Sized G
  first : e = p.first + taken p
  next : G.next = e + n
  fits : G.next + k ≤ G.ns
  own : ∀ j, p.first ≤ j → j < e → ¬ Filled G j
  beyond : ∀ j, G.next ≤ j → ¬ Filled G j
  ends : ∀ i, i < n → Filled G (e + i)

/-- The record behind the further variable's round. -/
def endQ (q : Psc) : Psc := { q with ended := true }

theorem endQ_first (q : Psc) : (endQ q).first = q.first := rfl

/-- From a sumcheck in course to one behind its end values. Stated of a letter q, so that the
unifier has nothing to unfold. -/
theorem ended_mk {q : Psc} {F' G : Fork} {n k : Nat} (hm : Mid q F' (n + k))
    (hne : q.vars.toList ≠ []) (r1 : Room G k) (r2 : G.next = F'.next + n)
    (r4 : ∀ i, i < n → Filled G (F'.next + i))
    (r5 : ∀ j, j < F'.next → (Filled G j ↔ Filled F' j)) : Ended (endQ q) G F'.next n k :=
  { noRow := hm.noRow, started := hm.started, sizes := hm.sizes, some := hne, pos := hm.pos,
    sized := r1.sized, first := hm.next, next := r2, fits := r1.fits,
    own := fun j h1 h2 hf => hm.free j h1 ((r5 j h2).1 hf), beyond := r1.free, ends := r4 }

/-- **The further variable's round and the end values.** -/
theorem pscEndsR {p : Psc} {F : Fork} {dY n k : Nat} (h : Mid p F (dY + n + k)) (h1 : 1 ≤ dY)
    (h2 : 1 ≤ n) (w w' : Nat) (sentY vals : List E) (beta : E) (t : Tape) (hs : sentY.length = dY)
    (hv : vals.length = n) :
    ∃ q G, Fl.pscEnds p dY n F (⟨some Model.RoundName.pscY.name, 1, w, sentY, [beta]⟩ ::
          ⟨some Model.RoundName.pscValues.name, 0, w', vals, []⟩ :: t) =
        some ((F.next + dY, q), G, t) ∧ Ended q G (F.next + dY) n k ∧ q.first = p.first ∧
      G.ns = F.ns ∧ ∀ j, j < F.next → (Filled G j ↔ Filled F j) := by
  have hm := mid_step (d := dY + 1) (n := n + k) (by
    have e : dY + 1 - 1 + (n + k) = dY + n + k := by omega
    rw [e]
    exact h) (by omega) zeroE sentY beta
  have e1 : dY + 1 - 1 = dY := by omega
  rw [e1] at hm
  -- the ledger's step
  have hroom : Room ({ F with next := F.next + dY } : Fork) (n + k) :=
    ⟨sized_next h.sized, hm.fits, fun j hj hf => h.free j (by
      have h3 : F.next + dY ≤ j := hj
      have := h.next
      omega) (filled_next.mp hf)⟩
  obtain ⟨G, hG, r1, r2, r3, r4, r5⟩ := takeHide hroom vals.toArray (by simpa using hv) beta
  have hread := readR (some Model.RoundName.pscValues.name) 0 w' [] t vals [] n hv.symm
    ({ F with next := F.next + dY } : Fork)
  rw [List.append_nil] at hread
  have hround := pscRoundR p zeroE (dY + 1) (by omega) Model.RoundName.pscY.name 1 w sentY beta
    (⟨some Model.RoundName.pscValues.name, 0, w', vals, []⟩ :: t) F (by omega)
  rw [e1] at hround
  have hbelow : ∀ j, j < F.next + dY → (Filled G j ↔ Filled F j) := fun j hj =>
    (r5 j hj).trans filled_next
  have hne : (stepQ p (OnBytes.Psc.Weight.equality zeroE (dY + 1)) sentY beta).vars.toList ≠
    [] := by
    unfold stepQ
    simp
  have hE : Ended (endQ (stepQ p (OnBytes.Psc.Weight.equality zeroE (dY + 1)) sentY beta)) G
      (F.next + dY) n k := ended_mk hm hne r1 r2 r4 r5
  refine ⟨endQ (stepQ p (OnBytes.Psc.Weight.equality zeroE (dY + 1)) sentY beta), G, ?_, hE,
    (endQ_first _).trans (stepQ_first _ _ _ _), r3, fun j hj => hbelow j (by omega)⟩
  unfold Fl.pscEnds
  refine bindR (mustR (by rw [h.notEnded]; simp [h1, h2]) _ _) ?_
  refine bindR hround ?_
  refine bindR hread ?_
  refine bindR (mustR (by show (vals.toArray.size == n) = true; simp [hv]) _ _) ?_
  refine bindR (onTapeR (emptyOn_mk _ w' t) _) ?_
  refine bindR (takeSlotsR n _ t) ?_
  refine bindR (changeR hG t) ?_
  rfl

/-- **The claim that a sumcheck leaves.** -/
theorem pscRowR {p : Psc} {G : Fork} {e n k : Nat} (h : Ended p G e n k) (S0 : E) (kept : Aff)
    (t : Tape) :
    ∃ H, Fl.pscRow p S0 kept G t = some ((p.rowForm S0 kept, { p with rowMade := true }), H, t) ∧
      Room H k ∧ H.next = G.next ∧ H.ns = G.ns ∧ ∀ j, Filled G j → Filled H j := by
  have hlen : p.walk.1.length = taken p := by
    have hl : p.vars.toList.length = p.r.toList.length := by
      rw [Array.length_toList, Array.length_toList, h.sizes]
    have hz : (p.vars.toList.zip p.r.toList).map Prod.fst = p.vars.toList :=
      List.map_fst_zip (Nat.le_of_eq hl)
    have hne : p.vars.toList.zip p.r.toList ≠ [] := by
      intro h0
      rw [h0] at hz
      exact h.some hz.symm
    unfold Psc.walk taken
    rw [zipT_eq, OnBytes.G4.hidingWalk_length _ hne (fun x hx => h.pos x.1 (by
      rw [← hz]
      exact List.mem_map_of_mem hx))]
    have e2 : (p.vars.toList.zip p.r.toList).map (fun x => x.1.d - 1) =
        ((p.vars.toList.zip p.r.toList).map Prod.fst).map fun w => w.d - 1 := by
      rw [List.map_map]
      rfl
    rw [e2, hz]
  obtain ⟨H, hH⟩ := hideRun_free (F := G) p.first (Array.replicate p.walk.1.length zeroE)
    (subE zeroE oneE) h.sized (by
      intro i hi
      rw [Array.size_replicate, hlen] at hi
      have h1 := h.first
      have h2 := h.next
      have h3 := h.fits
      exact ⟨by omega, h.own _ (by omega) (by omega)⟩)
  obtain ⟨a1, a2, a3, a4⟩ := hideRun_ok G H p.first _ _ h.sized hH
  have hsz : (Array.replicate p.walk.1.length zeroE : Array E).size = taken p := by
    rw [Array.size_replicate, hlen]
  refine ⟨H, ?_, ⟨a2, by rw [a1.next, a1.ns]; exact h.fits, fun j hj hf => ?_⟩, a1.next, a1.ns,
    fun j hj => ?_⟩
  · unfold Fl.pscRow
    refine bindR (mustR (by
      have hv : p.vars.isEmpty = false := by
        cases hq : p.vars.toList with
        | nil => exact absurd hq h.some
        | cons a l =>
          have : p.vars.size ≠ 0 := by
            rw [← Array.length_toList, hq]
            simp
          simpa [Array.isEmpty] using this
      rw [h.noRow, h.started, hv, h.sizes]
      simp) _ _) ?_
    refine bindR (changeR hH t) ?_
    rfl
  · rw [a1.next] at hj
    have h1 := h.first
    have h2 := h.next
    exact h.beyond j hj ((a4 j (Or.inr (by rw [hsz]; omega))).2.2.1 hf)
  · by_cases hin : p.first ≤ j ∧ j < p.first + taken p
    · have e' : p.first + (j - p.first) = j := by omega
      have := (a3 (j - p.first) (by rw [hsz]; omega)).2.2.1
      rw [e'] at this
      exact this
    · exact (a4 j (by rw [hsz]; omega)).2.2.2 hj

end D6.Ret

#print axioms D6.Ret.claimsInR
#print axioms D6.Ret.batchR
#print axioms D6.Ret.pointR
#print axioms D6.Ret.pscBeginR
#print axioms D6.Ret.roundInR
#print axioms D6.Ret.pscEndsR
#print axioms D6.Ret.pscRowR
