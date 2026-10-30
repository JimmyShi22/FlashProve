-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LaidLight.lean: the kind "the code switch" (K2): A LIGHT TEST
ON A FILLING WHOSE YES GIVES THE YES OF THE LOT's PUBLIC TEST (`ownLaid`, Honest/K2/AtPlan.lean;
`publicOk`, Honest/K2/Sim.lean), AND SO, WITH THE LIGHT TEST ON THE CLOSING
(Honest/K2/Law/ClosingLight.lean), THAT THE LOT's CLOSING RETURNS. Definitions with code; statements
with their proofs.

WHY. `ownLaid` asks of each array that the layout lays into a message whether the filling lays an
element of it SOMEWHERE (`arraysLaid`): it walks the message's rows and places from the first on
until it meets one. An array that begins far down a long message costs as many calls of the filling
as places stand in front of it. The light test asks AT THE FIRST PLACE OF EACH LAID BLOCK of the
array alone: as many calls as the array has blocks, at most. Of a message into which the layout lays
no array both tests say yes, as `arraysLaid`'s own docstring tells.

  `arraysLaidLight`   of each array of the message: at the first place of one of its laid blocks,
                    inside the message's rows and its code's message length, the filling lays an
                    element, and the layout's way back names that array there
  `ownLaidLight`    THE LIGHT TEST: `ownLaid`'s clauses, one by one, with `arraysLaidLight`
  `arraysLaid_of_light`   the light test's yes gives `arraysLaid`'s
  `forIn_yields`, `bind_yields`   two tools on a loop and a step that may refuse
  `ownLaid_of_light`, `publicOk_of_light`   THE LIGHT TEST's YES GIVES THAT `ownLaid` RETURNS, and
                    `publicOk`'s yes
  `returns_of_light`  where both light tests say yes the lot's closing returns, at every input with
                    that public instance, list of challenges and carried coins

Limits. ONE WAY ALONE: a filling that lays an array's elements but none at a block's first place
passes `ownLaid` and fails the light test: its no means nothing. How long either takes is not a
matter of Lean's: no time is stated here. Neither test is shown of any place or filling here.
Nothing on what the closing leaves. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2

variable {W₀ Rc Xi Tr : Type}

/-- **Each array of the message is laid at the first place of one of its laid blocks.** The letters
are `arraysLaid`'s. -/
def arraysLaidLight (D : RowData) (lay : OnBytes.Params.ReqLayout) (codes : OnBytes.Codes)
    (s : OnBytes.OracleShape) (seg m : Nat) (a : MsgAddr) : Bool :=
  ((lay.link.getD seg []).filter fun A => A.message == m).all fun A =>
    A.blocks.any fun b =>
      decide (b.firstRow < s.mainRows) &&
        decide (b.firstPlace < (codes.base.getD s.code default).ell) &&
        D.lays a b.firstRow b.firstPlace &&
        (laidBack lay seg m b.firstRow b.firstPlace).any fun x => x.1.name == A.name

/-- **THE LIGHT TEST.** The letters are `ownLaid`'s. -/
def ownLaidLight (D : RowData) (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace)
    (segs : List SegmentPub) : Bool :=
  (segs.zipIdx.all fun x =>
    (x.1.ownShapes (x.2 == 0)).zipIdx.all fun s =>
      (p.addrs x.2 s.2).any fun a => arraysLaidLight D lay x.1.sizes.codes s.1 x.2 s.2 a) &&
    (p.others.toList.take (p.others.size - 1)).zipIdx.all fun n =>
      arraysLaidLight D lay p.sizes.codes n.1.shape p.link n.2 (p.ownAddr n.2) &&
        D.readyAt [] (p.ownAddr n.2)

namespace Law

theorem arraysLaid_of_light {D : RowData} {lay : OnBytes.Params.ReqLayout} {codes : OnBytes.Codes}
    {s : OnBytes.OracleShape} {seg m : Nat} {a : MsgAddr}
    (h : arraysLaidLight D lay codes s seg m a = true) :
    arraysLaid D lay codes s seg m a = true := by
  unfold arraysLaidLight at h
  unfold arraysLaid
  rw [List.all_eq_true] at h ⊢
  intro A hA
  obtain ⟨b, _, hb⟩ := List.any_eq_true.1 (h A hA)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb
  refine List.any_eq_true.2 ⟨b.firstRow, List.mem_range.2 h1,
    List.any_eq_true.2 ⟨b.firstPlace, List.mem_range.2 h2, ?_⟩⟩
  rw [Bool.and_eq_true]
  exact ⟨h3, h4⟩

/-- A loop each of whose steps goes on returns. -/
theorem forIn_yields {α : Type} (l : List α) (f : α → PUnit → Except String (ForInStep PUnit))
    (h : ∀ x ∈ l, f x PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn l PUnit.unit f = (.ok PUnit.unit : Except String PUnit) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.forIn_cons, h a (by simp)]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- A step behind a step that returns. -/
theorem bind_yields {α β : Type} {x : Except String α} {k : α → Except String β} {a : α} {b : β}
    (h1 : x = .ok a) (h2 : k a = .ok b) : (x >>= k) = .ok b := by
  rw [h1]
  exact h2

/-- **The light test's yes gives that `ownLaid` returns.** -/
theorem ownLaid_of_light {D : RowData} {lay : OnBytes.Params.ReqLayout} {p : SwitchPlace}
    {segs : List SegmentPub} (h : ownLaidLight D lay p segs = true) :
    ownLaid D lay p segs = .ok () := by
  unfold ownLaidLight at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  unfold ownLaid
  refine bind_yields (forIn_yields _ _ fun x hx => ?_)
    (bind_yields (forIn_yields _ _ fun n hn => ?_) rfl)
  · have hx' := List.all_eq_true.1 (h1 x hx)
    refine bind_yields (forIn_yields _ _ fun s hs => ?_) rfl
    have hs' := hx' s hs
    cases ha : p.addrs x.2 s.2 with
    | none =>
      rw [ha] at hs'
      cases hs'
    | some a =>
      rw [ha] at hs'
      have hl := arraysLaid_of_light (show arraysLaidLight D lay x.1.sizes.codes s.1 x.2 s.2 a =
        true from hs')
      simp [hl]
      rfl
  · have hn' := h2 n hn
    rw [Bool.and_eq_true] at hn'
    have hl := arraysLaid_of_light hn'.1
    simp [hl, hn'.2]
    rfl

/-- So `publicOk` says yes. -/
theorem publicOk_of_light (D : RowDataOf Xi) (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace)
    (segs : List SegmentPub) (x : Xi) (h : ownLaidLight (D x) lay p segs = true) :
    publicOk D lay p segs x = true := by
  unfold publicOk
  rw [ownLaid_of_light h]

/-- **Where both light tests say yes the lot's closing returns.** -/
theorem returns_of_light (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace)
    (hc : closingOkLight freshTable (segs.take p.link) p = true) (w : Local W₀ Rc Xi Tr)
    (hd : ownLaidLight (D w.x) lay p (segs.take p.link) = true) (heard : List Fmt.Drawn)
    (ca : CsAll p.carries) :
    (lotClosingAt lay segs p (D w.x) (readers w) heard
      (Stretch.carried p.carries ca)).toOption.isSome = true :=
  (returnsLaw_light D readers lay segs p hc w heard ca).trans
    (publicOk_of_light D lay p (segs.take p.link) w.x hd)

end Law

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.Law.arraysLaid_of_light
#print axioms ProofFile.Honest.K2.Law.forIn_yields
#print axioms ProofFile.Honest.K2.Law.bind_yields
#print axioms ProofFile.Honest.K2.Law.ownLaid_of_light
#print axioms ProofFile.Honest.K2.Law.publicOk_of_light
#print axioms ProofFile.Honest.K2.Law.returns_of_light
#print axioms ProofFile.Honest.K2.arraysLaidLight
#print axioms ProofFile.Honest.K2.ownLaidLight
