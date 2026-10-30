-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/HandsOfK10.lean: WHAT A YES OF K10's BLOCK HANDS ON OF THE TABLE's FOUR
BOOLS ON THE RECORD, ALONG A `K10Step`: field by field, in the words of the form "Hands"
(HandsDef.lean). Statements and proofs. A file BESIDE the table of joints: it turns nothing of it.

Why. The files that type "each block's yes hands the growth on" for the proof file's first chain
have a form with six fields a block: mark, shape, rows, members, book, more (GrownBK.lean:
`Hands N links ps E k b`, over a block's
step's yes). They leave the 25 places of the kind K10 to K10's files. That file stands over other
paths than this file: so the six are typed here as six statements over `K10Step` (AsksOfMg.lean,
beside this file), each in that form's own words, and the step's yes is brought to `K10Step`.
  `step_decide`: a yes of a block's step is a yes of its decision, at some rounds and groups.
    `k10_step_of_yes`: so, at a block whose decision's yes is `closeFrame`'s (H: `seated_yes` pays
    it; at the lot's own block `closing_writes`), a yes of the step from s to s' is a `K10Step s
    s'`.
  `k10_step_mark`: the mark behind is the mark in front. `k10_step_shape`, `k10_step_rows`,
    `k10_step_members`, `k10_step_book`: at the k-th place of a list at which the two tests on the
    table say yes (`closersFit`, `closersNext`), of the kind K10: `shapeAt` behind from `shapeAt` in
    front; `rowsHeld` and `membersHeld` behind OUTRIGHT; `bookAt` behind from `bookAt` in front,
    under the plan's two numbers.
Limits. The sixth field ("more": further Bools on the record, a letter of that form) is not here:
what of the record rides along a `K10Step` is `k10_rides` (RidesBehind.lean). That form itself is
not named in code. The plan's two numbers are premises. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.AsksOfMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc.First (S Numbers Item ModelPart openSets start closersFit closersNext
  closersFit_at closersNext_at rowsHeld membersHeld bookAt rowsHeld_none membersHeld_none
  shapeAt_behind bookAt_behind)

/-- A yes of a block's step is a yes of its decision. -/
theorem step_decide {σ Cl : Type} (b : Block σ Cl) (ft : ℕ) (s s' : σ) (rs : List Fmt.RoundView)
    (cols : List Col) (n : ℕ) (h : b.step ft s rs cols = .ok (s', n)) :
    ∃ rs' gs, b.decide s rs' gs = .ok s' := by
  unfold Block.step at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨t, ht, h⟩ := ok_bind h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨_, _, ht⟩

/-- A yes of the step of a block whose decision's yes is the frame's closing's. -/
theorem k10_step_of_yes {Cl : Type} (Pr : Par) (b : Block S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (recOf s).owed (recOf s).frame
      (recOf s).st (entries Pr) rs = .ok x ∧ s' = putRec s ⟨none, x.1, x.2⟩)
    (s s' : S) (h : ∃ ft rs cols n, b.step ft s rs cols = .ok (s', n)) : K10Step s s' := by
  obtain ⟨ft, rs, cols, n, e⟩ := h
  obtain ⟨rs', gs, hd⟩ := step_decide b ft s s' rs cols n e
  obtain ⟨x, hx, hw⟩ := H _ _ _ _ hd
  exact ⟨_, _, x, hx, hw⟩

theorem k10_step_mark {s s' : S} (h : K10Step s s') : s'.failed = s.failed := by
  obtain ⟨es, rs, x, -, rfl⟩ := h
  exact (putRec_keeps s _).2.2.1

section
variable (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place)
  (hF : closersFit links ps (start links) = true) (hX : closersNext links ps = true)
  (hk : ps[k]? = some p) (hK : p.kind = .K10)

include hX hk hK in
theorem k10_step_shape {s s' : S} (h : K10Step s s')
    (hs : VerifiableInference.Desc.First.shapeAt links ps[k]? s = true) :
    VerifiableInference.Desc.First.shapeAt links ps[k + 1]? s' = true := by
  obtain ⟨es, rs, x, -, rfl⟩ := h
  obtain ⟨p', f1, f2, f3⟩ := closersNext_at links ps k p hX hk hK
  rw [hk] at hs
  rw [f1]
  exact shapeAt_behind links p p' s _ rfl f2 f3 hs

include hF hk hK in
theorem k10_step_rows (N : Numbers) (s' : S) :
    rowsHeld N ((openSets links ps (start links))[k + 1]?.getD []) s' = true := by
  obtain ⟨Ok, -, e2, -, -, e5⟩ := closersFit_at links ps _ k p hF hk hK
  rw [e2, Option.getD_some]
  exact rowsHeld_none N _ _ e5

include hF hk hK in
theorem k10_step_members (N : Numbers) (s' : S) :
    membersHeld N ((openSets links ps (start links))[k + 1]?.getD []) s' = true := by
  obtain ⟨Ok, -, e2, -, -, e5⟩ := closersFit_at links ps _ k p hF hk hK
  rw [e2, Option.getD_some]
  exact membersHeld_none N _ _ e5

theorem k10_step_book (N : Numbers) (ht : N.treesAt ps[k + 1]? = N.treesAt ps[k]?)
    (hm : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?) {s s' : S} (h : K10Step s s')
    (hb : bookAt N ps[k]? s = true) : bookAt N ps[k + 1]? s' = true := by
  obtain ⟨es, rs, x, hx, rfl⟩ := h
  obtain ⟨G, id, -, -, e3⟩ := closeFrame_st hx
  refine bookAt_behind N _ _ s _ ?_ ht hm hb
  show x.2.oracles.size = s.st.oracles.size
  rw [e3]
  exact behind_size _ _ _ _

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.step_decide
#print axioms VerifiableInference.Desc.First.Close.k10_step_of_yes
#print axioms VerifiableInference.Desc.First.Close.k10_step_mark
#print axioms VerifiableInference.Desc.First.Close.k10_step_shape
#print axioms VerifiableInference.Desc.First.Close.k10_step_rows
#print axioms VerifiableInference.Desc.First.Close.k10_step_members
#print axioms VerifiableInference.Desc.First.Close.k10_step_book
