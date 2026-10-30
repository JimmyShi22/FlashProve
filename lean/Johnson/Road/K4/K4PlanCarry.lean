-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanCarry.lean: WHAT `K4PlanFit` AND `K4PlanFitF` (Johnson/Road/K4/K4PinsEnd.lean,
K4PinsEndFirst.lean) READ OF THE TWO LETTERS ms AND N, AS LAWS. Of a member of ms they read its
shape and its (tree, tenant), never its radius; of N the fields sent (through it group) and index,
no other. So each structure at (ms, N) is the structure at every (ms', N') with the same list of
pairs (shape, seat) and the same two fields. Two definitions and eleven theorems. No draw, no count.

  `memPair`, `SamePairs ms ms'`: a member's (shape, seat); the two lists of pairs are one list.
  `memAt_pairs`, `sitsIn_pairs`, `groupsSeated_pairs`, `offPad_pairs`, `seamFit_pairs`: each
    condition carried across `SamePairs`.
  `seamFit_sameN`: `SeamFit` carried across N'.sent = N.sent.
  `planFit_carry`, `planFitF_carry`: the two structures carried across both at once.
  `samePairs_R`: the members by the make off the plan's seats (`memberListsR`,
    Johnson/P5T/MembersByMake.lean) at two families of radii have the same pairs:
    by `plain_membersR`.
  `seatsAsShapes_R`: these lists have as many seats as shapes, by the make.

Limits. K04_law IS NOT PROVED BY THIS. THE OTHER WAY ROUND: these conditions put no condition on a
member's radius, nor on N's other fields: what K04_law needs of those is owed elsewhere.

-/
import Johnson.Road.K4.K4PlanTests
import Johnson.Road.K4.K4PlanTestsFirst
import Johnson.P5T.MembersByMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls LayPub)
open VerifiableInference.Desc.Sound (Mem msOf seatOf numOf GroupsSeated OffPad)
open Cb.Pv.Tail (Size)
open Inst.Model.Layout (kRef hRef)

/-- A member's shape and seat. -/
def memPair (y : Mem) : OnBytes.OracleShape × (ℕ × ℕ) := ((y.1.l.get y.2).1, seatOf y)

/-- The two lists of members have one list of pairs (shape, seat). -/
def SamePairs (ms ms' : List Mem) : Prop := ms.map memPair = ms'.map memPair

section
variable {ms ms' : List Mem} (h : SamePairs ms ms')
include h

/-- A member of the one has a fellow in the other. -/
theorem mem_pairs {y : Mem} (hy : y ∈ ms') : ∃ y' ∈ ms, memPair y' = memPair y := by
  have e : memPair y ∈ ms.map memPair := by
    rw [h]
    exact List.mem_map.2 ⟨y, hy, rfl⟩
  obtain ⟨y', hy', e'⟩ := List.mem_map.1 e
  exact ⟨y', hy', e'⟩

/-- The first member at a seat has a fellow that is the first there in the other list. -/
theorem memAt_pairs {x : ℕ × ℕ} {u : Mem} (hu : memAt ms x = some u) :
    ∃ u', memAt ms' x = some u' ∧ memPair u' = memPair u := by
  have key : ∀ l : List Mem, (memAt l x).map memPair =
      (l.map memPair).find? fun q => decide (q.2 = x) := by
    intro l
    rw [List.find?_map]
    rfl
  have e : (memAt ms' x).map memPair = some (memPair u) := by
    rw [key ms', ← h, ← key ms, hu]
    rfl
  obtain ⟨u', hu', e'⟩ := Option.map_eq_some_iff.1 e
  exact ⟨u', hu', e'⟩

theorem sitsIn_pairs {l : List (OnBytes.OracleShape × ℕ)} {seat : Fin l.length → ℕ × ℕ}
    {N : Numbers} {m : ℕ} (S : SitsIn l seat ms N m) : SitsIn l seat ms' N m := by
  intro i
  obtain ⟨h1, u, hu, e⟩ := S i
  obtain ⟨u', hu', e'⟩ := memAt_pairs h hu
  exact ⟨h1, u', hu', (congrArg Prod.fst e').trans e⟩

theorem groupsSeated_pairs {N : Numbers} (G : GroupsSeated ms N) : GroupsSeated ms' N := by
  intro k x hx
  obtain ⟨y, hy, e⟩ := G k x hx
  obtain ⟨y', hy', e'⟩ := mem_pairs (ms := ms') (ms' := ms) h.symm hy
  exact ⟨y', hy', (congrArg Prod.snd e').trans e⟩

theorem offPad_pairs {cs : Codes} {arr : ℕ → ℕ → ℕ} {N : Numbers} {k n r p : ℕ}
    (O : OffPad cs arr ms N k n r p) : OffPad cs arr ms' N k n r p := by
  intro y hy hg hn
  obtain ⟨y', hy', e'⟩ := mem_pairs h hy
  have es : seatOf y' = seatOf y := congrArg Prod.snd e'
  have e1 : (memPair y').1 = (memPair y).1 := congrArg Prod.fst e'
  have eh : (y'.1.l.get y'.2).1 = (y.1.l.get y.2).1 := e1
  rw [← eh]
  refine O y' hy' (by rw [es]; exact hg) ?_
  show arr (seatOf y').1 (seatOf y').2 = n
  rw [es]
  exact hn

theorem seamFit_pairs {arr : ℕ → ℕ → ℕ} {N : Numbers} {s : ℕ → Size}
    {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {cs : Codes} {y : Model.Layer.Lay} {g : ℕ}
    (F : SeamFit arr ms N s seat cs y g) : SeamFit arr ms' N s seat cs y g :=
  ⟨F.sizes, F.seats, groupsSeated_pairs h F.seated, fun ha i hi c hc =>
    ⟨(F.each ha i hi c hc).1, (F.each ha i hi c hc).2.1,
      offPad_pairs h (F.each ha i hi c hc).2.2.1, offPad_pairs h (F.each ha i hi c hc).2.2.2⟩⟩

end

/-- `SeamFit` reads of N the field sent alone. -/
theorem seamFit_sameN {arr : ℕ → ℕ → ℕ} {ms : List Mem} {N N' : Numbers} (hs : N'.sent = N.sent)
    {s : ℕ → Size} {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {cs : Codes}
    {y : Model.Layer.Lay} {g : ℕ} (F : SeamFit arr ms N s seat cs y g) :
    SeamFit arr ms N' s seat cs y g := by
  cases N
  cases N'
  cases hs
  exact ⟨F.sizes, F.seats, F.seated, F.each⟩

section
variable {X : Public} {p : Par} {x : VerifiableInference.Desc.First.Look.Place} {q : LayPub}
  {D : Sent} {rad : OnBytes.OracleShape → ℕ}
  {seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ} {posI : ℕ → Bool × ℕ × ℕ}
  {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {arr : ℕ → ℕ → ℕ} {ms ms' : List Mem}
  {N N' : Numbers} {m nM nR nC first : ℕ} {s : ℕ → Size}
  {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {hd : ℕ}

/-- **`K4PlanFit` at (ms, N) is `K4PlanFit` at every (ms', N') with the same pairs, sent and
index.** -/
theorem planFit_carry {rows cols : ℕ} {enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg}
    (hp : SamePairs ms ms') (hs : N'.sent = N.sent) (hi : N'.index = N.index)
    (h : K4PlanFit (X := X) (p := p) x q D rad seatT posI oW enc wOf arr ms N m nM nR nC first s
      seat hd) :
    K4PlanFit (X := X) (p := p) x q D rad seatT posI oW enc wOf arr ms' N' m nM nR nC first s seat
      hd := by
  have h2 := seamFit_sameN hs (seamFit_pairs hp h.seam)
  have h1 := sitsIn_pairs hp h.sits
  have h3 := h.syms
  cases N
  cases N'
  cases hs
  cases hi
  exact ⟨h1, h.covers, h.place, h.keys, h.size, h3, h2, h.segment, h.notHead⟩

/-- **`K4PlanFitF` likewise.** -/
theorem planFitF_carry {enc : (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) → oW.Msg}
    (hp : SamePairs ms ms') (hs : N'.sent = N.sent) (hi : N'.index = N.index)
    (h : K4PlanFitF (X := X) (p := p) x q D rad seatT posI oW enc wOf arr ms N m nM nR nC first s
      seat hd) :
    K4PlanFitF (X := X) (p := p) x q D rad seatT posI oW enc wOf arr ms' N' m nM nR nC first s seat
      hd := by
  have h1 := sitsIn_pairs hp h.sits
  have h3 := h.syms
  cases N
  cases N'
  cases hs
  cases hi
  exact ⟨h1, h.covers, h.place, h.keys, h.size, h3, h.segment, h.notHead⟩

end

/-- **The members by the make, at two families of radii, have the same pairs.** -/
theorem samePairs_R (n : ℕ) (rad rad' : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) :
    SamePairs (msOf (P5T.memberListsR n rad ps)) (msOf (P5T.memberListsR n rad' ps)) :=
  (P5T.plain_membersR n rad ps).trans (P5T.plain_membersR n rad' ps).symm

/-- **The lists by the make have as many seats as shapes.** -/
theorem seatsAsShapes_R (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) :
    seatsAsShapesB (P5T.memberListsR n rad ps) = true := by
  unfold seatsAsShapesB P5T.memberListsR
  rw [List.all_eq_true]
  intro e he
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 he
  simp

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.memAt_pairs
#print axioms OnBytes.Road.K4.sitsIn_pairs
#print axioms OnBytes.Road.K4.seamFit_pairs
#print axioms OnBytes.Road.K4.seamFit_sameN
#print axioms OnBytes.Road.K4.planFit_carry
#print axioms OnBytes.Road.K4.planFitF_carry
#print axioms OnBytes.Road.K4.samePairs_R
#print axioms OnBytes.Road.K4.seatsAsShapes_R
