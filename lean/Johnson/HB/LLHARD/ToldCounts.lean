-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/ToldCounts.lean: what the tests on the list of rounds read of the letter told
(what each sub-protocol of the first chain tells of the trees that it sends): two counts at each of
the 359 borders. These counts as one closed list, made of the written sendings and the written list
of places; one premise on told, that its counts are that list; and under it the test `planBelowB`,
the binders hNt and hNm of the law on K13, and the two numbers by place at numbers that are laid off
told.

Row or tool. Definitions, closed facts, and laws under one premise on a letter. `countsFull` is a
reading of ours, made a definition, of which place tells which sending. That the sub-protocols tell
so is `CountsAre` at what they tell: it is shown by nobody yet.

(Where this and lean/THEOREM.md differ, the page holds.) Until it is, every fact above it
holds under that premise alone: none has a form in scope, and none counts as an example at the
release's own values. No law on a sub-protocol is named.

The arguments, their closed terms and their ties.
  L: `LFull` (Johnson/HB/LLHARD/LaidWritten.lean). Tie: `laid_at` there.
  the places: `First.flatPlacesOf Sound.linksFull true`: a constant in the laws' own binders.
  told: no closed term. The two premises `CountsAre told` and `TreesAre told` stand in its place.
    Who is to pay it: the test that holds the cut of the IOP as written in Lean to one written list,
    which is being typed by its owners.
    (Where this and lean/THEOREM.md differ, the page holds.)

What is here.
  `sendsAtPlace p`: how many sendings stand at a place: one at a place of the kinds K1 and K2, five
    at the last proximity test's (K12, in no segment), none elsewhere. This is a reading of ours of
    the sub-protocols, not a theorem on them.
  `walk`, `countsFull`: along the places, handing out the written sendings in their order: at each
    border the oracle messages and the trees in front.
  `counts_written`: the places ask for just the 82 written sendings; the list has 359 entries; it
    begins with (0, 0) three times; it has (197, 82) at 355 and at 356; it ends with (199, 83).
    `labelsOf`, `labelsFit`, `labels_written`, `labels_rejects`: the walk hands each place the
    sendings whose labels name it: "link l, moment m" at the place of segment l that is the m-th to
    send; "link 25, moment 0" at the last code switch; the five code switches' at the last proximity
    test; "W" at the last place. So the walk is right in its places and not in its counts alone.
    Without the first sending the test rejects.
  `CountsAre told`: at the borders 0 to 358 told's two counts are `countsFull`. `counts_at`: so they
    are at each border.
  `below_written`: `placesBelowB LFull` accepts at all 359 pairs. `planBelow_written`: so
    `planBelowB LFull 358 told` accepts under the premise. `below_rejects`: the negative test: with
    each border's count of trees taken one border earlier, it rejects.
  `places_fit`: 358 places, none twice. `borderOf_at`: in a list without a repeated place the border
    of the place number k is k. `told_at`: so, at numbers laid off told over the written places, the
    two numbers at the place number k are `countsFull`'s entry k.
  `hNt_hNm_of`: the binders hNt and hNm, to the letter, at such numbers. `tenantsFull`,
    `tenants_written`: how many oracle messages sit in each of the 83 trees, off the written layout.
    `TreesAre told`: the second premise: tree by tree told has as many tenants. The counts at the
    borders do not give it: the first place that tells, tells two trees with five oracle messages at
    once. `msgNo_of`, `indexNo_of`: under it the number of the oracle message at a tenant; the index
    masks' has the number 4.
By evaluations in Lean's kernel (`decide +kernel`): `counts_written`, `labels_written`,
`labels_rejects`, `below_written`, `below_rejects`, `places_fit`, `tenants_written`.

Limits. Everything under `CountsAre` or `TreesAre` is conditional. hNt and hNm say no more than that
the sub-protocol at place 355 tells nothing. Nothing on soundness.


-/
import Johnson.HB.LLHARD.LaidWritten
import Johnson.Desc.K13.Law.PlanTestsM3
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes Johnson.G
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Numbers flatPlacesOf treesTold msgsTold borderOf)
open VerifiableInference.Desc.K12.Door (Laid placesBelowB)
open VerifiableInference.Desc.Sound (linksFull)

/-- How many sendings stand at a place. -/
def sendsAtPlace (p : Place) : ℕ :=
  if p.kind == .K1 || p.kind == .K2 then 1 else if p.kind == .K12 && p.link.isNone then 5 else 0

/-- The trees that a list of sendings lays at the written codes, and its oracle messages. -/
def sizeOf (ss : List (List OracleNotice)) : ℕ × ℕ :=
  ((ss.map (·.length)).sum,
    (ss.map fun s => ((layTrees codesFull2 s.toArray).map (·.shapes.size)).getD 0).sum)

/-- Along the places, handing out the sendings in their order: at each border the oracle messages
and the trees in front. -/
def walk : List Place → List (List OracleNotice) → ℕ × ℕ → List (ℕ × ℕ)
  | [], _, x => [x]
  | p :: ps, ss, x =>
    x :: walk ps (ss.drop (sendsAtPlace p))
      (x.1 + (sizeOf (ss.take (sendsAtPlace p))).1, x.2 + (sizeOf (ss.take (sendsAtPlace p))).2)

/-- **The two counts at the 359 borders, closed.** -/
def countsFull : List (ℕ × ℕ) := walk (flatPlacesOf linksFull true) sentFull (0, 0)

set_option maxRecDepth 1000000 in
/-- **What the closed list comes to.** -/
theorem counts_written :
    ((flatPlacesOf linksFull true).map sendsAtPlace).sum = 82 ∧ countsFull.length = 359 ∧
      countsFull.take 3 = [(0, 0), (0, 0), (0, 0)] ∧ countsFull[355]? = some (197, 82) ∧
      countsFull[355 + 1]? = some (197, 82) ∧ countsFull[358]? = some (199, 83) := by
  decide +kernel

/-- The labels that the sendings at a place are to bear. m: how many places of the same segment have
had a sending before. -/
def labelsOf (p : Place) (m : ℕ) : List String :=
  match p.link with
  | some l => [s!"link {l}, moment {m}"]
  | none =>
    if p.kind == .K2 then ["link 25, moment 0"]
    else if p.kind == .K12 then
      (List.range 5).map fun i => s!"the last group's test, the code switch of stage {i + 1}"
    else ["W"]

/-- Along the places: each place is handed the sendings whose labels name it. -/
def labelsFit : List Place → List String → Option ℕ → ℕ → Bool
  | [], ls, _, _ => ls.isEmpty
  | p :: ps, ls, cur, m =>
    if sendsAtPlace p == 0 then labelsFit ps ls cur m
    else
      (ls.take (sendsAtPlace p) == labelsOf p (if p.link == cur then m else 0)) &&
        labelsFit ps (ls.drop (sendsAtPlace p)) p.link ((if p.link == cur then m else 0) + 1)

set_option maxRecDepth 1000000 in
/-- **The walk hands each place the sendings whose labels name it**: segment and moment. -/
theorem labels_written :
    labelsFit (flatPlacesOf linksFull true) (proofSendsFull.1.sends.map (·.label)) none 0 =
      true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: without the first sending, so that each place gets its neighbour's. -/
theorem labels_rejects :
    labelsFit (flatPlacesOf linksFull true) ((proofSendsFull.1.sends.map (·.label)).drop 1) none
      0 = false := by decide +kernel

/-- **The premise on told.** -/
def CountsAre (told : List (List Oracle)) : Prop :=
  (List.range 359).map (fun b => (msgsTold told b, treesTold told b)) = countsFull

/-- So they are at each border. -/
theorem counts_at {told : List (List Oracle)} (h : CountsAre told) {b : ℕ} (hb : b < 359) :
    countsFull[b]? = some (msgsTold told b, treesTold told b) := by
  rw [← h, List.getElem?_map, List.getElem?_range hb]
  rfl

set_option maxRecDepth 1000000 in
/-- The seats of the messages in front name trees in front, at all 359 pairs. -/
theorem below_written : (countsFull.all fun x => placesBelowB LFull x.1 x.2) = true := by
  decide +kernel

/-- **The test accepts under the premise.** -/
theorem planBelow_written {told : List (List Oracle)} (h : CountsAre told) :
    planBelowB LFull 358 told = true := by
  have e : planBelowB LFull 358 told =
      (((List.range 359).map fun b => (msgsTold told b, treesTold told b)).all
        fun x => placesBelowB LFull x.1 x.2) := by
    unfold planBelowB
    rw [List.all_map]
    rfl
  rw [e, h]
  exact below_written

set_option maxRecDepth 1000000 in
/-- **The negative test**: with each border's count of trees taken one border earlier. -/
theorem below_rejects :
    ((countsFull.zip ((0, 0) :: countsFull)).all fun x => placesBelowB LFull x.1.1 x.2.2) =
      false := by decide +kernel

/-! ## At numbers laid off told -/

set_option maxRecDepth 1000000 in
/-- 358 places, none twice. -/
theorem places_fit :
    (flatPlacesOf linksFull true).length = 358 ∧ (flatPlacesOf linksFull true).Nodup := by
  decide +kernel

/-- In a list without a repeated place the border of the place number k is k. -/
theorem borderOf_at {ps : List Place} (hn : ps.Nodup) {k : ℕ} (hk : k ≤ ps.length) :
    borderOf ps ps[k]? = k := by
  rcases Nat.lt_or_eq_of_le hk with hlt | rfl
  · rw [List.getElem?_eq_getElem hlt]
    exact hn.idxOf_getElem k hlt
  · rw [List.getElem?_eq_none (Nat.le_refl _)]
    rfl

/-- The two numbers by place, at numbers laid off told over the written places. -/
theorem told_at (N : Numbers) {told : List (List Oracle)} (h : CountsAre told) {k : ℕ}
    (hk : k ≤ 358) :
    countsFull[k]? = some
      ((N.withTold (flatPlacesOf linksFull true) told).msgsAt (flatPlacesOf linksFull true)[k]?,
        (N.withTold (flatPlacesOf linksFull true) told).treesAt
          (flatPlacesOf linksFull true)[k]?) := by
  have hb : borderOf (flatPlacesOf linksFull true) (flatPlacesOf linksFull true)[k]? = k :=
    borderOf_at places_fit.2 (by rw [places_fit.1]; exact hk)
  show _ = some (msgsTold told (borderOf _ _), treesTold told (borderOf _ _))
  rw [hb]
  exact counts_at h (Nat.lt_succ_of_le hk)

/-- **The binders hNt and hNm**, to the letter, at such numbers. -/
theorem hNt_hNm_of (N : Numbers) {told : List (List Oracle)} (h : CountsAre told) :
    (N.withTold (flatPlacesOf linksFull true) told).treesAt
          (flatPlacesOf linksFull true)[355 + 1]? =
        (N.withTold (flatPlacesOf linksFull true) told).treesAt
          (flatPlacesOf linksFull true)[355]? ∧
      (N.withTold (flatPlacesOf linksFull true) told).msgsAt
          (flatPlacesOf linksFull true)[355 + 1]? =
        (N.withTold (flatPlacesOf linksFull true) told).msgsAt
          (flatPlacesOf linksFull true)[355]? := by
  have a := counts_written.2.2.2.1.symm.trans (told_at N h (k := 355) (by omega))
  have b := counts_written.2.2.2.2.1.symm.trans (told_at N h (k := 355 + 1) (by omega))
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj (a.symm.trans b))
  exact ⟨e2.symm, e1.symm⟩

/-! ## The number of the index masks' oracle message -/

/-- How many oracle messages sit in each of the 83 trees, off the written layout. -/
def tenantsFull : List ℕ :=
  (List.range LFull.shapes.length).map fun j => (LFull.places.filter fun x => x.1 == j).length

set_option maxRecDepth 1000000 in
/-- 83 trees; 199 oracle messages; four in the first tree, one in the second. -/
theorem tenants_written :
    tenantsFull.length = 83 ∧ tenantsFull.sum = 199 ∧ tenantsFull.take 2 = [4, 1] := by
  decide +kernel

/-- **The second premise on told**: tree by tree, as many tenants as the written layout has. -/
def TreesAre (told : List (List Oracle)) : Prop :=
  told.flatten.map (·.tenants.length) = tenantsFull

/-- The number of the oracle message at a tenant, under it. -/
theorem msgNo_of {told : List (List Oracle)} (h : TreesAre told) (x : ℕ × ℕ) :
    First.msgNoOf told x = (tenantsFull.take x.1).sum + x.2 := by
  unfold First.msgNoOf
  rw [List.map_take, h]

/-- **The index masks' oracle message has the number 4**, at numbers laid off told. -/
theorem indexNo_of {N : Numbers} (hi : N.index = (1, 0)) {told : List (List Oracle)}
    (h : TreesAre told) (ps : List Place) : (N.withTold ps told).indexNo = 4 := by
  show First.msgNoOf told N.index = 4
  rw [hi, msgNo_of h]
  have e : tenantsFull.take 1 = [4] := by
    have t := congrArg (List.take 1) tenants_written.2.2
    rw [List.take_take] at t
    exact t
  show (tenantsFull.take 1).sum + 0 = 4
  rw [e]
  rfl

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.counts_written
#print axioms VerifiableInference.Desc.K13.Law.labels_written
#print axioms VerifiableInference.Desc.K13.Law.labels_rejects
#print axioms VerifiableInference.Desc.K13.Law.counts_at
#print axioms VerifiableInference.Desc.K13.Law.below_written
#print axioms VerifiableInference.Desc.K13.Law.planBelow_written
#print axioms VerifiableInference.Desc.K13.Law.below_rejects
#print axioms VerifiableInference.Desc.K13.Law.places_fit
#print axioms VerifiableInference.Desc.K13.Law.borderOf_at
#print axioms VerifiableInference.Desc.K13.Law.told_at
#print axioms VerifiableInference.Desc.K13.Law.hNt_hNm_of
#print axioms VerifiableInference.Desc.K13.Law.tenants_written
#print axioms VerifiableInference.Desc.K13.Law.msgNo_of
#print axioms VerifiableInference.Desc.K13.Law.indexNo_of
