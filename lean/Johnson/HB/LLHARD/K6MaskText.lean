-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6MaskText.lean: one of the seven conditions that are left in front of the law on
the sub-protocol K6 at the head (`K6LeftSeven`): `maskC`: the mask row of the
lookup on the head's calls sits as planned. It holds at the head: no premise beside the head.

Row or tool. General laws, closed facts on written values with a negative test, and a law at the
head by rewriting through named ties. A payer for a premise of another law.

The test's text. The condition is `AtFold.maskMeetsC` (Johnson/Desc/Kinds/Law/K6CallsTest.lean). Its
owners have shown that it is `maskMeetsV`, the same test at plain values (`maskMeetsC_view`,
Johnson/Desc/Kinds/Law/K6CallsView.lean). Neither file is imported by name. Here `sitsText`
and `maskText` spell out `sitsV` and `maskMeetsV`. The file K6MaskAtHead.lean beside this one says
the condition at its own name.

What the test reads, the written terms and the ties. All ties stand under the accept of the test
that holds the made plan to the written one, which `pins_of_laid` gives
(Johnson/Goal/Skeleton/PinsOfLaid.lean).
  the segment `x.link`: 24: `headAt_link` here, with `publicO_at_scope`
    (Johnson/Desc/K12/Law/Sizes/PublicOAtScope.lean).
  the numbering, the number of the mask's message, the group of segment 24, the caller's seats: off
    `P5T.seatsAllFull`, `P5T.N0Full`, `P5T.psFull`: `seats_in_scope`
    (Johnson/P5T/PlanSeatsTie.lean).
  of what the caller reads: the codes and the request's shape alone: `proofSizedFull.codes`,
    `proofSizedFull.request`: `first_written_in_scope` (Johnson/Goal/Numbers/MadeInScope.lean).
  of the members: each one's shape and seat. At the closed letters these come off the plan's seats
    by the make (`memsSame_atR`, Johnson/P5T/MembersByMake.lean); the radii and the rows' maker are
    not read.
  the head's number of slots `(At.X Zp).H.ns`: it stands in the view of the public data's shape:
    `xShape_in_scope`.

What is here.
  `lookAt_link`, `headAt_link`: the place that `headAt` gives has the head's segment's number.
  `find_any_same`: two lists with the same members, in which a seat has one member: the first member
    at a seat is the same in both.
  `sitsText`, `maskText`, `maskText_mems`.
  `memsW`: the sampled seats of `psFull`, each with its shape. `seats_one`: no seat stands twice
    among them.
  `mask_found`: at the written shape, segment 24 has a message with mask rows: so the test does not
    reject for want of one, and it is not idle.
  `mask_written`: the test accepts at the written values. `mask_rejects`: the negative test: with
    more slots than the mask code is long, it rejects.
  `maskText_at_head`.
By evaluations in Lean's kernel (`decide +kernel`): `seats_one`, `mask_found`, `mask_written`,
`mask_rejects`.

Limits. Nothing on soundness.


-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.Rad3Seat3At
import Johnson.P5T.MembersByMake
import Johnson.P5T.PlanSeatsTie
import Johnson.HB.LLHARD.SeatsNamedKey
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.First.Look.K3CallerHead
import Johnson.G.XShapeLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Params OnBytes.Model Johnson.G
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (Sent Place lookAt messagesAt keptAt sigListCalls)
open VerifiableInference.Desc.Kinds.Head.Law (headAt)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope xShape_in_scope)
open P5T (PSeat psFull seatsAllFull N0Full seats_in_scope arrOf numOfPlan)

/-- The place of a lookup on the calls has its segment's number. -/
theorem lookAt_link {X : Verify.Public} {i : ℕ} {x : Place} (h : lookAt X i false = some x) :
    x.link = i := by
  unfold lookAt at h
  simp only [Bool.false_eq_true, if_false] at h
  split_ifs at h
  all_goals first
    | (cases h
       rfl)
    | (obtain ⟨_, -, e⟩ := Option.bind_eq_some_iff.1 h
       cases e
       rfl)

theorem headAt_link {X : Verify.Public} {x : Place} (h : headAt X = some x) :
    x.link = (if X.p4 then 2 else 1) * X.NGr := by
  unfold headAt at h
  obtain ⟨y, hy, e⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, -, e2⟩ := Option.map_eq_some_iff.1 e
  rw [← e2]
  show y.link = _
  exact lookAt_link hy

/-- **One seat, one member: the first member at a seat is the same in both lists.** -/
theorem find_any_same {σ τ : Type} [DecidableEq τ] {l l' : List (σ × τ)}
    (hm : ∀ y, y ∈ l ↔ y ∈ l') (hu : ∀ y ∈ l', ∀ y' ∈ l', y.2 = y'.2 → y = y') (s : τ)
    (f : σ × τ → Bool) :
    ((l.find? fun y => decide (y.2 = s)).any f) = ((l'.find? fun y => decide (y.2 = s)).any f) := by
  cases h : l.find? fun y => decide (y.2 = s) with
  | none =>
    have h' : (l'.find? fun y => decide (y.2 = s)) = none := by
      rw [List.find?_eq_none] at h ⊢
      exact fun y hy => h y ((hm y).2 hy)
    rw [h']
  | some y =>
    have y1 : y ∈ l' := (hm y).1 (List.mem_of_find?_eq_some h)
    have y2 : y.2 = s :=
      of_decide_eq_true (List.find?_some (p := fun y : σ × τ => decide (y.2 = s)) h)
    cases h' : l'.find? fun y => decide (y.2 = s) with
    | none =>
      rw [List.find?_eq_none] at h'
      exact absurd (decide_eq_true y2) (h' y y1)
    | some z =>
      have z1 : z ∈ l' := List.mem_of_find?_eq_some h'
      have z2 : z.2 = s :=
        of_decide_eq_true (List.find?_some (p := fun y : σ × τ => decide (y.2 = s)) h')
      rw [hu y y1 z z1 (y2.trans z2.symm)]

/-- The text of `sitsV`. -/
def sitsText (arr : ℕ → ℕ → ℕ) (group : List (ℕ × ℕ)) (shs : List OracleShape)
    (seatN : ℕ → ℕ × ℕ) (mems : List (OracleShape × (ℕ × ℕ))) (k n : ℕ)
    (ok : OracleShape → Bool) : Bool :=
  (shs[k]?).any fun sh =>
    ok sh && group.contains (seatN k) && decide (arr (seatN k).1 (seatN k).2 = n) &&
      (mems.find? fun y => decide (y.2 = seatN k)).any fun y => decide (sh = y.1)

/-- The text of `maskMeetsV`. -/
def maskText (arr : ℕ → ℕ → ℕ) (group : List (ℕ × ℕ)) (D : Sent) (i : ℕ) (seatN : ℕ → ℕ × ℕ)
    (mems : List (OracleShape × (ℕ × ℕ))) (n ns : ℕ) : Bool :=
  ((messagesAt D i).findIdx? fun z => z.shape.maskRows != 0).any fun m0 =>
    ((group.filter fun x => arr x.1 x.2 == n).length == 1) &&
      sitsText arr group ((sigListCalls D (fun _ => 0) i).map (·.1)) seatN mems
        ((keptAt D i).length + m0) n fun s =>
          decide (0 < s.maskRows) &&
            (ns == 0 || decide (ns - 1 < (Johnson.Pack.pMask D.codes s).ell))

/-- The test reads of the members no more than who sits where. -/
theorem maskText_mems (arr : ℕ → ℕ → ℕ) (group : List (ℕ × ℕ)) (D : Sent) (i : ℕ)
    (seatN : ℕ → ℕ × ℕ) {l l' : List (OracleShape × (ℕ × ℕ))} (hm : ∀ y, y ∈ l ↔ y ∈ l')
    (hu : ∀ y ∈ l', ∀ y' ∈ l', y.2 = y'.2 → y = y') (n ns : ℕ) :
    maskText arr group D i seatN l n ns = maskText arr group D i seatN l' n ns := by
  unfold maskText sitsText
  simp only [find_any_same hm hu]

/-- The sampled seats of the written list, each with its shape. -/
def memsW : List (OracleShape × (ℕ × ℕ)) :=
  (psFull.filter (·.smpd)).map fun p => (p.shape, p.seat)

/-- What the caller reads, at the written codes and shape; a layout and lists of arrays ride. -/
def sentW (lay : ReqLayout) (arrs : Array (Array (ℕ × String))) : Sent :=
  ⟨proofSizedFull.codes, proofSizedFull.request, lay, arrs⟩

/-- The test at the written values; a layout and lists of arrays ride. -/
def maskW (lay : ReqLayout) (arrs : Array (Array (ℕ × String))) (ns : ℕ) : Bool :=
  maskText (arrOf seatsAllFull) (N0Full.group 24) (sentW lay arrs) 24
    (P6T.seatCallsT psFull (sentW lay arrs) 24) memsW (numOfPlan seatsAllFull 24 0) ns

/-- Neither the layout nor the lists of arrays is read. -/
theorem maskW_blind (lay : ReqLayout) (arrs : Array (Array (ℕ × String))) (ns : ℕ) :
    maskW lay arrs ns = maskW ⟨[]⟩ #[] ns := rfl

set_option maxRecDepth 1000000 in
/-- **No seat stands twice among the sampled seats.** -/
theorem seats_one : (memsW.map (·.2)).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **Segment 24 has a message with mask rows.** -/
theorem mask_found :
    ((messagesAt (sentW ⟨[]⟩ #[]) 24).findIdx? fun z => z.shape.maskRows != 0).isSome = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test accepts at the written values.** -/
theorem mask_written : maskW ⟨[]⟩ #[] xShapeFull.2.2.1 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: more slots than the mask code is long. -/
theorem mask_rejects : maskW ⟨[]⟩ #[] 1000000000 = false := by decide +kernel

/-- **The condition, at the head's own terms.** -/
theorem maskText_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    maskText h.𝔇.arr (h.𝔇.N.group 24) h.𝔇.sent x.link (h.𝔇.l3.seat x.link false)
      (h.𝔇.ms.map fun y => ((y.1.l.get y.2).1, VerifiableInference.Desc.Sound.seatOf y))
      (At.num Zp 24 0) (At.X Zp).H.ns = true := by
  have hZ := h.scope
  have L := h.laid
  have hy := (pins_of_laid hZ L).1
  have hl := LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks
  obtain ⟨hps, hAll, hN0⟩ := seats_in_scope hZ L.pub hy hl
  have hF := H2K.Sizes.publicO_at_scope hZ L.publicO
  have hx : x.link = 24 := by
    have h4 : (At.X Zp).p4 = true := hF.p4
    have hG : (At.X Zp).NGr = 12 := hF.groups
    rw [headAt_link h.headAt, h4, hG]
    rfl
  have FW := first_written_in_scope hZ L.pub hy
  have hns : (At.X Zp).H.ns = xShapeFull.2.2.1 :=
    congrArg (fun V => V.2.2.1) (xShape_in_scope hZ L.pub hy)
  have hs : (At.N Zp cF).sent = N0Full.sent := by
    rw [← hN0]
    rfl
  have hm : ∀ y, y ∈ (P5T.msAtR Zp (At.rad Zp Z.lay)).map
      (fun y => ((y.1.l.get y.2).1, VerifiableInference.Desc.Sound.seatOf y)) ↔ y ∈ memsW := by
    intro y
    rw [P5T.memsSame_atR, hps]
    rfl
  have hD : At.sentAt Zp = sentW (At.layout Zp) (Zp.made.p.built.links.map (·.arrayOf)) := by
    unfold At.sentAt sentW
    rw [show At.cs Zp = proofSizedFull.codes from FW.1,
      show At.shape Zp = proofSizedFull.request from FW.2.2.1]
  rw [hx, hns]
  show maskText (arrOf (P5T.planSeatsAll Zp Zp.D)) ((At.N Zp cF).group 24) (At.sentAt Zp) 24
    (P6T.seatCallsT (P5T.planSeats Zp Zp.D.1) (At.sentAt Zp) 24)
    ((P5T.msAtR Zp (At.rad Zp Z.lay)).map
      fun y => ((y.1.l.get y.2).1, VerifiableInference.Desc.Sound.seatOf y))
    (numOfPlan (P5T.planSeatsAll Zp Zp.D) 24 0) xShapeFull.2.2.1 = true
  rw [maskText_mems _ _ _ _ _ hm (List.inj_on_of_nodup_map seats_one), hAll, hps, hD,
    group_same hs 24]
  exact (maskW_blind _ _ _).trans mask_written

end P5J

#print axioms P5J.lookAt_link
#print axioms P5J.headAt_link
#print axioms P5J.find_any_same
#print axioms P5J.maskText_mems
#print axioms P5J.maskW_blind
#print axioms P5J.seats_one
#print axioms P5J.mask_found
#print axioms P5J.mask_written
#print axioms P5J.mask_rejects
#print axioms P5J.maskText_at_head
