-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/DoorAtHead.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): at a state without a mark that the first chain's own
sub-protocols reach, and that meets the promise which the table of the verifier's blocks carries
in front of the block of an attention segment's own rounds, at a filling whose public halves are
those of the library's closed filling (`P5J.mgAtAll h`): the library's list of tests and equations
in front of that block (`DoorYes`) holds, and what the lookup leaves is as the library's law on the
runs' returns asks it (`K3LeftOutIs`). So the segment's four runs of claims return behind the lay,
where the segment is open and the hearing returns.

It is `doorYes_narrow` (Johnson/Desc/K5/Honest/Law/DoorNarrow.lean) and `fiveAt_of_reach`
(Johnson/Desc/K5/Honest/Law/FiveReach.lean) at the head's letters. Of the first one's public
premises every one BUT the eight memberships (`Open8`) is paid by a lemma of the library's from the
head. Three public returns are asked beside: hL: the list of seats can be laid; ea: the group's
plan; hx: the place of the lookup on the calls. The library has all three from the head
(`P5J.At.laid_some` at the head's field `opts.laid`; `planAt_all`, `lookC_all`,
Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean).

Main names:
  `Open8 m Q`: a NAMED PREMISE: eight public items are open in the list Q.
  `fiveAt_head`: the five facts at a reached state, at the head's letters.
  `door_at_head`: **`DoorYes` and `K3LeftOutIs`.**
  `front_at_head`: so what the library's laws on the state behind the lay ask in front
    (`FrontAll`, `U3There`, the filled slots, the sized ledger).
  `runs_at_head`: **`RunsReturn`**, where the hearing returns.
  `own_at_head`: **the sentence on the forms of the segment's own runs, in the closed filling's
    own letters** (its reader, its list of runs, its seats), from what the claims say (`SayAt`):
    `own_of_runs` (Johnson/Desc/K5/Honest/Law/Own.lean); of its premises three are left: the
    hearing returns; what the lookup returned is laid in the open segment; the algebra.

The filling Mg is a letter with two equations (its tests with code and what its items say beside
them are the closed filling's): the strings y, the list of open items O and Q are letters too.
Where a called law of the library's has free letters that its conclusion does not read (a map from
forms to claims, a numbering of places, an extractor's types, a map to the field), trivial values
are laid for them in the proofs: the law holds at every value.
Limits. The head is a hypothesis; that it is met is not shown here. That a state of an honest run
is reached, meets the promise and bears no mark is not shown here. `Open8` is asked at the
caller's own list Q: that the eight are open at the table's own list at the border is not decided
here. At the function `OnBytes.secondHashFunction`, of which nothing is asked here; at the library's full size
alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.FiveReach
import Johnson.Desc.K5.Honest.Law.Own
import Johnson.Desc.First.Att.Door.Law.K5KindWhole
import Johnson.Desc.First.Att.Door.Law.LeftIsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent lookAt sigListCalls keptAt bornAt)
open VerifiableInference.Desc.First.Att.P (DoorYes K3LeftOutIs K5Place)
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

/-- A NAMED PREMISE: eight public items are open in the list Q. A test on the table's lists. -/
structure Open8 (m : ℕ) (Q : List Pub) : Prop where
  q1 : Pub.more (some m) "K5.liveReq" ∈ Q
  q2 : Pub.more (some m) "K5.readsThere" ∈ Q
  q3 : Pub.look m ∈ Q
  q4 : Pub.ledger m ∈ Q
  q5 : Pub.freeAbove m ∈ Q
  q6 : Pub.left m ∈ Q
  q8 : Pub.linkFresh m ∈ Q
  q11 : Pub.more (some m) "frame.sentIs" ∈ Q

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- The five facts at a reached state, at the head's letters. Conditional: the head; hL: the list
of seats is L; hr: the state is reached by the first chain's own sub-protocols; hu: no mark. -/
theorem fiveAt_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {k : ℕ} {π : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none) :
    FiveAt L (P5J.At.d12 Zp L).M h.𝔇.sent s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have F := fiveAt_of_reach h.scope h.reads O h.laid.planOk
    (P5J.sends_at O (P5J.sendsB_of_madeRow h.toAtMg (pins_at_head h.toAtMg).1)) hL hr hu
  exact ⟨F.seats, F.shapes, F.liveShape.trans rfl, F.liveLayout.trans rfl, F.codes.trans rfl⟩

/-- **The list of tests in front of the block, and what the lookup leaves, at the head's
letters.** Conditional: the head; hL; hg: the group; ea, hx: the group's plan and the place of the
lookup on the calls; hpub, hpubP: the filling's two public halves are the closed filling's; Oq:
`Open8`; hr, hu, hon: the state is reached, bears no mark and meets the promise in front of the
block. claim, io: letters of the library's law; free. -/
theorem door_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {Cl J₀ : Type} [DecidableEq J₀] (claim : Aff → Cl) (io : Fo.Pl → Option J₀) :
    ∃ (x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option J₀)) (gL : Forest.Heard),
      DoorYes (P5J.At.X Zp) x₁ h.𝔇.sent (bornAt h.𝔇.sent x₁.link)
        (keptAt h.𝔇.sent x₁.link).length (h.𝔇.pubD.N.sent x₁.link 0)
        (Att.P.psOf (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link) (seatAll h x₁)
          (Att.P.readMsgs h.𝔇.sent x₁ a.seam.tl))
        (Att.P.qsOf (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link)
          (Att.P.readMsgs h.𝔇.sent x₁ a.seam.tl)) a.ns gL s ∧
      K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard x₁.fs x₁.lm x₁.F.next io
        (fun F => Att.P.Room F a.ns x₁.F.next
          (Forest.elems x₁.fs + (Att.P.slotsOf (Att.P.script a.own) + 0))) x0 gL s := by
  obtain ⟨h4, _, _⟩ := scope_all h
  have hP := planIs_all h
  obtain ⟨_, _, hxl, _⟩ := Att.P.place_calls h4 ea hx
  have Ix : K5Place P5J.At.links (2 * g + 1) ⟨1, some (2 * g + 1), 3, .K5⟩
      ⟨1, some (2 * g + 1), 4, .K1⟩ := ⟨rfl, rfl, sub_full hg, rfl, rfl⟩
  obtain ⟨att, e⟩ := k5_here Ix (Att.P.onAt_shape hon hu)
  have T := dataIs_all h (2 * g + 1)
  have Sn := dataSent_all h
  have hatt : h.𝔇.pubD.d5.isAtt (2 * g + 1) = true :=
    isAtt_of h.𝔇.pubD.d5 (by rw [T.d5links]; exact sub_full hg)
  have hlay : FillK4.isLay h.𝔇.pubD.links (2 * g + 1) = false :=
    att_not_lay (by rw [T.links]; exact sub_full hg)
  have nH : (2 * g + 1 == h.𝔇.pubD.mH) = false := notHead_plus (mHIs_all h) h4
  have har : h.𝔇.pubD.d3.arrayOf.getD (2 * g + 1) #[] = h.𝔇.sent.arrayOf.getD (2 * g + 1) #[] := by
    rw [Sn.d3]
    rfl
  have hborn : bornOf h.𝔇.pubD.d5.shape (2 * g + 1) = bornAt h.𝔇.sent x₁.link := by
    rw [Sn.d5shape, hxl]
    rfl
  have hown : h.𝔇.pubD.d5.ownOf (2 * g + 1) = h.𝔇.pubD.N.sent x₁.link 0 := by rw [T.own, hxl]
  have Ts := ((k5CondAt_at_head h hL).each g hg a x₁ ea hx).tests
  obtain ⟨x0, gOf, hLI⟩ := leftIs_at claim hP h4 ea hx io
  have hleft : Mg.pubP (.left (2 * g + 1)) (π, s) →
      K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard x₁.fs x₁.lm x₁.F.next io
        (fun F => Att.P.Room F a.ns x₁.F.next
          (Forest.elems x₁.fs + (Att.P.slotsOf (Att.P.script a.own) + 0))) (x0 s) (gOf s) s := by
    intro hp
    rw [hpubP] at hp
    exact hLI s hp
  have R := doorYes_narrow h.𝔇.pubD L (P5J.At.d12 Zp L).M _ Mg (hpub.trans (hpubPlus_all h))
    (P5J.At.N Zp cF) P5J.At.links Ix O Q hatt hlay nH (nsOf_all h hg ea) Oq.q1 Oq.q2 Oq.q3 Oq.q4
    Oq.q5 Oq.q6 Oq.q8 Oq.q11 x₁ hxl h.𝔇.sent har (bornAt h.𝔇.sent x₁.link) hborn
    (keptAt h.𝔇.sent x₁.link).length _ _ π s y hon hu att e _ _ _ _ _ _ _ (gOf s) hleft
    (by rw [hown]; exact Ts.seatsPlan) Ts.shapesPlan (fiveAt_head h hL hr hu)
  rw [T.d5W, hown] at R
  exact ⟨x0 s, gOf s, R, hleft (Att.P.onAt_pubP hon hu _ Oq.q6)⟩

/-- The seats of the segment's first sending, by the table's numbers. -/
abbrev ownAt (x₁ : Look.Place) : List (ℕ × ℕ) := h.𝔇.pubD.N.sent x₁.link 0

/-- **What the library's laws on the state behind the lay ask in front, at the head's letters.**
Conditional as `door_at_head`, and e: the open segment. -/
theorem front_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) :
    ∃ ps qs gL, Att.P.FrontAll x₁ a h.𝔇.sent (ownAt h x₁) ps qs a.ns gL s ∧
      Att.P.U3There (ownAt h x₁) s att (Att.P.parCOf a) ∧ _root_.Fo.FilledA att.F gL.cEnd ∧
      OnBytes.Model.Road.Sized att.F := by
  obtain ⟨h4, _, _⟩ := scope_all h
  obtain ⟨_, _, hxl, _⟩ := Att.P.place_calls h4 ea hx
  have hA : (P5J.At.X Zp).A[x₁.link / 2]? = some a := by
    rw [hxl, show (2 * g + 1) / 2 = g by omega]
    exact ea
  obtain ⟨_, gL, Y, _⟩ := door_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon
    (id : Aff → Aff) (fun _ => (none : Option Unit))
  exact ⟨_, _, gL, front_of_door hA (ofPlan_all h ea) Y e⟩

/-- **The segment's four runs of claims return behind the lay, at the head's letters.**
Conditional as `door_at_head`, and e: the open segment; hh: the hearing of the segment's own
rounds returns from that segment's ledger. -/
theorem runs_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Att.P.Heard} {G : Fork}
    (hh : Att.P.hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) :
    Att.P.RunsReturn a s att hd G := by
  obtain ⟨h4, _, _⟩ := scope_all h
  obtain ⟨blk, hb⟩ := seated_all h hg
  obtain ⟨hok, hG⟩ := seatedOk_guard_all h hg hb
  obtain ⟨_, _, Y, hl⟩ := door_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon
    (id : Aff → Aff) (fun _ => (none : Option (Look.JAtt x₁.ns a.seam.tl)))
  exact runsReturn_of_door id (planIs_all h) h4 (beforeAll Zp g) ea hx hG
    (planOk_plus (beforeAll Zp g) hb hok ea) (claimsOk_plus (beforeAll Zp g) hb hok ea) h.𝔇.sent
    h.𝔇.l3.rad ⟨Unit, Unit, Unit, fun _ _ => ()⟩ Unit (fun _ => 0) hl Y e hh

/-- **The sentence on the forms of the segment's own runs, in the closed filling's own letters,
from what the claims say.** Conditional as `runs_at_head`, and hgL: what the lookup returned is
laid in the open segment; hS: `SayAt` in the sentence's world, at whatever the claims' reading at
the state behind the lay returns. St, rd: letters. -/
theorem own_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Att.P.Heard} {G : Fork}
    (hh : Att.P.hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) (St : Stated)
    (rd : ℕ × ℕ → MsgQ) {gL : Forest.Heard} (hgL : att.g = some gL)
    (hS : ∀ i K, Att.P.inOf (Att.P.seatCO (Att.P.parCOf a)) (Att.P.parCOf a)
        (Att.P.behind s att hd G) = some (i, K) →
      K5Law.SayAt Reading.gl (worldBehind St (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att hd G rd) a.S gL
        i K) :
    ∀ p ∈ h.𝔇.pubD.runs (2 * g + 1) 3 "own",
      formsTQ (h.𝔇.pubD.Rd (2 * g + 1)) St (h.𝔇.pubD.N.sent (2 * g + 1) 0) p.1 p.2
        (Att.P.behind s att hd G) rd := by
  obtain ⟨h4, _, _⟩ := scope_all h
  obtain ⟨_, _, hxl, _⟩ := Att.P.place_calls h4 ea hx
  obtain ⟨blk, hb⟩ := seated_all h hg
  obtain ⟨hok, hG⟩ := seatedOk_guard_all h hg hb
  have pOk := planOk_plus (beforeAll Zp g) hb hok ea
  have cOk := claimsOk_plus (beforeAll Zp g) hb hok ea
  obtain ⟨Lk, hLk⟩ := lkAt_all h hg
  have hRd := rds_plus h.𝔇.pubD g a _ Lk (hRd_plus (rdIs_all h) hLk) ProofFile.sameReply
    (statesAt_all h hg ea hLk) sameOut_all
  have gf := Att.P.geoFits_at_seat (planIs_all h) ea
    (okAll_plus (P5J.At.X Zp) g (beforeAll Zp g) a h.𝔇.sent h.𝔇.l3.rad (planIs_all h) h4 ea hG pOk
      cOk)
  obtain ⟨_, _, _, _, U, _, hz⟩ := front_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e
  have U' : Att.P.U3There (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att (Att.P.parCOf a) := by
    have := U
    unfold ownAt at this
    rwa [hxl] at this
  have Rt := runs_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hh
  have H := own_of_runs (h.𝔇.pubD.Rd (2 * g + 1)) St a (h.𝔇.pubD.N.sent (2 * g + 1) 0)
    (fun name R hn hR => hRd name _ R hn hR) hh hz Rt gf U' rd hgL hS
  intro p hp
  rw [runs3_plus h.𝔇.pubD g h.𝔇.links (runsIs_all h) (sub_full hg)] at hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact H "first" (by simp)
  · exact H "keys" (by simp)
  · exact H "second" (by simp)

end

end H2K5.Honest

#print axioms H2K5.Honest.fiveAt_head
#print axioms H2K5.Honest.door_at_head
#print axioms H2K5.Honest.front_at_head
#print axioms H2K5.Honest.runs_at_head
#print axioms H2K5.Honest.own_at_head
