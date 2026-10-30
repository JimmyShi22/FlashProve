-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PlanesAtHead.lean: CONDITIONAL, under the library's one head on the
public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): the table's sentence on the forms of the
lookup's run "planes" holds at the state behind the lay of an attention segment's own rounds, from
the table's item on the worth of the planes at the state in front, at the same witness, at one
reached state that meets the promise in front of the block.

It is `formsPlanes_behind` (Johnson/Desc/K5/Honest/Law/PlanesForward.lean) at the head's letters.
Its premises on the state come from `door_at_head`, `runs_at_head`
(Johnson/Desc/K5/Honest/Law/DoorAtHead.lean) and `bareLeft_head`
(Johnson/Desc/K5/Honest/Law/BehindAtHead.lean); that what the lookup left stands for some rounds
lies in `K3LeftOutIs`; its public premises are paid by lemmas of the library's from the head. Its
two premises over all states and all lists of forms speak of two letters of the filling by their
make, and are paid as the library pays them where it walks the road backward: "every message that a
form reads is a member of the composer's list" by `memAt_field`
(Johnson/Desc/First/Att/Door/Law/K5MemOfSome.lean), "the stated function is that of the plan's
tables" by `hSt_of_arm` (Johnson/Desc/First/Att/K05StatedArm.lean).

Main names:
  `planesIn_head`: the public test tied to the run "planes" accepts behind the lay.
  `planes_at_head`: **the sentence**, over the closed filling's own list of runs, its reader, its
    seats and its reading of the witness, from `K3WorthPlanes` in front.
  `planes_item_at_head`: the same between the closed filling's own two items: worth "planes" in
    front gives formsT "planes" behind.

Limits. The head is a hypothesis. That a state of an honest run is reached, bears no mark and meets
the promise in front, that the hearing returns there, and that the item in front holds of the honest
witness, are not shown here. Eight public items (`Open8`), and in the last two theorems a ninth
(`Pub.callerIn`), are asked to be open in the caller's own list Q: that they are open in the table's
own list is not decided here. `planes_item_at_head` speaks of the two items of the closed filling
`P5J.mgAtAll h`. A filling that is made of it by turning other fields has the same two items, by
unfolding (no theorem states it). One such filling is `honest` at it
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): it turns five fields, and neither of these two is
among them. Of a filling with other items nothing is said. At the function `OnBytes.secondHashFunction`, of
which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.BehindAtHead
import Johnson.Desc.K5.Honest.Law.PlanesForward

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (K5Place behind hear Heard fork_front)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (K3WorthPlanes attNu)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The public test tied to the run "planes" accepts behind the lay.** Conditional as
`runs_at_head`, at the border's own number. -/
theorem planesIn_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4) (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some (plK5 g)) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) :
    K9.formsInT (h.𝔇.pubD.Rd (2 * g + 1)) (h.𝔇.pubD.N.sent (2 * g + 1) 0) 1 "planes"
      (behind s att hd G) = true := by
  obtain ⟨h4, _, _⟩ := scope_all h
  obtain ⟨_, _, hxl, _⟩ := Att.P.place_calls h4 ea hx
  obtain ⟨blk, hat⟩ := seated_all h hg
  obtain ⟨_, gL, Y, hLf⟩ := door_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon
    (id : Aff → Aff) (fun _ => (none : Option Unit))
  obtain ⟨_, _, _, _, U, _, hz⟩ := front_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e
  have U' : Att.P.U3There (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att (Att.P.parCOf a) := by
    have := U
    unfold ownAt at this
    rwa [hxl] at this
  obtain ⟨i, K, _, _, _, _, _, _, hinOf, _⟩ :=
    runs_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hh
  obtain ⟨g₁, G₁, hlk, _, hfk, hlf⟩ := bareLeft_head h hg hr
  obtain rfl : g₁ = gL := Option.some.inj (hlk.symm.trans Y.heard)
  obtain rfl : G₁ = att.F := Option.some.inj (hfk.symm.trans (fork_front e))
  obtain ⟨Lk, hLk⟩ := lkAt_all h hg
  have hrP : h.𝔇.pubD.runs (2 * g + 1) 2 "planes" = [(1, "planes")] := by
    rw [runsIs_all h]
    exact runsAt_planes (sub_full hg)
  have hp := planesIn_at h.𝔇.pubD mgB0.pub (mgAtAll h) (hpubPlus_all h) (π := π) (id : Aff → Aff)
    (2 * g + 1) a hrP _ Lk (hRd_plus (rdIs_all h) hLk) K3Lot.ofForm clForm_lot a.S.cf.lmb
    (planesAt_all h hg ea hLk) sameOut_all e hh hz hinOf U' hLf hlf (planesOkAt_all h ea hx)
    (posG_all h hg ea hat) (colsFit_all h ea hx) rfl
  rw [hpubPlus_all h, pubAll_formsInT, hrP] at hp
  simpa only [List.all_cons, List.all_nil, Bool.and_true] using hp

/-- **The sentence on the forms of the run "planes", behind the lay, at the head's letters.**
Conditional: as `planesIn_head`; hcQ: one more public item is open in front; hW: the item on the
planes' worth holds in front, at the witness w. -/
theorem planes_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) (hcQ : Pub.callerIn (2 * g + 1) ∈ Q) {π : ProofFile.InstPub} {s : S}
    {y : Strs} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4) (π, s))
    (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some (plK5 g)) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) {Cells Tok : Type}
    {w : Wit Cells Tok MsgT}
    (hW : K3WorthPlanes (K3.seatCalls K3Lot.ofForm).fork (K3.seatCalls K3Lot.ofForm).heard x₁.fs
      x₁.lm x₁.F.next
      (attNu x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr) s w) :
    ∀ p ∈ h.𝔇.pubD.runs (2 * g + 1) 2 "planes",
      formsTQ (h.𝔇.pubD.Rd (2 * g + 1)) h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) p.1 p.2
        (behind s att hd G) (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w) := by
  obtain ⟨h4, _, _⟩ := scope_all h
  have hP := planIs_all h
  obtain ⟨_, hxns, hxl, hfs⟩ := Att.P.place_calls h4 ea hx
  obtain ⟨blk, hat⟩ := seated_all h hg
  obtain ⟨hok, hG⟩ := seatedOk_guard_all h hg hat
  have pOk := planOk_plus (beforeAll Zp g) hat hok ea
  have cOk := claimsOk_plus (beforeAll Zp g) hat hok ea
  have hA : (P5J.At.X Zp).A[x₁.link / 2]? = some a := by
    rw [hxl, show (2 * g + 1) / 2 = g by omega]
    exact ea
  have T := dataIs_all h (2 * g + 1)
  have hatt : h.𝔇.pubD.d5.isAtt (2 * g + 1) = true :=
    isAtt_of h.𝔇.pubD.d5 (by rw [T.d5links]; exact sub_full hg)
  have hlay : FillK4.isLay h.𝔇.pubD.links (2 * g + 1) = false :=
    att_not_lay (by rw [T.links]; exact sub_full hg)
  have nH : (2 * g + 1 == h.𝔇.pubD.mH) = false := notHead_plus (mHIs_all h) h4
  have hf : h.𝔇.pubD.d5.first? (2 * g + 1) = some (Forest.elems a.fs) :=
    first_at h.𝔇.pubD.d5 (by rw [T.d5W]; exact hP) (by rw [T.d5W]; exact h4)
      (by rw [T.d5W]; exact ea) (by rw [T.d5W]; exact hx)
  have h5 : att.heard5 = none := by
    have hc := Att.P.onAt_pub hon hu _ hcQ
    rw [hpub, hpubPlus_all h, pubAll_callerIn_att h.𝔇.pubD _ (2 * g + 1) hlay hatt, hf] at hc
    exact (Att.P.callerIn3_at e hc).1
  obtain ⟨_, gL, Y, hLf⟩ := door_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon
    K3Lot.ofForm (fun _ => (none : Option Unit))
  obtain ⟨i, K, _, _, _, _, _, _, hin, _⟩ :=
    runs_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hh
  obtain ⟨F₀, F', rsK, _, hnx, Lf, _, e2, _⟩ := hLf
  obtain rfl : F' = att.F :=
    Option.some.inj ((show s.fork? = some F' from e2).symm.trans (fork_front e))
  have hshape : gL.shape = x₁.fs := Lf.shape
  have hlm : x₁.lm = a.S.cf.lmb := lmIs_all h ea hx
  have hlk : att.lookHeard = some gL := by
    have := Y.heard
    rw [Att.P.lookHeard_front e] at this
    exact this
  have hBare : OnBytes.Road.Rows.Bare gL.leaves.start := by
    have hp := Att.P.onAt_pubP hon hu _ Oq.q6
    rw [hpubP] at hp
    have hp' : VerifiableInference.OnPublicFiles.k3LeftItemAt (P5J.At.X Zp) (2 * g + 1) s := hp
    obtain ⟨_, _, _, hb⟩ := hp'
    have he := hb _ Y.heard
    intro Qr z hz
    rw [he] at hz
    cases hz
  obtain ⟨Lk, hLk⟩ := lkAt_all h hg
  have C := k5CondAt_at_head h hL
  have Tc := C.each g hg a x₁ ea hx
  have hIn := planesIn_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hh
  have R := formsPlanes_behind x₁ a h.𝔇.sent h.𝔇.l3.rad ⟨Unit, Unit, Unit, fun _ _ => ()⟩ Unit
    (fun _ => 0) (ofPlan_all h ea) (posG_all h hg ea hat) _ Lk K3Lot.ofForm
    (fun f => (clForm_lot f).1) (planesAt_all h hg ea hLk) e hu h5 hh
    (by rw [silent_none (P5J.At.X Zp) nH Lk]) hin hlk (hshape.trans hfs)
    (by
      rw [hshape]
      exact VerifiableInference.OnPublicFiles.foOk_of_shape
        (attOK_plus (beforeAll Zp g) h.𝔇.sent h.𝔇.l3.rad hP h4 ea hx hG pOk cOk).shape)
    hBare (by rw [hshape]; exact colsFit_all h ea hx) x₁.F.next a.ns
    (Att.P.numsPlan a.own (x₁.F.next + Forest.elems x₁.fs)) (h.𝔇.pubD.Rd (2 * g + 1))
    (hRd_plus (rdIs_all h) hLk) h.𝔇.St h.𝔇.pubD.N h.𝔇.arr (seatAll h x₁) h.𝔇.ms a.ns
    (Att.P.frontAll_of_door hA (ofPlan_all h ea) Y) (tiePubCells_all h hg ea hx Tc.cells)
    (Nat.le_of_eq hxns.symm) (w := w) (by rw [hxl]; exact hIn)
    (by rw [hshape, ← hlm]; exact hW) (rsK := rsK)
    (by rw [hshape, ← hlm, ← hnx]; exact Lf.heardIs)
    (fun _ j _ => memAt_field C.head.oneShape _ _ Tc.tests.someMem j)
    (fun s' a₀ h' hl => Att.P.hSt_of_arm hA h.𝔇.uL h.𝔇.uH s' a₀ h' hl)
  rw [hxl] at R
  have hrP : h.𝔇.pubD.runs (2 * g + 1) 2 "planes" = [(1, "planes")] := by
    rw [runsIs_all h]
    exact runsAt_planes (sub_full hg)
  intro p hp
  rw [hrP] at hp
  obtain rfl := List.mem_singleton.1 hp
  exact R

/-- **Between the closed filling's own two items**: worth "planes" in front gives formsT "planes"
behind. Conditional as `planes_at_head`, with the item in the closed filling's own letters; y₁, y₂:
the items' strings, which neither sentence reads. -/
theorem planes_item_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) (hcQ : Pub.callerIn (2 * g + 1) ∈ Q) {π : ProofFile.InstPub} {s : S}
    {y : Strs} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4) (π, s))
    (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some (plK5 g)) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) (y₁ y₂ : Strs)
    {w : Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT}
    (hW : (mgAtAll h).worth (2 * g + 1) 2 "planes" (π, s) y₁ w) :
    (mgAtAll h).formsT (2 * g + 1) 2 "planes" (π, behind s att hd G) y₂ w := by
  have Gn := mgGains_all h (scope_all h).1 ea hx
  rw [Gn.planes] at hW
  rw [Gn.formsT]
  exact ⟨planes_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hcQ hr hu hon e hh hW,
    fun e' => absurd e' (by decide)⟩

end

end H2K5.Honest

#print axioms H2K5.Honest.planesIn_head
#print axioms H2K5.Honest.planes_at_head
#print axioms H2K5.Honest.planes_item_at_head
