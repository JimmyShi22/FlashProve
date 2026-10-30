-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/BehindAtHead.lean: CONDITIONAL, under the library's one head on the
public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): the promise which the table of the verifier's
blocks carries BEHIND the block of an attention segment's own rounds follows from the promise in
front of it, at one state that the first chain's own sub-protocols reach, at a filling Mg five of
whose fields are the library's closed filling's and whose three sentences on the strings hold
outright.

It is the library's law `k5_t2` (Johnson/Desc/First/Att/K05T2.lean), which is general in the
filling, with its premises paid: the place, the book and the plan from the head; `K5Fill` by
`k5Fill_honest` (Johnson/Desc/K5/Honest/Law/FillHonest.lean); the three premises on public tests
by Johnson/Desc/K5/Honest/Law/BehindParts.lean, at the one state, from `door_at_head` and
`runs_at_head` (Johnson/Desc/K5/Honest/Law/DoorAtHead.lean) and two further facts at the reached
state.

Main names:
  `HonestLike h Mg`: a NAMED PREMISE on the filling: five of its fields are the closed filling's;
    its three sentences on the strings hold outright.
  `AtBorder g O Q`: a NAMED PREMISE on the two lists of what is open in front of the block: tests
    on the table's lists.
  `bareLeft_head`: at a state that the first chain's own sub-protocols reach at the border in
    front of the block: something is held as received from the lookup; its kept rows name no
    entry; the library's test on what the lookup has left accepts at it and the ledger. By the
    library's two laws along the fold (`rowsBare_reached`, `leftAt_reached`,
    Johnson/Desc/First/Look/), which stand over the chain's flat list as it is.
  `behind_at_head`: **the promise behind the block.**

Limits. The head is a hypothesis. That a state of an honest run is reached, bears no mark and meets
the promise in front, that a filling meets `HonestLike` and that the table's own lists meet
`AtBorder` are not shown here. The last two are shown in
Johnson/Desc/ProofFile/Honest/K5/Law/Behind.lean (`honestLike_at`, `atBorder_at`). At the function
`OnBytes.secondHashFunction`, of which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.DoorAtHead
import Johnson.Desc.K5.Honest.Law.FillHonest
import Johnson.Desc.K5.Honest.Law.BehindParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (K5Place K5Book behind hear Heard SameBelow fork_front)
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

/-- The place of the block of the own rounds of the attention segment of group g. -/
abbrev plK5 (g : ℕ) : VerifiableInference.Desc.Place := ⟨1, some (2 * g + 1), 3, .K5⟩

/-- The place behind it. -/
abbrev plK1 (g : ℕ) : VerifiableInference.Desc.Place := ⟨1, some (2 * g + 1), 4, .K1⟩

/-- A NAMED PREMISE on the two lists of what is open in front of the block. Tests on the table's
lists. -/
structure AtBorder (g : ℕ) (O : List Item) (Q : List Pub) : Prop where
  /-- eight public items are open -/
  open8 : Open8 (2 * g + 1) Q
  /-- and a ninth, which the block's row asks -/
  caller : Pub.callerIn (2 * g + 1) ∈ Q
  /-- every open public item is one of a written list -/
  twenty : ∀ q ∈ Q, q ∈ ten (2 * g + 1) ∨ q ∈ quiet9 (2 * g + 1) ∨
    q = .more (some (2 * g + 1)) "ledger.treesAre" ∨ q = .more (some (2 * g + 1)) "K5.lookLeft"
  /-- none is one of the five names of the library's wider filling -/
  narrow : ∀ q ∈ Q, isWideQ q = false
  /-- beside the index's, one tied test is met at the border: that of the run "objects" -/
  ties : ∀ i ∈ O, (rowOf P5J.At.links (plK5 g)).ins.contains i = false → i ≠ .pinI →
    ∀ q ∈ tiesOf i, q = .formsInT (2 * g + 1) 2 "objects"

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- A NAMED PREMISE on a filling: five of its fields are the closed filling's; its three sentences
on the strings hold outright. -/
structure HonestLike {Cells Tok : Type} (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT)) :
    Prop where
  pub : Mg.pub = (mgAtAll h).pub
  pubP : Mg.pubP = (mgAtAll h).pubP
  held : Mg.held = (mgAtAll h).held
  inOrder : Mg.inOrder = (mgAtAll h).inOrder
  more : Mg.more = (mgAtAll h).more
  decodes : ∀ a y, Mg.decodes a y
  shown : ∀ j t y, Mg.shown j t y
  noColl : ∀ j t a y, Mg.noColl j t a y

include h in
/-- **Two further facts at a state that is reached at the border in front of the block.**
Conditional: the head; hg; hr. -/
theorem bareLeft_head {g : ℕ} (hg : g < 12) {π : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4) (π, s)) :
    ∃ g₁ G, s.lookHeard? = some g₁ ∧ (∀ f ∈ g₁.rows.toList, f.ents = #[]) ∧ s.fork? = some G ∧
      FillBare.leftAtB g₁ G = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, rs, cols, hf⟩ := hr.fold
  obtain ⟨g₁, e0, hb⟩ := VerifiableInference.OnPublicFiles.rowsBare_reached h.scope h.reads O
    h.laid.planOk (2 * g + 1) (by omega) false
    (by rw [VerifiableInference.OnPublicFiles.k3Ix_att]; exact hf)
  have e1 : s.lookHeard? = some g₁ := e0
  obtain ⟨g₂, G, e2, e3, hl⟩ := VerifiableInference.OnPublicFiles.leftAt_reached h.scope h.reads O
    h.laid.planOk (2 * g + 1) (by omega) (by rw [VerifiableInference.OnPublicFiles.k3Ix_att]; exact hf)
  obtain rfl : g₁ = g₂ := Option.some.inj (e1.symm.trans e2)
  exact ⟨g₁, G, e1, hb, e3, hl⟩

/-- **The promise behind the block from the promise in front, at one reached state.**
Conditional: the head; hL: the list of seats is L; hg; ea: the group's plan; E: `HonestLike`; B:
`AtBorder`; hy: the two strings agree below a base (a letter of the library's law); hr, hu, hon:
the state is reached at the border, bears no mark and meets the promise in front; e: the open
segment; hh: the hearing of the segment's own rounds returns from its ledger. -/
theorem behind_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {Cells Tok : Type}
    (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT)) (E : HonestLike h Mg) (O : List Item)
    (Q : List Pub) (B : AtBorder g O Q) {Fr : Frame} {bs : ℕ} {y y' : Fr.E.Str}
    (hy : SameBelow Fr bs y y') {π : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4) (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some (plK5 g)) O Q (π, s) (strsOf Fr y))
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) :
    onAt (P5J.At.N Zp cF) Mg P5J.At.links (some (plK1 g))
      (stepOpen O (rowOf P5J.At.links (plK5 g)))
      (pubStep Q (pubRowM Mg.more P5J.At.links (plK5 g))) (π, behind s att hd G)
      (strsOf Fr y') := by
  obtain ⟨Bs, base0, Op⟩ := h.laid.opened
  have hW : Bs.G₀.W = P5J.At.X Zp := Op.W
  obtain ⟨blk, Eb, a', x₁, xd, hfl, ho, _, _, H⟩ :=
    Att.P.k5_seat_of_open h.scope h.reads Op h.laid.planOk h.laid.asks hg
  rw [hW] at H
  obtain ⟨hP, h4, ea', hx, hxd, Pn, hat, hok, hG⟩ := H
  obtain rfl : a' = a := Option.some.inj (ea'.symm.trans ea)
  have Ix : K5Place P5J.At.links (2 * g + 1) (plK5 g) (plK1 g) :=
    ⟨rfl, rfl, sub_full hg, rfl, rfl⟩
  -- the block sends no oracle message
  have ht : (P5J.At.told cF)[14 * (2 * g + 1) + 4]? = some [] := by
    show (cF.blocksInOrder.map fun b => b.oracles.flatMap id)[14 * (2 * g + 1) + 4]? = some []
    rw [List.getElem?_map, hfl]
    show some (Eb.oracles.flatMap id) = some []
    rw [List.flatMap_id, ho]
  have Bk : K5Book (P5J.At.N Zp cF) (plK5 g) (plK1 g) := k5Book_full _ _ hg ht
  have T := dataIs_all h (2 * g + 1)
  have hpub : Mg.pub = pubAll h.𝔇.pubD mgB0.pub := E.pub.trans (hpubPlus_all h)
  have hatt : h.𝔇.pubD.d5.isAtt (2 * g + 1) = true :=
    isAtt_of h.𝔇.pubD.d5 (by rw [T.d5links]; exact sub_full hg)
  have hlay : FillK4.isLay h.𝔇.pubD.links (2 * g + 1) = false :=
    att_not_lay (by rw [T.links]; exact sub_full hg)
  have hf : h.𝔇.pubD.d5.first? (2 * g + 1) = some (Forest.elems a'.fs) :=
    first_at h.𝔇.pubD.d5 (by rw [T.d5W]; exact hP) (by rw [T.d5W]; exact h4)
      (by rw [T.d5W]; exact ea) (by rw [T.d5W]; exact hx)
  have hPl : ∀ m b, Mg.pubP (.left m) b =
      VerifiableInference.OnPublicFiles.k3LeftItemAt h.𝔇.pubD.d3.X m b.2 := fun m b => by
    rw [E.pubP]
    rfl
  have hPlo : ∀ m b, Mg.pubP (.leftOn m) b =
      VerifiableInference.OnPublicFiles.k3LeftOnItemAt h.𝔇.pubD.d3.X m b.2 := fun m b => by
    rw [E.pubP]
    rfl
  have hwm : ∀ q, q ∈ Q ∨ q ∈ made3 (2 * g + 1) → isWideQ q = false := by
    rintro q (hq | hq)
    · exact B.narrow q hq
    · simp only [made3, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> rfl
  have hPo : ∀ q b, (q ∈ Q ∨ q ∈ made3 (2 * g + 1)) → (∀ m', q ≠ .left m') →
      (∀ m', q ≠ .leftOn m') → Mg.pubP q b := fun q b hq h1 h2 => by
    rw [E.pubP]
    show (mgAll h.𝔇 mgB0).pubP q b
    rw [mgAll_pubP, Look.fill_pubP_other _ _ _ q b h1 h2]
    show (if FillP1.p1Item q = true then True else mgB0.pubP q b)
    split
    · trivial
    · exact baseP_all g Q B.twenty q b hq (hwm q hq) h1 h2
  have hin : ∀ b : ProofFile.InstPub × S, Mg.inOrder b =
      (mgB0.inOrder b && (_root_.Meaning.backReq (h.𝔇.reqB b.1)).isSome) := fun b => by
    rw [E.inOrder]
    rfl
  have Fi := k5Fill_honest h.𝔇.pubD mgB0.pub Mg π L (P5J.At.d12 Zp L).M hpub hPl hPlo
    (E.held.trans rfl) E.decodes E.shown E.noColl mgB0.inOrder
    (fun p => (_root_.Meaning.backReq (h.𝔇.reqB p)).isSome) hin hatt hlay hf (nsOf_all h hg ea)
    (by rw [T.d3X]; exact placeAt_of hx) (by rw [T.d3X]; exact placeAt_of hxd)
    (by rw [T.d3X]; exact sort2 h4 g) (by rw [T.d3X]; exact sort7 h4 g) (baseIn_all π)
    (P5J.At.N Zp cF) O Q Fr bs a'.own B.twenty B.narrow hPo
  have hQ : ∀ q ∈ (pubRowOf P5J.At.links (plK5 g)).asks, q ∈ Q := by
    intro q hq
    rw [(Att.P.k5_pubRow Ix).1] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact B.open8.q4
    · exact B.open8.q3
    · exact B.open8.q6
    · exact B.open8.q8
    · exact B.open8.q5
    · exact B.caller
  -- the facts at the one state
  obtain ⟨_, _, hxl, _⟩ := Att.P.place_calls h4 ea hx
  obtain ⟨_, gL, Y, hLf⟩ := door_at_head h hL hg ea hx Mg E.pub E.pubP O Q B.open8 hr hu hon
    (id : Aff → Aff) (fun _ => (none : Option Unit))
  obtain ⟨_, _, _, _, U, _, hz⟩ :=
    front_at_head h hL hg ea hx Mg E.pub E.pubP O Q B.open8 hr hu hon e
  have U' : Att.P.U3There (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att (Att.P.parCOf a') := by
    have := U
    unfold ownAt at this
    rwa [hxl] at this
  have Rt := runs_at_head h hL hg ea hx Mg E.pub E.pubP O Q B.open8 hr hu hon e hh
  obtain ⟨g₁, G₁, hlk, hbr, hfk, hlf⟩ := bareLeft_head h hg hr
  obtain rfl : g₁ = gL := Option.some.inj (hlk.symm.trans Y.heard)
  obtain rfl : G₁ = att.F := Option.some.inj (hfk.symm.trans (fork_front e))
  obtain ⟨Lk, hLk⟩ := lkAt_all h hg
  obtain ⟨hObj, hGst⟩ := objIs_gstIs_all h hg hLk
  have pOk := planOk_plus (beforeAll Zp g) hat hok ea
  have cOk := claimsOk_plus (beforeAll Zp g) hat hok ea
  have gf := Att.P.geoFits_at_seat hP ea
    (okAll_plus (P5J.At.X Zp) g (beforeAll Zp g) a' h.𝔇.sent h.𝔇.l3.rad hP h4 ea hG pOk cOk)
  have hRds := rds_plus h.𝔇.pubD g a' _ Lk (hRd_plus (rdIs_all h) hLk) ProofFile.sameReply
    (statesAt_all h hg ea hLk) sameOut_all
  have hin' := Rt
  obtain ⟨i, K, _, _, _, _, _, _, hinOf, _⟩ := hin'
  have hplanes := planesIn_at h.𝔇.pubD mgB0.pub Mg hpub (π := π) (id : Aff → Aff) (2 * g + 1) a'
    (by rw [runsIs_all h]; exact runsAt_planes (sub_full hg)) _ Lk (hRd_plus (rdIs_all h) hLk)
    K3Lot.ofForm clForm_lot a'.S.cf.lmb (planesAt_all h hg ea hLk) sameOut_all e hh hz hinOf U' hLf
    hlf (planesOkAt_all h ea hx) (posG_all h hg ea hat) (colsFit_all h ea hx) rfl
  have hAm : h.𝔇.pubD.d5.W.A[(2 * g + 1) / 2]? = some a' := by
    rw [T.d5W, show (2 * g + 1) / 2 = g by omega]
    exact ea
  have hreads : readsThereB h.𝔇.pubD.d5.W (h.𝔇.pubD.N.sent x₁.link 0) s = true := by
    rw [T.d5W]
    exact Y.reads
  exact Att.P.k5_t2 (P5J.At.N Zp cF) Mg P5J.At.links π (2 * g + 1) bs (plK5 g) (plK1 g) O Q a'.own
    _ _ _ _ _ _ _ Ix Bk Pn Fi hQ e hh hy hu hon
    (kept_at h.𝔇.pubD mgB0.pub Mg hpub P5J.At.links (plK5 g) O (2 * g + 1) B.ties
      (runsO_plus h.𝔇.pubD g h.𝔇.links (runsIs_all h) (sub_full hg)) hObj hGst e hh hz hlk hbr)
    (made_at h.𝔇.pubD mgB0.pub Mg hpub (2 * g + 1) a'
      (runs3_plus h.𝔇.pubD g h.𝔇.links (runsIs_all h) (sub_full hg))
      (runsJ_plus h.𝔇.pubD g h.𝔇.links (runsIs_all h) (sub_full hg)) hRds hh hz Rt gf U' hplanes)
    (madeMore_at h.𝔇.pubD mgB0.pub Mg hpub {} (E.more.trans (hm_all h)) P5J.At.links Ix rfl hatt
      hAm (fun b => ⟨hPo _ b (Or.inr (by simp [made3])) (fun _ => by simp) (fun _ => by simp),
        hPo _ b (Or.inr (by simp [made3])) (fun _ => by simp) (fun _ => by simp)⟩)
      e hh Y.sized gf (Att.P.k5_link Ix e (Att.P.onAt_shape hon hu)) hreads)

end

end H2K5.Honest

#print axioms H2K5.Honest.bareLeft_head
#print axioms H2K5.Honest.behind_at_head
