-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/BehindAtHead.lean: THE TABLE OF JOINTS' PROMISE BEHIND A YES OF THE
MEMBER "the output head's own rounds" (K6), FROM THE PROMISE IN FRONT, AT THE LETTERS OF THE FULL
SIZE's TABLE AND AT ANY FILLING THAT IS LIKE THE CLOSED ONE ON THE HONEST SIDE. Over the library and
files that import no frame of the honest side. EVERY THEOREM IS CONDITIONAL.

  `bare_of_member`   from the member's step to the bare block's decision
  `sentence_other`   what an open public item says beside its test, but for the lookups' two
  `pub_behind`       the fifteen public tests behind, from the twelve in front and the four made
  `leftOn_behind`    what "leftOn 24" says behind
  `k6_promise_behind_of_four`   the promise behind, with the four made tests as a premise
  `k6_promise_behind`           MAIN: these four paid (Honest/Law/BehindJoin.lean)
  `k6_promise_behind'`          the same, without two premises on the member's guard and place

HOW. The rule under which the promise rides past a block whose row closes and opens no class of rows
and no pin (`onAt_step_quiet`, Johnson/Desc/First/PromiseRides.lean) is called once. Of its fourteen
premises: the promise in front is a premise here; eight are Honest/Law/KeepsForm.lean's, at the
table's letters by Honest/Law/KeepsAtHead.lean; the three on the oracles' strings hold outright at
such a filling (`HonestLike`, Johnson/Desc/ProofFile/Honest/Small/PromiseParts.lean); the public
tests: `pub_behind`, by the library's two written lists of what is open at 341 and 342 (`open341`,
`open342`, Johnson/Desc/Kinds/Law/K6PubKept.lean), nine kept (Honest/Law/BehindKept.lean), four
made, and two that hold outright; the public sentences: `leftOn_behind` and `sentence_other` (over
`pubP_open342_mgBase`, Law/K6PubSentences.lean). The library has the like at a piece of the proof of
soundness (`k6_t2_kept`, Law/K6SecondKept.lean, with the gathering in Law/K6LawAtMgAll.lean): the
fifteen cases here follow that gathering's.

Relatives. Of the last arm of `pub_behind`: `weights_true` (Law/K6PubMore.lean): at the composed
meaning's test; here the test beneath is a letter. Of `bare_of_member`: `K6MemberIs.step_iff`
(Law/K6WayUp.lean) gives that the bare sub-protocol's step accepts under two facts more on the
member's guard and place; `K6MemberIs.step_down`, there, from the member's form alone.

WHAT IS PAID AT THE HYPOTHESIS h, BY CALLS: the test with code on the seats (`seatsC_at_head`,
Johnson/HB/LLHARD/K6SeatsAtHead.lean, with `reads_name_at_const`, Law/K6ReadsNameAtConst.lean); five
fields at the closed term (`paid_at_const`, Law/K06AtConst.lean); six facts on link 24
(`P4.six_at_head`, Law/K6StateAtHead.lean); at a reached state: `P4.k6Reached_341`,
`P4.leavesFilled_341`, `P4.bare_341` (Johnson/P4R/), `IM.tokSmallAt_border`
(Johnson/IMR/TokAtReach.lean); the plan's tests of two members (`P4.plan_at`,
Johnson/P4R/FreeAt341N.lean).

WHAT IS LEFT AS PREMISES of `k6_promise_behind'`: the hypothesis h that ties the letters to the IOP
as written in Lean; the filling is like the closed one; the member's form, that it stands at 341,
that its step accepts; every word of the rounds is below the prime; the state is reached at 341; the
list of seats is laid; five facts along the fold (`FoldAt`: not paid here; the library's
`foldAt_of_facts`, Law/K6RestOfFold.lean, has them at every reached state from another hypothesis,
`FoldFacts`, which that file takes as a premise); the promise in front. `k6_promise_behind` ASKS
BESIDES two facts on the member's guard and place (hk, hsm): IDLE IN SUBSTANCE: they go into
`four_of_front` alone, and there into a way down that needs neither.

Limits. THE FULL SIZE ALONE. The hypothesis h is met under the four premises of the library's
`P5J.head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean: in scope; the files are read; the
verifier's own three values are laid; one condition that others state); by that file's own limits
the first three are evaluated true at the release's full-size files (runs, no theorem), and the
fourth that file leaves to others. What is there stands at two named values of the letters D and r;
here both are letters. No yes of the member is shown. Modules under lean/Johnson/Goal/ are among
what this file imports: it imports no module of that folder by name and calls nothing that is
declared there: they lie beneath the library's files that it calls. Nothing on any property.

-/
import Johnson.Desc.K6.Honest.Law.KeepsAtHead
import Johnson.Desc.K6.Honest.Law.BehindKept
import Johnson.Desc.K6.Honest.Law.BehindJoin
import Johnson.HB.LLHARD.K6SeatsAtHead
import Johnson.Desc.Kinds.Law.K6ReadsNameAtConst
import Johnson.IMR.TokAtReach
import Johnson.Desc.Kinds.Law.K6StateAtHead
import Johnson.Desc.Kinds.Law.K06AtConst
import Johnson.Desc.Kinds.Law.K6PubSentences
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.Desc.First.BordersSucc
import Johnson.IMR.AtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Claim OpenedColumn Place Strs Chain Wit noDigest)
open VerifiableInference.Desc.First (S ModelPart Item Pub Numbers Meaning onAt stepOpen rowOf pubHeld
  pubOfItems onAt_step_quiet openSets_succ pubAll ledgerB)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase openQ pubQ mgMore)
open VerifiableInference.Desc.Kinds.Head.Law (K6MemberIs)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open ProofFile.Honest.Small (HonestLike partsAt_of_onAt)

/-- From the member's step to the bare block's decision. CONDITIONAL: the member's form; the yes. -/
theorem bare_of_member {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool}
    {a : Place} {b : Block S Claim} (M : K6MemberIs W l same a b) {ft n : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} (h : b.step ft s rs cols = .ok (s', n)) :
    ∃ i gs, (blockAt W.hS i ((OnBytes.Params.settingOf W.P.frame).workOf .field .request)
      l).decide s (rs.map noDigest) gs = .ok s' := by
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  obtain ⟨gs, hd⟩ := Law.Came.step_decide ft b s rs cols s' n h
  have h0 := (IM.alone_underR hla).2 _ _ _ _ hd
  obtain ⟨b0, hb0, rfl⟩ := Law.seatedClaims_some hS
  unfold blockClaims at hb0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp hb0
  exact ⟨i, gs, ((Law.tested_decide _ _ _ _ _ _ _ _).1 h0).1⟩

section Sentences
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (Dt : Sound.MgData Xi P Tok rows cols nR Wp)

/-- What a public item that is open behind says beside its test, but for the lookups' two: it holds
outright at the composed meaning over the closed base. -/
theorem sentence_other (j : Pub)
    (hj : j ∈ pubQ (mgAll Dt mgBase).more Sound.linksFull
      (First.flatPlacesOf Sound.linksFull true) (341 + 1))
    (h1 : ∀ m, j ≠ .left m) (h2 : ∀ m, j ≠ .leftOn m) (x : P × S) :
    (mgAll Dt mgBase).pubP j x := by
  rw [Sound.mgAll_pubP, First.Look.fill_pubP_other _ _ _ j x h1 h2]
  show if First.FillP1.p1Item j = true then True else mgBase.pubP j x
  split
  · trivial
  · exact Law.AtTable.pubP_open342_mgBase Dt j hj h1 h2 x

end Sentences

section General
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (Dt : Sound.MgData Xi P Tok rows cols nR Wp) (base : Pub → P × S → Bool) (z : P) {s s' : S}
  {i work : Nat} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
  (hd : (blockAt Wp.hS i work 24).decide s rs gs = .ok s')

include hd

/-- **The fifteen public tests behind**: nine kept from the front, four as the premise hFour has
them, two that hold outright. CONDITIONAL. -/
theorem pub_behind
    (hbase : ∀ (j : Pub) (t : S) w, base j (z, { t with here := w }) = base j (z, t))
    (hsort : First.Look.k3SortAt Wp 24 3 = some false) (sorts : Dt.links[24]? = some .head)
    {Lk : VerifiableInference.Desc.Link S Claim} {P8 : K8.ReadsQuiet.PH}
    {small : S → Option K9.Read}
    (readers : Dt.Rd 24 = K9.readersOfLink ⟨small, Law.k6Silent P8 (K9.statesOfLink Lk)⟩ Lk)
    (hruns : Law.AtTable.ObjectsStates (K9.statesOfLink Lk) 2)
    (hback : Law.AtTable.ObjectsBack (K9.statesOfLink Lk) 2)
    (hbare : ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[])
    (front : ∀ j ∈ [Pub.tokenSmall, .ledger 24, .linkFresh 24, .freeAbove 24,
      .more (some 24) "frame.sentIs", .more (some 24) "ledger.treesAre", .lookOut 24 3, .look 24,
      .left 24, .indexIs, .indexThere, .formsInT 24 3 "objects"],
      pubAll Dt.pubD base j (z, s) = true)
    (hFour : ∀ j ∈ [Pub.lookIn 24 8, .formsInT 24 4 "own", .formsInT 24 3 "planes",
      .formsInT 24 4 "join"], pubAll Dt.pubD base j (z, s') = true) :
    ∀ q ∈ [Pub.ledger 24, .linkFresh 24, .freeAbove 24, .more (some 24) "frame.sentIs",
      .more (some 24) "ledger.treesAre", .lookOut 24 3, .lookIn 24 8, .leftOn 24, .indexIs,
      .indexThere, .formsInT 24 3 "objects", .formsInT 24 4 "own", .formsInT 24 3 "planes",
      .formsInT 24 4 "join", .formsInT 24 4 "weights"], pubAll Dt.pubD base q (z, s') = true := by
  have hL : ledgerB s = true := front (.ledger 24) (by simp)
  have LF := kept_ledger_free _ i _ 24 hd Dt.pubD base z 24 (front _ (by simp)) (front _ (by simp))
  have four := kept_four_at _ i _ 24 hd Dt.pubD base z 24 hbase
  have hr5 := Law.AtTable.runs_at_head Dt sorts
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact LF.1
  · exact four _ (by simp) (front _ (by simp))
  · exact LF.2
  · exact four _ (by simp) (front _ (by simp))
  · exact kept_trees_at _ i _ 24 hd Dt.pubD base z 24 (front _ (by simp))
  · exact kept_lookOut_at _ i _ 24 hd Dt.pubD base z 24 3 hsort hL (front _ (by simp))
  · exact hFour _ (by simp)
  · rfl
  · exact four _ (by simp) (front _ (by simp))
  · exact four _ (by simp) (front _ (by simp))
  · exact kept_objects_at _ i _ 24 hd Dt.pubD base z 24 readers hr5.1 hruns hback hL hbare
      (front _ (by simp))
  · exact hFour _ (by simp)
  · exact hFour _ (by simp)
  · exact hFour _ (by simp)
  · rw [First.pubAll_formsInT]
    have e : Dt.pubD.runs 24 4 "weights" = [] := hr5.2.2.2.2
    rw [e]
    rfl

/-- **What "leftOn 24" says behind**, from what "left 24" says in front, at the composed meaning.
CONDITIONAL: what "left 24" says in front; the ledger in front has its sizes (which the first gives
too). -/
theorem leftOn_behind (Mg : Meaning P (Wit (Sound.CellsQ rows cols) Tok MsgT))
    (hL : ledgerB s = true) (hleft : (mgAll Dt Mg).pubP (.left 24) (z, s)) :
    (mgAll Dt Mg).pubP (.leftOn 24) (z, s') := by
  rw [Sound.mgAll_pubP] at hleft ⊢
  obtain ⟨p, hp, Lf⟩ : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 s := hleft
  exact ⟨p, hp, leftOn_at _ i _ 24 hd hL p Lf⟩

end General

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The promise behind, with the four made tests as a premise.** CONDITIONAL: the hypothesis h;
the filling is like the closed one; the member's form; its step's yes; the state is reached (spent
on one thing: no row that the lookup on the calls keeps names an entry); the promise in front;
hFour. -/
theorem k6_promise_behind_of_four
    (Mg : Meaning ProofFile.InstPub (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT))
    (E : HonestLike (mgAtAll h) Mg) {y y' : Strs} {π : ProofFile.InstPub} {s s' : S}
    {same : S → S → Bool} {a : Place} {b : Block S Claim}
    (M : K6MemberIs (P5J.At.X Zp) 24 same a b) {ft n : Nat}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} (hstep : b.step ft s rs cols = .ok (s', n))
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 341 (π, s))
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links P5J.At.ps[341]?
      (openQ P5J.At.links P5J.At.ps 341) (pubQ Mg.more P5J.At.links P5J.At.ps 341) (π, s) y)
    (hFour : ∀ i ∈ [Pub.lookIn 24 8, .formsInT 24 4 "own", .formsInT 24 3 "planes",
      .formsInT 24 4 "join"], Mg.pub i (π, s') = true) :
    onAt (P5J.At.N Zp cF) Mg P5J.At.links P5J.At.ps[341 + 1]?
      (openQ P5J.At.links P5J.At.ps (341 + 1)) (pubQ Mg.more P5J.At.links P5J.At.ps (341 + 1))
      (π, s') y' := by
  have K : K6Keeps s s' := k6_keeps_of_member_step M hstep
  have hsort : First.Look.k3SortAt (P5J.At.X Zp) 24 3 = some false :=
    (Law.k6Pub_says _ (Law.InScope.k6Pub_in_scope h.scope h.reads h.pubOne)).1
  obtain ⟨i, gs, hd⟩ := bare_of_member M hstep
  have Ix := k6Place_at
  have Bk := k6Book_at h.toAtMg
  have Bl := blindOrder_at h Mg E.held E.inOrder
  have hm : Mg.more = mgMore := E.more.trans (Sound.mgAll_more_base h.𝔇)
  obtain ⟨base, hbase, hpub⟩ : ∃ base : Pub → ProofFile.InstPub × S → Bool,
      (∀ (j : Pub) (t : S) w, base j (π, { t with here := w }) = base j (π, t)) ∧
        Mg.pub = pubAll h.𝔇.pubD base :=
    ⟨_, fun _ _ _ => rfl, E.pub.trans (Sound.mgAll_pub h.𝔇 mgBase)⟩
  have h342 : pubQ mgMore P5J.At.links P5J.At.ps (341 + 1) ++
      pubOfItems (openQ P5J.At.links P5J.At.ps (341 + 1)) = _ := Law.AtTable.open342
  have h341 : pubQ mgMore P5J.At.links P5J.At.ps 341 ++
      pubOfItems (openQ P5J.At.links P5J.At.ps 341) = _ := Law.AtTable.open341
  have eO : openQ P5J.At.links P5J.At.ps (341 + 1) =
      stepOpen (openQ P5J.At.links P5J.At.ps 341) (rowOf P5J.At.links plK6) :=
    openSets_succ _ _ _ _ _ k6_at341
  rw [k6_at341] at hon
  rw [k6_at342, eO]
  -- the public tests
  have hPub : s.failed = none →
      pubHeld Mg (openQ P5J.At.links P5J.At.ps 341) (pubQ Mg.more P5J.At.links P5J.At.ps 341)
        (π, s) = true →
      pubHeld Mg (stepOpen (openQ P5J.At.links P5J.At.ps 341) (rowOf P5J.At.links plK6))
        (pubQ Mg.more P5J.At.links P5J.At.ps (341 + 1)) (π, s') = true := by
    intro _ hf
    rw [← eO]
    unfold pubHeld at hf ⊢
    rw [hm] at hf ⊢
    rw [h341] at hf
    rw [h342]
    have front := List.all_eq_true.1 hf
    rw [hpub] at front hFour ⊢
    obtain ⟨Lk, hl, six⟩ := P4.six_at_head h
    have Pd := Law.AtTable.paid_at_const h Lk hl
    obtain ⟨Bs, base0, O⟩ := h.laid.opened
    have hbare := P4.bare_341 h.scope h.reads O h.laid.planOk hr
    exact List.all_eq_true.2 (pub_behind h.𝔇 base π hd hbase hsort Pd.sorts Pd.readers
      six.2.2.2.2.1 six.2.2.2.2.2 hbare front hFour)
  -- the public sentences
  have hPP : s.failed = none →
      (∀ q ∈ pubQ Mg.more P5J.At.links P5J.At.ps 341, Mg.pubP q (π, s)) →
      ∀ q ∈ pubQ Mg.more P5J.At.links P5J.At.ps (341 + 1), Mg.pubP q (π, s') := by
    intro hu hf q hq
    have hL : ledgerB s = true := by
      have h0 := First.Att.P.onAt_pub hon hu (.ledger 24) (by
        rw [hm]
        decide +kernel)
      rw [hpub] at h0
      exact h0
    rw [hm] at hf hq
    have hq15 :=
      h342 ▸ List.mem_append_left (pubOfItems (openQ P5J.At.links P5J.At.ps (341 + 1))) hq
    rw [E.pubP]
    have other : ∀ j : Pub, j ∈ pubQ mgMore P5J.At.links P5J.At.ps (341 + 1) →
        (∀ m, j ≠ .left m) → (∀ m, j ≠ .leftOn m) → (mgAll h.𝔇 mgBase).pubP j (π, s') := by
      intro j hj h1 h2
      exact sentence_other h.𝔇 j (by rw [Sound.mgAll_more_base]; exact hj) h1 h2 (π, s')
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq15
    rcases hq15 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    case inr.inr.inr.inr.inr.inr.inr.inl =>
      have hleft : Mg.pubP (.left 24) (π, s) := hf _ (by decide +kernel)
      rw [E.pubP] at hleft
      exact leftOn_behind h.𝔇 π hd mgBase hL hleft
    all_goals exact other _ hq (fun _ => by simp) (fun _ => by simp)
  exact onAt_step_quiet (P5J.At.N Zp cF) Mg P5J.At.links (some plK6) (some plK6') _ _ _
    (rowOf P5J.At.links plK6) (π, s) (π, s') y y' (keeps_quiet Ix) hon
    (fun hmk => by
      show s'.failed ≠ none
      rw [keeps_failed K]
      exact hmk)
    (fun _ => E.decodes _ _)
    (fun hu => keeps_shape Ix K (First.Att.P.onAt_shape hon hu))
    (keeps_groups K) (keeps_places K) (keeps_inOrder Bl K π) hPub
    (fun _ => keeps_book Bk K) hPP (fun x _ => keeps_held Bl K π x.1 x.2)
    (fun x _ _ => E.shown _ _ _) (fun x _ _ => E.noColl _ _ _ _)

/-- **THE TABLE's PROMISE BEHIND THE MEMBER's YES, FROM THE PROMISE IN FRONT.** CONDITIONAL: as the
head's list says; hk and hsm are idle in substance: `k6_promise_behind'` has the same conclusion
without them. -/
theorem k6_promise_behind
    (Mg : Meaning ProofFile.InstPub (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT))
    (E : HonestLike (mgAtAll h) Mg) {y y' : Strs} {π : ProofFile.InstPub} {s s' : S}
    {same : S → S → Bool} {a : Place} {b : Block S Claim}
    (M : K6MemberIs (P5J.At.X Zp) 24 same a b) (hk : a.kind ≠ VerifiableInference.Desc.KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true)
    (hfl : cF.blocksInOrder[341]? = some b) {ft n : Nat} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (hstep : b.step ft s rs cols = .ok (s', n)) (hcan : viewWordsBelowPrime ⟨rs.map noDigest, []⟩ = true)
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 341 (π, s)) {Lp : K12.Door.Laid}
    (hLp : P5J.At.laid? Zp = some Lp)
    (Fo : Law.AtFold.FoldAt Lp (K12.Door.msgsOfChain Zp.made.proof.1) h.𝔇.cs h.𝔇.shape
      (P5J.At.layout Zp) s)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links P5J.At.ps[341]?
      (openQ P5J.At.links P5J.At.ps 341) (pubQ Mg.more P5J.At.links P5J.At.ps 341) (π, s) y) :
    onAt (P5J.At.N Zp cF) Mg P5J.At.links P5J.At.ps[341 + 1]?
      (openQ P5J.At.links P5J.At.ps (341 + 1)) (pubQ Mg.more P5J.At.links P5J.At.ps (341 + 1))
      (π, s') y' := by
  have K : K6Keeps s s' := k6_keeps_of_member_step M hstep
  have hu : s.failed = none := (keeps_failed K).symm.trans K.1
  obtain ⟨Bs, base0, O⟩ := h.laid.opened
  obtain ⟨Lk, hl, six⟩ := P4.six_at_head h
  have Pd := Law.AtTable.paid_at_const h Lk hl
  have R : Law.K6FrontItems h.𝔇 mgBase (π, s) :=
    Law.frontItems_of_parts h.𝔇 mgBase rfl (π, s)
      (partsAt_of_onAt E P5J.At.links P5J.At.ps 341 (π, s) y hon hu)
  refine k6_promise_behind_of_four h Mg E M hstep hr hon ?_
  rw [E.pub]
  exact four_of_front h.𝔇 mgBase R M hk hsm (P4.plan_at O h.laid.planOk 341 b hfl) hstep hcan
    h.scope h.reads h.pubOne Pd.seg Pd.treesB Pd.sorts (P5J.At.layout Zp) (P5J.At.num Zp) Lp
    (K12.Door.msgsOfChain Zp.made.proof.1) Pd.roomC
    (Law.seatsC_at_head h Lp hLp (Law.AtTable.reads_name_at_const h)) six K9.smallReader Pd.readers
    (P4.k6Reached_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) hr) Fo
    (P4.leavesFilled_341 h.scope h.reads O h.laid.planOk hr)
    (IM.tokSmallAt_border h.scope h.reads O (by decide) hr)

/-- **THE TABLE's PROMISE BEHIND, WHERE THE MEMBER's STEP ACCEPTS, FROM THE PROMISE IN FRONT: AT
EVERY ADDRESS AND EVERY GUARD.** `k6_promise_behind` without its two premises on the member's guard
and place. The proof is that one's, line for line, but for the call of `four_of_front'`.
CONDITIONAL: as the head's list says. -/
theorem k6_promise_behind'
    (Mg : Meaning ProofFile.InstPub (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT))
    (E : HonestLike (mgAtAll h) Mg) {y y' : Strs} {π : ProofFile.InstPub} {s s' : S}
    {same : S → S → Bool} {a : Place} {b : Block S Claim}
    (M : K6MemberIs (P5J.At.X Zp) 24 same a b)
    (hfl : cF.blocksInOrder[341]? = some b) {ft n : Nat} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (hstep : b.step ft s rs cols = .ok (s', n)) (hcan : viewWordsBelowPrime ⟨rs.map noDigest, []⟩ = true)
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 341 (π, s)) {Lp : K12.Door.Laid}
    (hLp : P5J.At.laid? Zp = some Lp)
    (Fo : Law.AtFold.FoldAt Lp (K12.Door.msgsOfChain Zp.made.proof.1) h.𝔇.cs h.𝔇.shape
      (P5J.At.layout Zp) s)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links P5J.At.ps[341]?
      (openQ P5J.At.links P5J.At.ps 341) (pubQ Mg.more P5J.At.links P5J.At.ps 341) (π, s) y) :
    onAt (P5J.At.N Zp cF) Mg P5J.At.links P5J.At.ps[341 + 1]?
      (openQ P5J.At.links P5J.At.ps (341 + 1)) (pubQ Mg.more P5J.At.links P5J.At.ps (341 + 1))
      (π, s') y' := by
  have K : K6Keeps s s' := k6_keeps_of_member_step M hstep
  have hu : s.failed = none := (keeps_failed K).symm.trans K.1
  obtain ⟨Bs, base0, O⟩ := h.laid.opened
  obtain ⟨Lk, hl, six⟩ := P4.six_at_head h
  have Pd := Law.AtTable.paid_at_const h Lk hl
  have R : Law.K6FrontItems h.𝔇 mgBase (π, s) :=
    Law.frontItems_of_parts h.𝔇 mgBase rfl (π, s)
      (partsAt_of_onAt E P5J.At.links P5J.At.ps 341 (π, s) y hon hu)
  refine k6_promise_behind_of_four h Mg E M hstep hr hon ?_
  rw [E.pub]
  exact four_of_front' h.𝔇 mgBase R M (P4.plan_at O h.laid.planOk 341 b hfl) hstep hcan
    h.scope h.reads h.pubOne Pd.seg Pd.treesB Pd.sorts (P5J.At.layout Zp) (P5J.At.num Zp) Lp
    (K12.Door.msgsOfChain Zp.made.proof.1) Pd.roomC
    (Law.seatsC_at_head h Lp hLp (Law.AtTable.reads_name_at_const h)) six K9.smallReader Pd.readers
    (P4.k6Reached_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) hr) Fo
    (P4.leavesFilled_341 h.scope h.reads O h.laid.planOk hr)
    (IM.tokSmallAt_border h.scope h.reads O (by decide) hr)

end

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.bare_of_member
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sentence_other
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.pub_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.leftOn_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_promise_behind_of_four
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_promise_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_promise_behind'
