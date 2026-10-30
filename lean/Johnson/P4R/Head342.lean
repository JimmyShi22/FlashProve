-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/Head342.lean: AT A STATE REACHED AT THE BORDER 342 (behind the output head's own
sub-protocol, in front of the reads' place of the head's segment): THREE FACTS, EACH IN ITS OWN
TERMS: what the head has heard is read back (`K6HeardAt`); the runs of claims (`RunIs`,
with the reads' tables laid silently); the head's matrices are seated (`MatsSeated`). Statements
and proofs: a joining of other files' theorems. NO PREMISE SPEAKS OF THE TABLE's PROMISE AT 341,
AND NONE OF A STATE THAT NO RUN REACHES.
Why. A field of the condition of the kind K1 asks the three at the reached states at 342 inside
the promise at 342. The payers that lay spoke behind an accept of the output head's own
sub-protocol from a state inside the promise at 341. "Reached", one step back, hands the accept
and "reached at 341", not the promise there.
  `heardAt_of_wellLaid`: `heardAt_of_below` (Johnson/Desc/Kinds/Law/K6RecordPaid.lean) with its
  binder narrowed to what its proof spends: "the ledger in front is well laid".
  `heardAt_of_decideBy`: the same from the kind's own decision at canonical rounds.
  `P4.heard_342`: the last step of `RchAt` is taken back OVER THE WRAPPED LIST, so that the rounds
  are canonical; the sub-protocol at 341 is the seats' files' (`IM.k6_of`, `IM.k6_at_341`); "well
  laid" at 341 is `P4.wellLaid_341` (Johnson/P4R/FreeAt341N.lean).
  `P4.run_342`: `P4.reach_gives` (Johnson/P4R/ReachGivesN.lean), then `runIs_at_reach`
  (Johnson/Desc/Reads/RunIsAtBorder.lean).
  `fresh_open_342`: A FACT ON THE TABLE: the public item `linkFresh 24` is open at 342: the row at
  341 asks it, so it is open at 341; that row does not drop it.
  `sentIs_342`, `fresh_342`: so the promise AT 342 says both of the state at 342; the name
  "frame.sentIs" is asked by the row at 342 itself.
  `stateIsPlan_342`: `StateIsPlan` (Johnson/Desc/Kinds/Law/K6SeatsTest.lean) at the state at 342
  itself: where `stateIsPlan_behind` (Law/K6RestAt.lean) goes through the accept.
  `mats_342`: so `MatsSeated` at the four ranges, by `matsSeated_of_C`.
Premises. Public: hOk (the IOP's own test on the list of rounds), hfit (the table's own test), hC
(`seatsK6C`, AT THE NUMBER OF ORACLE MESSAGES IN FRONT OF 342), hJ, `Nums`. Along "reached": FF
(`FoldFacts`): five of its fields are spent, at 342.
Limits. That the premises can be met together is not shown here. The full size alone; the second
hash function alone; in the goals' scope. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P4R.K6AtRchAt
import Johnson.P4R.ReachGivesN
import Johnson.Desc.Kinds.Law.K6RecordPaid
import Johnson.Desc.Kinds.Law.K6RestOfFold
import Johnson.Desc.First.BordersSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S HeadOwn)

/-- **K6HeardAt behind the kind's own decision**, at canonical rounds, from a ledger that is well
laid. -/
theorem heardAt_of_decideBy (W : OnBytes.Model.Verify.Public) (s s' : S) (rs : List Fmt.RoundView)
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical rs)
    (hd : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge)
      (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s rs = .ok s') :
    K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s' := by
  obtain ⟨g, H, F, w, s1, s2, hg, hh, e1, e2, hs'⟩ := Came.decide_hears hd
  obtain ⟨b1, b2, b3, _⟩ := seatBack_at W.hS (readsOf W) (workOf W) s g rs [] F H w s1 s2 hg
    hWL hcan hh e1 e2
  rw [hs']
  exact ⟨g, H, _, F, rs, b3.trans hg, b2, hWL, hh, by rw [b1]; exact OnBytes.PscRun.Later.refl _⟩

/-- **`heardAt_of_below`, its binder narrowed to what its proof spends.** -/
theorem heardAt_of_wellLaid (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s))
    (h : (Sound.below b).decide s rs gs = .ok s') :
    K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s' := by
  obtain ⟨hcan, hd⟩ := canonical_of_below b s s' rs gs h
  obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp hb
  have hr : readsOf W = iU3 := by
    unfold readsOf
    rw [hu]
    rfl
  subst hbb
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge)
      (parOf W.hS (workOf W)) (seatAt W.hS iU3) s rs = .ok s' := hd
  rw [← hr] at hd'
  exact heardAt_of_decideBy W s s' rs hWL hcan hd'

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout ReqShape)
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning Pub More pubFit moreItem MoreName
  pubRowM pubRowOf pubStartM pubSets pubStep pubSets_succ FoldData FoldFacts)
open VerifiableInference.Desc.Sound (Frame MsgT onQ pubQ linksFull head_full MgData mgAll)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (asks_K6)

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- The reads' place of the head's segment. -/
def placeR : Place := { chain := 1, link := some 24, piece := 5, kind := .K1 }

set_option maxRecDepth 1000000 in
theorem place_341 : PS[341]? = some placeK6 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem place_342 : PS[342]? = some placeR := by decide +kernel

/-- What the table's own row at 341 drops. -/
theorem drops_K6 : (pubRowOf linksFull placeK6).drops = [.look 24, .left 24, .tokenSmall] := by
  decide

set_option maxRecDepth 1000000 in
/-- **A fact on the table: `linkFresh 24` is open at 342**, at every filling. -/
theorem fresh_open_342 (M : More) (hfit : pubFit M linksFull PS = true) :
    Pub.linkFresh 24 ∈ (pubSets M linksFull PS)[342]?.getD [] := by
  have h1 : Pub.linkFresh 24 ∈ (pubSets M linksFull PS)[341]?.getD [] :=
    Sound.asks_open (pubRowM M linksFull) PS (pubStartM M) 341 placeK6 hfit place_341 _
      (List.mem_append_left _ (by rw [asks_K6 linksFull placeK6 24 rfl head_full rfl]; simp))
  have hn : Pub.linkFresh 24 ∉ (pubRowM M linksFull placeK6).drops := by
    intro hm
    have hm' : Pub.linkFresh 24 ∈ (pubRowOf linksFull placeK6).drops ++
        (M.rows linksFull placeK6).drops.map moreItem := hm
    rcases List.mem_append.1 hm' with h | h
    · rw [drops_K6] at h
      simp at h
    · obtain ⟨x, -, hx⟩ := List.mem_map.1 h
      unfold moreItem at hx
      cases hx
  rw [show (342 : ℕ) = 341 + 1 from rfl, pubSets_succ M linksFull PS 341 placeK6 place_341]
  unfold pubStep
  exact List.mem_append_left _ (List.mem_filter.2 ⟨h1, by simpa using hn⟩)

/-- The open segment's part holds the state's statement and book. -/
theorem seg_st_book {s : S} {aK : K9.Part} (h : K9.segAt? s = some aK) :
    aK.d.st = s.st ∧ aK.d.book = s.book := by
  unfold K9.segAt? at h
  cases hL : s.link? with
  | none =>
    rw [hL] at h
    cases h
  | some L =>
    cases hF : s.fork? with
    | none =>
      rw [hL, hF] at h
      cases h
    | some F0 =>
      cases hT : s.tl? with
      | none =>
        rw [hL, hF, hT] at h
        cases h
      | some t0 =>
        rw [hL, hF, hT] at h
        rw [← Option.some.inj h]
        exact ⟨rfl, rfl⟩

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
  (Fr : Frame)

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The name is asked at the reads' place too, whatever Mg adds. -/
theorem sent_asked_342 :
    First.FillSent.sentName 24 ∈ ((MGA).more.rows linksFull placeR).asks := by
  rw [Sound.mgAll_more_merges]
  refine List.mem_filter.2 ⟨?_, by decide⟩
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  decide

/-- **The open segment's frame's five fields are the public terms, at 342.** -/
theorem sentIs_342 (hfit : pubFit (MGA).more linksFull PS = true) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 342 a) (hm : a.1.2.failed = none) :
    First.FillSent.sentIsB D.pubD.dS 24 a.1.2 = true := by
  have h : (MGA).pub (moreItem (First.FillSent.sentName 24)) a.1 = true :=
    asked_more Fr D.N MGA linksFull PS (fun a => a) hfit 342 placeR place_342 a ha hm
      (First.FillSent.sentName 24) (sent_asked_342 D Mg)
  rw [Sound.mgAll_pub] at h
  exact (First.pubAll_more_sentIs D.pubD Mg.pub 24 a.1).symm.trans h

/-- **The open segment's list of arrays is the public one, at 342.** -/
theorem fresh_342 (hfit : pubFit (MGA).more linksFull PS = true) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 342 a) (hm : a.1.2.failed = none) :
    VerifiableInference.OnPublicFiles.linkFreshB (D.sent.arrayOf.getD 24 #[]) a.1.2 = true := by
  have h : (MGA).pub (.linkFresh 24) a.1 = true :=
    (Sound.onParts_of_on D.N MGA linksFull PS (fun a => a) 342 a ha hm).pub _
      (List.mem_append_left _ (fresh_open_342 (MGA).more hfit))
  exact h

/-- **At 342 itself every reader is a term off the public parameters.** -/
theorem stateIsPlan_342 (Lp : K12.Door.Laid) (M : List OracleShape)
    (hfit : pubFit (MGA).more linksFull PS = true) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 342 a) (hm : a.1.2.failed = none)
    (F : FoldAt Lp M D.cs D.shape lay6 a.1.2) (aK : K9.Part)
    (hK : K9.segAt? a.1.2 = some aK) :
    StateIsPlan lay6 D.cs D.shape D.pubD.dS Lp M (D.sent.arrayOf.getD 24 #[])
      (D.N.msgsAt PS[342]?) a.1.2 aK := by
  have hL := link_of_seg hK
  obtain ⟨hst, hbk⟩ := seg_st_book hK
  have hlive : a.1.2.live = aK.L.check := by
    unfold First.S.live
    rw [hL]
  have hS := sentIs_342 D Mg Fr hfit a ha hm
  have hfr := fresh_342 D Mg Fr hfit a ha hm
  have hbo : First.bookAt D.N PS[342]? a.1.2 = true :=
    (Sound.onParts_of_on D.N MGA linksFull PS (fun a => a) 342 a ha hm).book
  unfold First.bookAt at hbo
  simp only [Bool.and_eq_true, beq_iff_eq] at hbo
  refine ⟨hK, ?_, ?_, ?_, ?_, arrays_of_fresh hfr hK, ?_, ?_, ?_, ?_, ?_⟩
  · intro born message
    exact First.FillSent.whereIs_of_sentIs hL hS born message
  · exact First.FillSent.link_of_sentIs hL hS
  · rw [← hlive]
    exact F.shape
  · rw [← hlive]
    exact F.layout
  · rw [hst]
    exact F.codes
  · rw [hst]
    exact F.msgs
  · rw [hbk]
    exact F.seats
  · rw [hbk, hbo.1.2, hbo.2]
  · rw [hst, hbo.2]

variable (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (d : FoldData) (reqW : P → Array UInt32)

/-- **The head's matrices are seated, at the reached states at 342 inside the promise at 342.** -/
theorem mats_342 (hfit : pubFit (MGA).more linksFull PS = true)
    (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull PS)
    (hd : d.sent = D.sent) (hlay : D.layout = lay6)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS d.L d.M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[342]?) = true) :
    ∀ a, Rch 342 a → onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 342 a →
      a.1.2.failed = none → ∀ aK, K9.segAt? a.1.2 = some aK →
      MatsSeated (ColFour Wp.hS Wp.HLy (borderOf Wp.y)) D.arr D.N Wp (D.N.sent 24 0) aK num
        lay6 :=
  fun a hr ha hm aK hK =>
    matsSeated_of_C hC
      (stateIsPlan_342 D Mg lay6 Fr d.L d.M hfit a ha hm
        (foldAt_of_facts D lay6 Fr Rch d reqW FF hd hlay 342 a hr hm) aK hK) _
      (fun x c h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega)

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S hearsReply)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.AtSeat (Nums runIs_at_reach dressed_yes)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {Str : Type}

/-- **What the head has heard is read back, at every state reached at 342.** -/
theorem heard_342 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (a : (ProofFile.InstPub × S) × Str) (h : RchAt (FD Z A B c) 342 a) :
    K6HeardAt Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) a.1.2 := by
  have h' : Reach 0 (c.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Z) (341 + 1)
      (a.1.1, a.1.2) := h
  obtain ⟨s0, b, h341, e, y⟩ := reach_last h'
  obtain ⟨rs, gs, d⟩ := step_yes y
  rw [List.getElem?_map] at e
  obtain ⟨c4, hc4, rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨hcan, d4⟩ := canonical_of_below c4 s0 a.1.2 rs gs d
  obtain ⟨Lk, c4', b', ms, e1, e2, hms, hsc, hla, hsz, -, -⟩ := IM.k6_of hS hR O
  obtain rfl : c4 = c4' := Option.some.inj (hc4.symm.trans (IM.k6_at_341 hS hR O e1 e2).1)
  have hla' : c4 = IM.seatedAs ProofFile.sameReply b' c4.name IM.k6Place := hla
  have d5 : (IM.seatedAs ProofFile.sameReply b' c4.name IM.k6Place).decide s0 rs gs = .ok a.1.2 := by
    rw [← hla']
    exact d4
  have db : b'.decide s0 rs gs = .ok a.1.2 :=
    dressed_yes (same := ProofFile.sameReply) (but := hearsReply) (a := IM.k6Place) (n := c4.name) d5
  obtain ⟨iU3, hi, hk⟩ := VerifiableInference.Reads.AtSeat.seated_yes hsc db
  have er : readsOf Bs.G₀.W = iU3 := by
    unfold readsOf
    rw [hi]
    rfl
  rw [← er] at hk
  exact heardAt_of_decideBy Bs.G₀.W s0 a.1.2 rs
    (wellLaid_341 hS hR O (plan_at O hOk 340) (reach_raw h341) _ _) hcan hk

/-- **The runs of claims, with the reads' tables laid silently, at every state reached at 342.** -/
theorem run_342 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (place : VerifiableInference.Desc.Place) (b : OnBytes.Model.Head.Border)
    (hJ : ∀ q, q < 6 → (Bs.G₀.W.HLy.calls.getD q default).lJ =
      (letI := Head.sizesOf Bs.G₀.W.hS; lJ (OnBytes.Model.Head.keyFloor Bs.G₀.W.hS) (callKeys q)))
    (Nm : Nums Bs.G₀.W) (a : (ProofFile.InstPub × S) × Str) (h : RchAt (FD Z A B c) 342 a) :
    ∀ (e : S) (v : Given × Behind × Places),
      withTables ⟨place, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩ a.1.2 = some e →
      lettersAt (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)) e =
        .ok v →
      ∃ o cov x t, e.here = .head o ∧ e.covered Bs.G₀.W.hS.T Bs.G₀.W.hS.V = .ok cov ∧
        o.x = some x ∧ o.t = some t ∧
        ReadsQuiet.tables Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H cov x = .ok t ∧
        (letI := v.1; letI := v.2.1
         RunIs ⟨Bs.G₀.W.hS, Bs.G₀.W.HLy, b, Bs.G₀.W.H, cov, x, t, readsOf Bs.G₀.W⟩) := by
  obtain ⟨n4, hG⟩ := reach_gives hS hR O (plan_at O hOk 340) (reach_of_rchAt h)
  exact runIs_at_reach Z Bs.G₀ ProofFile.sameReply hearsReply IM.k6Place n4 place b hJ Nm a.1.2 hG

end P4

#print axioms VerifiableInference.Desc.Kinds.Head.Law.heardAt_of_decideBy
#print axioms VerifiableInference.Desc.Kinds.Head.Law.heardAt_of_wellLaid
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.place_341
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.place_342
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.drops_K6
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.fresh_open_342
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.seg_st_book
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.sent_asked_342
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.sentIs_342
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.fresh_342
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.stateIsPlan_342
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.mats_342
#print axioms P4.heard_342
#print axioms P4.run_342
