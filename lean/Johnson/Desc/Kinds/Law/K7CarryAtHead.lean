-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7CarryAtHead.lean.
WHAT IT DOES NOT SHOW. No soundness. THE LAST DEBT OF THE NEXT TOKEN's CONDITION THAT IS NO TEST,
K7Carry, IS HAD HERE, NOT FOR NOTHING: SEVEN PREMISES STAY, BY NAME: unm ("reached" at 338 says
"unmarked": met by taking the law at "reached and unmarked": Law/TiedRMonoOn.lean) · book (a test
with code on public data; evaluated true; no theorem) · hs (a closed fact on the public part: the
place whose switch opens group 24 stands at the head; evaluated; a theorem of the code switching's
files under a named test and "25 links") · hb (the piece's base is at most the number of the first
chain's trees) · THREE FACTS ALONG "REACHED" AT 338, IN THE LETTERS OF THREE FIELDS OF FoldFacts:
bookInOrder (HERE AT THE SWITCH's OWN FIRST TREE, (par9 (ProofFile.pAtK2 Zp 23)).firstTree; the field
speaks at the fold data's d.ft: the equation of the two is ft_at_switch with d.ft = 0)
· bookFits · rowsSent. AT THE SECOND HASH FUNCTION ITSELF ALONE. The full size alone. No example.
WORDS. "The strings": the oracles' contents as the proof's frame holds them, in front of a piece and
behind it. "Unmarked": the verifier's state bears no mark of failure. "The promise": the table's
condition at a border (Desc/Sound/BordersQ.lean: onQ).
LETTERS. No "there is" in the statement. Rch: free but for unm.
OBJECT. Law/K7CondOfLaid.lean's K7Carry at the table's files' head AtMgA and its own row.
USER. Law/K7CondOfLaid.lean: k7Cond_of_laid's premise carry.
WHAT IT IS. ALL CALLS. THE SENTENCE "carry 23" GOES BACK OVER THE PLACE IN TWO STEPS, AND THE ORDER
MATTERS.
(1) THE STATES, AT THE STRINGS BEHIND: carry_over_reply_stands
(K2Caller/CarryOverReply.lean): its premises on the front, the book and the roots are
Law/ReplyFront.lean's place_front; where the chain stands on either side comes out of the two
promises (K2Caller/DoorOfPromise.lean: stand_of_promise); it holds at any two witnesses, so the
token laid is no matter.
(2) THE STRINGS, AT THE STATE IN FRONT: carry_back_door at doorLike_refl
(Walk/FrameCarryEnds.lean) with longFront_stays (Walk/FrameCarryBack.lean), under the fence
CarryFence at the piece's base: had from fence_of_in_doorData (Walk/FrameCarryFenceEnds.lean).
BEHIND THE PLACE THE CHAIN STANDS AT THE HEAD's LINK, WHERE THAT FILE SAYS NOTHING: hence the
strings are turned in front.
THE FENCE's FOURTH FACT, "the book's trees are at most the base", COMES OUT OF THE PROMISE IN FRONT
(its last clause, bookAt) with base_treesAt. That the strings stay beneath the
base: Walk/StaysBehind.lean: stays_behind.
size_of_promise: that fourth fact, kind-free. k7Carry_at_head: the statement.

-/
import Johnson.Desc.Kinds.Law.K7CondOfLaid
import Johnson.Desc.Kinds.Law.ReplyFront
import Johnson.Top.H0.K2Caller.CarryOverReply
import Johnson.Top.H0.Walk.FrameCarryFenceEnds
import Johnson.Top.H0.Walk.StaysBehind
import Johnson.Top.H0.Opts.WholeOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (HTailF2)
open OnBytes.Params (ReqLayout ReqShape)
open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc (Strs Place Block FileDescription Oracle KindName)
open VerifiableInference.Desc.First (S Numbers ModelPart Meaning PubData flatPlacesOf rowSegs sampledIn
  openSets start Item readsOpen pubHeld pubSets pubStep pubRowM pubOfItems stepOpen rowOf)
open VerifiableInference.Desc.K13 (indexIsC indexThereC)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_rest withFresh)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (standOf)
open VerifiableInference.Desc.First.K2 (par9)
open VerifiableInference.Desc.First.K2Caller (carryAtZ carry_over_reply_stands stand_of_promise
  out_of_between)
open Johnson.Desc.First.Walk.Tied (Stays stays_behind fence_of_in_doorData carry_back_door
  doorLike_refl longFront_stays)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The driver's list of places, at the full chain. -/
local notation "PS" => flatPlacesOf linksFull true

/-- **Out of the promise at an unmarked state: the book holds as many trees as the table's numbers
say at the border.** Kind-free. -/
theorem size_of_promise {A P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × S} {k : Nat} (a : A × Fr.E.Str)
    (ha : onQ N Mg links ps get k a) (hm : ¬ (get a.1).2.failed ≠ none) :
    (get a.1).2.book.trees.size = N.treesAt ps[k]? := by
  obtain ⟨-, h⟩ := ha
  rcases h with h | ⟨hb, -⟩
  · exact absurd h hm
  · simp only [Bool.and_eq_true] at hb
    have hh := hb.2
    unfold VerifiableInference.Desc.First.bookAt at hh
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.1.1

/-- **"carry 23" RIDES PAST THE NEXT TOKEN's PLACE.** -/
theorem k7Carry_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (Rch)
    (unm : ∀ a, Rch 338 a → ¬ a.1.2.failed ≠ none)
    (book : First.bookFit (dAt h).N PS (toldOf cF.blocksInOrder) = true)
    (hs : (ProofFile.pAtK2 Zp 23).stands = .head)
    (hb : ∀ q, (h.toAtMg.row L)[338]? = some q → q.base ≤ D.t₁)
    (bookInOrder : ∀ a, Rch 338 a → a.1.2.failed = none →
      VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Zp 23)).firstTree a.1.2 = true)
    (bookFits : ∀ a, Rch 338 a → a.1.2.failed = none →
      VerifiableInference.Desc.K12.Door.atFirstFits a.1.2 = true)
    (rowsSent : ∀ a, Rch 338 a → a.1.2.failed = none →
      ∀ o ∈ OnBytes.singleRowsOracles a.1.2.live.frame.rows, o < a.1.2.book.place.size) :
    ∀ B q, cF.blocksInOrder[338]? = some B → (h.toAtMg.row L)[338]? = some q →
      K7Carry h L.c₀ Rch B q := by
  intro B q hB hq z a τ b w hout hr ha hbq hc
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b₀, e1, e2, -, -, hyes, hfront⟩ := P4.k7_left_seat h.scope h.reads O
  have f1 : cF.blocksInOrder[338]? = some b₀ := by
    have q' := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope h.scope h.reads O (by decide) 0] at q'
  obtain rfl : B = b₀ := Option.some.inj (hB.symm.trans f1)
  obtain ⟨rs, gs, hy⟩ := Came.piece_yes hyes z a τ b hout
  obtain ⟨s0, h0, hfr, hbk, hrt⟩ :=
    place_front Bs.G₀.W 24 "H:1" (P4.k7Front Bs.G₀.W) Bs.G₀.W.H.tl hfront _ _ _ _ hy
  have lv := place_leaves Bs.G₀.W 24 "H:1" (P4.k7Front Bs.G₀.W) Bs.G₀.W.H.tl hfront _ _ _ _ hy
  have hm : ¬ a.1.failed ≠ none := unm _ hr
  have hm0 : a.1.failed = none := not_not.1 hm
  have hmb : ¬ b.1.failed ≠ none := by rw [lv.2.2.2.2.2.1]; exact hm
  have h1 : standOf a.1 = .between :=
    (stand_of_promise _ _ _ _ _ _ a ha hm _ place338).trans rfl
  have h2 : standOf b.1 = .headFront :=
    (stand_of_promise _ _ _ _ _ _ b hbq hmb _ place339).trans rfl
  -- (1) the states, at the strings behind
  have c1 : carryAtZ Zp _ 23 (z, a.1) (strsOf _ b.2)
      (⟨w.cells, P5J.tokOfHeard (z, b.1), w.msg, w.pad⟩ : Wit _ _ _) :=
    (carry_over_reply_stands Zp _ 23 hs z a.1 b.1 s0 _ h1 h2 h0 hfr hbk hrt _ w _).2 hc
  -- (2) the strings, at the state in front
  have hS : Stays q.base (strsOf _ a.2) (strsOf _ b.2) := by
    rw [out_behind _ a b τ hout]
    exact stays_behind _ _ _ _ _ _
  have hmore := atRow_more h.toAtMg L q₁ q₂ q₃ 338 q hq (atRow_in h.toAtMg 338 (by omega))
  have hbase : q.base = (dAt h).N.treesAt PS[338]? :=
    base_treesAt hmore.1 (atRow_blocks h.toAtMg) (dAt h).N PS (by rw [toldOf_held]; exact book)
      len338
  have hsz : a.1.book.trees.size ≤ q.base := by
    rw [hbase]
    exact le_of_eq (size_of_promise a ha hm)
  have hF := fence_of_in_doorData (P := ProofFile.InstPub) Zp D
    (P1M2.wholeAt_of_laid h.laid) 23 q.base (hb q hq) (fun y _ => y = (z, a.1))
    (by
      rintro p s y ⟨⟩
      exact ⟨bookInOrder _ hr hm0, bookFits _ hr hm0, rowsSent _ hr hm0, hsz⟩)
    (by
      rintro - p s y ⟨⟩
      exact (out_of_between a.1 h1).2)
  exact carry_back_door Zp _ 23 (doorLike_refl Zp 23 a.1)
    (fun s' fx q' hd hfx => longFront_stays (hF z a.1 (strsOf _ a.2) s' rfl hd) hS fx q' hfx)
    z _ c1

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.size_of_promise
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k7Carry_at_head
