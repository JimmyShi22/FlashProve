-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/WithinSeat.lean: AT THE PROOF FILE's SEAT EVERY SUB-PROTOCOL OF THE FIRST
CHAIN KEEPS "K13.pileWithin" AND "K13.oneRow"; so both accept at every reached state.

THE JOIN OF TWO WALKS, maker by maker: "the rows on the table stay" (PileStays:
Johnson/Desc/First/Pile/PileMakers.lean, PileSeated.lean; PileSeat.lean) and that on the
statement (StatementSeat.lean, at "grows" and at "the ledgers stay in order"). The three
writers of the pile go by themselves: link 0's "opened" (within_zero), "cleared" (within_push), kind
K13's batching (atM3_withinFact).
  seatKeeps_within, seatBack_within   the two structures of Johnson/IMR/SeatKeeps.lean at Rides
                   WithinFact.
  descPure_reach_within   THE TWO FIELDS: one premise left: every sub-protocol's own test on the
                   list of rounds passes.

What is not claimed. Of "K13.pileMasks". Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.LTPileR.PileSeat
import Johnson.Desc.AtSeats.StatementSeat
import Johnson.Desc.K13.Law.WithinReached
import Johnson.Desc.K13.Law.StatementGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9 (atS drawAlone adds batch)
open VerifiableInference.Desc.K13.Law (FitStays stKeeps_fit WithinFact withinFact_quiet
  withinFact_push withinFact_start atM3_withinFact reach_inv)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Pub)
open Johnson.Desc.First.Walk

abbrev WR : S → S → Prop := Rides WithinFact

/-- The heart of the join. -/
theorem within_same {s s' : S} (q : PileStays s s') (hg : GR s s') (hF : ByS FitStays s s') :
    WR s s' :=
  withinFact_quiet q.1 hg hF fun a' ha' => q.2.2 ⟨a', ha'⟩

theorem within_st {s s' : S} (q : PileStays s s') (e : s'.st = s.st) : WR s s' :=
  within_same q (by show Grows s.st s'.st; rw [e]; exact Grows.refl _)
    (by show FitStays s.st s'.st; rw [e]; exact fun x => x)

theorem whole_within {Cl : Type} {b : Block S Cl} (W : Whole PileStays b) (G : Whole GR b)
    (F : Whole (ByS FitStays) b) : Whole WR b :=
  ⟨fun s rs gs s' e => within_same (W.1 s rs gs s' e) (G.1 s rs gs s' e) (F.1 s rs gs s' e),
    fun c hc n s y e => within_same (W.2.1 c hc n s y e) (G.2.1 c hc n s y e) (F.2.1 c hc n s y e),
    fun c hc s s' e => within_same (W.2.2 c hc s s' e) (G.2.2 c hc s s' e) (F.2.2 c hc s s' e)⟩

theorem fn_within {f : S → Except String S} (W : Fn PileStays f) (G : Fn GR f)
    (F : Fn (ByS FitStays) f) : Fn WR f :=
  fun s t k => within_same (W s t k) (G s t k) (F s t k)

/-! ## The three writers -/

theorem within_zero (Q : LayPar) (fvs : List Bool) (kCol : Nat) :
    Fn WR (openLayZero Q fvs kCol) := fun s t k I => by
  obtain ⟨hr, -, hn⟩ := openLayZero_rows k
  have e : t.st = s.st := (openLayZero_enters Q fvs kCol s t k).1
  exact withinFact_quiet hr (by rw [e]; exact Grows.refl _) (by rw [e]; exact fun x => x)
    (fun a' ha' => absurd ha' (hn a')) I

theorem within_push (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
    (lay : WsLay) (lin : Params.LinShape) : Fn WR (clearWith X counts left
      fun masks w claims os => Pend.pendingRowO lay masks w claims lin os) := fun s t k I => by
  have hg : GR s t := clearWith_grows X counts left (pendingRowO_rowGrows lay lin) s t k
  have hF : ByS FitStays s t :=
    clearWith_by stKeeps_fit X counts left (pendingRowO_rowBy stKeeps_fit lay lin) s t k
  rcases clearWith_cases k with q | ⟨w, r, os, hrow, hr, -, -, hn⟩
  · exact within_same q hg hF I
  · exact withinFact_push hrow hr hg hF hn I

/-! ## The makers -/

open Johnson.Desc.First.Walk.Seat in
theorem framesOf_within {built : Array Stages.LinkH} {first : Params.First}
    {W : Verify.Public} {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn WR f.lay ∧ Fn WR f.opened ∧ Fn WR f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fun s t k => within_st (layFront_pile l s t k) (layFront_quiet l s t k).1.1,
        fun s t k I => by cases k; exact I, within_push _ _ _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨fun s t k => within_st (layFront_pile 0 s t k) (layFront_quiet 0 s t k).1.1,
          within_zero _ _ _, within_push _ _ _ _ _⟩
    · split at e
      · cases e
      · cases e
        exact ⟨fun s t k => within_st (layFront_pile l s t k) (layFront_quiet l s t k).1.1,
          fun s t k => within_st (openAtt_pile _ s t k) (openAtt_enters _ s t k).1,
          within_push _ _ _ _ _⟩
      · cases e
        exact ⟨fun s t k => within_st (layFront_pile l s t k) (layFront_quiet l s t k).1.1,
          fun s t k => within_st (openLay_pile _ s t k) (openLay_enters _ s t k).1,
          within_push _ _ _ _ _⟩

/-- Kind K9's batching: both of its own writes are the lens's, which leave the statement. -/
theorem batch_within (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl WR claims) : Whole WR (K9.batch K9.atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : WR s t₁ := by
    simp only [drawAlone] at h1
    split at h1
    · obtain ⟨q, hq, h1⟩ := bindE h1
      obtain ⟨chi, _, h1⟩ := bindE h1
      obtain ⟨o, ho, h1⟩ := bindE h1
      cases h1
      exact within_st (pile_atS_set _ _) (atS_get (there_some hq)).2
    · cases h1
  have a2 : WR t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    exact rides_trans _ _ _ (hcl t₁ x hx)
      (within_st (pile_atS_set _ _) (atS_get (there_some hq)).2)
  exact rides_trans _ _ _ a1 a2

theorem seatKeeps_within : SeatKeeps WR :=
  have HG : SeatKeeps GR := seatKeeps_by K13.Law.stKeeps_grows
  have HF := seatKeeps_by stKeeps_fit
  { refl := rides_refl
    trans := rides_trans
    frames := fun _ h => framesOf_within h
    k1First := fun q gp h0 => whole_within (firstAtS_pile q gp) (HG.k1First q gp h0)
      (HF.k1First q gp h0)
    k1Later := fun q gp l p m a h0 => whole_within (laterAt_pile q gp l p m a)
      (HG.k1Later q gp l p m a h0) (HF.k1Later q gp l p m a h0)
    reads := fun h => whole_within (readsQuietAt_pile h) (HG.reads h) (HF.reads h)
    k3 := fun c r X cs' sh' a _ h => whole_within (theStated_pile c r X cs' sh' a h)
      (HG.k3 c r X cs' sh' a h) (HF.k3 c r X cs' sh' a h)
    k4 := fun p => whole_within (blockAtC_pile p) (HG.k4 p) (HF.k4 p)
    k5 := fun W l g bf _ h => whole_within (k5AtN_pile W l g bf h) (HG.k5 W l g bf h)
      (HF.k5 W l g bf h)
    k6 := fun h => whole_within (seatedClaims_pile h) (HG.k6 h) (HF.k6 h)
    k7 := fun W l => whole_within (k7Of_pile W l) (HG.k7 W l) (HF.k7 W l)
    k8 := fun p => whole_within (k8Whole_pile p) (HG.k8 p) (HF.k8 p)
    k11 := fun Q => whole_within (headMerge11_pile Q) (HG.k11 Q) (HF.k11 Q)
    closeOf := fun p Q b hb => whole_within (closeOf_pile p Q b hb) (HG.closeOf p Q b hb)
      (HF.closeOf p Q b hb)
    batch := fun p _ hf => batch_within p hf
    k2 := fun p h0 => whole_within (k2_pile p) (HG.k2 p h0) (HF.k2 p h0)
    front := fun tl => fn_within (headFrontQ_pile tl) (HG.front tl) (HF.front tl)
    openQ := fun Q h0 => fn_within (headOpenQ_pile Q) (HG.openQ Q h0) (HF.openQ Q h0)
    finFront := fn_within finishFrontQ_pile HG.finFront HF.finFront
    finBehind := fn_within finishBehindQ_pile HG.finBehind HF.finBehind }

/-- "The statement grows" at the makers behind the last link. -/
theorem seatBack_grows : SeatBack GR :=
  seatBack_by K13.Law.stKeeps_grows

theorem seatBack_within : SeatBack WR :=
  have HG := seatBack_grows
  have HF := seatBack_by stKeeps_fit
  { k12 := fun m hp => whole_within (atFinish_pile _) (HG.k12 m hp) (HF.k12 m hp)
    k13M3 := fun p => ⟨atM3_withinFact p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
    k13M4 := fun p Q h0 => whole_within (atM4_pile p Q) (HG.k13M4 p Q h0) (HF.k13M4 p Q h0) }

/-- **THE TWO FIELDS, AT THE PROOF FILE's SEAT**: at every reached state of the first chain
"K13.pileWithin" and "K13.oneRow" accept. -/
theorem descPure_reach_within {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ((∀ b ∈ c.blocksInOrder, b.planOk = true) → ∀ (k : ℕ) (a : ProofFile.InstPub × S),
          Reach 0 c.blocksInOrder (ProofFile.startS Z) k a → WithinFact a.2) := by
  obtain ⟨Z, A, B, c, hZ, e, k⟩ :=
    descPure_flat seatKeeps_within seatBack_within (fun _ _ => trivial) h
  exact ⟨Z, A, B, c, hZ, e, fun hp _ _ hr =>
    reach_inv WithinFact (fun z => withinFact_start (startS_facts hZ z).1 (startS_facts hZ z).2.1
      (startS_facts hZ z).2.2) hp k hr⟩

#print axioms seatKeeps_within
#print axioms seatBack_within
#print axioms descPure_reach_within

end Meaning.K2
