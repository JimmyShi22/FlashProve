-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/LotsKeep.lean: PureKeeps.lean's one form for a lot (`LotKeeps R P L G`), PAID
LOT BY LOT for the two invariants on the messages' stored sample rows (SampleChain.lean's
`RowsInv Q`; AnsweredStored.lean's `AnsweredStored`), at the lots of the proof file's IOP as written
in Lean (Johnson/Desc/ProofFile/OnlineDescriptionBlocks.lean: `onlineFirstChainBlockTables`). A law file; no running text imports it.
Each lot's share is a call of a law typed in its own kind's files.

  `Rides P`, `rides_inv`, `rides_ans`   P is carried by SameRows; both invariants are.
  `RowsD b`, `RowsRuns b`   an accepting decision, each run of claims and each run behind the
                   batching give SameRows.
  `LotRows L G`, `LotRows.keeps`   a lot that gives SameRows wherever something is asked of it, and
                   supplies no batching, has `LotKeeps R P` at every P that rides, at every R.
  `mem_blocks`     a lot's sub-protocol comes of `own`, at the one type of a claim, or of `hearC`.
  `lotRows_frames`   the segments' frames: laid, opened, cleared.
  `lotKeeps_k2`    the code switch's lot, from the law of the lot's maker `pureAt`.
  `lotRows_k8`     the smallness test's lot.
  `lotRows_k11`    the lot of the merge of the claims on the weights.
  `lotRows_end`    the lot of the chain's end: it hands the state back.
Limits. The other lots of `onlineFirstChainBlockTables` are not treated here. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.K2Hands.PureKeeps
import Johnson.Top.H0.K2Hands.AnsweredStored
import Johnson.Top.H0.K2Hands.SampleOurs
import Johnson.Top.H0.Walk.FrameRows
import Johnson.Desc.ProofFile.OnlineDescriptionBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block KindName Place roundlessBlock)
open VerifiableInference.Desc.Keeps1

/-! ## SameRows carries both invariants -/

/-- P is carried by SameRows. -/
def Rides (P : S → Prop) : Prop := ∀ s s' : S, SameRows s.st s'.st → P s → P s'

theorem rides_inv {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop} : Rides (Inv Q) :=
  fun _ _ h hs => rowsInv_rows h hs

theorem rides_ans : Rides Ans := fun _ _ h hs => answered_rows h hs

variable {Cl : Type}

/-- An accepting decision gives SameRows. -/
def RowsD (b : Block S Cl) : Prop := ∀ s s' rs gs, b.decide s rs gs = .ok s' → SameRows s.st s'.st

/-- Each run of claims and each run behind the batching gives SameRows. -/
def RowsRuns (b : Block S Cl) : Prop :=
  (∀ c ∈ b.claims, ∀ n s y, c.2 n s = .ok y → SameRows s.st y.2.st) ∧
    ∀ c ∈ b.after, ∀ s s', c.2 s = .ok s' → SameRows s.st s'.st

variable {R : Fmt.RoundView → Prop} {P : S → Prop}

theorem RowsD.keeps {b : Block S Cl} (hP : Rides P) (h : RowsD b) : KeepsD R P b :=
  fun s s' rs gs _ hy hs => hP s s' (h s s' rs gs hy) hs

theorem RowsRuns.keeps {b : Block S Cl} (hP : Rides P) (h : RowsRuns b) : KeepsRuns P b :=
  ⟨fun c hc n s y hy hs => hP s y.2 (h.1 c hc n s y hy) hs,
    fun c hc s s' hy hs => hP s s' (h.2 c hc s s' hy) hs⟩

theorem rowsRuns_none {b : Block S Cl} (h1 : b.claims = []) (h2 : b.after = []) : RowsRuns b :=
  ⟨fun c hc => (by rw [h1] at hc; cases hc), fun c hc => (by rw [h2] at hc; cases hc)⟩

theorem keepsRuns_none {b : Block S Cl} (h1 : b.claims = []) (h2 : b.after = []) : KeepsRuns P b :=
  ⟨fun c hc => (by rw [h1] at hc; cases hc), fun c hc => (by rw [h2] at hc; cases hc)⟩

/-- A lot that gives SameRows wherever something is asked of it, and supplies no batching. -/
structure LotRows (L : ProofFile.Lot) (G : ProofFile.Ground) : Prop where
  decide : ∀ b ∈ L.blocks G, b.place.link ≠ none ∨ b.place.kind = KindName.frame → RowsD b
  runs : ∀ b ∈ L.blocks G, b.place.link ≠ none ∨ b.place.kind = KindName.frame →
    b.place.kind ≠ KindName.K9 → b.place.kind ≠ KindName.K10 → RowsRuns b
  batch : ∀ a, L.batch G a = none

theorem LotRows.keeps {L : ProofFile.Lot} {G : ProofFile.Ground} (hP : Rides P) (h : LotRows L G) :
    LotKeeps R P L G where
  decide := fun b hb hl _ => (h.decide b hb (Or.inl hl)).keeps hP
  frame := fun b hb hk => (h.decide b hb (Or.inr hk)).keeps hP
  runs := fun b hb ho h9 h10 => (h.runs b hb ho h9 h10).keeps hP
  batch := fun a mk hm => by rw [h.batch a] at hm; cases hm
  batchRuns := fun a mk hm => by rw [h.batch a] at hm; cases hm

/-- A lot's sub-protocol comes of `own`, at the one type of a claim, or of `hearC`. -/
theorem mem_blocks {L : ProofFile.Lot} {G : ProofFile.Ground} {b : Block S ProofFile.Cl} (h : b ∈ L.blocks G) :
    (∃ b₀ ∈ L.own G, b = b₀.retype) ∨ b ∈ L.hearC G := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨b₀, h0, rfl⟩ := List.mem_map.1 h
    exact Or.inl ⟨b₀, h0, rfl⟩
  · exact Or.inr h

/-! ## The segments' frames -/

open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame framesOf_row mapM_mem) in
/-- "Opened", at every row of the frame's value: the statement stays. -/
theorem frames_opened {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} (h : framesOf built first W = .ok fs) (hf : f ∈ fs)
    {s t : S} (hy : f.opened s = .ok t) : SameRows s.st t.st := by
  unfold framesOf at h
  obtain ⟨a, _, e⟩ := mapM_mem _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      cases hy
      exact SameRows.refl _
  · split at e
    · split at e
      · cases e
      · cases e
        exact sameRows_of_eq
          (Johnson.Desc.First.Walk.Tied.openedZeroGives _ _ _ s t hy).2.2.1.2.2.1
    · split at e
      · cases e
      · cases e
        exact sameRows_of_eq (Johnson.Desc.First.Walk.Tied.openedAttGives _ s t hy).2.2.1.2.2.1
      · cases e
        exact sameRows_of_eq (Johnson.Desc.First.Walk.Tied.openedLayGives _ s t hy).2.2.1.2.2.1

/-- Every sub-protocol of the frames' lot: SameRows, and no run. -/
theorem frames_block (Z : ProofFile.Pub) : ∀ b ∈ P1L20.blocksOf Z,
    RowsD b ∧ b.claims = [] ∧ b.after = [] := by
  intro b hb
  unfold P1L20.blocksOf at hb
  split at hb
  · rename_i fs hfs
    obtain ⟨f, hf, hb⟩ := List.mem_flatMap.1 hb
    obtain ⟨hlay, X, counts, left, hclear, -⟩ :=
      Johnson.Desc.First.Walk.Seat.framesOf_row hfs hf
    unfold ProofFile.frameBlocks at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · refine ⟨fun s s' _ _ hy => ?_, rfl, rfl⟩
      have hy' : f.lay s = .ok s' := hy
      rw [hlay] at hy'
      exact sameRows_of_eq (congrArg (·.st) (Johnson.Desc.First.Walk.Law.layFront_ok hy').1)
    · exact ⟨fun s s' _ _ hy => frames_opened hfs hf hy, rfl, rfl⟩
    · refine ⟨fun s s' _ _ hy => ?_, rfl, rfl⟩
      have hy' : f.clear s = .ok s' := hy
      rw [hclear] at hy'
      exact clearWith_smp hy'
  · obtain rfl := List.mem_singleton.1 hb
    exact ⟨fun s s' _ _ hy => (by cases hy), rfl, rfl⟩

theorem lotRows_frames (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotRows (ProofFile.framesLot Z) G where
  decide := fun b hb _ => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · exact (frames_block Z b₀ h0).1
    · cases h
  runs := fun b hb _ _ _ => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · exact rowsRuns_none rfl (frames_block Z b₀ h0).2.2
    · cases h
  batch := fun _ => rfl

/-! ## The code switch's lot -/

/-- No sub-protocol that the lot's maker makes states a run behind the batching. -/
theorem pureAt_after (G : ProofFile.Ground) (x : ProofFile.Spot × P2) (b : Block S Unit)
    (h : P1K2.pureAt (fun _ _ => some none) G x = some b) : b.after = [] := by
  unfold P1K2.pureAt at h
  dsimp only at h
  split at h
  · cases h
    rfl
  · obtain ⟨P, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨l, -, ho⟩ := Option.bind_eq_some_iff.1 ho
    cases ho
    rfl

/-- **The code switch's lot**, from the law of the lot's maker. -/
theorem lotKeeps_k2 (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hAt : ∀ x b, P1K2.pureAt (fun _ _ => some none) G x = some b → KeepsD R P b) :
    LotKeeps R P (ProofFile.k2Pure Z) G := by
  have key : ∀ b₀ ∈ P1K2.pureTable (fun _ _ => some none) Z G, KeepsD R P b₀ ∧ b₀.after = [] := by
    intro b₀ h0
    unfold P1K2.pureTable at h0
    dsimp only at h0
    obtain ⟨sp, -, rfl⟩ := List.mem_map.1 h0
    split
    · exact ⟨fun s s' _ _ _ hy => (by cases hy), rfl⟩
    · rename_i x _
      cases hq : P1K2.pureAt (fun _ _ => some none) G x with
      | none => exact ⟨fun s s' _ _ _ hy => (by cases hy), rfl⟩
      | some b => exact ⟨hAt x b hq, pureAt_after G x b hq⟩
  have all : ∀ b ∈ (ProofFile.k2Pure Z).blocks G, KeepsD R P b := by
    intro b hb
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · exact keepsD_retype (key b₀ h0).1
    · cases h
  refine ⟨fun b hb _ _ => all b hb, fun b hb _ => all b hb, fun b hb _ _ _ => ?_,
    fun a mk hm => (by cases hm), fun a mk hm => (by cases hm)⟩
  rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
  · exact keepsRuns_none rfl (key b₀ h0).2
  · cases h

theorem lotKeeps_k2_inv {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop}
    (hk : ∀ p : P2, KeepsInv Q (codeSwitchKind p : Block S Unit)) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotKeeps OkDrawn (Inv Q) (ProofFile.k2Pure Z) G :=
  lotKeeps_k2 Z G fun x b h => keepsInv_pureAt hk G x b h

theorem lotKeeps_k2_ans (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotKeeps (fun _ => True) Ans (ProofFile.k2Pure Z) G :=
  lotKeeps_k2 Z G fun x b h => keepsAns_pureAt G x b h

/-! ## The smallness test's lot -/

theorem lotRows_k8 (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotRows (ProofFile.P1K8.lot Z) G where
  decide := fun b hb _ => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · cases h0
    · obtain ⟨⟨X, l⟩, -, rfl⟩ := List.mem_map.1 h
      exact fun s s' rs gs hy => sameRows_of_eq
        (K8.hear_leaves_statement (Cl := VerifiableInference.Desc.Claim) _ s rs gs s' hy)
  runs := fun b hb _ _ _ => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · cases h0
    · obtain ⟨⟨X, l⟩, -, rfl⟩ := List.mem_map.1 h
      exact ⟨fun r hr n s y hy =>
          sameRows_of_eq (congrArg (·.1) (K8.whole_claims_rest _ r hr n s y hy)),
        fun r hr s s' hy => sameRows_of_eq (congrArg (·.1) (K8.whole_after_rest _ r hr s s' hy))⟩
  batch := fun _ => rfl

/-! ## The lot of the merge of the claims on the weights -/

/-- The merge's one run of claims leaves the statement. -/
theorem mergeClaim_st {n : Nat} {s : S} {y : List VerifiableInference.Desc.Claim × S}
    (h : Johnson.Desc.First.ForkMerge.headMergeClaim n s = .ok y) : y.2.st = s.st := by
  unfold Johnson.Desc.First.ForkMerge.headMergeClaim at h
  split at h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rfl
  · cases h

theorem lotRows_k11 (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotRows (K11.lot Z) G where
  decide := fun b hb _ => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · cases h0
    · obtain rfl := List.mem_singleton.1 h
      exact fun s s' rs gs hy => sameRows_of_eq (MergeLaw.leavesSeven _ s rs gs s' hy).1
  runs := fun b hb _ _ _ => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · cases h0
    · obtain rfl := List.mem_singleton.1 h
      refine ⟨fun c hc n s y hy => ?_, fun c hc => (by cases hc)⟩
      obtain rfl := List.mem_singleton.1 hc
      exact sameRows_of_eq (mergeClaim_st (n := n) hy)
  batch := fun _ => rfl

/-! ## The lot of the chain's end -/

theorem lotRows_end (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotRows (VerifiableInference.Desc.K13.lotEnd Z) G where
  decide := fun b hb _ => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · obtain rfl := List.mem_singleton.1 h0
      intro s s' rs gs hy
      have hy' : (VerifiableInference.Desc.ChainEnd.refuse (endAsks s)).map (fun _ => s) = .ok s' :=
        hy
      cases hq : VerifiableInference.Desc.ChainEnd.refuse (endAsks s) with
      | error e => rw [hq] at hy'; cases hy'
      | ok u =>
        rw [hq] at hy'
        cases hy'
        exact SameRows.refl _
    · cases h
  runs := fun b hb _ _ _ => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · obtain rfl := List.mem_singleton.1 h0
      exact rowsRuns_none rfl rfl
    · cases h
  batch := fun _ => rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.lotRows_frames
#print axioms VerifiableInference.Desc.First.K2.lotKeeps_k2_inv
#print axioms VerifiableInference.Desc.First.K2.lotKeeps_k2_ans
#print axioms VerifiableInference.Desc.First.K2.lotRows_k8
#print axioms VerifiableInference.Desc.First.K2.lotRows_k11
#print axioms VerifiableInference.Desc.First.K2.lotRows_end
