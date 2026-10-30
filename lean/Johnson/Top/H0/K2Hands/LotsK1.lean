-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/LotsK1.lean: LotsKeep.lean, continued: the commitments' lot
(Johnson/Desc/ProofFile/Lots/PureLots.lean: `k1Pure`) in PureKeeps.lean's one form for a lot. A law
file; no running text imports it.

The lot's sub-protocols are the first segment's opening; at each segment the commitment in front of
the smallness test, with a step without a round joined behind it; and the commitment behind that
test. The three sendings write stored sample rows: their laws stand in other files
(Johnson/Desc/K1/Law/RowsKept.lean, RowsKeptPlan.lean, RowsAnswered.lean). The joined step leaves
the statement (Johnson/Goal/Meaning/RecReads.lean, RecReadsAtt.lean).

  `quietBlockAt_rows`, `readsQuiet_rows`   the joined step, as `readsQuietAt` makes it: SameRows,
                   and no run.
  `lotKeeps_k1`    the lot, at every P that SameRows carries, from `KeepsD R P` of the sendings AT
                   THE PLACES THAT THE LOT LAYS, and no other, EACH UNDER ITS OWN TEST ON THE PLAN.
  `lotKeeps_k1_ans`   at AnsweredStored: NO PREMISE.
  `lotKeeps_k1_good`, `k1Share`   at RowsInv QGoodS: where every code's message length is a power
                   of two (Codes.lengthsOk): by Johnson/Desc/K1/Law/RowsKeptPlan.lean's
                   keepsInv_firstAtS_plan | keepsInv_laterAt_plan.
  `lettersBy_first`, `blankBy_first`, `lengths_of_desc`   that test holds wherever `onlineDescription`
                   returns.
  `both_front_good`   BothFront.lean's both_front at QGoodS WITH NO PREMISE ON K1.
Limits. hk (the code switch's own share) is a premise here; SampleChainS.lean pays it. Nothing on
soundness or on hiding.

-/
import Johnson.Top.H0.K2Hands.BothFront
import Johnson.Desc.K1.Law.RowsAnswered
import Johnson.Desc.K1.Law.RowsKeptPlan
import Johnson.Goal.Meaning.RecReads
import Johnson.Goal.Meaning.RecReadsAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block KindName Place)
open VerifiableInference.Desc.Keeps1
open VerifiableInference.Desc.K1 (laterAt firstSegmentOpening linkNumbers gpOf)

variable {R : Fmt.RoundView → Prop} {P : S → Prop}

theorem quietBlockAt_rows {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {b : Block S Unit}
    (h : VerifiableInference.Desc.K8.ReadsQuiet.blockAt G hS HLy H kinds l = some b) :
    RowsD b ∧ b.after = [] := by
  unfold VerifiableInference.Desc.K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨fun s s' _ _ hy => sameRows_of_eq (Meaning.K2.layers_st hy), rfl⟩
  · split at h
    · cases h
      exact ⟨fun s s' _ _ hy => sameRows_of_eq (Meaning.K2.head_st hy), rfl⟩
    · cases h

/-- The step without a round that is joined behind the commitment in front of the smallness test. -/
theorem readsQuiet_rows {G : ProofFile.Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) : RowsD b ∧ b.after = [] := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      unfold Att.readsAtO at h
      obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨fun s s' _ _ hy => sameRows_of_eq (Meaning.K2.readsAtSO_st hy), rfl⟩
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == if X.kind == 0 then 4 else 5) = true
    · rw [if_pos h2] at h
      exact quietBlockAt_rows h
    · rw [if_neg h2] at h
      cases h

theorem orLoud_rows {name : String} {a : Place} {what : String} {o : Option (Block S Unit)}
    (h : ∀ b, o = some b → RowsD b ∧ b.after = []) :
    RowsD (ProofFile.orLoud name a what o) ∧ (ProofFile.orLoud name a what o).after = [] := by
  cases o with
  | some b => exact h b rfl
  | none => exact ⟨fun s s' _ _ hy => (by cases hy), rfl⟩

/-- **The commitments' lot**, from the sendings at the places that the lot lays. -/
theorem lotKeeps_k1 (hP : Rides P) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hfirst : (firstSegmentOpening G.first (gpOf Z) : Block S Unit).planOk = true →
      KeepsD R P (firstSegmentOpening G.first (gpOf Z) : Block S Unit))
    (hlater : ∀ X l pr pd reads digits, (X, l) ∈ G.built.toList.zipIdx →
      linkNumbers G X = some (pr, pd, reads, digits) →
      ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).planOk = true →
        KeepsD R P (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit)) ∧
      ((laterAt G.first (gpOf Z) l pd 2 digits : Block S Unit).planOk = true →
        KeepsD R P (laterAt G.first (gpOf Z) l pd 2 digits : Block S Unit))) :
    LotKeeps R P (ProofFile.k1Pure Z) G := by
  have key : ∀ b₀ ∈ (ProofFile.k1Pure Z).own G,
      (b₀.planOk = true → KeepsD R P b₀) ∧ b₀.after = [] ∧ b₀.place.kind = KindName.K1 := by
    intro b₀ h0
    unfold ProofFile.k1Pure VerifiableInference.Desc.K1.lotWith VerifiableInference.Desc.K1.blocks at h0
    dsimp only at h0
    rcases List.mem_append.1 h0 with h0 | h0
    · obtain rfl := List.mem_singleton.1 h0
      exact ⟨hfirst, rfl, rfl⟩
    · obtain ⟨⟨X, l⟩, hx, h0⟩ := List.mem_flatMap.1 h0
      dsimp only at h0
      split at h0
      · cases h0
      · rename_i pr pd reads digits hn
        obtain ⟨k1, k2⟩ := hlater X l pr pd reads digits hx hn
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
        rcases h0 with rfl | rfl
        · have q := orLoud_rows
            (name := s!"link {l}: the step after the commitment before the smallness test")
            (a := ⟨1, some l, if X.kind == 0 || X.kind == 1 then 4 else 5, .K1⟩)
            (what := "the step after the commitment that comes before the smallness test")
            (o := ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5))
            fun b hb => readsQuiet_rows hb
          refine ⟨fun hp => keepsD_andThen _
            (k1 (Bool.and_eq_true _ _ ▸ hp).1) (q.1.keeps hP), ?_, rfl⟩
          show ([] : List (String × (S → Except String S))) ++ _ = []
          rw [q.2]
          rfl
        · exact ⟨k2, rfl, rfl⟩
  refine ⟨fun b hb _ hp => ?_, fun b hb hk => ?_, fun b hb _ _ _ => ?_,
    fun a mk hm => (by cases hm), fun a mk hm => (by cases hm)⟩
  · rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · exact keepsD_retype ((key b₀ h0).1 (Bool.and_eq_true _ _ ▸ hp).1)
    · cases h
  · rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · have e : b₀.place.kind = KindName.frame := hk
      rw [(key b₀ h0).2.2] at e
      cases e
    · cases h
  · rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · exact keepsRuns_none rfl (key b₀ h0).2.1
    · cases h

/-- **At AnsweredStored: no premise.** -/
theorem lotKeeps_k1_ans (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotKeeps (fun _ => True) Ans (ProofFile.k1Pure Z) G :=
  lotKeeps_k1 rides_ans Z G (fun _ => VerifiableInference.Desc.K1.keepsAns_firstAtS _ _)
    fun _ l pr pd reads digits _ _ =>
      ⟨fun _ => VerifiableInference.Desc.K1.keepsAns_laterAt _ _ l pr 1 reads,
        fun _ => VerifiableInference.Desc.K1.keepsAns_laterAt _ _ l pd 2 digits⟩

/-- **At RowsInv QGoodS**, where every code's message length is a power of two. -/
theorem lotKeeps_k1_good (Z : ProofFile.Pub) {G : ProofFile.Ground} (hl : G.first.codes.lengthsOk = true) :
    LotKeeps OkDrawn (Inv QGoodS) (ProofFile.k1Pure Z) G :=
  lotKeeps_k1 rides_inv Z G
    (fun hp => VerifiableInference.Desc.K1.keepsInv_firstAtS_plan _ _ hp hl)
    fun _ l pr pd reads digits _ _ =>
      ⟨fun hp => VerifiableInference.Desc.K1.keepsInv_laterAt_plan _ _ l pr 1 reads hp hl,
        fun hp => VerifiableInference.Desc.K1.keepsInv_laterAt_plan _ _ l pd 2 digits hp hl⟩

theorem k1Share (Z : ProofFile.Pub) {G : ProofFile.Ground} (hl : G.first.codes.lengthsOk = true) :
    K1Share QGoodS Z G := ⟨lotKeeps_k1_good Z hl, lotKeeps_k1_ans Z G⟩

/-! ## The codes' lengths, from the maker's own test at the start -/

theorem lettersBy_first {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {s : S} {G : ProofFile.Ground}
    (h : ProofFile.lettersBy mk Z s = .ok G) : G.first = Z.first := by
  unfold ProofFile.lettersBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; rfl)

theorem blankBy_first {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G) : G.first = Z.first := by
  have h' : (ProofFile.lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1]))).toOption =
      some G := h
  cases hx : ProofFile.lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1])) with
  | error e =>
    rw [hx] at h'
    cases h'
  | ok G' =>
    rw [hx] at h'
    have hG : G' = G := Option.some.inj h'
    exact hG ▸ lettersBy_first hx

/-- Where `onlineDescription` returns, every code's message length is a power of two: it is the first of the
four tests on the first chain's public parameters (`S.startOk`), which the maker asks while it
computes the public part (Johnson/Desc/ProofFile/Law/PureMade.lean: descPure_startOk). -/
theorem lengths_of_desc {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F)
    {Z : ProofFile.Pub} (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {mk : ProofFile.LinksBy} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G) : G.first.codes.lengthsOk = true := by
  obtain ⟨Z', hZ', hs⟩ := ProofFile.Law.descPure_startOk h
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  unfold S.startOk at hs
  rw [blankBy_first hG]
  exact (Bool.and_eq_true _ _ ▸ hs).1

/-- **The keepers' table as one term, at QGoodS: no premise on K1.** hk: the code switch's own
decision keeps RowsInv QGoodS: SampleChainS.lean's keepsS_k2. -/
theorem both_front_good {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F)
    (hpl : F.planOk = true) (hk : ∀ p : P2, KeepsInv QGoodS (codeSwitchKind p : Block S Unit)) :
    ∃ (Z : ProofFile.Pub) (c : VerifiableInference.Desc.Chain S ProofFile.Cl) (A : ProofFile.SharedSeat)
      (B' : ProofFile.SecondSeat),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B' (fun s => s) (ProofFile.startS Z) c ∧
      c.front = [] ∧ (Meaning.K2.frontOf c).length = 14 * (ProofFile.subsOf Z).length + 3 ∧
      ∀ k, k ≤ (Meaning.K2.frontOf c).length →
        (∀ b ∈ c.blocksInOrder.take k, KeepsInv QGoodS b) ∧ ∀ b ∈ c.blocksInOrder.take k, KeepsAns b :=
  both_front h hpl hk fun Z _ hZ hG => k1Share Z (lengths_of_desc h hZ hG)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.lotKeeps_k1
#print axioms VerifiableInference.Desc.First.K2.lotKeeps_k1_ans
#print axioms VerifiableInference.Desc.First.K2.lotKeeps_k1_good
#print axioms VerifiableInference.Desc.First.K2.k1Share
#print axioms VerifiableInference.Desc.First.K2.lengths_of_desc
#print axioms VerifiableInference.Desc.First.K2.both_front_good
