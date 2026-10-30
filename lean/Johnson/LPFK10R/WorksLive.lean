-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/WorksLive.lean: UNDER THE GATE's OWN YES, IN SCOPE, K10's SUB-PROTOCOLS HAVE NO PROOF OF WORK AND AT LEAST ONE FOLD ROUND: TWO PREMISES OF K10's ROAD ARE THEOREMS. Statements and proofs.
(In the Lean names a «block» is a sub-protocol and a «description» the IOP as written in Lean.)
WHY. K10's data at the maker's piece (PieceAtDescK10.lean, RoundsLive.lean) stood under «both of Q's numbers of proof of work are 0»: true by a run (ParGuard) alone. THE FIRST TEST THAT THE LAWS ASK OF THE LAID VALUE (LPFD.lawsAsk, Johnson/Desc/Laid/ProofAsks.lean) is
PlanWritten.seatPinnedProof: the gate's yes gives its yes (FlashProve.pseat_name's fourth conjunct); in scope seat_in_scope (Johnson/Goal/Numbers/PlanWrittenDescScope.lean) makes of it: the IOP's declared rounds, written out, ARE the full size's written lists.
  mapM_mem · round_entry · written_mem   writtenOf file D = .ok R: every declared round of the first chain has its entry among R.1's rounds.
  written_works    in dryProofFull.1 (48,293 rounds) no round «BAT» and no round «FOLD round» has proof of work: BY THE KERNEL.
  one_le_k   beneath the tests on the plan of the proof file's IOP stands K10's own: 1 ≤ Q.k.
  works_of_written   general in the description F: writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull · b ∈ F.first.blocksInOrder · b.rounds = (kind Q).rounds · 1 ≤ Q.k: Q.workField = 0 ∧ Q.workClose = 0.
  k10_works_live   InScope P · readFiles P = .ok pp · protocolDataWellFormed (asDescriptionFiles P) = true: THERE ARE F, Z, Bs, base, c, A, B WITH Open … · writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull · AND AT EVERY b OF c.blocksInOrder OF THE KIND K10: l < 25, p, Q with k9At Z l = some p ·
                   k10Par … = some Q · c.blocksInOrder[ixK10 l]? = some b · 1 ≤ Q.k (the sub-protocol's own test on the plan, beneath F.planOk) · Q.workField = 0 · Q.workClose = 0.
LIMITS. k10_works_live's three premises are shown here of no files. Other Lean files prove them at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`, not throughout the scope: the first two `VerifierAndGoals.filesRead` (Johnson/Goal/Files/FilesReadProof.lean), the third `theLive_zFull`, `theLive_zGap` (AtFullSide/Top/LiveAtFull.lean, LiveAtPolicies.lean: a side library). Limits there. The written lists were printed from this library's own planner (PlanWritten/Test.lean's own limit): a yes of the test is no second witness for them. WHICH of the written «BAT»s is b's is not said: so
Q.rows and Q.k are not yet tied to the l-th written closing's numbers. At OnBytes.secondHashFunction, in scope; the proof file alone. Nothing on soundness.

-/
import Johnson.LPFK10R.SitsLive
import Johnson.Goal.Numbers.PlanWrittenDescScope

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Close (Par kind entries)
open Johnson.G (dryProofFull)
open Johnson.G.OfPlan (writtenOf Decl3)
open ProofFile (Cl)
open IM

/-- A list carried through a function that may refuse: each member's value is a member. -/
theorem mapM_mem {α β ε : Type} (f : α → Except ε β) : ∀ (l : List α) (L : List β),
    l.mapM f = .ok L → ∀ r ∈ l, ∃ y ∈ L, f r = .ok y
  | [], _, _, _, hr => absurd hr List.not_mem_nil
  | a :: l, L, h, r, hr => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok y =>
      rw [ha] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok ys =>
        rw [hl] at h
        have hL : L = y :: ys := (Except.ok.inj h).symm
        subst hL
        rcases List.mem_cons.1 hr with rfl | hr'
        · exact ⟨y, List.mem_cons_self, ha⟩
        · obtain ⟨z, hz, e⟩ := mapM_mem f l ys hl r hr'
          exact ⟨z, List.mem_cons_of_mem _ hz, e⟩

/-- A declared round, written out, keeps its entry. -/
theorem round_entry {e : List (List ByteArray × ByteArray)} {r : Fmt.DeclaredRound} {x : Fmt.Round}
    (h : r.round e = some x) : x.entry = r.entry := by
  unfold Fmt.DeclaredRound.round at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨os, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- **Every declared round of the first chain has its entry among the written rounds.** -/
theorem written_mem {file : String} {D : Decl3}
    {R : OnBytes.Params.Rounds × OnBytes.Params.Rounds × OnBytes.Params.Rounds}
    (h : writtenOf file D = .ok R) : ∀ r ∈ D.1, ∃ y ∈ R.1, y.1.entry = r.entry := by
  intro r hr
  unfold writtenOf at h
  dsimp only at h
  obtain ⟨a, ha, h⟩ := VerifiableInference.Desc.First.Close.ok_bind h
  obtain ⟨b, -, h⟩ := VerifiableInference.Desc.First.Close.ok_bind h
  obtain ⟨c, -, h⟩ := VerifiableInference.Desc.First.Close.ok_bind h
  have hR : R = (a, b, c) := (Except.ok.inj h).symm
  subst hR
  obtain ⟨y, hy, e⟩ := mapM_mem _ _ _ ha r hr
  refine ⟨y, hy, ?_⟩
  cases hx : r.round [] with
  | none => rw [hx] at e; cases e
  | some x =>
    rw [hx] at e
    have : y = (x, r.stored) := (Except.ok.inj e).symm
    subst this
    exact round_entry hx

set_option maxRecDepth 1000000 in
/-- In the full size's first written list no round "BAT" and no round "FOLD round" has proof of
work: by the kernel. -/
theorem written_works : dryProofFull.1.all (fun y =>
    !(y.1.entry.name == "BAT" || y.1.entry.name == "FOLD round") || y.1.entry.work == 0) = true := by
  decide +kernel

/-- **A sub-protocol of a first chain whose declared rounds, written out, are the full size's written
list, and which declares K10's rounds at Q with at least one fold round: BOTH OF Q's NUMBERS OF PROOF
OF WORK ARE 0.** -/
theorem works_of_written {Xi : Type} {F : FileDescription Xi}
    (hw : writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull) {b : Block F.S₁ F.Cl}
    (hb : b ∈ F.first.blocksInOrder) {Q : Par} (hr : b.rounds = (kind (Cl := Unit) Q).rounds)
    (hk : 1 ≤ Q.k) : Q.workField = 0 ∧ Q.workClose = 0 := by
  have hin : ∀ r ∈ b.rounds, r ∈ F.roundsDeclaredByBlocks.1 := fun r h => List.mem_flatMap.2 ⟨b, hb, h⟩
  have key : ∀ e ∈ entries Q, (e.name = "BAT" ∨ e.name = "FOLD round") → e.work = 0 := by
    intro e he hn
    have h1 : ({ entry := e } : Fmt.DeclaredRound) ∈ b.rounds := by
      rw [hr]
      exact List.mem_map_of_mem he
    obtain ⟨y, hy, ey⟩ := written_mem hw _ (hin _ h1)
    have h2 := List.all_eq_true.1 written_works y hy
    rw [ey] at h2
    rcases hn with hn | hn <;> simpa [hn] using h2
  constructor
  · exact key { name := "BAT", work := Q.workField, drawE := 1, rows := Q.rows }
      List.mem_cons_self (Or.inl rfl)
  · refine key { name := "FOLD round", work := Q.workClose, msg := 48, drawE := 1 } ?_ (Or.inr rfl)
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    exact List.mem_replicate.2 ⟨by omega, rfl⟩

/-- Beneath the tests on the plan of the proof file's IOP stands K10's own: at least one fold
round. -/
theorem one_le_k {Z : ProofFile.Pub} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {c : Chain S Cl}
    (h2 : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c).planOk = true) {b : Block S Cl} (hb : b ∈ c.blocksInOrder) {Q : Par} {name : String} {a : Place}
    (e6 : LaidAlone ProofFile.sameReply b
      (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype name a) : 1 ≤ Q.k := by
  have hbo : b.planOk = true := by
    have h := h2
    unfold FileDescription.planOk FileDescription.planOkCore at h
    simp only [Bool.and_eq_true] at h
    have hb1 := h.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    have := List.all_eq_true.1 hb1 b hb
    simp only [Bool.and_eq_true] at this
    exact this.1
  rw [alone_planOk e6] at hbo
  have h' : (decide (1 ≤ Q.k) && decide (Q.h ≤ Q.k)) = true := (retype_planOk _ hbo).1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact h'.1

/-- **UNDER THE GATE's OWN YES, IN SCOPE: AT EVERY SUB-PROTOCOL OF THE KIND K10 OF THE FIRST CHAIN BOTH
NUMBERS OF PROOF OF WORK ARE 0, AND IT HAS AT LEAST ONE FOLD ROUND.** -/
theorem k10_works_live (P : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true) :
    ∃ (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull ∧
      ∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
        ∃ l < 25, ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par),
          k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
          c.blocksInOrder[ixK10 l]? = some b ∧ 1 ≤ Q.k ∧ Q.workField = 0 ∧ Q.workClose = 0 := by
  obtain ⟨F, Z, Bs, base, c, A, B, -, h2, -, h4, -, O, ⟨rfl, -⟩, -, -, -⟩ :=
    k10_sits_live P hS hR live
  have hpin : VerifiableInference.PlanWritten.seatPinnedProof P.pol
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) =
      true := h4 _ List.mem_cons_self
  have hw := (VerifiableInference.PlanWritten.seat_in_scope _ _ P hS hpin).1
  refine ⟨_, Z, Bs, base, c, A, B, O, hw, fun b hb hk => ?_⟩
  obtain ⟨l, hl, Lk, p, Q, -, e2, e3, -, e5, e6⟩ := k10_sits_each hS hR O b hb hk
  have hk1 : 1 ≤ Q.k := one_le_k h2 hb e6
  obtain ⟨w1, w2⟩ := works_of_written hw (b := b) hb (alone_rounds e6) hk1
  exact ⟨l, hl, p, Q, e2, e3, e5, hk1, w1, w2⟩

end LPFK10

#print axioms LPFK10.one_le_k
#print axioms LPFK10.works_of_written
#print axioms LPFK10.k10_works_live
#print axioms LPFK10.mapM_mem
#print axioms LPFK10.written_mem
#print axioms LPFK10.written_works
