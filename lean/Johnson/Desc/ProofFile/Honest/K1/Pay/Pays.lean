-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Pay/Pays.lean: (P1) FOR THE KIND K1 AT THE BASE PROVER, WHOLE.

  k1_pays     at the first, the shared and the second chain the kind K1 pays (KindPays,
              Honest/Law/ReadyOfSides.lean). The third conjunct is empty: no sub-protocol of the
              second chain is of the kind K1
  k1_whole    at each sub-protocol of the kind K1 the prover has a side: K1's arm of halved and of
              rooted. The third conjunct is empty
  k1_sidesWhere   K1's line of KindsWhole (SidesWhole.lean) at the first and the shared chain
  k1_counts   the description has 52, 2 and 0 sub-protocols of the kind K1

The shared chain's two sides are the hash build's sendings (nowSharedBy, proverSidesOfSharedSendings): here only their
counts are read.

Limits. Under the head and a return of the maker, at the filling onlineProverPartsInUse, at any reader of
the index. "It pays" says that chainSteps returns and nothing on whether a part plays or a verifier
accepts. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K1.Pay.Sides
import Johnson.Desc.ProofFile.Honest.K1.Pay.SidesWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1.Pay
open VerifiableInference.Desc
open VerifiableInference.Desc (Block FileDescription Place KindName Chain)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.K1 (qAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open ProofFile.Honest.FirstFill ProofFile.Honest.BookShared
open ProofFile.Honest.K14 (sendPlace sendingPart jobU jobOmega SendPub liftSend takesOf)
open AtPublicFiles.TreeReads (sized_at written_proof)
open VerifiableInference.PlanWritten (proofSizedFull)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## The counts of the shared chain's two sendings -/

/-- The count of "send o_u", off the codes and the shape. -/
def takesU (c : OnBytes.Codes) (S : OnBytes.Params.LinShape) : Due :=
  takesOf c ((Desc.K14.withU S).getD #[]) fun k =>
    if k == 0 then .plain S.fold.rowsHigh
    else match S.testU.head? with
      | some s => .fresh s.k s.h
      | none => .plain false

/-- The count of "send o_omega", off the codes and the shape. -/
def takesO (c : OnBytes.Codes) (S : OnBytes.Params.LinShape) : Due :=
  takesOf c (Desc.K14.withOmega S) fun _ => .plain S.omegaRowsHigh

theorem takes_u (A : SendPub) : (sendingPart (jobU A)).takes = takesU A.P.codes A.P.S := by
  show takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort = _
  rw [show (jobU A).Q.sent = (Desc.K14.withU A.P.S).getD #[] from Desc.K14.Law.parK1_sent A.P 2 _ _]
  rfl

theorem takes_o (A : SendPub) : (sendingPart (jobOmega A)).takes = takesO A.P.codes A.P.S := by
  show takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort = _
  rw [show (jobOmega A).Q.sent = Desc.K14.withOmega A.P.S from Desc.K14.Law.parK1_sent A.P 5 _ _]
  rfl

theorem takes_written :
    takesU proofSizedFull.codes proofSizedFull.batch.shape = ⟨0, 10975⟩ ∧
    takesO proofSizedFull.codes proofSizedFull.batch.shape = ⟨0, 43069⟩ := by
  decide +kernel

/-- Under the head the public part's codes and shape are the written ones. -/
theorem codes_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (qAt Zp Np).codes = proofSizedFull.codes ∧
      (qAt Zp Np).S = proofSizedFull.batch.shape := by
  have e : Zp.p.chains.made.sized.proof = proofSizedFull := by
    rw [sized_at h.scope h.laid, written_proof]
  exact ⟨congrArg (·.codes) e, congrArg (·.batch.shape) e⟩

/-- **The book's counts at the shared chain's two sendings**, at any return of the maker. -/
theorem shared_dues (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    dueAt (A.B.rowsOf 1) ⟨sendPlace 2, 0⟩ = ⟨0, 10975⟩ ∧
      dueAt (A.B.rowsOf 1) ⟨sendPlace 5, 0⟩ = ⟨0, 43069⟩ := by
  obtain ⟨r0, r1, r2, s0, s1, s2, tail, -, e1, -, -, -, -, -, -, ef, -, -⟩ :=
    bookRaw_rows (raw_of_whole (K14.atPure_book_at_head h hA))
  rw [K14.made_sends_at_files h.scope h.laid, ← rowsIn_alike (K14.planAlike_at_head h).shared,
    rowsIn_shared_written] at e1
  obtain rfl := (Except.ok.inj e1)
  show dueAt A.B.shared _ = _ ∧ dueAt A.B.shared _ = _
  rw [ef, List.append_assoc]
  exact ⟨dueAt_append_hit rfl, dueAt_append_hit rfl⟩

section
variable {W₀ : Type} (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- The test on G_u stands at its place. -/
theorem bareU_place {W X : Type} {Zq : ProofFile.Pub} {J : K12.TestJob W X}
    (h : K12.AtProof.bareU Zq = some J) : J.p.place = K12.AtProof.placeU := by
  unfold K12.AtProof.bareU at h
  obtain ⟨F, hF, h⟩ := opt_bind h
  obtain ⟨A', -, rfl⟩ := opt_map h
  unfold K12.AtProof.four at hF
  split at hF
  · obtain rfl := Option.some.inj hF
    exact K12.AtProof.p12At_place _ _
  · cases hF

/-- The test on G_omega stands at its place. -/
theorem bareO_place {W X : Type} {Zq : ProofFile.Pub} {J : K12.TestJob W X}
    (h : K12.AtProof.bareO Zq = some J) : J.p.place = K12.AtProof.placeO := by
  unfold K12.AtProof.bareO at h
  obtain ⟨F, hF, h⟩ := opt_bind h
  obtain ⟨p, hp, h⟩ := opt_bind h
  obtain ⟨A', -, rfl⟩ := opt_map h
  unfold K12.AtProof.four at hF
  split at hF
  · obtain rfl := Option.some.inj hF
    obtain ⟨x, -, rfl⟩ := opt_map hp
    exact K12.AtProof.p12At_place _ _
  · cases hF

/-- **The shared chain's list of sides**: the six, then the pairs of the two tests. -/
theorem shared_list (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    A.H.shared = (K14.proverSidesOfSharedRounds { S := (qAt Zp Np).S, atPoint := 0, atZeta := 6 } (I.weights Zp) ++
      K14.proverSidesOfSharedSendings { P := qAt Zp Np, atPoint := 0 } (I.weights Zp)
        (K14.randNow (qAt Zp Np))) ++
      K12.AtProof.halfU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp ++
      K12.AtProof.halfO (I.weights Zp) Zp := by
  obtain ⟨-, -, -, -, -, -, -, -, eS, -⟩ := atPure_ok hA
  obtain ⟨eZ, -⟩ := atPure_at_laid h.laid hA
  rw [eS, eZ]
  show K12.AtProof.sharedWithUO I Zp = _
  rw [K12.AtProof.sharedWithUO_ok I (K14.nowSharedBy_at_head h _),
    sharedWithU_ok I (K14.nowSharedBy_at_head h _)]

/-- **Every side of the kind K1 in the shared chain has the form, and the book's count.** -/
theorem shared_form (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∀ g ∈ A.H.shared, g.place.kind = .K1 →
      ∃ p, OnePart g p ∧ p.takes = dueAt (A.B.rowsOf 1) ⟨g.place, 0⟩ := by
  obtain ⟨d2, d5⟩ := shared_dues h hA
  obtain ⟨ec, eS⟩ := codes_head h
  intro g hg hk
  rw [shared_list I S O h hA, K14.sendHalves_eq] at hg
  rcases List.mem_append.1 hg with hg | hg
  · rcases List.mem_append.1 hg with hg | hg
    · rcases List.mem_append.1 hg with hg | hg
      · unfold K14.proverSidesOfSharedRounds at hg
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with (rfl | rfl | rfl) | hg
        · cases hk
        · cases hk
        · cases hk
        · split at hg
          · rcases List.mem_singleton.1 hg with rfl
            cases hk
          · cases hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · refine ⟨_, ⟨rfl, by simp [liftSend, Part.lift, sendingPart], rfl, rfl⟩, ?_⟩
          show (sendingPart (jobU _)).takes = _
          rw [d2, takes_u]
          show takesU (qAt Zp Np).codes (qAt Zp Np).S = _
          rw [ec, eS]
          exact takes_written.1
        · refine ⟨_, ⟨rfl, by simp [liftSend, Part.lift, sendingPart], rfl, rfl⟩, ?_⟩
          show (sendingPart (jobOmega _)).takes = _
          rw [d5, takes_o]
          show takesO (qAt Zp Np).codes (qAt Zp Np).S = _
          rw [ec, eS]
          exact takes_written.2
    · unfold K12.AtProof.halfU at hg
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hg
      obtain ⟨J₀, hb, ep, -⟩ := K12.AtProof.realU_bare _ _ _ J (Option.mem_toList.1 hJ)
      have e : (K12.proverSideOfProximityTest J : Placed Empty _ Unit).place = K12.AtProof.placeU := by
        show J.p.place = _
        rw [ep]
        exact bareU_place hb
      rw [e] at hk
      cases hk
  · unfold K12.AtProof.halfO at hg
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hg
    obtain ⟨J₀, hb, ep, -⟩ := K12.AtProof.realO_bare _ _ J (Option.mem_toList.1 hJ)
    have e : ((K12.proverSideOfProximityTest J : Placed Empty _ Unit).needsField).place =
        K12.AtProof.placeO := by
      show J.p.place = _
      rw [ep]
      exact bareO_place hb
    rw [e] at hk
    cases hk

/-- A place of a side stands in the chain, where the maker's test on strays has accepted. -/
theorem of_strays {S' Cl V W Y : Type} {bs : List (Block S' Cl)} {hs : List (Placed V W Y)}
    (h : (strays bs hs).isEmpty = true) {g : Placed V W Y} (hg : g ∈ hs) :
    ∃ b ∈ bs, b.place = g.place := by
  have e := List.isEmpty_iff.1 h
  unfold strays at e
  have e' := List.map_eq_nil_iff.1 e
  have hn : ¬ ((!(bs.any fun b => b.place == g.place)) = true) :=
    List.filter_eq_nil_iff.1 e' g hg
  cases hx : bs.any (fun b => b.place == g.place) with
  | true =>
    obtain ⟨b, hb, e2⟩ := List.any_eq_true.1 hx
    exact ⟨b, hb, beq_iff_eq.1 e2⟩
  | false =>
    rw [hx] at hn
    exact absurd rfl hn

/-- **(P1) FOR THE KIND K1 AT THE BASE PROVER.** The third conjunct is empty. -/
theorem k1_pays (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first .K1 ∧
      KindPays A.B 1 A.F.shared.blocksInOrder A.H.shared .K1 ∧
      KindPays A.B 2 A.F.second.blocksInOrder A.H.second .K1 := by
  obtain ⟨hpl, C, p0, p1, p2, M, hB⟩ := head_pack h hA
  have hp := Johnson.RunOne.Sound.placesOk_of_planOk _ hpl
  refine ⟨k1_pays_first I S O h hA, ?_, ?_⟩
  · intro g hg hk
    obtain ⟨p, ho, hd⟩ := shared_form I S O h hA g hg hk
    refine sidePays_one (atPure_tests hA).1 hp (.inr (.inl rfl)) _ g p ho fun b hb e => ?_
    exact bookAt_shared hB hpl C hb (by rw [e]; exact hk) (by rw [e]; exact hd)
  · intro g hg hk
    obtain ⟨b, hb, e⟩ := of_strays (atPure_tests hA).2.2.2.1 hg
    have := place_of_test C.p3 (mem_planOf hb) (by show b.place.kind = _; rw [e]; exact hk)
    cases this

/-- **The sides that the prover has at K1's own lot.** -/
theorem side_of_lot_job (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    {J : SendJob (PlaceIn ProofFile.Inst) Unit}
    (hJ : J ∈ lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z A.G) :
    (A.H.first.any fun g => g.place == J.P.place) = true := by
  obtain ⟨-, -, -, -, -, -, -, eH, -⟩ := atPure_ok hA
  refine List.any_eq_true.2 ⟨placeHalf (witOf I A.Z) J, ?_, by simp [placeHalf]⟩
  rw [eH]
  refine List.mem_flatMap.2
    ⟨HLot.byPub I.weights (LongLots.plain OnBytes.secondHashFunction S O).k1, ?_, ?_⟩
  · rw [widerFillAtCPUOWM_lots]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
    rw [widerFillAt_lots]
    exact List.mem_map.2 ⟨_, List.Mem.head _, rfl⟩
  · show placeHalf (witOf I A.Z) J ∈ lotHalves (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (X := Unit)
      (witOf I A.Z) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z A.G
    rw [lotHalves_jobs]
    exact List.mem_map_of_mem hJ

/-- **K1's ARM OF halved AND OF rooted.** The third conjunct is empty. -/
theorem k1_whole (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    (∀ b ∈ A.F.first.blocksInOrder, b.place.kind = .K1 →
      (A.H.first.any fun g => g.place == b.place) = true) ∧
    (∀ b ∈ A.F.shared.blocksInOrder, b.place.kind = .K1 →
      (A.H.shared.any fun g => g.place == b.place) = true) ∧
    (∀ b ∈ A.F.second.blocksInOrder, b.place.kind = .K1 →
      (A.H.second.any fun g => g.place == b.place) = true) := by
  obtain ⟨hpl, C, -⟩ := head_pack h hA
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  obtain ⟨-, -, -, -, -, -, -, eH, -⟩ := atPure_ok hA
  refine ⟨fun b hb hk => ?_, fun b hb hk => ?_, fun b hb hk => ?_⟩
  · have hm := place_of_test C.p1 (mem_planOf hb) hk
    have hm' : b.place ∈ k1PlacesW := hm
    have jobs := lotJobs_at_head h O' (lotNo OnBytes.secondHashFunction A.Z) (lotData S) (X := Unit)
    rw [← eZ, ← eG] at jobs
    have fifty : ∀ l, l < 25 → ∀ d,
        (A.H.first.any fun g => g.place == IM.k1PlaceL l d) = true := by
      intro l hl d
      have hm₂ : laterJobAt (X := Unit) A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1)
          (if d then 2 else 1) (lotNo OnBytes.secondHashFunction A.Z ⟨1, some l, IM.k1Ix l d + 1, .K1⟩)
          (lotData S A.Z A.G) ∈
          lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z A.G := by
        rw [jobs]
        exact List.mem_map.2 ⟨_, mem_k1Members.2 (.inr ⟨l, hl, d, rfl⟩), rfl⟩
      have := side_of_lot_job I S O hA hm₂
      cases d <;> exact this
    simp only [k1PlacesW, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
      List.not_mem_nil, or_false] at hm'
    rcases hm' with (e | ⟨l, hl, e | e⟩) | e
    · rw [e]
      have hm₂ : placeJob (X := Unit) (K1.firstPar A.G.first (K1.gpOf A.Z))
          (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩) (firstFold A.G.first)
          (lotData S A.Z A.G) ∈
          lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z A.G := by
        rw [jobs]
        exact List.mem_map.2 ⟨_, List.Mem.head _, rfl⟩
      exact side_of_lot_job I S O hA hm₂
    · rw [e]
      exact fifty l hl false
    · rw [e]
      exact fifty l hl true
    · rw [e]
      have hm₂ : OnBytes.linMessageW A.Z.first.lin = some wMsgFull := by
        rw [eZ]
        exact msg_w_head h O'
      refine List.any_eq_true.2 ⟨placeHalf (witOf I A.Z) (wJobAt (X := Unit) A.Z.first (wGp A.Z) 4
        wMsgFull (lotNo OnBytes.secondHashFunction A.Z ⟨1, none, 4, .K1⟩) (K13.wDataAt O.pile A.Z A.G)), ?_,
        by simp [placeHalf, wJobAt, placeJob, K1.parW]⟩
      rw [eH]
      refine List.mem_flatMap.2 ⟨wLotAt I OnBytes.secondHashFunction O, ?_, ?_⟩
      · rw [widerFillAtCPUOWM_lots]
        exact List.mem_append_right _ (.head _)
      · rw [wLotAt_halves, hm₂]
        exact List.Mem.head _
  · have hm := place_of_test C.p2 (mem_planOf hb) hk
    have hm' : b.place ∈ k1PlacesS := hm
    rw [shared_list I S O h hA, K14.sendHalves_eq]
    simp only [k1PlacesS, List.mem_cons, List.not_mem_nil, or_false] at hm'
    rcases hm' with e | e <;> · rw [e]; simp [List.any_append, K14.sendPlace]
  · have := place_of_test C.p3 (mem_planOf hb) hk
    cases this

/-- **K1's line of KindsWhole.** -/
theorem k1_sidesWhere (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K1 ∧ SidesWhere A.F.shared.blocksInOrder A.H.shared .K1 :=
  ⟨fun b hb hk _ => (k1_whole I S O h hA).1 b hb hk,
    fun b hb hk _ => (k1_whole I S O h hA).2.1 b hb hk⟩

end

/-- **THE COUNTS.** At any return of the maker. -/
theorem k1_counts (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    (A.F.first.blocksInOrder.filter (·.place.kind == .K1)).length = 52 ∧
      (A.F.shared.blocksInOrder.filter (·.place.kind == .K1)).length = 2 ∧
      (A.F.second.blocksInOrder.filter (·.place.kind == .K1)).length = 0 := by
  obtain ⟨-, C, -⟩ := head_pack h hA
  rw [k1Count_planOf, k1Count_planOf, k1Count_planOf]
  exact ⟨C.c1, C.c2, C.c3⟩

end ProofFile.Honest.K1.Pay

#print axioms ProofFile.Honest.K1.Pay.k1_pays
#print axioms ProofFile.Honest.K1.Pay.k1_whole
#print axioms ProofFile.Honest.K1.Pay.k1_sidesWhere
#print axioms ProofFile.Honest.K1.Pay.k1_counts
