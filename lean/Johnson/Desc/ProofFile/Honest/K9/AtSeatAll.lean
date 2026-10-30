-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/AtSeatAll.lean: K9's LAWS AND COUNT FOR ITS "free-slot" TEST AT THE BATCHING BLOCK THAT
THE PROOF FILE's DESCRIPTION SEATS AT EACH OF ITS 25 SEGMENTS. Lemmas ON THE VERIFIER's TEXT; no prover is in this file,
and no goal is stated. Assemblies, after part 1's `fall_at_seat`, `fall_at_seat_att` and `fall_at_seat_head`
(Johnson/P1K8R/), whose road through the sealed library they follow.

  `SeatedFree c Z l k Lk p w`   what is said of segment l, as one structure: Lk is the chain's segment l, with k
      hearing blocks; p the batching's numbers; w K9's numbers off the public parameters; the block at number 14 l + k
      + 2 of the chain's flat list is Lk's batching at the frame's own gatherer over Lk's own hearing blocks; the
      block at the next number is the frame's block behind the batching, AND ITS PLACE IS `quietPlace p`
      (Honest/K9/Quiet.lean): the place at which K9's fall is laid (`quietFall`, Honest/K9/Falls.lean);
      `laws`: `RunsLaw` AT EVERY STATE: A LAW ON THE YESES OF DRAW AND GATHERER: where they never return it holds idly;
      `few`: THE COUNT at every state that is good (`goodS`, WHICH HOLDS A YES OF DRAW AND GATHERER): at most
      n * (THE STATE's ledger's plan's number of claims - 1) readings of a chi at which THAT SEATED BLOCK's decision
      says yes and K9's "free-slot" AT n SLOTS speaks behind;
      `refuses`: A FALL, SO A REFUSAL: where K9's share at the public parameters' number of filled slots speaks at a
      state, the block behind the batching refuses there;
      `tests`: THE SEGMENT's TESTS BEHIND THE ADDING, BOTH WAYS: they say yes just where the state stands in a
      segment, K9's Bool at that number is true and the sort's counts hold. (The block behind the batching then runs
      the other kinds' runs: of these nothing is said.)
      `alone`, `seat`, `order`, `each`, `keeps`: FOR THE YES (Honest/K9/YesAll.lean): the seated block is K9's batching
      laid alone at a place that is not K7's · that place is the one at which K9's half stands (`batHalf p`) · the
      order is the driver's for the segment's sort · the test behind a run is K9's at that sort · WHEREVER THE
      GATHERER RETURNS from a state at which K9's lens answers, the lens answers behind it and the ledger's core is
      kept (`LedgerCore`): by part 1's `core_layers`, `core_att`, `core_head` (Johnson/Desc/K8/Honest/CoreGathers.lean)
  `plainTies_layers`   part 1's premises (`PlainTies`, Honest/K9/PlainFree.lean) out of the ties at a feed-forward
      segment; at attention and the head they are laid inside the proofs, out of part 1's `att_pre`, `head_pre`,
      `head_post`
  `seated_of_ties`   `SeatedFree` out of `PlainTies` and what the sealed library says of a seated segment
  **`free_at_seat_layers`**, **`free_at_seat_att`**, **`free_at_seat_head`**, **`free_at_seat_all`**   WHEREVER THE
      DESCRIPTION CAN BE OPENED IN THE GOALS' SCOPE (the premises hS, hR, O: that they can be met together is shown by
      no theorem known to this pen): `SeatedFree` at each feed-forward and attention segment (seven hearing blocks),
      at the head's (segment 24; nine), and so at each l < 25
  `SeatedFree.shape`   the seated block's one round, its one empty list of oracle messages, and its place, read off
      `alone` and `seat`
WHAT IS NOT CLAIMED. THAT DRAW AND GATHERER RETURN AT ANY STATE AND CHALLENGE. THAT A STATE IS GOOD: `goodS` is a
premise, and here no Bool on written lists stands for it (at a feed-forward segment: Honest/K9/AtSeat.lean). THAT THE
STATE's PLAN's NUMBER IS THE PUBLIC PARAMETERS' (w.2.1), or that n is w.2.2.filled: n is free in `few`. What a state
that the chain's own blocks reach holds. The count is at the block's decision at no column and at the round as
`drawnOne` gives it (the step: Honest/K9/AtStep.lean). Readings, not words; no probability. The full size, the
format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.PlainFree
import Johnson.P1K8R.FallAtSeatAtt
import Johnson.P1K8R.FallAtSeatHead
import Johnson.Desc.K8.Honest.CoreGathers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest (attPre att_pre post_nil headPre headPost head_pre head_post
  plain_objectsCalls plain_objectsDigits plain_idle plain_front behind_back)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)

/-- What is said of a seated segment. k: the number of its hearing blocks. -/
structure SeatedFree (c : Chain S Claim) (Z : ProofFile.Pub) (l k : ℕ) (Lk : Link S Claim) (p : Desc.K9.Where)
    (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) : Prop where
  link : c.links[l]? = some Lk
  hears : Lk.hear.length = k
  numbers : IM.k9At Z l = some p
  tested : Desc.K9.testsWhere Z.p.X l 0 = some w
  batching : c.blocksInOrder[14 * l + k + 2]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order))
  behind : ∃ b, c.blocksInOrder[14 * l + k + 3]? = some b ∧ b.place = quietPlace p ∧
    ∀ s rs gs, b.decide s rs gs = Lk.runBehind s
  laws : ∀ s : S, RunsLaw p (claimsInBy Lk.each Lk.hear Lk.order) s
  few : ∀ (s : S) (a0 : Desc.K9.Part) (n : ℕ), Desc.K9.atS.get? s = some a0 →
    goodS p (claimsInBy Lk.each Lk.hear Lk.order) s n →
    Prob.cnt (fun z : Cb.Gl.E => ∃ x : E, Reading.gl.val x = z ∧
      FallsAt (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s n none x) ≤ n * (a0.F.planClaimsF - 1)
  refuses : ∀ s₁ : S, (freeSlotShare w.2.2.filled s₁).isSome = true → ∀ t, Lk.runBehind s₁ ≠ .ok t
  tests : ∀ s₁ : S, Lk.tests s₁ = .ok () ↔ (Desc.K9.tAtS.get? s₁).isSome = true ∧
    slotsFree w.2.2.filled s₁ = true ∧ Desc.K9.countsHold (Desc.K9.countsAt w.1 w.2.1) s₁ = .ok ()
  alone : ∃ a : Place, a.kind ≠ KindName.K7 ∧
    IM.LaidAlone ProofFile.sameReply (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order))
      (Desc.K9.batch Desc.K9.atS p (claimsInBy Lk.each Lk.hear Lk.order))
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).name a
  seat : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place = ⟨p.chain, some p.link, p.piece, .K9⟩
  order : Lk.order = VerifiableInference.Desc.First.orderOf (IM.subAt l)
  each : Lk.each = Desc.K9.eachAtS (IM.sortAt l)
  keeps : ∀ (t e : S) (cls : List Claim) (x : Desc.K9.Part),
    claimsInBy Lk.each Lk.hear Lk.order t = .ok (cls, e) → Desc.K9.atS.get? t = some x →
    ∃ y, Desc.K9.atS.get? e = some y ∧ LedgerCore x y

/-- A fall, so a refusal: at a segment whose tests behind the adding are `k9Tests`. -/
theorem refuses_of_tests (Z : ProofFile.Pub) (l : ℕ) (Lk : Link S Claim) (T : S → Except String Unit)
    (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (hw : Desc.K9.testsWhere Z.p.X l 0 = some w)
    (hT : ProofFile.k9Tests Z l = some T) (hLT : Lk.tests = T) (s₁ : S)
    (hq : (freeSlotShare w.2.2.filled s₁).isSome = true) (t : S) : Lk.runBehind s₁ ≠ .ok t := by
  intro ht
  unfold Link.runBehind at ht
  rw [hLT] at ht
  cases hts : T s₁ with
  | error m => rw [hts] at ht; exact nomatch ht
  | ok u =>
    obtain ⟨w', hw', _, hfree, _⟩ := (tests_iff Z l T hT s₁).1 hts
    obtain rfl : w = w' := Option.some.inj (hw.symm.trans hw')
    unfold freeSlotShare at hq
    rw [hfree] at hq
    exact nomatch hq

/-- The segment's tests behind the adding, both ways: at a segment whose tests are `k9Tests`. -/
theorem tests_of_tests (Z : ProofFile.Pub) (l : ℕ) (Lk : Link S Claim) (T : S → Except String Unit)
    (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (hw : Desc.K9.testsWhere Z.p.X l 0 = some w)
    (hT : ProofFile.k9Tests Z l = some T) (hLT : Lk.tests = T) (s₁ : S) :
    Lk.tests s₁ = .ok () ↔ (Desc.K9.tAtS.get? s₁).isSome = true ∧
      slotsFree w.2.2.filled s₁ = true ∧ Desc.K9.countsHold (Desc.K9.countsAt w.1 w.2.1) s₁ = .ok () := by
  rw [hLT, tests_iff Z l T hT s₁]
  constructor
  · rintro ⟨w', hw', h1, h2, h3⟩
    obtain rfl : w = w' := Option.some.inj (hw.symm.trans hw')
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨w, hw, h1, h2, h3⟩

/-- Part 1's premises at a feed-forward segment, out of the ties. After the proof of part 1's `gathers_layers_plain`
(Johnson/Desc/K8/Honest/FallAtt.lean). -/
theorem plainTies_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array ℕ)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits)
    (hord : L.order = VerifiableInference.Desc.First.orderOf .layers) :
    PlainTies L 4 [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")] [(2, "back")] := by
  refine ⟨by rw [hord]; rfl, ?_, ?_, ties.tEq⟩
  · intro o ho run hat
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, tC run hat, plain_objectsCalls⟩
    · exact ⟨_, ties.tGuests 1 (by simp) run hat, plain_idle⟩
    · obtain ⟨r, l, u⟩ := ties.tFront run hat
      exact ⟨r, u, plain_front p4 r l⟩
    · exact ⟨_, tD run hat, plain_objectsDigits⟩
    · exact ⟨_, ties.tGuests 6 (by simp) run hat, plain_idle⟩
  · intro o ho run hat
    obtain rfl : o = (2, "back") := List.mem_singleton.1 ho
    obtain ⟨r, l, u⟩ := ties.tBack run hat
    exact ⟨r, u, behind_back p4 r l⟩

/-- Part 1's `SameCore` (Johnson/Desc/K8/Honest/SameCore.lean) gives K9's `LedgerCore`. -/
theorem ledgerCore_of_sameCore (x y : Desc.K9.Part)
    (h : VerifiableInference.Desc.First.K8.Honest.SameCore x.F y.F) : LedgerCore x y :=
  ⟨h.sums.theta, h.sums.LS, h.sums.ns, h.sums.plan, h.sums.nClaim, h.door, h.drawn, h.kapMap, by rw [h.sums.trees]⟩

/-- `SeatedFree` out of `PlainTies` and what the sealed library says of a seated segment. -/
theorem seated_of_ties {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} {T : S → Except String Unit} {i : ℕ}
    {pre post : List (ℕ × String)} {a : Place} (PT : PlainTies Lk i pre post) (e1 : c.links[l]? = some Lk)
    (hk7 : Lk.hear.length = k)
    (e2 : IM.k9At Z l = some p) (hw : Desc.K9.testsWhere Z.p.X l 0 = some w)
    (hflat : c.blocksInOrder[14 * l + k + 2]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (f10 : c.blocksInOrder[14 * l + k + 3]? = some Lk.behindB) (hplace : Lk.behindB.place = quietPlace p)
    (hb : IM.LaidAlone ProofFile.sameReply (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order))
      (Desc.K9.batch Desc.K9.atS p (claimsInBy Lk.each Lk.hear Lk.order))
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).name a) (hk : a.kind ≠ KindName.K7)
    (hT : ProofFile.k9Tests Z l = some T) (hLT : Lk.tests = T)
    (hseat : a = ⟨p.chain, some p.link, p.piece, .K9⟩)
    (hord : Lk.order = VerifiableInference.Desc.First.orderOf (IM.subAt l))
    (heach : Lk.each = Desc.K9.eachAtS (IM.sortAt l))
    (hcore : ∀ (t e : S) (cls : List Claim) (x : Desc.K9.Part),
      claimsInBy Lk.each Lk.hear Lk.order t = .ok (cls, e) → Desc.K9.atS.get? t = some x →
      ∃ y, Desc.K9.atS.get? e = some y ∧ VerifiableInference.Desc.First.K8.Honest.SameCore x.F y.F) :
    SeatedFree c Z l k Lk p w := by
  refine ⟨e1, hk7, e2, hw, hflat, ⟨Lk.behindB, f10, hplace, fun _ _ _ => rfl⟩,
    fun s => runsLaw_plain Lk i pre post PT p s, ?_, refuses_of_tests Z _ Lk T w hw hT hLT,
    tests_of_tests Z _ Lk T w hw hT hLT, ⟨a, hk, hb⟩, (IM.alone_place hb).trans hseat, hord, heach,
    fun t e cls x hg hx => by
      obtain ⟨y, hy, hc⟩ := hcore t e cls x hg hx
      exact ⟨y, hy, ledgerCore_of_sameCore x y hc⟩⟩
  intro s a0 n ha0 hgood
  refine free_few_plain Lk i pre post PT p s a0 ha0 n hgood none (Or.inl rfl) _ ?_
  intro rs t hyes
  exact ((IM.yes_alone hb hk s t rs []).1 hyes).1

/-- **At a feed-forward segment.** (With "good" as a written Bool, and K4's test: Honest/K9/AtSeat.lean.) -/
theorem free_at_seat_layers {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) : ∃ Lk p w, SeatedFree c Z l 7 Lk p w := by
  obtain ⟨Lk, p, w, T, e1, e2, hpc, hpch, hpl, -, hb, hflat, -, hLc, hLn, hord, -, hlen, hw, hw1, heach, hT, hLT⟩ :=
    (IM.k9_of hS hR O).2 l hl
  obtain ⟨Lk₂, p₂, Q, -, -, hsit⟩ := LPFK9.k09_sits hS hR O l hl
  obtain rfl : Lk = Lk₂ := Option.some.inj (e1.symm.trans hsit.link)
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hw1] at heach
  have hplace : Lk.behindB.place = quietPlace p := by
    show (⟨Lk.chain, some Lk.number, Lk.hear.length + 2, .frame⟩ : Place) = ⟨p.chain, some p.link, p.piece + 1, .frame⟩
    rw [hLc, hLn, hpch, hpl, hpc, hlen]
  have hseat : IM.a9Of l (IM.subAt l) = ⟨p.chain, some p.link, p.piece, .K9⟩ := by
    show (⟨1, some l, _, .K9⟩ : Place) = _
    rw [hpch, hpl, hpc]
  have hord0 := hord
  rw [hsub] at hs25 hord hlen
  have h7 : Lk.hear.length = 7 := by
    rw [hlen]
    cases (l == 0) <;> rfl
  obtain ⟨Lk', p4, X, e1', -, -, ties⟩ := LPFK9.layers_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  have h24 : l ≠ 24 := by
    intro e
    rw [e] at hsub
    exact absurd hsub (by decide)
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', P1K8.objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', P1K8.objectsRun_at.2]
    exact LinkJoin.under_refl _
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  rw [h7] at hflat
  have f10 := hsit.flat₂
  rw [h7] at f10
  exact ⟨Lk, p, w, seated_of_ties (plainTies_layers Lk p4 _ ties tC tD hord) e1 h7 e2 hw hflat f10 hplace
    (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne hT hLT hseat hord0 heach fun t e cls x hg hx =>
      VerifiableInference.Desc.First.K8.Honest.core_layers Lk p4 _ ties tC tD hord t e cls hg x hx⟩

/-- **At an attention segment.** -/
theorem free_at_seat_att {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .attention) : ∃ Lk p w, SeatedFree c Z l 7 Lk p w := by
  obtain ⟨Lk, p, w, T, e1, e2, hpc, hpch, hpl, -, hb, hflat, -, hLc, hLn, hord, -, hlen, hw, hw1, heach, hT, hLT⟩ :=
    (IM.k9_of hS hR O).2 l hl
  obtain ⟨Lk₂, p₂, Q, -, -, hsit⟩ := LPFK9.k09_sits hS hR O l hl
  obtain rfl : Lk = Lk₂ := Option.some.inj (e1.symm.trans hsit.link)
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hw1] at heach
  have hplace : Lk.behindB.place = quietPlace p := by
    show (⟨Lk.chain, some Lk.number, Lk.hear.length + 2, .frame⟩ : Place) = ⟨p.chain, some p.link, p.piece + 1, .frame⟩
    rw [hLc, hLn, hpch, hpl, hpc, hlen]
  have hseat : IM.a9Of l (IM.subAt l) = ⟨p.chain, some p.link, p.piece, .K9⟩ := by
    show (⟨1, some l, _, .K9⟩ : Place) = _
    rw [hpch, hpl, hpc]
  have hord0 := hord
  rw [hsub] at hs25 hord hlen
  have h7 : Lk.hear.length = 7 := by
    rw [hlen]
    cases (l == 0) <;> rfl
  obtain ⟨Lk', Xl, Ap, X, e1', hXl, -, hA, hX, ties⟩ :=
    LPFK9.att_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, g, hg, rfl⟩ := Att.P.att_only O.pub O.blank hs25
  obtain ⟨Xl', hXl', -, hgX, -⟩ := Att.P.built_att O.pub O.blank h4 hg
  obtain rfl : Xl' = Xl := Option.some.inj (hXl'.symm.trans hXl)
  rw [hgX] at hA
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', P1K8.objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', P1K8.objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tJ : ∀ run, LinkJoin.At Lk (2, "join") run →
      LinkJoin.Under run
        (Desc.K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    rw [LinkJoin.at_join_is O h4 hg hA e1 hrun]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (1, "planes") run →
      ∃ lm, LinkJoin.Under run
        (Desc.K9.planesCalls lm
          (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "planes") run := by
      simpa [IM.k3Ix, h24] using hrun
    obtain ⟨q, -, rfl⟩ :=
      OnPublicFiles.at_planes_is hS hR O hl e1 (H2K5.Door.readersAt_att h4 hA) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  have PT : PlainTies Lk 4 attPre [] :=
    ⟨by rw [hord]; rfl, att_pre Lk (Att.P.parCOf Ap) (ProofFile.k8NU Bs.G₀ X) ties tC tD tJ tP, post_nil Lk,
      ties.tEq⟩
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  rw [h7] at hflat
  have f10 := hsit.flat₂
  rw [h7] at f10
  exact ⟨Lk, p, w, seated_of_ties PT e1 h7 e2 hw hflat f10 hplace (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne
    hT hLT hseat hord0 heach fun t e cls x hg hx =>
      VerifiableInference.Desc.First.K8.Honest.core_att Lk (Att.P.parCOf Ap) (ProofFile.k8NU Bs.G₀ X) ties tC tD tJ tP hord
        t e cls hg x hx⟩

/-- **At the head's segment.** -/
theorem free_at_seat_head {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ Lk p w, SeatedFree c Z 24 9 Lk p w := by
  have hl : 24 < 25 := by omega
  have hsub : IM.subAt 24 = .head := rfl
  obtain ⟨Lk, p, w, T, e1, e2, hpc, hpch, hpl, -, hb, hflat, -, hLc, hLn, hord, -, hlen, hw, hw1, heach, hT, hLT⟩ :=
    (IM.k9_of hS hR O).2 24 hl
  obtain ⟨Lk₂, p₂, Q, -, -, hsit⟩ := LPFK9.k09_sits hS hR O 24 hl
  obtain rfl : Lk = Lk₂ := Option.some.inj (e1.symm.trans hsit.link)
  have hs25 := IM.subs_scope hS hR O 24 hl
  rw [hw1] at heach
  have hplace : Lk.behindB.place = quietPlace p := by
    show (⟨Lk.chain, some Lk.number, Lk.hear.length + 2, .frame⟩ : Place) = ⟨p.chain, some p.link, p.piece + 1, .frame⟩
    rw [hLc, hLn, hpch, hpl, hpc, hlen]
  have hseat : IM.a9Of 24 (IM.subAt 24) = ⟨p.chain, some p.link, p.piece, .K9⟩ := by
    show (⟨1, some 24, _, .K9⟩ : Place) = _
    rw [hpch, hpl, hpc]
  have hord0 := hord
  rw [hsub] at hs25 hord hlen
  have h9 : Lk.hear.length = 9 := by
    rw [hlen]
    rfl
  have hU3 := P1K8.head_u3 O.public
  obtain ⟨Lk', X, e1', hX, ties⟩ := LPFK9.head_ties_at O.made O.places O.chain 24 hs25 0 hU3
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, hN⟩ := head_24 hS O.public
  have hH : K3.isHead Bs.G₀.W 24 = true := by
    unfold K3.isHead
    rw [h4, hN]
    rfl
  have tC : ∀ run, LinkJoin.At Lk (2, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', P1K8.objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (7, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 true, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', P1K8.objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (2, "planes") run →
      ∃ lm, LinkJoin.Under run (Desc.K9.planesCalls lm (callerReaders (planesAt 0))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "planes") run := hrun
    obtain ⟨q, -, rfl⟩ := OnPublicFiles.at_planes_is hS hR O hl e1 (OnPublicFiles.readersAt_head hH hU3) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  have PT : PlainTies Lk 5 headPre headPost :=
    ⟨by rw [hord]; rfl, head_pre Lk _ 0 _ 4 _ (ProofFile.k8NU Bs.G₀ X) ties tC tD tP,
      head_post Lk _ 0 _ 4 _ (ProofFile.k8NU Bs.G₀ X) ties, ties.tEq⟩
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  rw [h9] at hflat
  have f10 := hsit.flat₂
  rw [h9] at f10
  exact ⟨Lk, p, w, seated_of_ties PT e1 h9 e2 hw hflat f10 hplace (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne
    hT hLT hseat hord0 heach fun t e cls x hg hx =>
      VerifiableInference.Desc.First.K8.Honest.core_head Lk _ 0 _ 4 _ (ProofFile.k8NU Bs.G₀ X) ties tC tD tP hord
        t e cls hg x hx⟩

/-- **AT EACH OF THE 25 SEGMENTS.** -/
theorem free_at_seat_all {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) :
    ∃ Lk p w, SeatedFree c Z l (if l = 24 then 9 else 7) Lk p w := by
  have not24 : ∀ m, m < 25 → IM.subAt m ≠ .head → m ≠ 24 := by decide
  cases hsub : IM.subAt l with
  | layers =>
    rw [if_neg (not24 l hl (by rw [hsub]; exact fun h => nomatch h))]
    exact free_at_seat_layers hS hR O l hl hsub
  | attention =>
    rw [if_neg (not24 l hl (by rw [hsub]; exact fun h => nomatch h))]
    exact free_at_seat_att hS hR O l hl hsub
  | head =>
    have e : l = 24 := by
      by_contra hne
      have : ∀ m, m < 25 → m ≠ 24 → IM.subAt m ≠ .head := by decide
      exact this l hl hne hsub
    subst e
    exact free_at_seat_head hS hR O

/-- The seated block's rounds, oracle messages and place. -/
theorem SeatedFree.shape {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree c Z l k Lk p w) :
    (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).rounds = [{ entry := Desc.K9.entry p }] ∧
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).oracles = [[]] ∧
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place = ⟨p.chain, some p.link, p.piece, .K9⟩ := by
  obtain ⟨a, _, hb⟩ := Sd.alone
  exact ⟨IM.alone_rounds hb, IM.alone_oracles hb, Sd.seat⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.SeatedFree.shape
#print axioms ProofFile.Honest.K9.refuses_of_tests
#print axioms ProofFile.Honest.K9.tests_of_tests
#print axioms ProofFile.Honest.K9.plainTies_layers
#print axioms ProofFile.Honest.K9.ledgerCore_of_sameCore
#print axioms ProofFile.Honest.K9.seated_of_ties
#print axioms ProofFile.Honest.K9.free_at_seat_layers
#print axioms ProofFile.Honest.K9.free_at_seat_all
#print axioms ProofFile.Honest.K9.free_at_seat_att
#print axioms ProofFile.Honest.K9.free_at_seat_head
#print axioms ProofFile.Honest.K9.SeatedFree
