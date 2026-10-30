-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/FirstSeatedAtReads.lean: THE STATE's HALF OF THE CLAUSE SymsIn, FirstSeated
(Johnson/Desc/K1/Law/ArmSyms.lean), IN FRONT OF EACH SEGMENT's READS, AT THE CLOSED CONSTANT
(P5J.mgAtAll, MgAtAll.lean): at the open part, each own message of moment 0 of the segment and each
kept message is there (ReqFrame.whereIs) and sits at a seat of the segment's first commitment.

OBJECT. FirstSeated (N.sent l 0) A l at a state in front of sub-protocol 14 l + k1Ix l false + 2.
USER. Whoever pays JAtt | JLay through symsIn_at_reads; the fence's invariant J at "reached".
LETTERS. Zl, D, r₀, Zp, Np, cF, x₀: the head's own.

HOW. The sentence is brought down to ONE TEST ON PUBLIC DATA, firstSeatedB, and the test is
evaluated by Lean's kernel at the written values.
  what the state gives, each by another file's theorem:
    the frame's lists are the plan's terms     "frame.sentIs" stands open in front of the reads
        (sentIn_mg: the kernel, at the composed meaning's closed list) and the table's promise
        holds it: inAt_pubQ, pubAll_more_sentIs, whereIs_of_sentIs
    the book has just the plan's count         the promise's clause bookAt: inAt_bookHeld
    the book's places are the listed seats     factsK13_reached's field seats
        (Johnson/Desc/AtSeats/K01FactsAtAll.lean)
    the frame's shape is the public one        live_reached (the same file), at link_two's place
  what the public files give, under hP1 and hC:
    the shape is the written one (first_written_in_scope) · what the sub-protocols tell is the
    written cut's (told_of_cut) · the planner's seats are the written ones (seats_in_scope)
Main names.
  candsAt, mem_cands       firstOrKeptB accepts pairs of a finite list alone
  firstSeatedB             the test · firstSeated_of_B: its law, general in the part
  firstSeated_written      the test accepts at the written values · firstSeated_asks: 85 pairs
  firstSeated_rejects, firstSeated_moment_rejects   negative tests: the listed seats shifted by
                           one; the second sendings' seats in the first's place: both reject
  **firstSeated_at_reads** the sentence, from hA, hP1, hC, "reached", the promise, no mark

PREMISES. hA: the shared head. hP1, hC: the entry tests' first comparison's accept and the first
chain's cut: facts on the public files, NOT PAID HERE. The promise onQ … is spent (two clauses).
What is not claimed. That the premises can be met together: NO MEMBER. Nothing on soundness.
The recursion limit is raised at the five kernel facts (maxRecDepth 1000000).

-/
import Johnson.Desc.K1.Law.ArmSyms
import Johnson.Desc.AtSeats.K01FactsOf
import Johnson.Desc.K1.Law.HpubAtPlus13
import Johnson.Desc.K1.Law.K01FiftyR
import Johnson.Desc.First.SentTerms
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat Johnson.G
open VerifiableInference.Desc (Chain Place Oracle)
open VerifiableInference.Desc.First (S ModelPart Pub Numbers flatPlacesOf shift)
open VerifiableInference.Desc.First.FillSent
open VerifiableInference.Desc.Sound
open VerifiableInference.PlanWritten
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_raw)
open ProofFile (Cl)
open IM (k1Ix)

/-- The pairs that the test firstOrKeptB can accept at segment l: a finite list. -/
def candsAt (shp : ReqShape) (l : ℕ) : List (ℕ × ℕ) :=
  (List.range ((shp.link[l]?.map (·.messages)).getD []).length).map (fun k => (l, k)) ++
    ((reqGroups shp).getD l {}).born.toList

theorem mem_cands {shp : ReqShape} {l born k : ℕ} (h : firstOrKeptB shp l born k = true) :
    (born, k) ∈ candsAt shp l := by
  unfold firstOrKeptB at h
  unfold candsAt
  by_cases e : (born == l) = true
  · rw [if_pos e] at h
    obtain rfl : born = l := eq_of_beq e
    refine List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 ?_, rfl⟩)
    cases hL : shp.link[born]? with
    | none =>
      rw [hL] at h
      cases h
    | some L =>
      rw [hL] at h
      cases hm : L.messages[k]? with
      | none =>
        rw [Option.bind_some, hm] at h
        cases h
      | some m => exact (List.getElem?_eq_some_iff.1 hm).1
  · rw [if_neg e] at h
    exact List.mem_append_right _ (by simpa using h)

/-- **A TEST ON PUBLIC DATA ALONE**: at each of the 25 segments, each own message of moment 0 and
each kept message has a number by the plan's term, below the count of messages in front of the
segment's reads, and the listed seat of that number is one of the segment's first commitment. -/
def firstSeatedB (shp : ReqShape) (msgs : Option Place → ℕ) (sent : ℕ → ℕ → List (ℕ × ℕ))
    (places : List (ℕ × ℕ)) : Bool :=
  (List.range 25).all fun l => (candsAt shp l).all fun b =>
    !firstOrKeptB shp l b.1 b.2 ||
      match whereIsP (sentDataOf shp (fun m => msgs ((flatPlacesOf linksFull true).find? fun p =>
          p.link == some m && p.piece == 1 + ((linksFull[m]?).map shift).getD 0)) fun _ => [])
          l b.1 b.2 with
      | some o =>
        decide (o < msgs (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]?) &&
          match places[o]? with
          | some x => (sent l 0).contains x
          | none => false
      | none => false

/-- **The test's law.** -/
theorem firstSeated_of_B {shp : ReqShape} {msgs : Option Place → ℕ}
    {sent : ℕ → ℕ → List (ℕ × ℕ)} {places : List (ℕ × ℕ)}
    (hB : firstSeatedB shp msgs sent places = true) {l : ℕ} (hl : l < 25) {a : K9.Part}
    (hsh : a.L.check.frame.shape = shp)
    (hw : ∀ born k, a.L.check.frame.whereIs born k =
      whereIsP (sentDataOf shp (fun m => msgs ((flatPlacesOf linksFull true).find? fun p =>
        p.link == some m && p.piece == 1 + ((linksFull[m]?).map shift).getD 0)) fun _ => [])
        l born k)
    (hsz : a.d.book.place.size = msgs (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]?)
    (hpl : a.d.book.place.toList = places.take a.d.book.place.size) :
    FirstSeated (sent l 0) a l := by
  intro born k hk
  rw [hsh] at hk
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 hB l (List.mem_range.2 hl)) (born, k)
    (mem_cands hk)
  simp only [hk, Bool.not_true, Bool.false_or] at h1
  rw [← hw born k] at h1
  cases ho : a.L.check.frame.whereIs born k with
  | none =>
    rw [ho] at h1
    cases h1
  | some o =>
    rw [ho] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨hlt, h2⟩ := h1
    cases hx : places[o]? with
    | none =>
      rw [hx] at h2
      cases h2
    | some x =>
      rw [hx] at h2
      refine ⟨o, x, rfl, ?_⟩
      have hp : a.d.book.place[o]? = some x := by
        rw [← Array.getElem?_toList, hpl, List.getElem?_take_of_lt (by omega)]
        exact hx
      unfold K9.seatAt
      rw [hp]
      show (if (sent l 0).contains x = true then some x else none) = some x
      rw [if_pos h2]

/-- What the sub-protocols of the written cut tell. -/
def toldFull : List (List Oracle) := cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)

/-- The written numbers, as far as the test reads them. -/
def numsW : Numbers := (P5T.numbersOf P5T.psFull).withTold P5J.At.ps toldFull

set_option maxRecDepth 1000000 in
/-- **The test accepts at the written values** (Lean's kernel): 85 pairs are asked. -/
theorem firstSeated_written :
    firstSeatedB proofSizedFull.request numsW.msgsAt numsW.sent K13.Law.LFull.places = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It asks something: 85 pairs. -/
theorem firstSeated_asks : (((List.range 25).map fun l =>
    ((candsAt proofSizedFull.request l).filter fun b =>
      firstOrKeptB proofSizedFull.request l b.1 b.2).length).sum) = 85 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: with the listed seats shifted by one the test rejects. -/
theorem firstSeated_rejects :
    firstSeatedB proofSizedFull.request numsW.msgsAt numsW.sent (K13.Law.LFull.places.drop 1) =
      false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: at the second sendings' seats in the first's place it rejects. -/
theorem firstSeated_moment_rejects :
    firstSeatedB proofSizedFull.request numsW.msgsAt (fun l _ => numsW.sent l 1)
      K13.Law.LFull.places = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- In front of each segment's reads "frame.sentIs" stands open, at the composed meaning's own
closed list of named public items. -/
theorem sentIn_mg : ((List.range 25).all fun l =>
    inSetB mgMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)
      (.more (some l) "frame.sentIs")) = true := by
  decide +kernel

/-- **FirstSeated in front of each segment's reads, at the closed constant.** -/
theorem firstSeated_at_reads {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hC : cutOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = cutFirstFull) :
    ∀ l, l < 25 → ∀ a,
      RchAt (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
          (D.at frS.P.T.a).key₁ 0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (14 * l + k1Ix l false + 2) a →
      onQ hA.𝔇.N (mgAll hA.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a)
        (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → ∀ A, K9.segAt? a.1.2 = some A →
      FirstSeated (hA.𝔇.N.sent l 0) A l := by
  intro l hl a hr hon hm A hseg
  obtain ⟨_, hL, -, -, hbook⟩ := segAt_some hseg
  have hIn : InAt hA.𝔇.N (mgAll hA.𝔇 mgBase) linksFull (flatPlacesOf linksFull true)
      (14 * l + k1Ix l false + 2) a.1 (strsOf _ a.2) := ⟨hon, hm⟩
  have h0 : sentIsB hA.𝔇.pubD.dS l a.1.2 = true := by
    have h := inAt_pubQ hIn (.more (some l) "frame.sentIs") (by
      rw [mgAll_more_base]
      exact inSet_of (List.all_eq_true.1 sentIn_mg l (List.mem_range.2 hl)))
    rwa [mgAll_pub, First.pubAll_more_sentIs] at h
  have hbk := inAt_bookHeld hIn
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  have hreach := rchAt_raw hr
  have hF := (K13.Law.factsK13_reached hA hP1 _ a.1 hreach hm).seats
  unfold K12.Door.atFirstSeats K12.Door.seatsCarriedB at hF
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hF
  obtain ⟨p, hp, hpl⟩ := link_two l hl false _ (Or.inl rfl)
  have hsh := (K13.Law.live_reached hA _ a.1 hreach hm hp hpl A.L hL).2
  have hl' := hA.laid.run ▸ LPFD.Full.laidPOf_of hA.laid.value hA.laid.planOk hA.laid.data
    hA.laid.asks
  have e1 : hA.𝔇.shape = proofSizedFull.request :=
    (Joined.first_written_in_scope hA.scope hA.laid.pub hP1).2.2.1
  have e2 : hA.𝔇.N.msgsAt = numsW.msgsAt := by
    show (fun p => First.msgsTold (P5J.At.told cF) (First.borderOf P5J.At.ps p)) = _
    rw [K13.Law.told_of_cut (cF := cF) hC]
    rfl
  have e3 : hA.𝔇.N.sent = numsW.sent := by
    show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).sent = _
    rw [(P5T.seats_in_scope hA.scope hA.laid.pub hP1 hl').2.2]
    rfl
  rw [e3]
  refine firstSeated_of_B firstSeated_written hl (hsh.trans e1) (fun born k => ?_) ?_ ?_
  · rw [whereIs_of_sentIs hL h0 born k, ← e2, ← e1]
    rfl
  · rw [hbook, hbk.1.2, hbk.2, e2]
  · rw [hbook]
    exact hF.1.1.1

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.mem_cands
#print axioms VerifiableInference.Desc.K1.firstSeated_of_B
#print axioms VerifiableInference.Desc.K1.firstSeated_written
#print axioms VerifiableInference.Desc.K1.firstSeated_asks
#print axioms VerifiableInference.Desc.K1.firstSeated_rejects
#print axioms VerifiableInference.Desc.K1.firstSeated_moment_rejects
#print axioms VerifiableInference.Desc.K1.sentIn_mg
#print axioms VerifiableInference.Desc.K1.firstSeated_at_reads
