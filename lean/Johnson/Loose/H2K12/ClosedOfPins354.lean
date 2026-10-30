-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.PublicAt354
import Johnson.Loose.H2K12.ToldAt354
import Johnson.P5T.PlanSeatsFull
import Johnson.P5T.MembersByMake
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Numbers.WrittenInScope
/-
Johnson/Loose/H2K12/ClosedOfPins354.lean:
The proximity test (the kind K12) on the proof file's first chain, sub-protocol number 354 of the
table of joints: THE CLOSED DEBTS OF ITS LAW, FROM THE VERIFIER's ENTRY TESTS ON THE WRITTEN VALUES. Definitions,
statements and proofs: other files' ties, called; two general lemmas on lists; closed facts at the
written values by Lean's kernel; beside six of them stands a second fact at a bent value (`…_no`).
  `Written354 Zp`: the four equations that the entry tests give: the proof file's sendings, the first
    chain's codes, the shape of a request and the declared rounds' entries are the written ones.
  `written354_of_pins`: in the goals' scope, at what `ProofFile.pubPlain` returns, where the row `madeRow` accepts
    and the proof file's value is laid ⊢ `Written354`. Calls alone.
  `pseats_written`: so the list of rounds' seats of the first chain are the closed list `P5T.psFull`.
  `WrittenAll354`, `writtenAll354_of_pins`, `pseatsAll_written`: the like with all three
    chains' declared rounds: all three chains' seats are the closed list `P5T.seatsAllFull`.
  `map_seatOf_msOf`, `allSeats_R`, `lengths_R`, `entryB`, `entry_gen`: general: the seats of the members of plain lists are the
    lists' seats, in order; those by the make read no radius.
  `seats_full` | `seats_full_no`, `sent_full`, `entry_full` | `entry_full_no`, `rise_full`, `laid_full`,
    `front_full` | `front_full_no`, `index_full`, `rad_full` | `rad_full_no`: THE CLOSED FACTS.
  `rad_of_written`, `rows_return`, `mine75_full`: the radius from the equation that `rad_in_scope`
    (Johnson/HB/LLHARD/RadiiInScope.lean) concludes; and that the rows' maker has returned, from the test on the radii.
  `tieB`, `tie_of_B`, `tieAll_full` | `_no`, `msgs_full` | `_no`, `notices_full`, `psFull_apart`: more of them.
  `seatsOnce_of`, `sent_of`, `entry_of`, `laid_written`, `laid_of`, `placesOnce_of`, `places_of`, `member_full`, `tieAll_of`,
    `shapesListed_of`, `cut_of`: what they give at Zp.
  `publicLeft_of_pins`: `PublicLeft354` (H2K12/PublicAt354.lean) from `Written354`, the laying's return, ONE
    EQUATION ON A RADIUS, an equation on the letter N and the field "told".
WHAT STAYS. The radius: the listed radius of the one member is read off the rows of the sendings that an older
maker returns at the files (`Johnson.G.sendRowsOf`). This library has no statement that in scope these are
written rows. It is a premise here: one equation. Its payers to be, by report (neither is read
here): `radii_in_scope` (Johnson/HB/LLHARD/RadiiInScope.lean) and `radius_at_links`
(Johnson/Bridge/RowsRadii.lean [not in this library]). "told": H2K12/ToldAt354.lean.
What it is not. NO EXAMPLE BY A THEOREM OF THIS FILE: that `madeRow` accepts and the value is laid at files in scope is
said by evaluations. The written values were laid by programs from prints of one maker of the
lists of rounds. The full size alone. No soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open OnBytes Johnson.Pack Johnson.G
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers Item)
open VerifiableInference.Desc.K12.Door (Laid laidOf laidAtCodes)
open VerifiableInference.PlanWritten (madeRow madePinnedAt pinnedAt_of_row made_of_pinned first_of_made
  key_in_scope_pure plans_written pubBy_entries)
open P5T (psFull memberListsR)

/-! ## 1 What the entry tests give -/

/-- **The four equations.** -/
structure Written354 (Zp : ProofFile.Pub) : Prop where
  sends : Zp.made.proof = proofSendsFull
  codes : Zp.first.codes = codesFull2
  shape : Zp.first.shape = VerifiableInference.Desc.ReqLit.shapeFull
  entries : Zp.D.1.map (·.entry) = P5T.esFull.1

/-- **In scope, where the row accepts and the value is laid.** -/
theorem written354_of_pins {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} (hS : VerifierAndGoals.InScope Z = true)
    (hZ : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp) (hm : madeRow Zp = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r)) : Written354 Zp := by
  have hZ' : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp := hZ
  have hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true :=
    pinnedAt_of_row (by rw [hm, Bool.or_true])
  have hy' := hy
  unfold madePinnedAt at hy'
  rw [key_in_scope_pure hS hZ'] at hy'
  obtain ⟨_, _, hs, _⟩ := made_of_pinned hy'
  obtain ⟨Z₁, hZ₁, e1, _, _⟩ := plans_written hS hl
  obtain rfl : Zp = Z₁ := Except.ok.inj (hZ.symm.trans hZ₁)
  exact ⟨hs, _root_.Desc.K14.Law.first_codes_in_scope hS hZ' (first_of_made hy),
    _root_.Desc.K14.Law.first_shape_in_scope hS hZ' (first_of_made hy),
    (pubBy_entries hZ).1.trans e1⟩

/-- **The list of rounds' seats of the first chain are the closed list.** -/
theorem pseats_written {Zp : ProofFile.Pub} (W : Written354 Zp) :
    P5T.planSeats Zp Zp.D.1 = psFull := by
  rw [P5T.planSeats_at, W.sends, W.shape, W.entries]
  exact P5T.psFull_is

/-- **The same with the entries of all three chains' declared rounds.** -/
structure WrittenAll354 (Zp : ProofFile.Pub) : Prop extends Written354 Zp where
  entries₂ : Zp.D.2.1.map (·.entry) = P5T.esFull.2.1
  entries₃ : Zp.D.2.2.map (·.entry) = P5T.esFull.2.2

theorem writtenAll354_of_pins {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} (hS : VerifierAndGoals.InScope Z = true)
    (hZ : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp) (hm : madeRow Zp = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r)) : WrittenAll354 Zp := by
  obtain ⟨Z₁, hZ₁, _, e2, e3⟩ := plans_written hS hl
  obtain rfl : Zp = Z₁ := Except.ok.inj (hZ.symm.trans hZ₁)
  exact ⟨written354_of_pins hS hZ hm hl, (pubBy_entries hZ).2.1.trans e2,
    (pubBy_entries hZ).2.2.trans e3⟩

/-- **All three chains' seats are the closed list.** -/
theorem pseatsAll_written {Zp : ProofFile.Pub} (W : WrittenAll354 Zp) :
    P5T.planSeatsAll Zp Zp.D = P5T.seatsAllFull := by
  rw [P5T.planSeatsAll_at, W.sends, W.shape, W.entries, W.entries₂, W.entries₃]
  exact P5T.seatsAllFull_is

/-! ## 2 Two general lemmas -/

/-- The seats of the members of plain lists are the lists' seats, in order. -/
theorem map_seatOf_msOf : ∀ (L : MemberLists), (∀ p ∈ L, p.1.length = p.2.length) →
    (msOf L).map seatOf = allSeats L
  | [], _ => rfl
  | p :: L, h => by
    have ih := map_seatOf_msOf L fun q hq => h q (List.mem_cons_of_mem p hq)
    have hp := h p List.mem_cons_self
    have e : ((List.finRange p.1.length).map fun i : Fin p.1.length => p.2.getD i.val (0, 0)) =
        p.2 := by
      apply List.ext_getElem
      · rw [List.length_map, List.length_finRange, hp]
      · intro i h1 h2
        rw [List.getElem_map, List.getElem_finRange, List.getD_eq_getElem?_getD]
        simp [List.getElem?_eq_getElem h2]
    show ((((List.finRange p.1.length).map fun i => (⟨VerifiableInference.Desc.Sound.Sending.ofLists p.1 p.2, i⟩ : Mem)) ++
      msOf L).map seatOf) = p.2 ++ allSeats L
    rw [List.map_append, ih, List.map_map]
    exact congrArg (· ++ allSeats L) e

/-- The seats of the lists by the make: no radius is read. -/
theorem allSeats_R (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) :
    allSeats (memberListsR n rad ps) =
      (List.range n).flatMap fun k => (P5T.mineAt ps k).map (·.seat) := by
  unfold allSeats memberListsR
  rw [List.flatMap_map]

theorem lengths_R (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) :
    ∀ p ∈ memberListsR n rad ps, p.1.length = p.2.length := by
  intro p hp
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 hp
  simp

/-- The test: among the sampled seats of the first n sendings the seat q stands at place i0 of sending k0
alone, with the shape s. -/
def entryB (ps : List P5T.PSeat) (n : ℕ) (q : ℕ × ℕ) (k0 i0 : ℕ) (s : OracleShape) : Bool :=
  (List.range n).all fun k => (P5T.mineAt ps k).zipIdx.all fun y =>
    y.1.seat != q || (k == k0 && y.2 == i0 && decide (y.1.shape = s))

/-- Where that test accepts, the entry of the member at the seat q. General. -/
theorem entry_gen (ps : List P5T.PSeat) (n : ℕ) (q : ℕ × ℕ) (k0 i0 : ℕ) (s : OracleShape)
    (h : entryB ps n q k0 i0 s = true) (rad : ℕ → ℕ → ℕ) (x : Mem)
    (hx : x ∈ msOf (memberListsR n rad ps)) (hs : seatOf x = q) :
    x.1.l.get x.2 = (s, rad k0 i0) := by
  obtain ⟨p, hp, i, rfl⟩ := mem_msOf' _ x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
  have hi : i.val < (P5T.mineAt ps k).length := by
    have := i.isLt
    simpa using this
  have hy : ((P5T.mineAt ps k)[i.val], i.val) ∈ (P5T.mineAt ps k).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem hi]
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h k hk) _ hy
  have hs' : (P5T.mineAt ps k)[i.val].seat = q := by
    have e : seatOf ⟨VerifiableInference.Desc.Sound.Sending.ofLists _ ((P5T.mineAt ps k).map (·.seat)), i⟩ =
        (P5T.mineAt ps k)[i.val].seat := by
      show ((P5T.mineAt ps k).map (·.seat)).getD i.val (0, 0) = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
      rfl
    rw [← e]
    exact hs
  simp only [hs', bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h1
  obtain ⟨⟨rfl, h0⟩, hsh⟩ := h1
  show ((P5T.mineAt ps k).zipIdx.map fun y => (y.1.shape, rad k y.2)).get i = _
  rw [List.get_eq_getElem, List.getElem_map, List.getElem_zipIdx]
  simp only [Nat.zero_add]
  rw [hsh, h0]

/-! ## 3 The closed facts, by the kernel -/

/-- The sampled seats at the written values, sending by sending. -/
def seatsFull : List (ℕ × ℕ) := (List.range 82).flatMap fun k => (P5T.mineAt psFull k).map (·.seat)

theorem sends_full : proofSendsFull.1.sends.length = 82 := by decide +kernel

theorem seats_full : seatsFull.Nodup := by decide +kernel

/-- A closed fact; no control: true of every list with a member (its first seat stands twice). -/
theorem seats_full_no : ¬ (seatsFull ++ seatsFull.take 1).Nodup := by decide +kernel

/-- What segment 25 sends at its moment 0. -/
theorem sent_full : P5T.N0Full.sent 25 0 = [(76, 0)] := by decide +kernel

theorem entry_full : entryB psFull 82 (76, 0) 75 0 shL = true := by decide +kernel

/-- The negative test: at another code's number. -/
theorem entry_full_no : entryB psFull 82 (76, 0) 75 0 { shL with code := 1 } = false := by
  decide +kernel

/-- The written sendings' entries rise: so the sort is idle. -/
theorem rise_full : proofSendsFull.1.sends.Pairwise fun a b => (decide (a.entry ≤ b.entry)) = true := by
  decide +kernel

/-- The written sendings' notices. -/
def noticesFull : List (List OracleNotice) := proofSendsFull.1.sends.map (·.sent)

/-- The places that the laying gives are the closed list's seats. -/
theorem laid_full : (laidOf codesFull2 noticesFull).map (·.places) = some (psFull.map (·.seat)) := by
  decide +kernel

/-- In front of sending 75: 76 trees. -/
theorem front_full : (laidOf codesFull2 (noticesFull.take 75)).map (·.shapes.length) = some 76 := by
  decide +kernel

/-- The negative test: one sending shorter. -/
theorem front_full_no :
    (laidOf codesFull2 (noticesFull.take 74)).map (·.shapes.length) ≠ some 76 := by decide +kernel

/-- Message number 4 sits at (1, 0); number 185 at (76, 0). -/
theorem index_full : ((psFull.map (·.seat))[4]?, (psFull.map (·.seat))[185]?) =
    (some (1, 0), some (76, 0)) := by decide +kernel

/-- At the written rows of the sendings (entries 24 to 105 of the written list of all chains' rows): sending 75
has one sampled message: the closed shape with the closed radius. -/
theorem rad_full : (((packFullLit.drop 24).take 82).map (·.2))[75]? = some [(shL, e0L)] := by
  decide +kernel

/-- The negative test: sending 74's is another. -/
theorem rad_full_no : (((packFullLit.drop 24).take 82).map (·.2))[74]? ≠ some [(shL, e0L)] := by
  decide +kernel

/-- Where the rows' radius at place 0 of sending 75 is the written rows', it is the closed one.
-/
theorem rad_of_written (rows : List SendRow)
    (h : P5T.rad? rows 75 0 =
      (((((packFullLit.drop 24).take 82).map (·.2))[75]?).bind (·[0]?)).map (·.2)) :
    P5T.radOf rows 75 0 = e0L := by
  unfold P5T.radOf
  rw [h, rad_full]
  rfl

/-- **Where the test on the radii accepts and some sending has a sampled seat, the maker of the rows of the
sendings has returned.** General. -/
theorem rows_return (pol lay KL : ByteArray) (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List P5T.PSeat)
    (h : P5T.radIsB ((P5T.rowsAt? pol lay KL).getD []) n rad ps = true) (k : ℕ) (hk : k < n)
    (hne : 0 < (P5T.mineAt ps k).length) :
    ∃ R, sendRowsOf pol lay KL = .ok R ∧ (P5T.rowsAt? pol lay KL).getD [] = R := by
  cases hR : sendRowsOf pol lay KL with
  | ok R => exact ⟨R, rfl, by simp [P5T.rowsAt?, hR, Except.toOption]⟩
  | error e =>
    exfalso
    have e0 : (P5T.rowsAt? pol lay KL).getD [] = [] := by simp [P5T.rowsAt?, hR, Except.toOption]
    rw [e0] at h
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 h k (List.mem_range.2 hk)) 0
      (List.mem_range.2 hne)
    simp [P5T.rad?, P5T.firstRows] at h1

/-- Sending 75 has a sampled seat. -/
theorem mine75_full : 0 < (P5T.mineAt psFull 75).length := by decide +kernel

/-- The kind K1's four tests on a shape, as one test with code. -/
def tieB (cs : Codes) (s : OracleShape) : Bool :=
  decide (s.answers = 1) && cs.lengthsOk && Blk.shapeOk cs s && (K1.Msg.of cs s).padFits

theorem tie_of_B {cs : Codes} {s : OracleShape} (h : tieB cs s = true) : K1.Tie cs s := by
  simp only [tieB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- At every sampled seat of the closed list. -/
theorem tieAll_full : ((psFull.filter (·.smpd)).all fun p => tieB codesFull2 p.shape) = true := by
  decide +kernel

/-- A closed fact; no control: it cannot fail (`tieB` asks one answer; the shape is given two). -/
theorem tieAll_full_no : tieB codesFull2 { shL with answers := 2 } = false := by decide +kernel

/-- The written notices' shapes, in order, are the closed list's. -/
theorem msgs_full : K12.Door.msgsOf noticesFull = psFull.map (·.shape) := by decide +kernel

/-- The negative test: shifted by one. -/
theorem msgs_full_no : (K12.Door.msgsOf noticesFull).drop 1 ≠ (psFull.map (·.shape)).take 198 := by
  decide +kernel

theorem notices_full : noticesFull.length = 82 := by decide +kernel

/-- No two seats of the closed list are one. -/
theorem psFull_apart : (psFull.map (·.seat)).Nodup := by
  have h := P5T.seatsAllFull_apart
  unfold P5T.seatsAllFull at h
  rw [List.map_append, List.map_append, List.append_assoc] at h
  exact (List.nodup_append.1 h).1

/-! ## 4 What they give at Zp -/

section
variable {Zp : ProofFile.Pub} (W : Written354 Zp) (rad : ℕ → ℕ → ℕ)
include W

theorem ms_lists : P5T.msAtR Zp rad = msOf (memberListsR 82 rad psFull) := by
  unfold P5T.msAtR
  rw [pseats_written W, W.sends, sends_full]

/-- **No two members have one seat.** -/
theorem seatsOnce_of : ((P5T.msAtR Zp rad).map seatOf).Nodup := by
  rw [ms_lists W rad, map_seatOf_msOf _ (lengths_R 82 rad psFull), allSeats_R]
  exact seats_full

/-- **What segment 25 sends at its moment 0.** -/
theorem sent_of : (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).sent 25 0 = [(76, 0)] := by
  rw [pseats_written W]
  exact sent_full

/-- **The entry of the member at (76, 0)**: the closed shape, and the radius at place 0 of sending 75. -/
theorem entry_of (x : Mem) (hx : x ∈ P5T.msAtR Zp rad) (hs : seatOf x = (76, 0)) :
    x.1.l.get x.2 = (shL, rad 75 0) := by
  rw [ms_lists W rad] at hx
  exact entry_gen psFull 82 (76, 0) 75 0 shL entry_full rad x hx hs

/-- **The laying's return is the laying of the written notices at the written codes**: a closed term:
whoever wants a closed fact on its places or shapes evaluates that term. -/
theorem laid_written (L : Laid) (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    laidOf codesFull2 noticesFull = some L := by
  unfold laidAtCodes at hL
  rw [W.codes, W.sends, List.mergeSort_of_pairwise rise_full] at hL
  exact hL

/-- Its places are the closed list's seats. -/
theorem laid_of (L : Laid) (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    L.places = psFull.map (·.seat) := by
  have h := laid_full
  rw [laid_written W L hL] at h
  exact Option.some.inj h

theorem placesOnce_of (L : Laid) (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    L.places.Nodup := by
  rw [laid_of W L hL]
  exact psFull_apart

/-- **The listed places are the list of rounds' seats.** -/
theorem places_of (L : Laid) (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    L.places = (P5T.planSeats Zp Zp.D.1).map fun p => (p.j, p.t) := by
  rw [pseats_written W]
  exact laid_of W L hL

/-- A member's shape and seat are a sampled seat's of the closed list. -/
theorem member_full (y : Mem) (hy : y ∈ P5T.msAtR Zp rad) :
    ∃ p ∈ psFull, p.smpd = true ∧ p.shape = (y.1.l.get y.2).1 ∧ p.seat = seatOf y := by
  have h1 : ((y.1.l.get y.2).1, seatOf y) ∈
      (P5T.msAtR Zp rad).map fun x => ((x.1.l.get x.2).1, seatOf x) := List.mem_map.2 ⟨y, hy, rfl⟩
  rw [P5T.memsSame_atR, pseats_written W] at h1
  obtain ⟨p, hp, e⟩ := List.mem_map.1 h1
  obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
  exact ⟨p, hp1, hp2, congrArg Prod.fst e, congrArg Prod.snd e⟩

/-- **The kind K1's four tests at every member.** -/
theorem tieAll_of (y : Mem) (hy : y ∈ P5T.msAtR Zp rad) :
    K1.Tie Zp.first.codes (y.1.l.get y.2).1 := by
  obtain ⟨p, hp, hs, e, _⟩ := member_full W rad y hy
  rw [W.codes, ← e]
  exact tie_of_B (List.all_eq_true.1 tieAll_full p (List.mem_filter.2 ⟨hp, hs⟩))

/-- **The list of shapes has, at a listed member's number, that member's shape.** -/
theorem shapesListed_of (L : Laid) (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L)
    (o : ℕ) (y : Mem) (h : ListedAt (P5T.msAtR Zp rad) L.places o y) :
    (K12.Door.msgsOfChain Zp.made.proof.1)[o]? = some (y.1.l.get y.2).1 := by
  obtain ⟨p, hp, _, e1, e2⟩ := member_full W rad y h.1
  have hpl := h.2
  rw [laid_of W L hL, List.getElem?_map] at hpl
  obtain ⟨p', hp', e3⟩ := Option.map_eq_some_iff.1 hpl
  obtain rfl : p' = p :=
    List.inj_on_of_nodup_map psFull_apart (List.mem_of_getElem? hp') hp (e3.trans e2.symm)
  unfold K12.Door.msgsOfChain
  rw [W.sends, List.mergeSort_of_pairwise rise_full]
  show (K12.Door.msgsOf noticesFull)[o]? = _
  rw [msgs_full, List.getElem?_map, hp', ← e1]
  rfl

/-- **The sendings' cut at sending 75, with 76 trees listed in front**: the two closed clauses of
`ToldTies` (H2K12/ToldAt354.lean). -/
theorem cut_of (L : Laid) (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    ∃ sent, laidOf Zp.first.codes (noticesFull.take 75 ++ sent :: noticesFull.drop 76) = some L ∧
      ∀ Lp, laidOf Zp.first.codes (noticesFull.take 75) = some Lp → Lp.shapes.length = 76 := by
  have h75 : 75 < noticesFull.length := by rw [notices_full]; decide
  refine ⟨noticesFull[75], ?_, fun Lp hLp => ?_⟩
  · unfold laidAtCodes at hL
    rw [W.sends, List.mergeSort_of_pairwise rise_full] at hL
    rw [← List.drop_eq_getElem_cons h75, List.take_append_drop]
    exact hL
  · have h := front_full
    rw [W.codes] at hLp
    rw [hLp] at h
    exact Option.some.inj h

end

/-- **`PublicLeft354` from the entry tests' equations**, one equation on a radius, and "told". -/
theorem publicLeft_of_pins {Zp : ProofFile.Pub} (W : Written354 Zp) (rad : ℕ → ℕ → ℕ) {Xi : Type}
    (G : FileDescription Xi) (d : First.FoldData) (N : Numbers)
    (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some d.L) (hrad : rad 75 0 = e0L)
    (hN : N.sent 25 0 = (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).sent 25 0)
    (told : ∀ x ∈ P5T.msAtR Zp rad, seatOf x ∈ pinsOpen N O354 25 → MemberTold G d.L.shapes x) :
    PublicLeft354 Zp.first.codes G d N 25 O354 (P5T.msAtR Zp rad) := by
  refine ⟨seatsOnce_of W rad, placesOnce_of W d.L hL, fun x hx hp => ?_, by rw [W.codes]; exact tie_full,
    by rw [W.codes]; exact long_full, told⟩
  rw [pins_354, hN, sent_of W, List.mem_singleton] at hp
  rw [entry_of W rad x hx hp, hrad]

end H2K12

#print axioms H2K12.written354_of_pins
#print axioms H2K12.pseats_written
#print axioms H2K12.writtenAll354_of_pins
#print axioms H2K12.pseatsAll_written
#print axioms H2K12.map_seatOf_msOf
#print axioms H2K12.allSeats_R
#print axioms H2K12.entry_gen
#print axioms H2K12.seats_full
#print axioms H2K12.seats_full_no
#print axioms H2K12.sent_full
#print axioms H2K12.entry_full
#print axioms H2K12.entry_full_no
#print axioms H2K12.rise_full
#print axioms H2K12.laid_full
#print axioms H2K12.front_full
#print axioms H2K12.front_full_no
#print axioms H2K12.index_full
#print axioms H2K12.rad_full
#print axioms H2K12.rad_full_no
#print axioms H2K12.seatsOnce_of
#print axioms H2K12.sent_of
#print axioms H2K12.entry_of
#print axioms H2K12.laid_written
#print axioms H2K12.laid_of
#print axioms H2K12.placesOnce_of
#print axioms H2K12.tieAll_full
#print axioms H2K12.tieAll_full_no
#print axioms H2K12.msgs_full
#print axioms H2K12.msgs_full_no
#print axioms H2K12.places_of
#print axioms H2K12.tieAll_of
#print axioms H2K12.shapesListed_of
#print axioms H2K12.cut_of
#print axioms H2K12.sends_full
#print axioms H2K12.lengths_R
#print axioms H2K12.tie_of_B
#print axioms H2K12.notices_full
#print axioms H2K12.psFull_apart
#print axioms H2K12.ms_lists
#print axioms H2K12.member_full
#print axioms H2K12.rad_of_written
#print axioms H2K12.rows_return
#print axioms H2K12.mine75_full
#print axioms H2K12.publicLeft_of_pins
