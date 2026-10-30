-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/SamplesAtEnd.lean: hFirst OF samples_at_lastThread, AT A STATE THAT PASSES THE LIBRARY's TESTS ON THE FIRST CHAIN's LAST STATE (ToldDesc.rcLastB; the payer at the head: hRc_at_left, ToldDescR/HRcAtLeft.lean), FROM THE TWO PINS' MEANING AT THAT STATE, at any witness.

  sampleAt_facts   what the library's test sampleAtB gives of a message: one sample row, that names it alone, and the code lengths
  one_member       hM's clauses at one message, from its pin
  samples_of_rc    the statement

What is not here. hI, hV: that the pins hold at this state and at the witness that the last thread names: LastThreadParts.ends and .meaning are free fields: L25's tie, owed. hNoI, hNoW, hShI, hShW: public, on the plan's list of seats against the book, and on the shapes of the members that sit there.

This letter is for the honest run's own forms alone. NEVER ON SOUNDNESS's ROAD.
NO PROPERTY IS CLAIMED. -/
import AtFullSide.K1.SaysAtFirstEnd
import Johnson.ToldDescR.RcLastCode
import Johnson.Desc.K12.Law.SampleLaw
import Johnson.Desc.K12.Law.SaysSample
import Johnson.Desc.Last.OwnSits
import Johnson.Desc.K12.Door.DoorGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Means
open OnBytes.Slice (rdE GE readE)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt Sending seatOf seatBy noFirst numAt smpNamed wordsFirst bookFitsB)
open VerifiableInference.Desc.Third (firstOfS FirstEnd₃)
open VerifiableInference.Desc.Last (OwnSeats ownSitsB ownSitsB_iff)
open VerifiableInference.Desc.K12.Door (Laid bookInOrderB)
open VerifiableInference.Desc.First.Close (NamesOne)
open ToldDesc (rcLastB sampleAtB sampleTwoB)
open Johnson.Pack

/-- **What the test gives of a message.** -/
theorem sampleAt_facts {cs : Codes} {sh : OracleShape} {St : Statement} {o : ℕ}
    (h : sampleAtB cs sh St o = true) :
    ∃ (x : Oracle) (r : Row), St.oracles[o]? = some x ∧ x.shape = sh ∧ x.sampleRows.toList = [r] ∧
      NamesOne r o ∧ (0 < sh.mainRows → 2 ^ ceilLog2 (pMain cs sh).ell = (pMain cs sh).ell) ∧
      (0 < sh.maskRows → 2 ^ ceilLog2 (pMask cs sh).ell = (pMask cs sh).ell) := by
  unfold sampleAtB at h
  cases hx : St.oracles[o]? with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨e, hL⟩ := h
    obtain ⟨seed, row0, tt, β, hf, hr, -, -, -, -, h1, h2⟩ := H2K.Pin.sample_of_L hL
    refine ⟨x, { row0 with target := tt }, rfl, e, hr, ?_, h1, h2⟩
    intro o' hne part i
    exact OnBytes.Slice.coefAt_form_other cs sh o seed 0 row0 hf o' hne part i

/-- The reader of seats at a place of the book, where the book is in order. -/
theorem seatBy_first {B : TreeBook} {roots : ℕ} (b1 : bookInOrderB 0 B roots = true)
    (b2 : bookFitsB B = true) {o : ℕ} {q : ℕ × ℕ} (hq : B.place[o]? = some q) :
    seatBy noFirst B o = some q := by
  unfold VerifiableInference.Desc.Sound.bookFitsB at b2
  have e0 := List.all_eq_true.1 b2 o (List.mem_range.2 (Array.getElem?_eq_some_iff.1 hq).1)
  rw [hq] at e0
  unfold seatBy noFirst
  rw [hq]
  show (B.trees[q.1]?).map _ = _
  cases ht : B.trees[q.1]? with
  | none =>
    have e0' : (match B.trees[q.1]? with
      | some t => decide (t.parts[q.2]? = some o)
      | none => false) = true := e0
    rw [ht] at e0'
    cases e0'
  | some t =>
    unfold bookInOrderB at b1
    simp only [Bool.and_eq_true] at b1
    have hlt := (Array.getElem?_eq_some_iff.1 ht).1
    have e1 := List.all_eq_true.1 b1.2 q.1 (List.mem_range.2 hlt)
    rw [ht] at e1
    have e2 : t.number = 0 + q.1 := by simpa using e1
    have e3 : t.number = q.1 := by omega
    show some (t.number, q.2) = some q
    rw [e3]

variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- **hM's clauses at one message, from its pin.** -/
theorem one_member {Pb : Type} {seats : List (ℕ × ℕ)} {ms : List Mem} {p : Pb} {s : S} {sh : OracleShape}
    {o : ℕ} {q : ℕ × ℕ} {y : Strs} {w : Wit Cells Tok MsgT}
    (hA : sampleAtB s.st.codes sh s.st o = true) (hpl : s.book.place[o]? = some q)
    (b1 : bookInOrderB 0 s.book s.roots = true) (b2 : bookFitsB s.book = true)
    (hans : ansJT s.st.codes arr (smpNamed s.st.codes seats) ms q.1 q.2 (p, s) y w)
    (hNo : q ∈ seats ∧ seats.idxOf q = o)
    (hSh : ∀ μ ∈ ms, SitsAt μ q.1 q.2 → (μ.1.l.get μ.2).1 = sh) :
    ∃ (x : Oracle) (r : Row) (μ : Mem), s.st.oracles[o]? = some x ∧
      x.sampleRows.toList = [r] ∧ NamesOne r o ∧
      (0 < x.shape.mainRows →
        2 ^ ceilLog2 (pMain s.st.codes x.shape).ell = (pMain s.st.codes x.shape).ell) ∧
      (0 < x.shape.maskRows →
        2 ^ ceilLog2 (pMask s.st.codes x.shape).ell = (pMask s.st.codes x.shape).ell) ∧
      seatBy noFirst s.book o = some (seatOf μ) ∧ μ.1.seat μ.2 ∈ seats ∧ numAt seats μ = o ∧
      (μ.1.l.get μ.2).1 = x.shape ∧
      AnsAt s.st.codes arr μ.1.l μ.1.seat (fun a => smpNamed s.st.codes seats a μ.1) μ.2 (p, s) w := by
  obtain ⟨x, r, hx, rfl, hr, hN, h1, h2⟩ := sampleAt_facts hA
  obtain ⟨⟨μ, hμ, hsit⟩, hall⟩ := hans
  have es : seatOf μ = q := hsit
  have hseat : μ.1.seat μ.2 = q := es
  refine ⟨x, r, μ, hx, hr, hN, h1, h2, ?_, ?_, ?_, hSh μ hμ hsit, hall μ hμ hsit⟩
  · rw [es]
    exact seatBy_first b1 b2 hpl
  · rw [hseat]
    exact hNo.1
  · show seats.idxOf (seatOf μ) = o
    rw [es]
    exact hNo.2

/-- **hFirst's end at a state that passes the tests, from the two pins' meaning there.** -/
theorem samples_of_rc {Pb : Type} {seats : List (ℕ × ℕ)} {ms : List Mem} {V : OwnSeats} {L : Laid}
    {p : Pb} {s : S} (hRc : rcLastB 0 V L s.st.codes s = true) (w : Wit Cells Tok MsgT) (y : Strs)
    (hI : ansJT s.st.codes arr (smpNamed s.st.codes seats) ms V.index.1 V.index.2 (p, s) y w)
    (hV : ansJT s.st.codes arr (smpNamed s.st.codes seats) ms V.w.1 V.w.2 (p, s) y w)
    (hNoI : ∀ i, s.book.place[i]? = some V.index → V.index ∈ seats ∧ seats.idxOf V.index = i)
    (hNoW : ∀ i, s.book.place[i]? = some V.w → V.w ∈ seats ∧ seats.idxOf V.w = i)
    (hShI : ∀ μ ∈ ms, SitsAt μ V.index.1 V.index.2 → (μ.1.l.get μ.2).1 = V.indexShape)
    (hShW : ∀ μ ∈ ms, SitsAt μ V.w.1 V.w.2 → (μ.1.l.get μ.2).1 = V.wShape)
    {f : FirstEnd₃} (hf : firstOfS s = some f) {G : Group} (hG : f.st.groups[f.own]? = some G) :
    sampleItem rdE f.st G.members.toList (wordsFirst arr f.st f.book w) := by
  unfold rcLastB at hRc
  simp only [Bool.and_eq_true] at hRc
  obtain ⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, -⟩ := hRc
  obtain ⟨G', i₁, i₂, hG', hm, p1, p2, -, -⟩ := (ownSitsB_iff V s).1 b3 f hf
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
  have hfe : f.st = s.st ∧ f.book = s.book := by
    obtain ⟨e, -, rfl⟩ := Option.map_eq_some_iff.1 hf
    exact ⟨rfl, rfl⟩
  unfold sampleTwoB at b4
  rw [hf] at b4
  simp only [hG', hm, Bool.and_eq_true] at b4
  obtain ⟨a1, a2⟩ := b4
  rw [hfe.1] at a1 a2
  rw [hfe.2] at p1 p2
  refine sampleItem_of_ans arr seats (p := p) hf w fun o ho => ?_
  rw [hm] at ho
  rcases List.mem_cons.1 ho with rfl | ho
  · exact one_member arr a1 p1 b1 b2 hI (hNoI _ p1) hShI
  · obtain rfl := List.mem_singleton.1 ho
    exact one_member arr a2 p2 b1 b2 hV (hNoW _ p2) hShW

/-- The number of a place of the book, where the list of seats is the laid places and has no repeat. -/
theorem idx_of_place {L : Laid} {B : TreeBook} (hC : VerifiableInference.Desc.K12.Door.seatsCarriedB L B = true)
    {seats : List (ℕ × ℕ)} (hP : L.places = seats) (hN : seats.Nodup) {i : ℕ} {q : ℕ × ℕ}
    (hq : B.place[i]? = some q) : q ∈ seats ∧ seats.idxOf q = i := by
  have e := VerifiableInference.Desc.K12.Door.place_of_seats hC i (Array.getElem?_eq_some_iff.1 hq).1
  rw [hq, hP] at e
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.1 e.symm
  refine ⟨he ▸ List.getElem_mem hl, ?_⟩
  rw [← he]
  exact hN.idxOf_getElem i hl

/-- **samples_of_rc at the plan's list of seats**: the numbers come off the test seatsCarried. -/
theorem samples_of_rc_seats {Pb : Type} {seats : List (ℕ × ℕ)} {ms : List Mem} {V : OwnSeats} {L : Laid}
    {p : Pb} {s : S} (hRc : rcLastB 0 V L s.st.codes s = true) (w : Wit Cells Tok MsgT) (y : Strs)
    (hI : ansJT s.st.codes arr (smpNamed s.st.codes seats) ms V.index.1 V.index.2 (p, s) y w)
    (hV : ansJT s.st.codes arr (smpNamed s.st.codes seats) ms V.w.1 V.w.2 (p, s) y w)
    (hP : L.places = seats) (hN : seats.Nodup)
    (hShI : ∀ μ ∈ ms, SitsAt μ V.index.1 V.index.2 → (μ.1.l.get μ.2).1 = V.indexShape)
    (hShW : ∀ μ ∈ ms, SitsAt μ V.w.1 V.w.2 → (μ.1.l.get μ.2).1 = V.wShape)
    {f : FirstEnd₃} (hf : firstOfS s = some f) {G : Group} (hG : f.st.groups[f.own]? = some G) :
    sampleItem rdE f.st G.members.toList (wordsFirst arr f.st f.book w) := by
  have hC : VerifiableInference.Desc.K12.Door.seatsCarriedB L s.book = true := by
    have h' := hRc
    unfold rcLastB at h'
    simp only [Bool.and_eq_true] at h'
    exact h'.2
  exact samples_of_rc arr hRc w y hI hV (fun _ h => idx_of_place hC hP hN h)
    (fun _ h => idx_of_place hC hP hN h) hShI hShW hf hG

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.idx_of_place
#print axioms ProofFile.Honest.K1.samples_of_rc_seats
#print axioms ProofFile.Honest.K1.sampleAt_facts
#print axioms ProofFile.Honest.K1.seatBy_first
#print axioms ProofFile.Honest.K1.one_member
#print axioms ProofFile.Honest.K1.samples_of_rc
