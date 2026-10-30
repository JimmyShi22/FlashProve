-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieMatPaid.lean: MatSeatF (TieMatFront.lean) AT THE HEAD, AT THE READS OF SEGMENT l, from the library's laws along
"reached": the parts and their ride (front_at_reads); the seated arrays (symsIn_of_B under the test hB); the state's book and shapes
(factsK13_reached); the live copy (liveIs_at_rch); the link's list of arrays (arrays_at_reads_b).

  matSeatF_head   the statement. Left as premises: hTl, the record behind the member against the plan tlW; hB; hPub, a sentence on
                  the plan's written data alone

This letter is for the honest run's own forms alone: no statement on any other party may take it. NEVER ON SOUNDNESS's ROAD: it
stands over laws at the meaning "honest".
NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieMatFront
import Johnson.Desc.ProofFile.Honest.K1.Law.FrontAtReads
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAttEntryB
import Johnson.Desc.ProofFile.Honest.K1.Twin.FirstSeatedAtLinkNoB
import Johnson.Desc.AtSeats.LiveAtRch
import Johnson.Desc.AtSeats.K01FactsAtAll
import Johnson.Desc.AtSeats.K13KindRowB

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT Mem linksFull mgAll mgBase strsOf Rides seatOf seatBy noFirst)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open P5J (AtMgA CellsM TS F0T)
open OnBytes.HonestTrace (Sz)
open Johnson.Desc.First.Walk.Tied (rchAt_raw)

/-- **MatSeatF at the head, at the reads of segment l.** -/
theorem matSeatF_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {l NM : ℕ} (hl : l < 25) {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ} {ms : List Mem} {Sz₀ : Sz}
    {own : ℕ → ℕ × ℕ × ℕ × ReqArray} (tlW : HTailF2)
    (hcs : ∀ k s μ E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (K1.noL l false) k s μ E → s.st.codes = cs)
    (hTl : ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs[K1.noL l false]? = some blk →
      ∀ k s μ E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (K1.noL l false) k s μ E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s μ E ds y cols s' →
      ∀ tl : HTailF2, s'.tl? = some tl → tl.NM = NM ∧ tl.gtTree = tlW.gtTree)
    (hNM : tlW.NM = NM)
    (hB : K1.symsSeatedB (h.𝔇.pubD.d3.arrayOf.getD l #[]) h.𝔇.layout h.𝔇.shape l tlW = true)
    (hPub : ∀ ν, ν < NM → ∀ (c₁ : ℕ × String) (a₁ : ReqArray) (o : ℕ) (q : ℕ × ℕ) (sh : OracleShape),
      (h.𝔇.pubD.d3.arrayOf.getD l #[])[tlW.gtTree.getD ν 0]? = some c₁ →
      reqArray h.𝔇.layout c₁.1 c₁.2 = some a₁ →
      First.FillSent.whereIsP h.𝔇.pubD.dS l c₁.1 a₁.message = some o →
      K13.Law.d12Full.L.places[o]? = some q →
      K13.Law.d12Full.M[o]? = some sh → (h.𝔇.N.sent l 0).contains q = true →
      ∃ (yM : Mem) (l₀ ν₀ : ℕ), (ms.find? fun z => decide (seatOf z = q)) = some yM ∧
        (yM.1.l.get yM.2).1 = sh ∧
        laidMatrixOk a₁ (ceilLog2 (sh.rows Part.main))
          (if sh.rows Part.main == 0 then 0 else (cs.base.getD sh.code default).logEll) = true ∧
        own ν = (arr q.1 q.2, l₀, ν₀, a₁) ∧ Sz₀.packedShape l ν = Sz₀.packedShape l₀ ν₀ ∧
        ∀ i c rp, i < (Sz₀.packedShape l ν).1 → c < (Sz₀.packedShape l ν).2 →
          laidAt a₁ i c = some rp → rp.1 < sh.mainRows ∧ padB cs sh false rp.1 rp.2 = false) :
    MatSeatF (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said cs arr ms Sz₀
      (K1.noL l false) l NM (h.𝔇.N.sent l 0) own := by
  intro blk hb k s μ E ds y cols s' hT hd hS tl htl
  obtain ⟨hNM', hgt⟩ := hTl blk hb k s μ E ds y cols s' hT hd hS tl htl
  refine ⟨hNM', ?_⟩
  obtain ⟨A, B, hA, hB', hR, hF⟩ := front_at_reads h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    hSaid hl hb hT hS
  have hT' : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (K1.noL l false) k s μ E := ⟨hT.1, hSaid _ _ _ hT.2⟩
  have hbl : K1.noL l false ≤ cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb).1.le
  have hIn := inAt_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hT
  have σ : (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
      (D.at frS.P.T.a).key₁ 0).E.Str := (fun _ => default, fun _ => default)
  have hr := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w σ hbl hT'
  have hm : s.failed = none := (hIn (strsOf _ σ)).2
  have Fk := K13.Law.factsK13_reached h (K1.pin1_atAll h) _ _ (rchAt_raw hr) hm
  obtain ⟨eS, eL⟩ := K1.liveIs_at_rch h _ ((μ.st.input.x.pub, s), σ) hr hm
  have harr := K1.arrays_at_reads_b h.𝔇 K13.Law.d12Full mgBase rfl l hl _ _ (hIn (strsOf _ σ)) A hA
  obtain ⟨_, hLa, _, _, hbk⟩ := K1.segAt_some hA
  have hst : A.d.st = s.st := K1.segAt_st hA
  have hlv : s.live = A.L.check := by
    unfold S.live
    rw [hLa]
  have eS' : A.L.check.frame.shape = h.𝔇.shape := by rw [← hlv]; exact eS
  have eL' : A.L.check.rows.layout = h.𝔇.layout := by rw [← hlv]; exact eL
  have hsent : First.FillSent.sentIsB h.𝔇.pubD.dS l s = true := K1.sentIs_at_reads_b h l hl
    ((μ.st.input.x.pub, s), σ) (hIn (strsOf _ σ)).1 hm
  have hSy : K1.SymsIn (h.𝔇.N.sent l 0) A tlW := K1.symsIn_of_B (by rw [harr, eS', eL']; exact hB) hF
  refine ⟨A, B, hA, hB', hR, by rw [hst]; exact hcs k s μ E hT, fun ν hν => ?_⟩
  have hνW : ν < tlW.NM := hNM ▸ hν
  obtain ⟨Ar, hAr⟩ := Option.isSome_iff_exists.1 (hSy ν hνW)
  obtain ⟨c₁, o, q, h1, h2, h3, h4⟩ := K9.arrayIn_some _ A _ Ar hAr
  have hcon : (h.𝔇.N.sent l 0).contains q = true := by
    have e := K9.seatAt_mem _ _ _ _ h4
    exact List.contains_iff_mem.2 e
  have hq : A.d.book.place[o]? = some q := by
    unfold K9.seatAt at h4
    obtain ⟨y', hy', e⟩ := Option.bind_eq_some_iff.1 h4
    by_cases hc : (h.𝔇.N.sent l 0).contains y' = true
    · rw [if_pos hc] at e
      rw [hy', Option.some.inj e]
    · rw [if_neg hc] at e
      cases e
  have hqs : s.book.place[o]? = some q := by rw [← hbk]; exact hq
  have hosz : o < s.st.oracles.size := by
    have e : s.book.place.size = s.st.oracles.size := (K1.inAt_book (hIn (strsOf _ σ))).1
    have : o < s.book.place.size := (Array.getElem?_eq_some_iff.1 hqs).1
    omega
  have hsh₀ := K12.Door.msgShape_at (show K12.Door.msgShapesB K13.Law.d12Full.M s.st = true from Fk.shapes) o hosz
  cases hxo : s.st.oracles[o]? with
  | none =>
    have := (Array.getElem?_eq_none_iff.1 hxo)
    omega
  | some x₀ =>
    rw [hxo] at hsh₀
    have hM : K13.Law.d12Full.M[o]? = some x₀.shape := hsh₀.symm
    have hLq : K13.Law.d12Full.L.places[o]? = some q := by
      have e : K12.Door.atFirstSeats K13.Law.d12Full.L s = true := Fk.seats
      unfold K12.Door.atFirstSeats K12.Door.seatsCarriedB at e
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at e
      have e1 : s.book.place.toList = K13.Law.d12Full.L.places.take s.book.place.size := e.1.1.1
      have e2 : s.book.place.toList[o]? = some q := by rw [Array.getElem?_toList]; exact hqs
      rw [e1, List.getElem?_take_of_lt (Array.getElem?_eq_some_iff.1 hqs).1] at e2
      exact e2
    obtain ⟨yM, l₀, ν₀, hy, hsh, hlaid, hO, hShape, hroom⟩ := hPub ν hν c₁ Ar o q x₀.shape
      (by rw [← harr]; exact h1) (by rw [← eL']; exact h2)
      (by rw [← First.FillSent.whereIs_of_sentIs hLa hsent]; exact h3) hLq hM hcon
    have hseat : seatBy noFirst A.d.book o = some q := by
      have ebk : K12.Door.atFirstBook K13.Law.d12Full.ft s = true := Fk.book
      have efit : K12.Door.atFirstFits s = true := Fk.fits
      rw [hbk]
      unfold seatBy noFirst
      rw [hqs]
      show (s.book.trees[q.1]?).map _ = _
      unfold K12.Door.atFirstFits Sound.bookFitsB at efit
      have e0 := List.all_eq_true.1 efit o (List.mem_range.2 (Array.getElem?_eq_some_iff.1 hqs).1)
      rw [hqs] at e0
      cases ht : s.book.trees[q.1]? with
      | none =>
        have e0' : (match s.book.trees[q.1]? with
          | some t => decide (t.parts[q.2]? = some o)
          | none => false) = true := e0
        rw [ht] at e0'
        cases e0'
      | some t =>
        unfold K12.Door.atFirstBook K12.Door.bookInOrderB at ebk
        simp only [Bool.and_eq_true] at ebk
        have hlt := (Array.getElem?_eq_some_iff.1 ht).1
        have e1 := List.all_eq_true.1 ebk.2 q.1 (List.mem_range.2 hlt)
        rw [ht] at e1
        have e2 : t.number = K13.Law.d12Full.ft + q.1 := by simpa using e1
        have e3 : t.number = q.1 := by
          rw [e2]
          show 0 + q.1 = q.1
          exact Nat.zero_add _
        show some (t.number, q.2) = some q
        rw [e3]
    refine ⟨q, yM, o, x₀, x₀.shape, c₁, Ar, l₀, ν₀, hcon, by rw [hst]; exact hxo, rfl, hq, hseat, hy, hsh,
      by rw [hgt]; exact h1, h2, h3, ?_, hO, hShape, hroom⟩
    rw [hst]
    unfold Statement.rowBits Statement.placeBits
    rw [hxo]
    have hcc : s.st.codes = cs := hcs k s μ E hT
    simp only [hcc]
    exact hlaid

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.matSeatF_head
