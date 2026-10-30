-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/ReadsStepAtHead.lean: THE KIND K1's SHARES AT THE ITEMS "forms
m piece run", AT THE 25 READS' MEMBERS, AT ProofFile's lettersHead: THE PREMISE ReadsStepS OF
exchangeAtS_forms (Honest/K1/Law/FormsShare.lean), PAID UNDER THE LIBRARY's HEAD ALONE. PUBLIC: NO
WITNESS IN IT. Six theorems; no definition.

THIS LETTER IS FOR THE HONEST RUN's OWN FORMS ALONE: NO STATEMENT ON ANY OTHER PARTY MAY TAKE IT.
NEVER ON SOUNDNESS's ROAD. (A fence. WHY IT BINDS HERE:
five of the six laws TAKE the thread's invariant Thr, whose clause on the promise stands at L.mgP,
the meaning adapted to the honest side, which asks less than the library's own. They GIVE no
sentence at that meaning: of that clause they spend, through another house's partsAt_of_thr, what
reads the verifier's state alone, at the library's own meaning L.MgP.)

WHAT THE THREAD's INVARIANT GIVES OF THE STATE IN FRONT, at lettersHead, under h (A HYPOTHESIS):
  - reach_head    the state is reached in the library's sense: ProofFile's reach_of_made
                  (Honest/Thread/MadeLaw.lean) at the clause Made.
  - frameShape_head    at a border up to 353: the open link's frame's shape is h.𝔇.shape: ALONG
                  THE VERIFIER's RUN: the sealed liveShape_inFront (Johnson/IMR/AtReach.lean),
                  live_link and front_len. No meaning stands in it.
  - pubs_head     every public item that is open or tied at the border passes pubAll h.𝔇.pubD
                  mgBase.pub: part 4's partsAt_of_thr (Honest/Small/FormParts.lean: PartsAt.pub),
                  with the sealed mgAll_more_base and mgMore_is.
  - book_head     the test on the book (bookAt) at the border: PartsAt.book.
AND ONE FACT ON THE TABLE:
  - formsT_in_rowQ   at a run of the row, formsT l j n is among what the library's own rowQ closes
                  at the reads' number: so the sealed formsInT_of_ins
                  (Johnson/Desc/K1/Law/HbackMw1.lean) has the public item formsInT l j n tied
                  there.
THE END:
  - readsStepS_head  UNDER h, l < 25, (j, n) ∈ earlyRuns (subAt l): ReadsStepS at lettersHead, at
                  the member number K1.noL l false, the segment l, the library's own letters of the
                  forms. ITS SIX CONJUNCTS: RecRides and Booked: the sealed laterSend_blkL · Grows:
                  laterGrows_k1Reads · the book has a place for every message: book_head · the new
                  seats lie in the group: seats_new, seats_in_group, hP_of (planK1_head) ·
                  SecondFound: our sealed found_later_all · ReadersStay: our sealed
                  readers_later_all. THE PAYERS UNDER THE HEAD ARE THOSE OF OUR SEALED
                  pub_later_head (Honest/K1/Law/PubBehindAtFifty.lean), which took the frame's
                  shape and "reached at 342" as premises: HERE THE THREAD PAYS BOTH.

Limits. IT PAYS A PREMISE's FORM, NOT A SHARE. ThrS and Stepped stand in ReadsStepS as hypotheses:
no law says that the thread holds at any run. THE FULL SIZE, THE FORMAT's EARLIER HASH. Nothing on
any property. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormsReadsPublic
import Johnson.Desc.ProofFile.Honest.K1.Law.YesAtFifty
import Johnson.Desc.ProofFile.Honest.K1.Law.PubBehindAtFifty
import Johnson.Desc.ProofFile.Honest.Small.FormParts
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.K1.Law.HbackMw1
import Johnson.Desc.First.Link.Law.PartFitsReached
import Johnson.Desc.Sound.MgBase
import Johnson.IMR.AtReach
import Johnson.IMR.FinPin
import Johnson.IMR.RootsWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Strs Place)
open VerifiableInference.Desc.First (Item Pub earlyRuns flatPlacesOf pubAll)
open VerifiableInference.Desc.Sound (MsgT uBySort linksFull moreAll mgBase rowQ)
open VerifiableInference.Desc.K13.Law (openAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.Small (partsAt_of_thr)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- At a run of the row, formsT is among what the library's own row closes at the reads' number. -/
theorem formsT_in_rowQ {l : ℕ} (hl : l < 25) {j : ℕ} {n : String}
    (h : (j, n) ∈ earlyRuns (IM.subAt l)) :
    Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (K1.noL l false)).ins := by
  unfold rowQ
  rw [show (flatPlacesOf linksFull true)[K1.noL l false]? = _ from place_reads hl]
  show Item.formsT l j n ∈ (First.rowOf linksFull
    { chain := 1, link := some l, piece := 4 + First.shift (IM.subAt l), kind := .K1 }).ins
  unfold First.rowOf
  simp only [show linksFull[l]? = some (IM.subAt l) from links_reads hl]
  exact formsT_in_of h l

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **WHERE THE THREAD HOLDS THE STATE IS REACHED.** -/
theorem reach_head {b : Nat} {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s μ E) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (μ.st.input.x.pub, s) :=
  reach_of_made (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (ProofFile.startS Zp)
    μ.st.input.x.pub hb (fun _ e => e) hT.2.2.2.2.1

/-- **THE OPEN LINK's FRAME's SHAPE IS THE PLAN's**, at a border up to 353: along the run. -/
theorem frameShape_head {b : Nat} {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hb : b ≤ 353)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s μ E) :
    ∀ Lk, s.link? = some Lk → Lk.check.frame.shape = h.𝔇.shape := by
  intro Lk hLk
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hf := Meaning.K2.front_len h.scope h.reads O
  have hlen : b ≤ cF.blocksInOrder.length := by
    have := Meaning.Carry.flat_len h.scope h.reads O
    omega
  have hm := (partsAt_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT).1
  rw [← LinkJoin.live_link hLk,
    Meaning.K2.liveShape_inFront h.scope h.reads O
      (reach_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT) hm (by rw [hf]; exact hb),
    K1.hDsh_atAll h O (K1.pin1_atAll h)]
  show Zp.first.shape = _
  rw [← O.first]
  exact K1.hs_atAll h O (K1.pin1_atAll h)

/-- **EVERY PUBLIC ITEM THAT IS OPEN OR TIED AT THE BORDER PASSES.** -/
theorem pubs_head {b : Nat} {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s μ E) :
    ∀ q ∈ (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[b]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) b),
      pubAll h.𝔇.pubD (mgBase : First.Meaning ProofFile.InstPub WtF).pub q (μ.st.input.x.pub, s) =
        true := by
  intro q hq
  refine (partsAt_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT).2.pub q ?_
  rw [show (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).MgP.more = moreAll from
    Sound.mgAll_more_base h.𝔇]
  exact hq

/-- **THE TEST ON THE BOOK AT THE BORDER.** -/
theorem book_head {b : Nat} {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s μ E) :
    First.bookAt h.𝔇.N (flatPlacesOf linksFull true)[b]? s = true :=
  (partsAt_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT).2.book

/-- **ReadsStepS AT lettersHead, UNDER THE HEAD ALONE.** -/
theorem readsStepS_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : ℕ}
    (hl : l < 25) {j : ℕ} {n : String} (hjn : (j, n) ∈ earlyRuns (IM.subAt l)) :
    ReadsStepS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said
      ⟨h.𝔇.pubD, h.𝔇.ms, h.𝔇.St, uBySort h.𝔇.uL h.𝔇.uA h.𝔇.uH, h.𝔇.after, h.𝔇.wt, h.𝔇.rw⟩
      (K1.noL l false) l j n := by
  intro blk hblk k s μ E ds y cols s' hT _ hS
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hb : cF.blocksInOrder[K1.noL l false]? = some blk := hblk
  have hno : K1.noL l false ≤ 353 := by
    have : IM.k1Ix l false ≤ 4 := by
      by_cases h24 : l = 24 <;> simp [IM.k1Ix, h24]
    show 14 * l + IM.k1Ix l false + 2 ≤ 353
    omega
  obtain ⟨X', arrs, r₁, r₂, gs, -, hY, hdec⟩ :=
    yesOf_reads_two h O hl hb (yes_of_stepped _ hS) μ.st.input.x.pub
  have hbk := book_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1
  have hbk' := hbk
  unfold First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  obtain ⟨⟨htr, hfull⟩, -⟩ := hbk'
  obtain ⟨-, hRR, hBk⟩ := K1.laterSend_blkL Zp Bs.G₀ l false X' arrs s s' [r₁, r₂] gs rfl hdec
  have hPl := planK1_head h O
  have hs := K1.hs_atAll h O (K1.pin1_atAll h)
  obtain ⟨-, hSo, -⟩ := sides_later_head h O
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hsh := frameShape_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hno hT.1
  have hF := pubs_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1
  have hlen : K1.noL l false ≤ cF.blocksInOrder.length := by
    have := Meaning.Carry.flat_len h.scope h.reads O
    omega
  have hR := reach_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT.1
  refine ⟨(K1.idsOf (K1.parL Zp Bs.G₀ l false) s.st.oracles.size).toList, hRR,
    K1.laterGrows_k1Reads Zp Bs.G₀ l X' _ arrs s s' [r₁, r₂] gs hdec, hfull, ?_, ?_, ?_⟩
  · exact K1.seats_new hBk hfull _ (by
      rw [htr]
      exact K1.seats_in_group h.𝔇.N (K1.parL Zp Bs.G₀ l false) l 1 _ (by decide)
        (K1.hP_of hPl hs l hl false))
  · exact found_later_all h.𝔇 _ Zp Bs.G₀ l hl X' arrs _ _ hY hF hsh
      (K1.hAt_scope h.𝔇 (K1.hDsh_atAll h O (K1.pin1_atAll h)) Zp Bs.G₀ hs l hl)
  · exact (readers_later_all h.𝔇 h.scope h.reads O (K1.hDlk_atAll h) (K1.hlk_atAll h)
      ((K1.sortB_iff _).1 hSo) (by rw [eW]; exact ⟨rfl, rfl, rfl⟩) l hl false X' arrs _ _ hY
      (fun h1 _ => K1.tablesOk_of_no _ _ _ _ (K1.no_tables_342 h.scope h.reads O _ (by
        subst h1
        exact hR))) l j n
      (Or.inr (List.mem_append_right _ (K1.formsInT_of_ins l hl j n (formsT_in_rowQ hl hjn))))).2

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.formsT_in_rowQ
#print axioms ProofFile.Honest.K1.reach_head
#print axioms ProofFile.Honest.K1.frameShape_head
#print axioms ProofFile.Honest.K1.pubs_head
#print axioms ProofFile.Honest.K1.book_head
#print axioms ProofFile.Honest.K1.readsStepS_head
