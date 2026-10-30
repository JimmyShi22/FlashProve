-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/AcrossOfSits.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's
FIRST CHAIN: what the fifth tie spends of the two states at an accept of the test (Across,
H2K12/Rides354.lean) FOLLOWS FROM the piece's make, the table's promise in
front and four facts on the state in front. Definitions, statements and proofs.
Main names:
  FactsF          the four facts: tests with code that stand as fields of FoldFacts
                  (Johnson/Desc/First/FoldFacts.lean): the book is in order, the seats are carried,
                  the book fits, the pending rows name the index masks' message alone.
  factsF_of_fold  FactsF from FoldFacts.
  sampled_of_held, mask_unsampled, sampled_no_mask   the index masks' message is not the message
                  that holds the test's first fold's mask: the promise says that the state holds the
                  first one's out-of-domain (OOD) sample (samplesHeld,
                  Johnson/Desc/First/Borders.lean; smpHeld, Johnson/Desc/SmpRows.lean), so it is
                  marked as sampled; the test's own front (frontL, Johnson/Desc/K12/Front.lean;
                  block_front_holds, Johnson/Desc/K12/SeatLaws.lean) accepts no mask's message that
                  is.
  across_of_sits  Across, field by field. The accept is carried to the kind's own decision
                  (yes_step, step_of_held, step_decide: Johnson/Desc/K12/Coin/; Sits:
                  Johnson/Desc/K12/Law/Sits.lean); the way out lays the statement, the book and the
                  count of roots alone (LaysOnly, Johnson/Desc/K12/Coin/K12Grows.lean). The codes
                  and the book: k12_out (Johnson/Desc/K12/Law/OutK.lean). The message's shape and
                  what a reader of its OOD sample reads: k12_smp
                  (Johnson/Desc/K12/Coin/SamplesThrough.lean), which speaks of every older message
                  but the first mask: hence the three lemmas above; then smpAt_congr
                  (Johnson/Desc/Sound/SmpShared.lean). Where the message sits: promise_index
                  (Johnson/Desc/K13/Law/AtTable.lean) and indexSeat_of_carried
                  (Johnson/Desc/K1/Law/IndexSeatCarried.lean).
  rides_of_facts  THE FIFTH TIE (T5At, H2K12/Frame354.lean) with FactsF in the
                  place of Across.
  pinI_open_written   at the written lists the index masks' pin is open in front of number 354:
                  decided by the kernel.
Limits. (1) A JOINING OVER LETTERS. FactsF is a premise, asked at every state inside the promise and
the condition Rch, without a mark. (2) hsmp (the reader of samples is K1.smpAt at a listed message),
hII, hIT, hheld (three equations on the meaning's public tests), hL (a number of the list of
places), hft (the chain's first tree has the number 0) are premises on letters. (3) WHETHER ALL
PREMISES CAN BE MET TOGETHER IS SHOWN NOWHERE HERE. No soundness statement. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.HeldYes
import Johnson.Desc.K12.Coin.MaskOfYes
import Johnson.Desc.K12.Coin.K12Grows
import Johnson.Desc.K12.Coin.SamplesThrough
import Johnson.Desc.Sound.SmpShared
import Johnson.Desc.Sound.BookTestsLaw
import Johnson.Desc.K13.Law.AtTable
import Johnson.Desc.K13.Law.FillK13Laws
import Johnson.Desc.K13.Law.PileMasksIff
import Johnson.Desc.K1.Law.IndexSeatCarried
import Johnson.Desc.K12.Coin.BookRides
import Johnson.Desc.K12.Door.DoorIs
import Johnson.Loose.H2K12.Promise354
import Johnson.Loose.H2K12.Rides354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (FileDescription Wit Place Block)
open VerifiableInference.Desc.Sound (Mem Sending MsgT seatOf strsOf)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)

/-- **What the fifth tie spends of a reached, unmarked state in front of the test.** -/
structure FactsF (d : VerifiableInference.Desc.First.FoldData)
    (s : VerifiableInference.Desc.First.S) : Prop where
  /-- FoldFacts.bookInOrder -/
  book : VerifiableInference.Desc.K12.Door.atFirstBook d.ft s = true
  /-- FoldFacts.seatsCarried -/
  seats : VerifiableInference.Desc.K12.Door.atFirstSeats d.L s = true
  /-- FoldFacts.bookFits -/
  fits : VerifiableInference.Desc.K12.Door.atFirstFits s = true
  /-- FoldFacts.pileMasks -/
  masks : VerifiableInference.Desc.K13.pileMasksC s = true

/-- Where the state holds a tenant's out-of-domain (OOD) sample and the book fits, the message that
has the tenant's place is marked as sampled. -/
theorem sampled_of_held {st : OnBytes.Statement} {book : OnBytes.TreeBook} {q : ℕ × ℕ} {i : ℕ}
    (hb : VerifiableInference.Desc.Book.BookFits book)
    (h : VerifiableInference.Desc.smpHeld st book q.1 q.2 = true) (hi : book.place[i]? = some q) :
    ∃ x, st.oracles[i]? = some x ∧ x.sampled = true := by
  unfold VerifiableInference.Desc.smpHeld VerifiableInference.Desc.smpSeed at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨i', ho, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨rows, hr, _⟩ := Option.bind_eq_some_iff.1 hv
  have hp : book.place[i']? = some (q.1, q.2) := by
    unfold VerifiableInference.Desc.oracleNo at ho
    have := List.find?_some ho
    simpa using this
  obtain rfl : i' = i := VerifiableInference.Desc.Book.places_inj hb hp hi
  unfold VerifiableInference.Desc.smpRows at hr
  rw [ho, Option.bind_some, hx, Option.bind_some] at hr
  split at hr
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact ⟨x, hx, hc.1.1⟩
  · cases hr

/-- By the clauses at the test's front: the message that holds the first fold's mask is not marked
as sampled. -/
theorem mask_unsampled {St : OnBytes.Statement} {B : OnBytes.TreeBook} {g : ℕ} {mask : Option ℕ}
    (h : ∀ c ∈ VerifiableInference.Desc.K12.frontL St B g mask, c.2 = true) {m : ℕ}
    (hm : mask = some m) (x : OnBytes.Oracle) (hx : St.oracles[m]? = some x) :
    x.sampled = false := by
  have := h ("front: the mask's message is not sampled",
    VerifiableInference.Desc.Ground.on (mask.bind fun m => St.oracles[m]?) (!·.sampled))
    (by simp [VerifiableInference.Desc.K12.frontL])
  subst hm
  simpa [hx, VerifiableInference.Desc.Ground.on] using this

/-- So a message that is marked as sampled is not the one that holds the first fold's mask. -/
theorem sampled_no_mask {St : OnBytes.Statement} {B : OnBytes.TreeBook} {g : ℕ} {mask : Option ℕ}
    (h : ∀ c ∈ VerifiableInference.Desc.K12.frontL St B g mask, c.2 = true) {i : ℕ}
    {x : OnBytes.Oracle} (hx : St.oracles[i]? = some x) (hs : x.sampled = true) :
    mask ≠ some i := by
  intro hm
  have h2 := mask_unsampled h hm x hx
  rw [hs] at h2
  cases h2

/-- FactsF out of FoldFacts (Johnson/Desc/First/FoldFacts.lean): four of its fields. -/
theorem factsF_of_fold {X P : Type} {Rch : ℕ → X → Prop}
    {at_ : X → P × VerifiableInference.Desc.First.S} {d : VerifiableInference.Desc.First.FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (hf : VerifiableInference.Desc.First.FoldFacts Rch at_ d reqW links ps) (k : ℕ) (a : X)
    (hr : Rch k a) (hm : (at_ a).2.failed = none) : FactsF d (at_ a).2 :=
  ⟨hf.bookInOrder k a hr hm, hf.seatsCarried k a hr hm, hf.bookFits k a hr hm,
    hf.pileMasks k a hr hm⟩

section
variable {P W Cl : Type} {Fr : VerifiableInference.Desc.Sound.Frame} (cs : OnBytes.Codes)
  (π : VerifiableInference.Desc.K12.P12) (d : VerifiableInference.Desc.First.FoldData)
  (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)

/-- **WHAT AN ACCEPT OF THE TEST LEAVES, FROM THE PIECE's MAKE, THE PROMISE AND FactsF.** -/
theorem across_of_sits (k : ℕ)
    (q : VerifiableInference.Desc.Sound.Piece (_root_.Run.ckP .two) Fr
      (P × VerifiableInference.Desc.First.S) Cl W)
    (B : Block VerifiableInference.Desc.First.S Cl)
    (leave : VerifiableInference.Desc.First.S → VerifiableInference.Desc.K12.T12 →
      Except String VerifiableInference.Desc.First.S)
    (hb : q.b = VerifiableInference.Desc.Sound.held (P := P) B) (h0 : q.back = [])
    (hS : H2K.JointK.Sits B (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      π : Block VerifiableInference.Desc.K12.T12 Unit) VerifiableInference.Desc.K12.enterFinish
      leave)
    (hl : VerifiableInference.Desc.K12.Coin.LaysOnly leave) (he : π.early = true)
    (ha : π.answers = 1)
    (hpinI : Item.pinI ∈ VerifiableInference.Desc.K13.Law.openAt links ps k)
    (hII : ∀ x, Mg.pub .indexIs x = VerifiableInference.Desc.K13.indexIsC N.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = VerifiableInference.Desc.K13.indexThereC x.2)
    (hheld : Mg.held = fun j t x => VerifiableInference.Desc.smpHeld x.2.st x.2.book j t)
    (hL : d.L.places[N.indexNo]? = some N.index) (hft : d.ft = 0)
    (hsmp : ∀ a o x, ListedAt ms d.L.places o x → smp a x.1 x.2 =
      VerifiableInference.Desc.K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 a.2.st o)
    (a b : (P × VerifiableInference.Desc.First.S) × Fr.E.Str)
    (τ : Iop.Tr (OnBytes.Maker.uLT (_root_.Run.ckP .two) q.ds))
    (hon : VerifiableInference.Desc.Sound.onQ N Mg links ps
      (fun x : P × VerifiableInference.Desc.First.S => x) k a)
    (hm : a.1.2.failed = none) (hout : q.ior.red.out a τ = some b) (F : FactsF d a.1.2) :
    Rid354.Across cs smp ms N a b := by
  -- the accept, at the kind's own decision
  obtain ⟨_, n, hst, _⟩ := VerifiableInference.Desc.K12.Coin.yes_step q h0 a τ b hout
  rw [hb] at hst
  obtain ⟨h1, hpub⟩ := VerifiableInference.Desc.K12.Coin.step_of_held B Fr.ft a.1 b.1 _ _ n hst
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step Fr.ft _ _ _ _ n h1
  obtain ⟨gs, hd⟩ := VerifiableInference.Desc.K12.Coin.step_decide _ Fr.ft t t' _ _ n e2
  have eb := hl _ _ _ e3
  obtain ⟨o, _, _, _, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok a.1.2 t e1
  have O := H2K.Out.k12_out π he ha _ t' _ gs hd
  -- where the index masks' message sits, by the promise
  obtain ⟨hii, hit, hbk, _⟩ := VerifiableInference.Desc.K13.Law.promise_index N Mg links ps
    (fun x : P × VerifiableInference.Desc.First.S => x) k hpinI a hon hm
  have hI : VerifiableInference.Desc.K1.indexIsB N.indexNo a.1.2 = true := by
    rw [← VerifiableInference.Desc.K13.Law.indexIsC_eq, ← hII]
    exact hii
  have hT : VerifiableInference.Desc.K1.indexThereB a.1.2 = true := by
    rw [← VerifiableInference.Desc.K13.Law.indexThereC_eq, ← hIT]
    exact hit
  have hbk' := hbk
  unfold VerifiableInference.Desc.First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  have hseat : a.1.2.book.place[a.1.2.out.indexMasks]? = some N.index :=
    eq_of_beq (VerifiableInference.Desc.K1.indexSeat_of_carried
      ((VerifiableInference.Desc.K12.Coin.seatsPrefix_iff
        (VerifiableInference.Desc.K12.Door.toTree d.L) _).1 F.seats) hbk'.1.2 hT hI hL)
  have hthere : a.1.2.out.indexMasks < a.1.2.st.oracles.size := by
    have e : (a.1.2.st.oracles[a.1.2.out.indexMasks]?).isSome = true := hT
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 e
    exact (Array.getElem?_eq_some_iff.1 hx).1
  have hBF := (VerifiableInference.Desc.Sound.bookFitsB_iff a.1.2.book).1 F.fits
  -- the index masks' message is not the message that holds the first fold's mask
  have hmk : o.mask ≠ some a.1.2.out.indexMasks := by
    intro hmask
    have hSH : VerifiableInference.Desc.First.samplesHeld N Mg
        (VerifiableInference.Desc.K13.Law.openAt links ps k) a.1 = true :=
      ((hon.2.resolve_left fun h => h hm).2).1
    have h1 := List.all_eq_true.1 hSH N.index (List.mem_flatMap.2 ⟨.pinI, hpinI, by simp⟩)
    rw [hheld] at h1
    obtain ⟨x, hx, hs⟩ := sampled_of_held hBF h1 hseat
    exact sampled_no_mask
      (VerifiableInference.Desc.K12.Seat.block_front_holds π _ t' _ gs hd).2.1 hx hs hmask
  have hsp : (b.1.2.st.oracles[a.1.2.out.indexMasks]?).map
      VerifiableInference.Desc.K12.Coin.smpPart =
      (a.1.2.st.oracles[a.1.2.out.indexMasks]?).map VerifiableInference.Desc.K12.Coin.smpPart := by
    rw [eb]
    exact VerifiableInference.Desc.K12.Coin.k12_smp π he ha _ t' _ gs hd _ hthere hmk
  -- the tree at that place
  obtain ⟨T, hTr, -⟩ := hBF _ _ hseat
  obtain ⟨T', hTr', -, hnum, -⟩ := O.book.tree _ T hTr
  have hsa : VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst a.1.2.book
      a.1.2.out.indexMasks = some (T.number, N.index.2) :=
    VerifiableInference.Desc.Sound.seatBy_some _ a.1.2.book _ N.index T hseat hTr
  refine ⟨hpub, fun z hz hs => ?_, by rw [eb]; rfl, by rw [eb], 
    (VerifiableInference.Desc.K13.Law.pileMasksC_iff a.1.2).1 F.masks, by rw [eb]; exact O.codes,
    ?_, ?_, fun q' hq' => ?_⟩
  · have hl' : ListedAt ms d.L.places a.1.2.out.indexMasks z := by
      refine ⟨hz, ?_⟩
      have es : seatOf z = N.index := hs
      rw [es]
      exact place_listed d.L a.1.2 F.seats _ _ hseat
    rw [hsmp b.1 _ z hl', hsmp a.1 _ z hl']
    exact VerifiableInference.Desc.Sound.smpAt_congr cs _ _ a.1.2.st b.1.2.st _ hsp
  · have := congrArg (Option.map fun x : OnBytes.OracleShape × Bool × Array OnBytes.Row => x.1) hsp
    rwa [Option.map_map, Option.map_map] at this
  · rw [hsa, eb]
    show VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst t'.book
      a.1.2.out.indexMasks = _
    rw [VerifiableInference.Desc.Sound.seatBy_some _ t'.book _ N.index T'
      (O.book.place _ _ hseat) hTr']
    show some (T'.number, N.index.2) = some (T.number, N.index.2)
    rw [hnum]
  · rw [hsa] at hq'
    have h2 := bookOrd_of d.ft a.1.2 F.book _ T hTr
    rw [hft, Nat.zero_add] at h2
    rw [← Option.some.inj hq', h2]

end

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok Cl : Type} {nR kk : ℕ}
  (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × VerifiableInference.Desc.First.S → Tok) (N : Numbers)
  (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
  {Fr : VerifiableInference.Desc.Sound.Frame}
  (mat : Cells → Fin nR → (Fin kk → Bool) → OnBytes.Slice.GE)

/-- **THE FIFTH TIE, WITH FactsF AT EVERY REACHED, UNMARKED STATE INSIDE THE PROMISE IN THE PLACE OF
Across.** -/
theorem rides_of_facts (k : ℕ) (hp : ps[k]? = some Rid354.pK)
    (hrid : Rid354.ridersB links ps k = true)
    (hro : VerifiableInference.Desc.First.readsOpen links ps
      (VerifiableInference.Desc.First.start links) = true)
    (hra : VerifiableInference.Desc.Sound.rowsApart links ps = true)
    (hpinI : Item.pinI ∈ VerifiableInference.Desc.K13.Law.openAt links ps k)
    (hcl : Rid354.clearB arr N links ps k = true)
    (hpin : Mg.pin = VerifiableInference.Desc.Sound.pinJT cs G arr smp ms)
    (hpinW : Mg.pinW = VerifiableInference.Desc.Sound.pinWOf decT)
    (hpile : Mg.pile = fun x _ w => VerifiableInference.Desc.K13.Law.RowsTrue
      (VerifiableInference.Desc.K13.Law.rwBook arr mat x) x.2 w)
    (hdec : VerifiableInference.Desc.K13.Law.DecBlind decT)
    (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (q : VerifiableInference.Desc.Sound.Piece (_root_.Run.ckP .two) Fr
      (P × VerifiableInference.Desc.First.S) Cl (Wit Cells Tok MsgT))
    (hfen : N.index.1 < q.base) (π : VerifiableInference.Desc.K12.P12)
    (d : VerifiableInference.Desc.First.FoldData)
    (B : Block VerifiableInference.Desc.First.S Cl)
    (leave : VerifiableInference.Desc.First.S → VerifiableInference.Desc.K12.T12 →
      Except String VerifiableInference.Desc.First.S)
    (hb : q.b = VerifiableInference.Desc.Sound.held (P := P) B) (h0 : q.back = [])
    (hS : H2K.JointK.Sits B (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      π : Block VerifiableInference.Desc.K12.T12 Unit) VerifiableInference.Desc.K12.enterFinish
      leave)
    (hl : VerifiableInference.Desc.K12.Coin.LaysOnly leave) (he : π.early = true)
    (ha : π.answers = 1)
    (hII : ∀ x, Mg.pub .indexIs x = VerifiableInference.Desc.K13.indexIsC N.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = VerifiableInference.Desc.K13.indexThereC x.2)
    (hheld : Mg.held = fun j t x => VerifiableInference.Desc.smpHeld x.2.st x.2.book j t)
    (hL : d.L.places[N.indexNo]? = some N.index) (hft : d.ft = 0)
    (hsmp : ∀ a o x, ListedAt ms d.L.places o x → smp a x.1 x.2 =
      VerifiableInference.Desc.K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 a.2.st o)
    (hFacts : ∀ a : (P × VerifiableInference.Desc.First.S) × Fr.E.Str,
      VerifiableInference.Desc.Sound.onQ N Mg links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k a → Rch k a →
      ¬ a.1.2.failed ≠ none → FactsF d a.1.2) :
    T5At N Mg links ps Rch k q
      (VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT c₀ tokOf N links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k) :=
  Rid354.rides_at cs G arr smp ms decT c₀ tokOf N Mg links ps mat k hp hrid hro hra hcl hpin hpinW
    hpile hdec Rch q hfen fun a τ b hon hr hm hout _ =>
      across_of_sits cs π d smp ms N Mg links ps k q B leave hb h0 hS hl he ha hpinI hII hIT hheld
        hL hft hsmp a b τ hon (not_not.1 hm) hout (hFacts a hon hr hm)

end

set_option maxRecDepth 1000000 in
/-- By the kernel: at the written lists the index masks' pin is open in front of number 354. -/
theorem pinI_open_written : Item.pinI ∈ VerifiableInference.Desc.K13.Law.openAt
    VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
    354 := by decide +kernel

end H2K12

#print axioms H2K12.sampled_of_held
#print axioms H2K12.mask_unsampled
#print axioms H2K12.sampled_no_mask
#print axioms H2K12.factsF_of_fold
#print axioms H2K12.across_of_sits
#print axioms H2K12.rides_of_facts
#print axioms H2K12.pinI_open_written
