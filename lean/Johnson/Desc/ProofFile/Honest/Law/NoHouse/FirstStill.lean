-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/FirstStill.lean: THE RECORD `NoHouse`
(Honest/Law/NoHouse/Bare.lean) AT THE FIRST CHAIN's FRONT, «start:0» (number 0 of the 358; place ⟨1,
none, 0, frame⟩), AND AT «link l: laid», AT EACH OF THE 25 LINKS (number 14 l + 1; place ⟨1, some l,
0, frame⟩): at the first chain's thread at the library's head (`lettersHead`,
Honest/Thread/FirstHead.lean), GENERAL IN l, under named premises. Members without a round WHOSE YES
HANDS THE STATE ON AS IT IS (the front asks nothing; «laid» is three tests: `Law.layFront_ok`,
Johnson/Top/H0/Walk/FrameLaw.lean).

WHAT THIS IS. Conditional lemmas on definitions of ours and on the library's own texts. None of the
library's goals.

  1  GENERAL IN THE FIRST CHAIN's LETTERS: `form_next_still` ((P) one border on, at the state as it
     was, at a row that closes and opens nothing: `form_next_quiet` at s' := s, its
     premises from the library's `NoneBetween` and `DoorIdle`, Johnson/Top/H0/Walk/FrameTied.lean) ·
     `form_between` · `row_still_owes` · `between_of_stand` · `shape_front`, `shape_laid` (the
     book-keeping's Bool one border on: the arguments stand inside the library's `step_front`,
     `step_laid`, FrameTiedLaid.lean: typed out here as lemmas) · `noHouse_first_still`
  2  AT THE HEAD: `noHouse_start0`, `noHouse_laid`

WHICH FIELDS FALL OUT OF THE LIBRARY's OWN LAWS, AND WHICH ARE CONTENT.
  seat     A CALL: `IM.front_of` · `IM.frame_of`, at the head's own opening.
  bare     no round, no oracle message: CALLS (`IM.front_oracles`, `IM.frame_oracles`); the place:
           `IM.place_at`; «no half stands there»: a premise on the prover (noHalf).
  behind   (P) one border on: PAID: the places (`P1L20.front_places_full`, `places_full`), «no tree
           and no message between» (`P1L20.still_atAll`) and «no public item is made»
           (`P1L20.door_idle9`) are laws at the head. The reply's rider: from b₀ ≠ the
           border behind. The other riders and the place's clause of «keeps», at a state that does
           not turn: premises on letters (hRd, hKp).
  owes     NOTHING IS OWED: the table's rows there are empty.
  yes      AT THE FRONT: PAID OUTRIGHT: no premise of content. AT «laid» the block's yes is the
           library's `Props.LayFront l s` (`layFront_iff`, Johnson/Top/H0/Walk/FrameProps.lean):
           three tests. THE FIRST IS PAID: «no link is open in the record»: (P)'s book-keeping at
           that place says that the chain stands between two links (`form_between`). **CONTENT:
           asks: THE OTHER TWO AT THE THREAD's STATE: a link's first call is due (`FirstDue
           s.check`) · the chain stands at link l (`s.check.frame.link = l`)**: they read the
           record's field check, which no Bool of the promise that we have read names. No mark: from
           (P). The reply as it was: `IM.sameReply_self`.
  said, rides   PREMISES, as the record has them.

MET FOR NOTHING. As `NoHouse`. Limits. THE FULL SIZE ALONE, and the format's second hash function alone, as
the head. The library's head has a member at the name under four premises on the public files (the
seal's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of our files calls it; no
member of the head TOGETHER WITH the thread's sentence is shown. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Later
import Johnson.P1L20R.FramePaidAll
import Johnson.P1L20R.FrameAt9
import Johnson.IMR.FrameQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Place Strs Wit KindName)
open VerifiableInference.Desc.First (S ModelPart Item Pub Numbers Meaning onAt openSets pubSets start
  rowOf segRow quietRow shapeAt standAt standOf Stand mayWait pubHeld bookAt)
open VerifiableInference.Desc.K13.Law (stepOpen_empty)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk (layFront)
open Johnson.Desc.First.Walk.Props (LayFront FirstDue layFront_iff)
open Johnson.Desc.First.Walk.Tied (NoneBetween DoorIdle mem_pubStep)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 General in the first chain's letters -/

/-- Where the chain stands between two links no link is open in the record. (The other way round:
the library's `standOf_between`, Johnson/Top/H0/Walk/FrameTiedCleared.lean.) -/
theorem between_of_stand {s : S} (h : standOf s = Stand.between) : s.atBetween = true := by
  unfold standOf at h
  unfold VerifiableInference.Desc.First.S.atBetween
  cases hq : s.here with
  | between => rfl
  | lay a => rw [hq] at h; cases h
  | att a => rw [hq] at h; cases h
  | head a =>
    rw [hq] at h
    simp only at h
    split at h <;> cases h
  | fin a => rw [hq] at h; cases h
  | mem a => rw [hq] at h; cases h

/-- The book-keeping's Bool behind the chain's front. -/
theorem shape_front {links : List ModelPart} {ps : List Place}
    (hk : ps[0]? = some ⟨1, none, 0, KindName.frame⟩)
    (hk' : ps[0 + 1]? = some ⟨1, some 0, 0, KindName.frame⟩) (s : S)
    (h : shapeAt links ps[0]? s = true) : shapeAt links ps[0 + 1]? s = true := by
  rw [hk] at h
  rw [hk']
  simp only [shapeAt, standAt, mayWait, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨by simpa using h1, by simpa using h2⟩, ?_⟩
  cases hL' : s.link? with
  | none => rfl
  | some L =>
    rw [hL'] at h3
    simp at h3

/-- The book-keeping's Bool behind «link m: laid». -/
theorem shape_laid {links : List ModelPart} {ps : List Place} {k m : Nat} {p' : Place}
    (hk : ps[k]? = some ⟨1, some m, 0, KindName.frame⟩) (hk' : ps[k + 1]? = some p')
    (hl : p'.link = some m) (hp : p'.piece = 1) (s : S)
    (h : shapeAt links ps[k]? s = true) : shapeAt links ps[k + 1]? s = true := by
  obtain ⟨c, l, pc, kd⟩ := p'
  simp only at hl hp
  subst hl hp
  rw [hk] at h
  rw [hk']
  simpa [shapeAt, standAt, mayWait] using h

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}
  {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M}

/-- **(P) ONE BORDER ON, AT THE STATE AS IT WAS**, at a row that closes and opens nothing. -/
theorem form_next_still {b : Nat} {p : Place} (hp : L.ps[b]? = some p)
    (hi : (rowOf L.links p).ins = []) (ho : (rowOf L.links p).outs = [])
    (hn : NoneBetween L.N L.ps b)
    (hsh : ∀ s, shapeAt L.links L.ps[b]? s = true → shapeAt L.links L.ps[b + 1]? s = true)
    (hm : DoorIdle L.mgP L.links p) {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X}
    (hF : L.thread.Form b k s m) : L.thread.Form (b + 1) k s m := by
  have hfail : s.failed = none := by
    have h1 : s.failed.isNone = true := hF.1
    exact Option.isNone_iff_eq_none.1 h1
  have hon : onAt L.N L.mgP L.links L.ps[b]?
      (((openSets L.links L.ps (start L.links))[b]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b]?).getD []) (L.pubOf m.st.input.x, s) noStrs := hF.2
  obtain ⟨-, hr⟩ := hon
  obtain ⟨hB, -⟩ := hr.resolve_left (fun h => h hfail)
  simp only [Bool.and_eq_true] at hB
  have hs := hB.1.1.1.1.1
  refine form_next_quiet L hp ?_ hF rfl rfl rfl (hsh s hs) ?_ id ?_ ?_ (fun _ _ => id)
  · simp [quietRow, hi, ho]
  · intro hbk
    unfold bookAt at hbk ⊢
    rw [hn.1, hn.2]
    exact hbk
  · intro hP
    rw [stepOpen_empty _ _ hi ho]
    unfold pubHeld at hP ⊢
    refine List.all_eq_true.2 fun x hx => List.all_eq_true.1 hP x ?_
    rcases List.mem_append.1 hx with hx | hx
    · exact List.mem_append_left _ (mem_pubStep hm hx)
    · exact List.mem_append_right _ hx
  · exact fun h x hx => h x (mem_pubStep hm hx)

/-- At a place at which the chain is to stand between two links (P) says that no link is open in the
record. -/
theorem form_between {b : Nat} {p : Place} (hp : L.ps[b]? = some p)
    (hst : standAt L.links p = Stand.between) {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s m) : s.atBetween = true := by
  have hfail : s.failed = none := by
    have h1 : s.failed.isNone = true := hF.1
    exact Option.isNone_iff_eq_none.1 h1
  have hon : onAt L.N L.mgP L.links L.ps[b]?
      (((openSets L.links L.ps (start L.links))[b]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b]?).getD []) (L.pubOf m.st.input.x, s) noStrs := hF.2
  obtain ⟨-, hr⟩ := hon
  obtain ⟨hB, -⟩ := hr.resolve_left (fun h => h hfail)
  simp only [Bool.and_eq_true] at hB
  have hs := hB.1.1.1.1.1
  rw [hp] at hs
  unfold shapeAt at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  exact between_of_stand (hs.1.1.trans hst)

/-- An empty row owes nothing, at a place that is not of the kind K1. -/
theorem row_still_owes {b : Nat} {p : Place} (hp : L.ps[b]? = some p)
    (hi : (rowOf L.links p).ins = []) (ho : (rowOf L.links p).outs = [])
    (hc : (rowOf L.links p).ctx = []) (hk : p.kind ≠ KindName.K1) :
    (L.thread.row b).owes = [] := by
  have hk' : (p.kind == KindName.K1) = false := by simpa using hk
  show (((L.ps[b]?).map (FirstRows.rowAt L.links)).getD {}).owes = []
  rw [hp]
  show (FirstRows.turn p (FwdRow.of (rowOf L.links p).ins (rowOf L.links p).outs
    (rowOf L.links p).ctx)).owes = []
  unfold FirstRows.turn
  rw [hk', hi, ho, hc]
  simp [FwdRow.of]

/-- **THE RECORD AT A MEMBER OF THE FIRST CHAIN WITHOUT A ROUND AND WITHOUT A HOUSE WHOSE YES HANDS
THE STATE ON**, at an empty row. -/
theorem noHouse_first_still {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
    {fall : Nat → S → List Fmt.Drawn → Option String} {b : Nat} {p : Place} {blk : Block S Cl}
    {G : S → Prop} (seat : L.bs[b]? = some blk) (hr : blk.rounds = []) (hor : blk.oracles = [])
    (hpl : blk.place = p) (hkf : p.kind = KindName.frame)
    (noHalf : ∀ g ∈ L.hs, g.place.kind ≠ KindName.frame)
    (hd : ∀ s t, blk.decide s [] [] = .ok t ↔ t = s ∧ G s)
    (hp : L.ps[b]? = some p) (hi : (rowOf L.links p).ins = [])
    (ho : (rowOf L.links p).outs = []) (hc : (rowOf L.links p).ctx = [])
    (hn : NoneBetween L.N L.ps b)
    (hsh : ∀ s, shapeAt L.links L.ps[b]? s = true → shapeAt L.links L.ps[b + 1]? s = true)
    (hm : DoorIdle L.mgP L.links p) (said : ∀ k m, Said b k m → Said (b + 1) k m)
    (hrd : ∀ v s, L.rides b v s → L.rides (b + 1) v s)
    (hkp : ∀ s, s.failed = none → L.keeps b s s)
    (asks : ∀ k s m E, ThrS L.thread Said b k s m E → fall b s [] = none → G s)
    (rides : RidesPastS L.thread Said b) : NoHouse L.thread Said fall b blk :=
  noHouse_quiet_still seat hr hor
    (noHalf_of_kind fun g hg => by
      rw [hpl, hkf]
      exact noHalf g hg)
    hd said (fun k s m E hA _ => form_next_still hp hi ho hn hsh hm hA.1.2.2.1) hrd
    (fun _ s _ _ hA => hkp s (Option.isNone_iff_eq_none.1 hA.1.2.2.1.1))
    (row_still_owes hp hi ho hc (by rw [hkf]; decide)) asks rides

end

/-! ## 2 At the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`NoHouse` AT THE FIRST CHAIN's FRONT**: the block asks nothing: NO PREMISE OF CONTENT. hb₀:
the border behind the member that hears the reply is not the border behind the front. -/
theorem noHouse_start0 {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    {fall : Nat → TS → List Fmt.Drawn → Option String}
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (said : ∀ k m, Said 0 k m → Said (0 + 1) k m) (hb₀ : b₀ ≠ 0 + 1)
    (hRd : ∀ v s, Rd 0 v s → Rd (0 + 1) v s)
    (hKp : ∀ s, s.failed = none → Kp ⟨1, none, 0, KindName.frame⟩ s s)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 0) :
    ∃ blk, cF.blocksInOrder[0]? = some blk ∧
      NoHouse (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 0 blk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b0, e0, hr, -, hpl, -, hd⟩ := IM.front_of O
  obtain ⟨p, hp, hm, -⟩ := P1L20.door_idle9 h.𝔇 (k := 0) List.mem_cons_self
  obtain rfl := Option.some.inj (P1L20.front_places_full.1.symm.trans hp)
  refine ⟨b0, e0, noHouse_first_still (G := fun _ => True) e0 hr (IM.front_oracles O e0) hpl rfl
    noHalf (fun s t => ⟨fun e => ⟨(hd s [] [] t).1 e, trivial⟩, fun e => (hd s [] [] t).2 e.1⟩)
    hp (by simp [rowOf]) (by simp [rowOf]) (by simp [rowOf]) (P1L20.still_atAll h).1
    (shape_front hp P1L20.front_places_full.2) hm said
    (fun v s hv => ⟨fun hb => hv.1 (by omega), hRd v s hv.2⟩)
    (fun s h0 => (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s).2 (hKp s h0))
    (fun _ _ _ _ _ _ => trivial) rides⟩

/-- **`NoHouse` AT «LINK l: LAID»**, at each of the 25 links. hb₀: as above. **asks: TWO OF THE
BLOCK's THREE TESTS AT THE THREAD's STATE: THE CONTENT.** -/
theorem noHouse_laid {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    {fall : Nat → TS → List Fmt.Drawn → Option String} {l : Nat} (hl : l < 25)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (said : ∀ k m, Said (14 * l + 1) k m → Said (14 * l + 1 + 1) k m)
    (hb₀ : b₀ ≠ 14 * l + 1 + 1)
    (hRd : ∀ v s, Rd (14 * l + 1) v s → Rd (14 * l + 1 + 1) v s)
    (hKp : ∀ s, s.failed = none → Kp ⟨1, some l, 0, KindName.frame⟩ s s)
    (asks : ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + 1) k s m E → fall (14 * l + 1) s [] = none →
      FirstDue s.check ∧ s.check.frame.link = l)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + 1)) :
    ∃ blk, cF.blocksInOrder[14 * l + 1]? = some blk ∧
      NoHouse (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
        (14 * l + 1) blk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, -, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, bL, bB, bC, -, -, -, -, hlayf, hLay, -, iL, rL, dL, -⟩ := hall l hl
  obtain ⟨Lk', bL', bB', bC', -, -, iL', oL, -⟩ := IM.frame_oracles h.scope h.reads O l hl
  obtain rfl := Option.some.inj (iL.symm.trans iL')
  obtain ⟨hp, ⟨p', hp', hl', hpc'⟩, -⟩ := P1L20.places_full hl
  have hpl : bL.place = ⟨1, some l, 0, KindName.frame⟩ := by
    have e := IM.place_at h.scope h.reads O iL
    rw [P1L20.placesW_eq, hp] at e
    exact (Option.some.inj e).symm
  obtain ⟨p, hp2, hm, -⟩ := P1L20.door_idle9 h.𝔇 (k := 14 * l + 1)
    (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)))
  obtain rfl := Option.some.inj (hp.symm.trans hp2)
  have hrow : ∀ links : List ModelPart, (rowOf links ⟨1, some l, 0, KindName.frame⟩).ins = [] ∧
      (rowOf links ⟨1, some l, 0, KindName.frame⟩).outs = [] ∧
      (rowOf links ⟨1, some l, 0, KindName.frame⟩).ctx = [] := fun links => by
    cases hs : links[l]? <;> simp [rowOf, hs, segRow]
  refine ⟨bL, iL, noHouse_first_still (G := fun s => LayFront l s ∧ s.failed = none) iL rL
    oL hpl rfl noHalf (fun s t => ?_) hp (hrow _).1 (hrow _).2.1 (hrow _).2.2
    ((P1L20.still_atAll h).2.1 l hl) (shape_laid hp hp' hl' hpc') hm said
    (fun v s hv => ⟨fun hb => hv.1 (by omega), hRd v s hv.2⟩)
    (fun s h0 => (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s).2 (hKp s h0))
    (fun k s m E hA hf => ⟨⟨form_between hp (by simp [standAt]) hA.1.2.2.1,
      asks k s m E hA hf⟩, by
      have h1 : s.failed.isNone = true := hA.1.2.2.1.1
      exact Option.isNone_iff_eq_none.1 h1⟩) rides⟩
  rw [dL, hLay, hlayf, layFront_iff]
  constructor
  · rintro ⟨⟨rfl, h1⟩, h2, -⟩
    exact ⟨rfl, h1, h2⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨⟨rfl, h1⟩, h2, IM.sameReply_self _⟩

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.between_of_stand
#print axioms ProofFile.Honest.FirstThread.shape_front
#print axioms ProofFile.Honest.FirstThread.shape_laid
#print axioms ProofFile.Honest.FirstThread.form_next_still
#print axioms ProofFile.Honest.FirstThread.form_between
#print axioms ProofFile.Honest.FirstThread.row_still_owes
#print axioms ProofFile.Honest.FirstThread.noHouse_first_still
#print axioms ProofFile.Honest.FirstThread.noHouse_start0
#print axioms ProofFile.Honest.FirstThread.noHouse_laid
