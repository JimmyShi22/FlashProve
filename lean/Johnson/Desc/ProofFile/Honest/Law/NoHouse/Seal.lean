-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/Seal.lean: THE RECORD `NoHouse`
(Honest/Law/NoHouse/Bare.lean: what is owed at a member of a chain at whose place no half stands) AT
THE FIRST CHAIN's LAST MEMBER, THE SEAL: number 357 of the 358 of the proof file's description at
the full size, place ⟨1, none, 5, frame⟩: at the first chain's thread at the library's head
(`lettersHead`, Honest/Thread/FirstHead.lean), UNDER NAMED PREMISES. A member with one round, which
shows no item.

WHAT THIS IS. Conditional lemmas on definitions of ours and on the library's own texts. None of the
library's goals.

  1  GENERAL: `roundsFit_plain`   rounds that state no item but roots, at challenges that they can
     draw, showing no item, pass the library's test on the rounds
  2  GENERAL IN THE FIRST CHAIN's LETTERS: `form_past` (the clause (P) reads of where the run stands
     the input alone) · `form_next_seal` ((P) one border on, at the state as it was, at a row that
     meets the library's `RowSeal`) · `form_noneWaits` · `row_seal_owes` (such a row owes nothing) ·
     `noHouse_still` (THE RECORD at a member whose yes returns the state, at such a row)
  3  THE BLOCK: `refuse_cons` · `seal_decide` (what the seated block decides) · `seal_bare` ·
     `seal_same` · `seal_says`
  4  AT THE HEAD: `head_seat357`, `head_sealed`, `head_rowSeal`, `noHouse_seal357`

WHICH FIELDS FALL OUT OF THE LIBRARY's OWN LAWS, AND WHICH ARE CONTENT (at `noHouse_seal357`).
  seat     A CALL: `IM.back_numbers` at the head's own opening.
  bare     its lists and «plain»: BY THE BLOCK's TEXT (`ChainEnd.chainEnd`, through
           `IM.seal_seated`); «no half stands there»: A PREMISE ON THE PROVER (noHalf: no half is of
           the kind frame).
  behind   (P) at the last border: PAID: the library's `RowSeal` at the head (`rowSeal_mgAll'`,
           `counts_357_atAll`) and `form_next_quiet`; the block's yes returns the
           state (`Keeps.chainEnd_same`). The reply's rider: paid from b₀ ≠ 357 + 1. The other
           riders and the place's clause of «keeps»: PREMISES ON LETTERS (hRd, hKp), at a state that
           does not turn.
  owes     NOTHING IS OWED: the table's row there is empty.
  yes      OF THE FIVE CLAUSES OF `First.endAsks` THE FIRST IS PAID: «no count of claims is owed» is
           `S.closeOk`, which is `S.noneWaits` by its text, and (P) at the seal's place says that
           (`form_noneWaits`). **CONTENT: asks: THE OTHER FOUR (`First.untestedButOwnL`) AT THE
           THREAD's STATE IN FRONT OF THE SEAL**: the own group is the last · W is in it and in no
           other · a proximity test has begun on every other group · every sampled message but the
           own group's is in a tested group. A search by program over the statements of the
           library and of the houses' packs at hand FOUND no law that says
           was not opened for it.
           They are structure that many members turn along the chain (what the 25 closings and the
           test behind the links have laid; what W's sending has laid): WHO IS MEANT TO PAY: a
           shape's run, or a law at reached states. The rest of the yes is paid: no mark (from (P)),
           the reply as it was, the test on the rounds.
  said, rides   PREMISES, as the record has them: they name no block.

MET FOR NOTHING. As `NoHouse`: at a thread that is false everywhere; asks at a fall that speaks
wherever a clause fails. Limits. THE FULL SIZE ALONE, and the format's second hash function alone, as the
head. The library's head has a member at the name under four premises on the public files (the
seal's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of our files calls it; no
member of the head TOGETHER WITH the thread's sentence is shown. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FormNext
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Fill
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.AtSeats.Seal357AtAll
import Johnson.IMR.FlatCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Place Strs Wit KindName roundsFit itemOf step_iff)
open VerifiableInference.Desc.First (S ModelPart Item Pub Numbers Meaning onAt openSets pubSets start
  rowOf quietRow shapeAt pubHeld bookAt endAsks untestedButOwnL)
open VerifiableInference.Desc.K13.Law (RowSeal stepOpen_empty placeSeal)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open VerifiableInference.Desc.ChainEnd (chainEnd sealRound refuse)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 General -/

/-- **Rounds that state no item but roots, showing no item.** -/
theorem roundsFit_plain : ∀ (l : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
    (∀ r ∈ l, r.items.filter (· != .root) = []) → drawsFit l ds = true →
    roundsFit l (ds.map fun d => ⟨[], d⟩) = true
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [drawsFit] at h
  | _ :: _, [], _, h => by simp [drawsFit] at h
  | d :: l, R :: Rs, hi, h => by
    simp only [drawsFit, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [drawFit, Bool.and_eq_true] at h1
    obtain ⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, -⟩, -⟩ := h1
    have ih := roundsFit_plain l Rs (fun r hr => hi r (List.mem_cons_of_mem _ hr)) h2
    have hv : (([] : List Fmt.ItemValue).map itemOf == d.items.filter (· != .root)) = true := by
      rw [hi d List.mem_cons_self]
      rfl
    show roundsFit (d :: l) (⟨[], R⟩ :: Rs.map fun d => ⟨[], d⟩) = true
    simp only [roundsFit, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨hv, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, ih⟩

/-! ## 2 General in the first chain's letters -/

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)

/-- The clause (P) reads of where the prover's run stands the input alone. -/
theorem form_past (b : Nat) (k : Coins Bk) (s : S) (m : Mid (Local W₀ Rc Xi Tr) X)
    (ds : List Fmt.Drawn) : L.thread.Form b k s (m.past ds) ↔ L.thread.Form b k s m := by
  show (L.thread.form b (L.pubOf (m.past ds).st.input.x, s) = true ∧
      L.thread.formP b (L.pubOf (m.past ds).st.input.x, s)) ↔
    (L.thread.form b (L.pubOf m.st.input.x, s) = true ∧
      L.thread.formP b (L.pubOf m.st.input.x, s))
  rw [past_input]

variable {L}

/-- **(P) ONE BORDER ON, AT THE STATE AS IT WAS**, at a row that meets the library's `RowSeal`. -/
theorem form_next_seal {b : Nat} {p : Place} (hT : RowSeal L.N L.mgP.more L.links L.ps b p)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s m) :
    L.thread.Form (b + 1) k s m := by
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
  refine form_next_quiet L hT.place ?_ hF rfl rfl rfl ?_ ?_ id ?_ ?_ (fun _ _ => id)
  · unfold quietRow
    rw [hT.ins, hT.outs]
    rfl
  · rw [hT.place] at hs
    rw [hT.last]
    unfold shapeAt at hs ⊢
    simp only [Bool.and_eq_true, hT.stand, hT.noWait, Bool.or_false] at hs ⊢
    exact ⟨hs.1.1, hs.1.2⟩
  · intro hbk
    unfold bookAt at hbk ⊢
    rw [hT.trees, hT.msgs]
    exact hbk
  · intro hP
    rw [stepOpen_empty _ _ hT.ins hT.outs]
    unfold pubHeld at hP ⊢
    refine List.all_eq_true.2 fun x hx => List.all_eq_true.1 hP x ?_
    rcases List.mem_append.1 hx with hx | hx
    · exact List.mem_append_left _ (hT.pubs x hx)
    · exact List.mem_append_right _ hx
  · exact fun h x hx => h x (hT.pubs x hx)

/-- At such a row (P) says that no count of rows waits. -/
theorem form_noneWaits {b : Nat} {p : Place} (hT : RowSeal L.N L.mgP.more L.links L.ps b p)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s m) :
    s.noneWaits = true := by
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
  rw [hT.place] at hs
  unfold shapeAt at hs
  simp only [Bool.and_eq_true, hT.stand, hT.noWait, Bool.or_false] at hs
  exact hs.1.2

/-- Such a row owes nothing, at a place that is not of the kind K1. -/
theorem row_seal_owes {b : Nat} {p : Place} (hT : RowSeal L.N L.mgP.more L.links L.ps b p)
    (hk : p.kind ≠ KindName.K1) : (L.thread.row b).owes = [] := by
  have hk' : (p.kind == KindName.K1) = false := by simpa using hk
  show (((L.ps[b]?).map (FirstRows.rowAt L.links)).getD {}).owes = []
  rw [hT.place]
  show (FirstRows.turn p (FwdRow.of (rowOf L.links p).ins (rowOf L.links p).outs
    (rowOf L.links p).ctx)).owes = []
  unfold FirstRows.turn
  rw [hk', hT.ins, hT.outs, hT.ctx]
  simp [FwdRow.of]

/-- **THE RECORD AT A MEMBER WITHOUT A HOUSE WHOSE YES RETURNS THE STATE, AT SUCH A ROW.** -/
theorem noHouse_still {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
    {fall : Nat → S → List Fmt.Drawn → Option String} {b : Nat} {p : Place} {blk : Block S Cl}
    (seat : L.bs[b]? = some blk) (bare : Bare L.hs blk)
    (hT : RowSeal L.N L.mgP.more L.links L.ps b p) (hk : p.kind ≠ KindName.K1)
    (same : ∀ (s : S) (ds : List Fmt.Drawn) (s' : S),
      blk.step 0 s (ds.map fun d => ⟨[], d⟩) [] = .ok (s', 0) → s' = s)
    (said : ∀ k m ds, Said b k m → drawsFit blk.rounds ds = true → Said (b + 1) k (m.past ds))
    (hr : ∀ v s, L.rides b v s → L.rides (b + 1) v s)
    (hkp : ∀ s, s.failed = none → L.keeps b s s)
    (yes : ∀ k s m E ds, ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      fall b s ds = none → ∃ s', blk.step 0 s (ds.map fun d => ⟨[], d⟩) [] = .ok (s', 0))
    (rides : RidesPastS L.thread Said b) : NoHouse L.thread Said fall b blk where
  seat := seat
  bare := bare
  said := said
  behind := fun k s m E ds s' hA _ hs => by
    obtain rfl := same s ds s' hs
    exact ⟨(form_past L (b + 1) k s' m ds).2 (form_next_seal hT hA.1.2.2.1),
      hr _ _ hA.1.2.2.2.2.2.1, hkp s' (Option.isNone_iff_eq_none.1 hA.1.2.2.1.1)⟩
  owes := fun k s m E ds s' _ _ _ ds' i hi => by
    rw [row_seal_owes hT hk] at hi
    cases hi
  yes := yes
  rides := rides

end

/-! ## 3 The block -/

section
variable {Cl : Type} {b : Block S ProofFile.Cl} {inF : List Fmt.DeclaredRound} {name : String} {a : Place}

/-- A clause that holds is passed over. -/
theorem refuse_cons {n : String} {c : Bool} {l : VerifiableInference.Desc.ChainEnd.Clauses}
    (hc : c = true) : refuse ((n, c) :: l) = refuse l := by
  subst hc
  rfl

/-- **What the seated block decides**: the five clauses; no mark; the state as it was. -/
theorem seal_decide
    (hla : IM.LaidAlone ProofFile.sameReply b
      ((chainEnd 1 5 true inF endAsks : Block S Unit).retype : Block S ProofFile.Cl) name a)
    (hk : a.kind ≠ KindName.K7) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = .ok t ↔ refuse (endAsks s) = .ok () ∧ s.failed = none ∧ t = s := by
  rw [IM.yes_alone hla hk]
  constructor
  · rintro ⟨h1, h2, -⟩
    have h1' : (chainEnd 1 5 true inF endAsks : Block S Unit).decide s rs gs = .ok t := h1
    obtain rfl := VerifiableInference.Desc.Keeps.chainEnd_same 1 5 true inF endAsks h1'
    have h1'' : (refuse (endAsks t)).map (fun _ => t) = .ok t := h1'
    refine ⟨?_, h2, rfl⟩
    cases hq : refuse (endAsks t) with
    | error e =>
      rw [hq] at h1''
      cases h1''
    | ok u => rfl
  · rintro ⟨h1, h2, rfl⟩
    refine ⟨?_, h2, IM.sameReply_self t⟩
    show (refuse (endAsks t)).map (fun _ => t) = .ok t
    rw [h1]
    rfl

variable
  (hla : IM.LaidAlone ProofFile.sameReply b
    ((chainEnd 1 5 true inF endAsks : Block S Unit).retype : Block S ProofFile.Cl) name a)
include hla

theorem seal_rounds : b.rounds = [sealRound] := IM.alone_rounds hla
theorem seal_oracles : b.oracles = [[]] := IM.alone_oracles hla

/-- **`Bare` BY THE BLOCK's TEXT**, where no half stands at its place. q: the flat list's own test
on the plan, laid over the block's. -/
theorem seal_bare {V W X : Type} {hs : List (Placed V W X)} (q : Bool)
    (hn : (hs.find? fun g => g.place == b.place) = none) : Bare hs { b with planOk := q } where
  none := hn
  lists := by
    show b.oracles = b.rounds.map fun _ => []
    rw [seal_rounds hla, seal_oracles hla]
    rfl
  plain := fun r hr => by
    have hr' : r ∈ b.rounds := hr
    rw [seal_rounds hla] at hr'
    obtain rfl := List.mem_singleton.1 hr'
    exact ⟨rfl, rfl, rfl⟩

/-- A yes of its step returns the state. -/
theorem seal_same (hk : a.kind ≠ KindName.K7) (q : Bool) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) (n : Nat)
    (h : ({ b with planOk := q } : Block S ProofFile.Cl).step 0 s rs cols = .ok (s', n)) : s' = s :=
  ((seal_decide hla hk s s' _ _).1 ((step_iff 0 _ s s' rs cols n).1 h).2.1).2.2

/-- **ITS STEP SAYS YES at a round that shows no item**, at a challenge that the round can draw, at
a state without a mark that meets the five clauses. -/
theorem seal_says (hk : a.kind ≠ KindName.K7) (q : Bool) (s : S) (ds : List Fmt.Drawn)
    (hd : drawsFit ({ b with planOk := q } : Block S ProofFile.Cl).rounds ds = true)
    (ha : refuse (endAsks s) = .ok ()) (hf : s.failed = none) :
    ({ b with planOk := q } : Block S ProofFile.Cl).step 0 s (ds.map fun d => ⟨[], d⟩) [] =
      .ok (s, 0) := by
  have hr : ({ b with planOk := q } : Block S ProofFile.Cl).rounds = [sealRound] := by
    show b.rounds = [sealRound]
    exact seal_rounds hla
  have hw : ({ b with planOk := q } : Block S ProofFile.Cl).want 0 (ds.map fun d => ⟨[], d⟩) = [] := by
    unfold VerifiableInference.Desc.Block.want
    rw [hr]
    cases ds with
    | nil => rfl
    | cons d t => rfl
  refine (step_iff 0 _ s s _ [] 0).2 ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hr] at hd ⊢
    exact roundsFit_plain _ _ (fun r hr' => by
      obtain rfl := List.mem_singleton.1 hr'
      rfl) hd
  · rw [hw]
    rfl
  · exact (seal_decide hla hk s s _ _).2 ⟨ha, hf, rfl⟩
  · rw [hw]
    rfl

end

/-! ## 4 At the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- The seal's seat in the flat list: a call. -/
theorem head_seat357 :
    cF.blocksInOrder[357]? = some { cF.last with planOk := cF.last.planOk && cF.last.hasNoClaimsAndNothingAfter } := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact (IM.back_numbers h.scope h.reads O).2

/-- The block there is the library's chain's end, alone: a call. -/
theorem head_sealed : IM.LaidAlone ProofFile.sameReply cF.last
    ((chainEnd 1 5 true (VerifiableInference.Desc.K13.inFrontOf Zp) endAsks :
      Block S Unit).retype : Block S ProofFile.Cl) cF.last.name
    { chain := 1, link := none, piece := 5, kind := .frame } := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', -, rfl, hla⟩ := IM.seal_seated O
  exact hla

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The library's `RowSeal` at the head's letters**: two calls. -/
theorem head_rowSeal :
    RowSeal (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps 357 placeSeal :=
  VerifiableInference.Desc.Sound.rowSeal_mgAll' h.𝔇 mgBase rfl _
    (VerifiableInference.Desc.K13.Law.counts_357_atAll h).1
    (VerifiableInference.Desc.K13.Law.counts_357_atAll h).2

/-- **`NoHouse` AT THE SEAL**, at the first chain's thread at the head. noHalf: no half of the
prover's first chain is of the kind frame. hb₀: the border behind the member that hears the reply is
not the last border. hRd, hKp: the other riders, and the place's clause of «keeps», at a state that
does not turn. **asks: FOUR OF THE BLOCK's FIVE CLAUSES AT THE THREAD's STATE: THE CONTENT.** -/
theorem noHouse_seal357
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    {fall : Nat → TS → List Fmt.Drawn → Option String}
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (said : ∀ k m ds, Said 357 k m → drawsFit [sealRound] ds = true → Said 358 k (m.past ds))
    (hb₀ : b₀ ≠ 357 + 1) (hRd : ∀ v s, Rd 357 v s → Rd 358 v s)
    (hKp : ∀ s, s.failed = none → Kp placeSeal s s)
    (asks : ∀ k s m E ds,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 357 k s m E →
      fall 357 s ds = none → refuse (untestedButOwnL s) = .ok ())
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 357) :
    NoHouse (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 357
      { cF.last with planOk := cF.last.planOk && cF.last.hasNoClaimsAndNothingAfter } := by
  have hla := head_sealed h
  have hT := head_rowSeal h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  have hk7 : ({ chain := 1, link := none, piece := 5, kind := .frame } : Place).kind ≠
      KindName.K7 := by decide
  refine noHouse_still (head_seat357 h)
    (seal_bare hla _ (noHalf_of_kind fun g hg => by
      rw [IM.alone_place hla]
      exact noHalf g hg)) hT (by decide)
    (fun s ds s' hs => seal_same hla hk7 _ s s' _ _ _ hs)
    (fun k m ds hS hd => said k m ds hS (by
      have e : ({ cF.last with planOk := cF.last.planOk && cF.last.hasNoClaimsAndNothingAfter } :
          Block S ProofFile.Cl).rounds = [sealRound] := by
        show cF.last.rounds = [sealRound]
        exact seal_rounds hla
      rw [e] at hd
      exact hd))
    (fun v s hr => ⟨fun hb => hr.1 (by omega), hRd v s hr.2⟩)
    (fun s h0 =>
      (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.place s s).2 (hKp s h0))
    (fun k s m E ds hA hd hf => ⟨s, seal_says hla hk7 _ s ds hd
      ((refuse_cons (form_noneWaits hT hA.1.2.2.1)).trans (asks k s m E ds hA hf)) (by
      have h1 : s.failed.isNone = true := hA.1.2.2.1.1
      exact Option.isNone_iff_eq_none.1 h1)⟩)
    rides

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.roundsFit_plain
#print axioms ProofFile.Honest.FirstThread.form_past
#print axioms ProofFile.Honest.FirstThread.form_next_seal
#print axioms ProofFile.Honest.FirstThread.form_noneWaits
#print axioms ProofFile.Honest.FirstThread.row_seal_owes
#print axioms ProofFile.Honest.FirstThread.noHouse_still
#print axioms ProofFile.Honest.FirstThread.refuse_cons
#print axioms ProofFile.Honest.FirstThread.seal_decide
#print axioms ProofFile.Honest.FirstThread.seal_rounds
#print axioms ProofFile.Honest.FirstThread.seal_oracles
#print axioms ProofFile.Honest.FirstThread.seal_bare
#print axioms ProofFile.Honest.FirstThread.seal_same
#print axioms ProofFile.Honest.FirstThread.seal_says
#print axioms ProofFile.Honest.FirstThread.head_seat357
#print axioms ProofFile.Honest.FirstThread.head_sealed
#print axioms ProofFile.Honest.FirstThread.head_rowSeal
#print axioms ProofFile.Honest.FirstThread.noHouse_seal357
