-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherFramesT.lean: the gathering `owesS_framesS`
(GatherFramesS.lean) once more, with its six hypotheses on `ExchangeS` asked item by item, and not
at the items that are owed again. No definition.

  1  `housesW`, `housesW_control`   a closed test on the library's written list of places, and its
     control. `any_some`, `house_of`, `house_hear`, `house_back`, `house_tail`: what the test's yes
     gives at each number
  2  `exchangeS_of_new`   at a sub-protocol of a kind other than `frame`: `ExchangeS` from `BehindS`
     and the shares at the other owed items
  3  `behindS_fHeadHS`   `BehindS` at every sub-protocol, from the columns of `owesS_fHeadHS`
     `owesS_fHeadHT`     `owesS_fHeadHS` with `BehindS` at hand in the column `hX`
     `owesS_framesNT`    `owesS_framesNS` with the six hypotheses turned
     `owesS_framesT`     `owesS_framesS` with the six hypotheses turned
     `owesS_framesS_of_T`  the statement of `owesS_framesS`, sign for sign, by one call of
     `owesS_framesT`: so the new lemma is no weaker than the old one

What turns. Each hypothesis "`ExchangeS` at the sub-protocol number b" becomes: `ExchangeAtS`
(Honest/Thread/SharesS.lean) at each item that the row at b owes, except an item that is open before
b and is a `pin`, `pinI`, `pinW`, or a `constr` at one of the four parts of the library's
`P5J.parts4`. The condition is written out in each hypothesis.

Why. An item that is open before a sub-protocol and is owed again after it holds after it if it
passes over the sub-protocol: `exchangeAtS_again`, from `BehindS` and `RidesPastAtS`. For these four
sorts `RidesPastAtS` is proved at every sub-protocol of a kind other than `frame`, with no
hypothesis on the row (`cell_pin`, `cell_pinI`, CellsByKindB.lean; `cell_pinW`, `cell_constr4`,
CellsByKindC.lean). `BehindS` follows from the columns that the gathering proves in any case.

Why the closed test. `cell_pin` and `cell_pinI` ask that the place at the number is of a kind other
than `frame`. The gathering's hypotheses go by number. `housesW` says, of the 281 numbers at which
they are asked, that the written list has such a place there.

Limits.
  * All other hypotheses are those of `owesS_framesS`. What the prover's sides play and exchange,
    and the riders, are proved here of no prover.
  * The lemmas do not count how many items the new hypotheses leave.
  * An item of another sort that is open before a sub-protocol and owed again stays in the
    hypotheses.
  * `housesW` and its control are evaluations in Lean's kernel (`decide +kernel`): no compiled code.
  * Nothing here shows that the invariant holds at any state of a run, or that `carryExact` holds at
    any state.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherFramesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.LinkJoin (hearN)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)

/-! ## 1 The places at the 281 numbers -/

/-- At each of the 281 numbers at which `all_but_frames` (GatherFrames.lean) asks its last six
hypotheses, the written list of places has a place, and its kind is not `frame`. A closed test on
the library's written list, evaluated by Lean's kernel. -/
theorem housesW :
    (((List.range 25).all fun l =>
        ((List.range (IM.nAt l)).all fun i =>
          (P5J.At.ps[14 * l + i + 2]?).any fun p => p.kind != KindName.frame) &&
        ([2, 4, 5, 6].all fun j =>
          (P5J.At.ps[14 * l + IM.nAt l + j]?).any fun p => p.kind != KindName.frame)) &&
      ([353, 354, 355, 356].all fun b =>
        (P5J.At.ps[b]?).any fun p => p.kind != KindName.frame)) = true := by
  decide +kernel

/-- The control: at the number after a segment's first border the same test says no. -/
theorem housesW_control :
    ((P5J.At.ps[14 * 0 + 1]?).any fun p => p.kind != KindName.frame) = false := by
  decide +kernel

/-- Where `Option.any` says yes there is a value, and the test says yes of it. -/
theorem any_some {α : Type} {o : Option α} {q : α → Bool} (e : o.any q = true) :
    ∃ a, o = some a ∧ q a = true := by
  cases o with
  | none => exact absurd (show false = true from e) (by decide)
  | some a => exact ⟨a, rfl, e⟩

/-- From the closed test's yes at one number: a place there, of a kind other than `frame`. -/
theorem house_of {b : Nat}
    (e : ((P5J.At.ps[b]?).any fun p => p.kind != KindName.frame) = true) :
    ∃ p, P5J.At.ps[b]? = some p ∧ p.kind ≠ KindName.frame := by
  obtain ⟨p, hp, hq⟩ := any_some e
  refine ⟨p, hp, fun hk => ?_⟩
  have hq' : (p.kind != KindName.frame) = true := hq
  rw [hk] at hq'
  exact absurd hq' (by decide)

/-- The numbers 14 l + i + 2. -/
theorem house_hear {l i : Nat} (hl : l < 25) (hi : i < IM.nAt l) :
    ∃ p, P5J.At.ps[14 * l + i + 2]? = some p ∧ p.kind ≠ KindName.frame :=
  house_of (List.all_eq_true.1 ((Bool.and_eq_true _ _).mp (List.all_eq_true.1
    ((Bool.and_eq_true _ _).mp housesW).1 l (List.mem_range.2 hl))).1 i (List.mem_range.2 hi))

/-- The numbers 14 l + `IM.nAt` l + c, at c = 2, 4, 5, 6. -/
theorem house_back {l c : Nat} (hl : l < 25) (hc : c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 6) :
    ∃ p, P5J.At.ps[14 * l + IM.nAt l + c]? = some p ∧ p.kind ≠ KindName.frame :=
  house_of (List.all_eq_true.1 ((Bool.and_eq_true _ _).mp (List.all_eq_true.1
    ((Bool.and_eq_true _ _).mp housesW).1 l (List.mem_range.2 hl))).2 c (by
      rcases hc with rfl | rfl | rfl | rfl <;> decide))

/-- The numbers 353 to 356. -/
theorem house_tail {b : Nat} (hb : b ∈ [353, 354, 355, 356]) :
    ∃ p, P5J.At.ps[b]? = some p ∧ p.kind ≠ KindName.frame :=
  house_of (List.all_eq_true.1 ((Bool.and_eq_true _ _).mp housesW).2 b hb)

/-! ## 2 The shares at the items that are owed again -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- At a sub-protocol of a kind other than `frame`: `ExchangeS`, from `BehindS` and from
`ExchangeAtS` at the owed items other than those that are open before the sub-protocol and are a
`pin`, `pinI`, `pinW`, or a `constr` at one of the library's `parts4`. -/
theorem exchangeS_of_new {b : Nat}
    (hh : ∃ p, P5J.At.ps[b]? = some p ∧ p.kind ≠ KindName.frame)
    (hB : ∀ c, c < 358 → BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said c)
    (hX : ∀ j : Item, j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b j) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b := by
  obtain ⟨p, hp, hk⟩ := hh
  have hb : b < 358 := by
    have e := (List.getElem?_eq_some_iff.1 hp).1
    have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
    rw [← e', IM.places_len] at e
    exact e
  refine (exchangeS_iff _ _).2 fun (j : Item) hj => ?_
  by_cases ho : j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b
  · cases j with
    | pin m t =>
      exact exchangeAtS_again _ Said ho (hB b hb)
        (cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
          (cell_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp hk m t))
    | pinI =>
      exact exchangeAtS_again _ Said ho (hB b hb)
        (cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
          (cell_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp hk))
    | pinW =>
      exact exchangeAtS_again _ Said ho (hB b hb)
        (cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
          (cell_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b))
    | constr m q =>
      by_cases hq : q ∈ parts4
      · exact exchangeAtS_again _ Said ho (hB b hb)
          (cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
            (cell_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m hq))
      · exact hX _ hj fun _ => ⟨(fun _ _ e => nomatch e), (fun e => nomatch e),
          (fun e => nomatch e), (fun _ _ hq' e => hq (by cases e; exact hq'))⟩
    | _ =>
      exact hX _ hj fun _ => ⟨(fun _ _ e => nomatch e), (fun e => nomatch e),
        (fun e => nomatch e), (fun _ _ _ e => nomatch e)⟩
  · exact hX j hj fun ho' => absurd ho' ho

end

/-! ## 3 The gathering -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- `BehindS` at every sub-protocol, from the columns `hF` (at `SaidOk`), `h₀` and `hl`. -/
theorem behindS_fHeadHS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2)
    (h₀ : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      b₀ ≤ b + 1 → s'.out.reply = some m.st.input.x.asked)
    (hl : ∀ b, b < L.thread.bs.length → ∀ c ∈ csHead ν st R, c.lo = b + 1 →
      LaysAtS L.thread Said b c) :
    ∀ b, b < L.thread.bs.length → BehindS L.thread Said b := by
  subst hL
  intro b hb
  exact behindS_of_keeps_and _ Said
    (R₀ := fun c v s => b₀ ≤ c → s.out.reply = some v.x.asked)
    (head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd (csHead ν st R)
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (fun blk hblk k s m E ds y cols s' hA hd hS =>
      ⟨hF b hb blk hblk k s m E ds y cols s' (thrS_mono _ hSaid hA) hd hS,
        (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
          (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) w hblk rfl s s').2
          ⟨fHeadG_hK h H Q test carryX item n₁ n₂ b₀ Vd _ _ w hB hF b hb blk hblk k s m E ds y cols
              s' (thrS_mono _ hSaid hA) hd hS,
            head_hbook_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said hB b hb blk hblk k s m E
              ds y cols s' hA hd hS⟩⟩)
    (h₀ b hb)
    (fun c hc h1 h2 => head_staysBy_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s'
        (kpBy_fHeadG _ _ _ _ _ _ p s s' (kpBy_fHeadH _ _ _ _ _ _ p s s' hk)))
      (fHead_hst_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ _ _ _ _ w hσ b c hc h1 h2))
    (hl b hb)

/-- `owesS_fHeadHS` with `BehindS` at hand in the column `hX`. -/
theorem owesS_fHeadHT (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread Said b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2)
    (h₀ : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      b₀ ≤ b + 1 → s'.out.reply = some m.st.input.x.asked)
    (hl : ∀ b, b < L.thread.bs.length → ∀ c ∈ csHead ν st R, c.lo = b + 1 →
      LaysAtS L.thread Said b c)
    (hX : (∀ c, c < L.thread.bs.length → BehindS L.thread Said c) →
      ∀ b, b < L.thread.bs.length → ∀ i ∈ (L.thread.row b).owes, ExchangeAtS L.thread Said b i)
    (hok : ∀ b p i, P5J.At.ps[b]? = some p → i ∈ L.thread.opened b →
      i ∉ (L.thread.row b).shuts → i ∉ (L.thread.row b).owes → rideOkF p i = true →
      RidesPastAtS L.thread Said b i) : OwesS L.thread Said :=
  owesS_fHeadHS h H Q test carryX item n₁ n₂ b₀ Vd w Said hSaid hB hσ hL hP hF h₀ hl
    (hX (behindS_fHeadHS h H Q test carryX item n₁ n₂ b₀ Vd w Said hSaid hB hσ hL hF h₀ hl))
    hok

/-- `owesS_framesNS` with the six hypotheses on `ExchangeS` asked item by item, and not at the items
that are owed again. -/
theorem owesS_framesNT (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (hb₀ : b₀ = 339) (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) {Vh : Nat}
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    {L L₀ : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hL₀ : L₀ = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp))) w)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame →
      (∀ l, p.link = some l → p.piece ≠ hearN P5J.At.links l + 2) → ∀ m,
      RidesPastAt L₀.thread b (Item.carry m))
    (htst : ∀ l, l < 25 → ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none)
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      PlaysS L.thread Said (14 * l + IM.nAt l + j))
    (hP353 : PlaysS L.thread Said 353) (hP354 : PlaysS L.thread Said 354)
    (hP355 : PlaysS L.thread Said 355) (hP356 : PlaysS L.thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + i + 2)).owes →
      (j ∈ L.thread.opened (14 * l + i + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + i + 2) j)
    (hXback : ∀ l, l < 25 → ∀ c, c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 6 →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + IM.nAt l + c)).owes →
      (j ∈ L.thread.opened (14 * l + IM.nAt l + c) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + IM.nAt l + c) j)
    (hX353 : ∀ j : Item, j ∈ (L.thread.row (353)).owes →
      (j ∈ L.thread.opened (353) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (353) j)
    (hX354 : ∀ j : Item, j ∈ (L.thread.row (354)).owes →
      (j ∈ L.thread.opened (354) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (354) j)
    (hX355 : ∀ j : Item, j ∈ (L.thread.row (355)).owes →
      (j ∈ L.thread.opened (355) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (355) j)
    (hX356 : ∀ j : Item, j ∈ (L.thread.row (356)).owes →
      (j ∈ L.thread.opened (356) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (356) j)
    (hnx : LaysAtS L.thread Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS L.thread Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS L.thread Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS L.thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g))
    (hX : ∀ (m : Nat) (z : ProofFile.InstPub) (s s' : TS) (y y' : Strs) (v : WtF),
      doorZ Zp m s' = doorZ Zp m s → carryX m (z, s) y v → carryX m (z, s') y' v)
    (hcar7 : ∀ b p m, P5J.At.ps[b]? = some p → p.kind = KindName.K7 →
      Item.carry m ∈ L.thread.opened b → Item.carry m ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread Said b (Item.carry m))
    (hwor : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.worth m k ρ ∈ L.thread.opened b → Item.worth m k ρ ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread Said b (Item.worth m k ρ)) : OwesS L.thread Said := by
  subst hL
  subst hL₀
  have a0 := frame_all_frontN h H Q test carryX item n₁ n₂ b₀ Vd ν st R
    (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry
  have aL := fun l (hl : l < 25) =>
    frame_all_laidN h H Q test carryX item n₁ n₂ b₀ Vd ν st R
      (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry hl
  have aB := fun l (hl : l < 25) =>
    frame_all_behindN h H Q test carryX item n₁ n₂ b₀ Vd ν st R
      (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry hl
      (htst l hl)
  have aC := fun l (hl : l < 25) =>
    frame_all_clearedN h H Q test carryX item n₁ n₂ b₀ Vd ν st R
      (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry hl
  have aS := frame_all_sealN h H Q test carryX item n₁ n₂ b₀ Vd ν st R
    (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry
  have hlen : ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread.bs.length → b < 358 := by
    intro b hb
    have hb' : b < cF.blocksInOrder.length := hb
    rw [head_len h] at hb'
    exact hb'
  have hlen' : ∀ b, b < 358 → b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd
      (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread.bs.length := by
    intro b hb
    show b < cF.blocksInOrder.length
    rw [head_len h]
    exact hb
  have eC : ∀ l, 14 * l + IM.nAt l + 7 = P1L20.clearIx l := by
    intro l
    have e' := clearIx_is l
    omega
  refine owesS_fHeadHT h H Q test carryX item n₁ n₂ b₀ Vd w Said hSaid hB hσ rfl ?_ ?_ ?_
    (fun b _ c hc he => fHead_hl h H Q test carryX item n₁ n₂ b₀ Vd ν st R _ w Said hB
      hnx hs hstl hatt b c hc he) ?_ ?_
  · intro b hb
    exact all_but_frames _
      (playsS_mono _ hSaid (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk a0.1))
      (fun l hl => playsS_mono _ hSaid
        (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aL l hl).1))
      (fun l hl => playsS_mono _ hSaid
        (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aB l hl).1))
      (fun l hl => playsS_mono _ hSaid
        (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aC l hl).1))
      (playsS_mono _ hSaid (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk aS.1))
      hPhear hPback hP353 hP354 hP355 hP356 b (hlen b hb)
  · exact formBehind_column.1 (head_hF_ok h H Q test carryX item n₁ n₂ b₀ Vd _ _ w
      (head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk
        (formBehindAtS_of_behindS a0.2.1))
      (fun l hl => head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk
        (formBehindAtS_of_behindS (aL l hl).2.1))
      (fun l hl => head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk
        (formBehindAtS_of_behindS (aB l hl).2.1))
      (fun l hl => by
        rw [eC l]
        exact head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk
          (formBehindAtS_of_behindS (aC l hl).2.1))
      (head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk
        (formBehindAtS_of_behindS aS.2.1)))
  · exact head_h0 h H Q test carryX item n₁ n₂ b₀ Vd _ _ w hb₀ Said hhalf
  · intro hBe b hb
    have hB' := fun c (hc : c < 358) => hBe c (hlen' c hc)
    exact (exchangeS_iff _ _).1 (all_but_frames _
      (exchangeS_mono _ hSaid
        (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk a0.2.2.1))
      (fun l hl => exchangeS_mono _ hSaid
        (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aL l hl).2.2.1))
      (fun l hl => exchangeS_mono _ hSaid
        (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aB l hl).2.2.1))
      (fun l hl => exchangeS_mono _ hSaid
        (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aC l hl).2.2.1))
      (exchangeS_mono _ hSaid
        (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk aS.2.2.1))
      (fun l hl i hi => exchangeS_of_new h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (house_hear hl hi) hB' (hXhear l hl i hi))
      (fun l hl c hc => exchangeS_of_new h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (house_back hl hc) hB' (hXback l hl c hc))
      (exchangeS_of_new h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (house_tail (by decide)) hB' hX353)
      (exchangeS_of_new h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (house_tail (by decide)) hB' hX354)
      (exchangeS_of_new h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (house_tail (by decide)) hB' hX355)
      (exchangeS_of_new h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (house_tail (by decide)) hB' hX356)
      b (hlen b hb))
  · intro b p i hp hi h1 h2 hr
    by_cases hk : p.kind = KindName.frame
    · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s'
          (kpBy_fHeadG _ _ _ _ _ _ p s s' (kpBy_fHeadH _ _ _ _ _ _ p s s' hk))) Said
        (frame_cellsSN h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said rfl hcarry b p i hp hk
          hr)
    · exact head_hok h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (fun b p m hp e hi h1 => e.elim (fun e7 => hcar7 b p m hp e7 hi h1) fun e9 =>
          cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
            (cell_carry_k9 h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said hX
              (by
                have e' := (List.getElem?_eq_some_iff.1 hp).1
                have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
                rw [← eW, IM.places_len] at e'
                exact e') hp e9 hi h1))
        hwor
        (fun b p m k ρ hp e hi h1 => ridesPastAtS_mono _ hSaid <|
          cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ SaidOk
            (cell_forms_k11 h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ hB
              (by
                have e' := (List.getElem?_eq_some_iff.1 hp).1
                have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
                rw [← eW, IM.places_len] at e'
                exact e') hp e hi h1))
        b p i hp hk hi h1 h2 hr

/-- **`OwesS` at the first chain's invariant at the full size**, at `keeps` := `fHeadH`,
`carryX` := `carryExact Zp (P5J.At.arr Zp)` and every family that implies `SaidOk`, with the
exchange asked item by item, and not at the items that are owed again. -/
theorem owesS_framesT (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (hb₀ : b₀ = 339) (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) {Vh : Nat}
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (htst : ∀ l, l < 25 → ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none)
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      PlaysS L.thread Said (14 * l + IM.nAt l + j))
    (hP353 : PlaysS L.thread Said 353) (hP354 : PlaysS L.thread Said 354)
    (hP355 : PlaysS L.thread Said 355) (hP356 : PlaysS L.thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + i + 2)).owes →
      (j ∈ L.thread.opened (14 * l + i + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + i + 2) j)
    (hXback : ∀ l, l < 25 → ∀ c, c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 6 →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + IM.nAt l + c)).owes →
      (j ∈ L.thread.opened (14 * l + IM.nAt l + c) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + IM.nAt l + c) j)
    (hX353 : ∀ j : Item, j ∈ (L.thread.row (353)).owes →
      (j ∈ L.thread.opened (353) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (353) j)
    (hX354 : ∀ j : Item, j ∈ (L.thread.row (354)).owes →
      (j ∈ L.thread.opened (354) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (354) j)
    (hX355 : ∀ j : Item, j ∈ (L.thread.row (355)).owes →
      (j ∈ L.thread.opened (355) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (355) j)
    (hX356 : ∀ j : Item, j ∈ (L.thread.row (356)).owes →
      (j ∈ L.thread.opened (356) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (356) j)
    (hnx : LaysAtS L.thread Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS L.thread Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS L.thread Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS L.thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g))
    (hcar7 : ∀ b p m, P5J.At.ps[b]? = some p → p.kind = KindName.K7 →
      Item.carry m ∈ L.thread.opened b → Item.carry m ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread Said b (Item.carry m))
    (hwor : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.worth m k ρ ∈ L.thread.opened b → Item.worth m k ρ ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread Said b (Item.worth m k ρ)) : OwesS L.thread Said :=
  owesS_framesNT h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd w Said hSaid hB hσ hb₀
    noHalf hhalf
    hL rfl (carry_frame_exact_paid h H Q test item n₁ n₂ b₀ Vd _ _ w rfl)
    htst hPhear hPback hP353 hP354 hP355 hP356 hXhear hXback hX353 hX354 hX355 hX356 hnx hs hstl
    hatt (carryExact_door Zp (P5J.At.arr Zp)) hcar7 hwor

/-- The statement of `owesS_framesS`, by one call of `owesS_framesT`. -/
theorem owesS_framesS_of_T (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (hb₀ : b₀ = 339) (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) {Vh : Nat}
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (htst : ∀ l, l < 25 → ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none)
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      PlaysS L.thread Said (14 * l + IM.nAt l + j))
    (hP353 : PlaysS L.thread Said 353) (hP354 : PlaysS L.thread Said 354)
    (hP355 : PlaysS L.thread Said 355) (hP356 : PlaysS L.thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → ExchangeS L.thread Said (14 * l + i + 2))
    (hXback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      ExchangeS L.thread Said (14 * l + IM.nAt l + j))
    (hX353 : ExchangeS L.thread Said 353) (hX354 : ExchangeS L.thread Said 354)
    (hX355 : ExchangeS L.thread Said 355) (hX356 : ExchangeS L.thread Said 356)
    (hnx : LaysAtS L.thread Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS L.thread Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS L.thread Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS L.thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g))
    (hcar7 : ∀ b p m, P5J.At.ps[b]? = some p → p.kind = KindName.K7 →
      Item.carry m ∈ L.thread.opened b → Item.carry m ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread Said b (Item.carry m))
    (hwor : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.worth m k ρ ∈ L.thread.opened b → Item.worth m k ρ ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread Said b (Item.worth m k ρ)) : OwesS L.thread Said :=
  owesS_framesT h H Q test item n₁ n₂ b₀ Vd w Said hSaid hB hσ hb₀ noHalf hhalf hL
    htst hPhear hPback hP353 hP354 hP355 hP356
    (fun l hl i hi j hj _ => (exchangeS_iff _ _).1 (hXhear l hl i hi) j hj)
    (fun l hl c hc j hj _ => (exchangeS_iff _ _).1 (hXback l hl c hc) j hj)
    (fun j hj _ => (exchangeS_iff _ _).1 hX353 j hj)
    (fun j hj _ => (exchangeS_iff _ _).1 hX354 j hj)
    (fun j hj _ => (exchangeS_iff _ _).1 hX355 j hj)
    (fun j hj _ => (exchangeS_iff _ _).1 hX356 j hj)
    hnx hs hstl hatt hcar7 hwor

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.housesW
#print axioms ProofFile.Honest.FirstThread.housesW_control
#print axioms ProofFile.Honest.FirstThread.any_some
#print axioms ProofFile.Honest.FirstThread.house_of
#print axioms ProofFile.Honest.FirstThread.house_hear
#print axioms ProofFile.Honest.FirstThread.house_back
#print axioms ProofFile.Honest.FirstThread.house_tail
#print axioms ProofFile.Honest.FirstThread.exchangeS_of_new
#print axioms ProofFile.Honest.FirstThread.behindS_fHeadHS
#print axioms ProofFile.Honest.FirstThread.owesS_fHeadHT
#print axioms ProofFile.Honest.FirstThread.owesS_framesNT
#print axioms ProofFile.Honest.FirstThread.owesS_framesT
#print axioms ProofFile.Honest.FirstThread.owesS_framesS_of_T
