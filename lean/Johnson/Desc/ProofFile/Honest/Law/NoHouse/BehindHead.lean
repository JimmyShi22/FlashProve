-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BehindHead.lean: «LINK m: BEHIND THE BATCHING» AT THE
LIBRARY's HEAD: THE RECORD `NoHouse` AT THE REAL DESCRIPTION's MEMBER, AT EACH OF THE 25 LINKS. The
threads' pen's letters at the head (`lettersHead`, Honest/Thread/FirstHead.lean); the library's
facts on the seat at link m (`P5J.AtMgA.Sits`, `P5J.sits_at`, Johnson/P5J/K09List.lean): there the
member is the term `Lk.behindB`, at the number `batchAt fullLinks At.ps m + 1` of the first chain's
flat list. `noHouse_behind_mg` (Honest/Law/NoHouse/BehindMg.lean) is called; of its premises these
are PAID HERE: the seat; no round, no oracle message, the decision (by the member's text); the
promise's meaning (by unfolding); the two Bools on the table (the library's, by the kernel); the two
places; the piece; THE PLAN's TWO COUNTS (`behind_counts`: the library's `numbers_atAll`,
`noneBetween_withTold`); THE RUNS' SHARE (`after_share_head`, `after_state`,
Honest/Law/NoHouse/BehindShare.lean: from the ties at the head); the item's tie (`behind_after`),
with «rw rides» (`behind_rw_head`).

WHAT THIS IS. Conditional lemmas on definitions of ours at the library's own terms: an assembly. THE
FULL SIZE ALONE, and the format's second hash function alone, as the head. None of the library's goals.

  `behind_seat`, `behind_counts`, `noHouse_behind_head`

WHAT STAYS A PREMISE. hnum (the link's own number is m): the written list, through
`head_place`: an evaluation. hn: no half of the prover's stands at a place of the kind frame. howes,
hopen, hctxO: the table's row and open set at that number: evaluations. hg: the falls'.
 htest: whoever lays the thread's fall and the item's test from one text. hctx, hKp,
hRd, said, rides: letters; hb₀: this member is not the one in front of the border
from which the reply's clause is said: then that clause rides (the library's `rest9` keeps what goes
on to the later chains).

MET FOR NOTHING. As `NoHouse`. The library's head has a member at the name under four premises on
the public files (the seal's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of
our files calls it; no member of the head TOGETHER WITH the thread's sentence is shown. Limits.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindMg
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindPays
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindShare
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.P5J.K09List
import Johnson.P1L20R.FramePaidAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Block Link)
open VerifiableInference.Desc.First (Item flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.LinkJoin (batchAt hearN)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- The member's seat in the flat list. -/
theorem behind_seat {m : Nat} {Lk : Link TS ProofFile.Cl} {p9 : Where}
    {Q9 : VerifiableInference.Desc.First.Close.Par} {b₃ b₅ : Block TS ProofFile.Cl}
    (St : h.Sits m Lk p9 Q9 b₃ b₅) :
    cF.blocksInOrder[batchAt fullLinks P5J.At.ps m + 1]? = some Lk.behindB := St.atK1

/-- **THE PLAN's TWO COUNTS ARE ALIKE IN FRONT OF THE MEMBER AND BEHIND IT**: it tells nothing. -/
theorem behind_counts {m : Nat} {Lk : Link TS ProofFile.Cl} {p9 : Where}
    {Q9 : VerifiableInference.Desc.First.Close.Par} {b₃ b₅ : Block TS ProofFile.Cl}
    (St : h.Sits m Lk p9 Q9 b₃ b₅) :
    Johnson.Desc.First.Walk.Tied.NoneBetween (P5J.At.N Zp cF) P5J.At.ps
      (batchAt fullLinks P5J.At.ps m + 1) := by
  have hs := behind_seat h St
  have e : VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder = P5J.At.ps :=
    P5J.At.places_paid h.scope h.reads h.laid
  have hk : batchAt fullLinks P5J.At.ps m + 1 < (flatPlacesOf
      VerifiableInference.Desc.Sound.linksFull true).length := by
    have h1 := (List.getElem?_eq_some_iff.1 hs).1
    have h2 : (VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder).length = cF.blocksInOrder.length := by
      unfold VerifiableInference.Desc.First.blockPlaces
      rw [List.length_map]
    rw [e] at h2
    show _ < P5J.At.ps.length
    rw [h2]
    exact h1
  have hN : P5J.At.N Zp cF = _ := P1L20.numbers_atAll h
  rw [hN]
  exact Johnson.Desc.First.Walk.Tied.noneBetween_withTold _ P1L20.places_nodup_full hk (by
    rw [List.getElem?_map, hs]
    rfl)

section
variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **«LINK m: BEHIND THE BATCHING»: THE RECORD AT THE REAL MEMBER.** -/
theorem noHouse_behind_head
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {m : Nat} {Lk : Link TS ProofFile.Cl}
    {p9 : Where} {Q9 : VerifiableInference.Desc.First.Close.Par} {b₃ b₅ : Block TS ProofFile.Cl}
    {ctx : List Item} (hm : m < 25) (St : h.Sits m Lk p9 Q9 b₃ b₅) (hnum : Lk.number = m)
    (hn : (H.first.find? fun g => g.place == Lk.behindB.place) = none)
    (howes : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row
      (batchAt fullLinks P5J.At.ps m + 1)).owes = Item.total m :: ctx)
    (hopen : Item.totalB m ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
      (batchAt fullLinks P5J.At.ps m + 1))
    (hctxO : ∀ i ∈ ctx, i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
      (batchAt fullLinks P5J.At.ps m + 1))
    (hg : FallGuards 0 Lk.behindB (fall (batchAt fullLinks P5J.At.ps m + 1)))
    (htest : ∀ s, fall (batchAt fullLinks P5J.At.ps m + 1) s [] = none → test m s = none)
    (hctx : ∀ v i a s' y u, i ∈ ctx → Lk.runBehind a.2 = .ok s' →
      Item.holds (P5J.At.N Zp cF)
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v) i a y u →
      Item.holds (P5J.At.N Zp cF)
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v) i (a.1, s') y u)
    (hKp : ∀ s s', s.failed = none → Lk.runBehind s = .ok s' → Kp Lk.behindB.place s s')
    (hRd : ∀ v s s', Rd (batchAt fullLinks P5J.At.ps m + 1) v s → Lk.runBehind s = .ok s' →
      Rd (batchAt fullLinks P5J.At.ps m + 1 + 1) v s')
    (hb₀ : b₀ ≠ batchAt fullLinks P5J.At.ps m + 1 + 1)
    (said : ∀ k μ, Said (batchAt fullLinks P5J.At.ps m + 1) k μ →
      Said (batchAt fullLinks P5J.At.ps m + 1 + 1) k μ)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (batchAt fullLinks P5J.At.ps m + 1)) :
    NoHouse (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
      (batchAt fullLinks P5J.At.ps m + 1) Lk.behindB := by
  have hs := behind_seat h St
  have A := after_share_head h hm St.lk St.seg
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (b := _) (blk := Lk.behindB) hs
  have hp' := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (b := _) (blk := b₃) St.atK2
  obtain ⟨c1, c2⟩ := behind_counts h St
  have hpc : Lk.behindB.place.piece = hearN P5J.At.links m + 2 := by
    show Lk.hear.length + 2 = hearN fullLinks m + 2
    unfold hearN
    rw [St.sort, St.seg.hear]
    rfl
  refine noHouse_behind_mg h.𝔇 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) rfl
    Said fall hs rfl rfl hn
    (fun _ _ _ => rfl) P5J.linkFit_links P5J.pubFit9_links hp hp'
    (by show some Lk.number = some m; rw [hnum]) hpc c1 c2 howes hopen hctxO
    (fun s s' hy => ⟨(after_state Lk A s s' hy).1,
      ⟨{ check := s.check }, {}, {}, (after_state Lk A s s' hy).2.1 _ _ _⟩,
      (after_state Lk A s s' hy).2.2⟩) (fun v a y u hh => ?_) hg htest hctx
    (fun s s' h0 hy => (head_keepsAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hs s s').2
      (hKp s s' h0 hy))
    (fun v s s' hr hy => ?_) said rides
  · exact behind_after { h.𝔇 with decT := fun _ _ => some (Q.cells v), cr1 := carryX } mgBase m Lk
      St.lk (behind_rw_head h hm St.lk St.seg) a y u hh
  · obtain ⟨r1, r2⟩ := hr
    refine ⟨fun hb => ?_, hRd v s s' r2 hy⟩
    have e9 := (after_state Lk A s s' hy).2.1 { check := s.check } {} {}
    have eo' : (VerifiableInference.Desc.LinkJoin.rest9 { check := s.check } {} {} s').out =
        (VerifiableInference.Desc.LinkJoin.rest9 { check := s.check } {} {} s).out :=
      congrArg (fun z : TS => z.out) e9
    have eo : s'.out = s.out := eo'
    rw [eo]
    exact r1 (by omega)

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.behind_seat
#print axioms ProofFile.Honest.FirstThread.behind_counts
#print axioms ProofFile.Honest.FirstThread.noHouse_behind_head
