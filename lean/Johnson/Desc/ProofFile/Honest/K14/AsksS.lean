-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/AsksS.lean: kind K14: WHAT FOLLOWS FROM K14Asks
(Honest/K14/Asks.lean) AT EACH OF THE EIGHT MEMBERS, IN THE FORMS FROM THE PAIR
(Honest/Thread/PaysS.lean, SharesS.lean: the thread's sentence in front AND a letter Said), WITH
Said A VARIABLE, AND «Exchange» AND «RidesPast» ITEM BY ITEM: at each item that the member's row
owes; at each item that is open in front, not shut and not owed. The proofs are k14_asks and the
frame's own lemmas from the one form to the other.

  ridesPastAt_of  «RidesPast» at a member gives its share at each item that goes past
  k14_asksS       **PlaysS, FormKeepsS, AcceptedS at every fall, ExchangeAtS at each owed item,
                  RidesPastAtS at each item that goes past**, at each b, 1 ≤ b ≤ 8
  k14_behindS, k14_behindS_and   a whole BehindS at each of them, as Honest/K14/Asks.lean's
                  k14_behind and k14_behind_and

What is not claimed. As in Honest/K14/Asks.lean: that K14Asks holds at any L; that the thread's
sentence in front holds at any stand. Nothing is spent of Said. Nothing in the library calls the
four yet. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Asks
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block)
open Desc.K14 (P14 St)

/-- «RidesPast» at a member gives its share at each item that goes past. No kind is named. -/
theorem ridesPastAt_of {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : Nat}
    (h : RidesPast T b) (i : T.ι) (h1 : i ∈ T.opened b) (h2 : i ∉ (T.row b).shuts)
    (h3 : i ∉ (T.row b).owes) : RidesPastAt T b i :=
  fun k s m E s' ps v hA hK h0 => h k s m E s' ps i v hA hK h1 h2 h3 h0

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Cl Wt : Type} {ℓ : WitLens Wt}
  {L : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt} {Q : P14}
  {sentU : Array OracleNotice} {layO : TreeLay} {c : Model.Verify.Chains}
  {tests : List (Block St Unit)} {last : List (Block St Unit) → Block St Unit} {A : Data}
  {weights : W₀ → Weights} {rand : Rc → TableRand}

/-- **From the structure, at each member b of the eight, in the forms from the pair, Said a
variable; «Exchange» and «RidesPast» item by item.** -/
theorem k14_asksS (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8) :
    PlaysS L.thread Said b ∧ FormKeepsS L.thread Said b ∧ AcceptedS L.thread Said fall b ∧
      (∀ i ∈ (L.thread.row b).owes, ExchangeAtS L.thread Said b i) ∧
      ∀ i ∈ L.thread.opened b, i ∉ (L.thread.row b).shuts → i ∉ (L.thread.row b).owes →
        RidesPastAtS L.thread Said b i := by
  obtain ⟨p, bh, ex, rp, ac⟩ := k14_asks h fall b h1 h8
  exact ⟨playsS_of _ _ p, formKeepsS_of _ bh, acceptedS_of _ _ ac,
    fun i hi => exchangeAtS_of _ _ ((exchange_iff _).1 ex i hi),
    fun i a1 a2 a3 => ridesPastAtS_of _ _ (ridesPastAt_of _ rp i a1 a2 a3)⟩

/-- **A WHOLE «BehindS» at each member b of the eight**: as k14_behind (Honest/K14/Asks.lean), from
the pair. -/
theorem k14_behindS (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    {cs : List (RiderCl (Common W₀ Rc TableKey) St)}
    (hr : ∀ b w s, L.thread.rides b w s ↔ ridersOf cs b w s) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8)
    (hst : ∀ x ∈ cs, x.lo ≤ b → b + 1 ≤ x.hi → StaysBy L.thread b x)
    (hno : ∀ x ∈ cs, x.lo ≠ b + 1) : BehindS L.thread Said b :=
  behindS_of _ _ (k14_behind h hr b h1 h8 hst hno)

/-- The like where the letter rides is a sentence R₀ and a list of clauses (Honest/Thread/
RidersAnd.lean), all from the pair: h₀: R₀ holds behind the member's accepted step: whoever lays R₀
shows it. A call of behindS_of_keeps_and. -/
theorem k14_behindS_and (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    {R₀ : Nat → Common W₀ Rc TableKey → St → Prop}
    {cs : List (RiderCl (Common W₀ Rc TableKey) St)}
    (hr : ∀ b w s, L.thread.rides b w s ↔ R₀ b w s ∧ ridersOf cs b w s) (b : Nat) (h1 : 1 ≤ b)
    (h8 : b ≤ 8)
    (h₀ : ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ x ∈ cs, x.lo ≤ b → b + 1 ≤ x.hi → StaysBy L.thread b x)
    (hno : ∀ x ∈ cs, x.lo ≠ b + 1) : BehindS L.thread Said b :=
  behindS_of_keeps_and L.thread Said hr
    (k14_asksS h Said (fun _ _ _ => none) b h1 h8).2.1 h₀ hst fun x hx e => absurd e (hno x hx)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.k14_behindS_and
#print axioms ProofFile.Honest.K14.ridesPastAt_of
#print axioms ProofFile.Honest.K14.k14_asksS
#print axioms ProofFile.Honest.K14.k14_behindS
