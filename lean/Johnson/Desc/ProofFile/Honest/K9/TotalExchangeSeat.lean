-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalExchangeSeat.lean: THE FRAME's DEBT AT THE ITEM totalB AT THE BATCHING's MEMBER,
AT A VARIABLE THREAD: OF K9 IT ASKS THE SEAT AND THE BLOCK AT THE NUMBER ALONE; hG, hfront, hmeans ARE PREMISES.
Statements and proofs; no definition; no prover is made; no goal is stated.
  `stand_of_seat`: a stand (`BatStand`) from Sd : `SeatedFree` (Honest/K9/AtSeatAll.lean), the pair in front and the
      member's step
  **`exchange_totalB_seat`**: Sd · hbs : the thread's block at b is the seated batching · hG : `GivesTotalB` · hfront :
      the open items' meanings give Front at every entry of the order · hmeans : the item's sentence gives what the
      letter means says at iB: `ExchangeAtS T SaidOk b iB`
WHAT IS NOT CLAIMED. Any premise at any thread. That a stand is there. Called by Honest/K9/TotalExchangeFree.lean alone.
Nothing on any property.
GROUND: beneath this file, beside the sealed library (laws.11), lie 69 files, this one among them: reading copies, all
but ours.
-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFront
import Johnson.Desc.ProofFile.Honest.K9.ThrBehind
import Johnson.Desc.ProofFile.Honest.K9.FromYes
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

variable {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ} {c : Chain S Claim} {Z : ProofFile.Pub}
  {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- A stand, from K9's seat, the pair in front and the member's step. -/
theorem stand_of_seat (Sd : SeatedFree c Z l k Lk p w) (κ : Coins Bk) (s : S) (m : Mid W X) (En : Env) (ds : List
    Fmt.Drawn) (y : List Played × Mid W X) (cols : List Desc.OpenedColumn) (s' : S) (hT : ThrS T SaidOk b κ s m En) (hd :
             drawsFit (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).rounds ds = true) (hS : T.Stepped (Lk.batch
             (claimsInBy Lk.each Lk.hear Lk.order)) κ s m En ds y cols s') : ∃ x z G, BatStand Lk p T b κ s m En ds y cols s'
    x z G := by
  obtain ⟨_, tr, _, _, _, z, G, hB, _, _⟩ := behind_of_step Sd T.ft s s' _ cols _ hS.2
  exact ⟨_, z, G, hT, hd, hS, hB⟩

/-- **The frame's debt at the item**, from K9's seat (Sd), the block at the number (hbs) and the three premises hG,
hfront, hmeans. -/
theorem exchange_totalB_seat (Sd : SeatedFree c Z l k Lk p w) (hbs : T.bs[b]? = some (Lk.batch (claimsInBy Lk.each
    Lk.hear Lk.order))) (own : List (ℕ × ℕ)) (rdW : T.Wt → ℕ × ℕ → Sound.MsgQ) (rw : S → Bool) (test : S → Option
    String) (Front : ℕ × String → S → T.Wt → Prop) (iB : T.ι) (hG : GivesTotalB Lk p T b own rdW rw test Front)
    (hfront : ∀ wI a st v, (∀ j ∈ T.opened b, T.means wI j a st v) → ∀ o ∈ Lk.order, Front o a.2 v) (hmeans : ∀ wI a
    st v, (test a.2 = none → Sound.totalBQ Lk.runBehind own a.2 (rdW v) ∧ rw a.2 = true) → T.means wI iB a st v) :
    ExchangeAtS T SaidOk b iB := by
  intro blk hblk κ s m En ds y cols s' hT hd hS
  rw [hbs] at hblk
  cases hblk
  obtain ⟨x, z, G, St⟩ := stand_of_seat Sd κ s m En ds y cols s' hT hd hS
  obtain ⟨hi, hh⟩ := moved_mid T _ κ m En _ y cols hS.1
  intro ds' i hiB
  obtain rfl := List.mem_singleton.1 hiB
  refine hmeans _ _ _ _ fun htest => ?_
  rw [hi, hh, List.append_assoc]
  exact hG κ s m En _ y cols s' x z G St _
    (hfront m.st.input (T.seat κ m s) (T.strs En) _ fun j hj => hT.1.2.2.2.1 _ j hj) htest

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.stand_of_seat
#print axioms ProofFile.Honest.K9.exchange_totalB_seat
