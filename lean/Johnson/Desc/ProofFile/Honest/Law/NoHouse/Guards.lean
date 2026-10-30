-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/Guards.lean: A FALL THAT GUARDS AN ITEM. At a member
without a round whose yes an item in front has promised UNDER «NO FALL» (the quiet member behind a
batching), the debts behind its yes (`BehindS`, `ExchangeS`, Honest/Thread/PaysS.lean) have the
step's yes in hand and no «no fall»: as the debts are cut, no fall is in them. So what the item says
can be spent there only through «the step's yes ⟹ the fall says nothing»: `FallGuards`. Here that
sentence, and the two debts from the item under it.

THE TWO SIDES OF A FALL's TEST, TOGETHER. It is to speak ONLY WHERE THE MEMBER's STEP REFUSES:
`FallGuards`: else what is owed behind the yes cannot be had from an item that is said under «no
fall». And it is NOT to speak WHEREVER the step refuses: else the member's yes (`AcceptedS`) is
idle: what holds it from that side is its share. A fall's test names the verifier's own tests that
it holds: so its writer can show the first from that very text.

WHAT THIS IS. A definition (a premise's form), and conditional lemmas on our own definitions. None
of the library's goals.

  `FallGuards`, `thr_item_at`, `behindS_item`, `exchangeS_item`

MET FOR NOTHING. `FallGuards`: at the fall that never speaks; at a block whose step never says yes.
The two lemmas: as every debt. Limits. The item's own letter for the fall (at the first chain's
honest letters: test m) is tied to the thread's letter fall by whoever lays both: the lemmas hand
over «fall b s [] = none». Nothing is shown of any fall of the protocol. This file proves nothing
about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Quiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The fall at a member speaks only where the member refuses**: where the member's own step says
yes at a state and its own rounds, the letter fall says nothing there. A test on the block's text
and the fall's: no run, no coin, no input is in it. It pins the fall from the other side than the
known danger (a fall that speaks WHEREVER the step refuses makes the yes idle). -/
def FallGuards (ft : Nat) (blk : Block S Cl) (fall : S → List Fmt.Drawn → Option String) : Prop :=
  ∀ s rs cols s' n, blk.step ft s rs cols = .ok (s', n) → fall s (rs.map (·.drawn)) = none

variable (T : Thread Bk S Cl V W X Pb)

/-- The thread's (I), at one open item and one continuation of the challenges heard. -/
theorem thr_item_at {b : Nat} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (h : Thr T b k s m E)
    {i : T.ι} (hi : i ∈ T.opened b) (ds : List Fmt.Drawn) :
    T.means m.st.input i (T.seat k m s) (T.strs E) (T.wit k m.st.input (m.st.heard ++ ds)) :=
  h.2.2.2.1 ds i hi

section
variable (Said : Nat → Coins Bk → Mid W X → Prop) {b : Nat} {blk : Block S Cl}
  {fall : Nat → S → List Fmt.Drawn → Option String}

/-- **BEHIND ITS YES, FROM AN OPEN ITEM THAT IS SAID UNDER «NO FALL».** -/
theorem behindS_item (hblk : T.bs[b]? = some blk) (hr : blk.rounds = [])
    (hg : FallGuards T.ft blk (fall b)) (i : T.ι) (hi : i ∈ T.opened b)
    (hm : ∀ k s m E s', ThrS T Said b k s m E →
      T.means m.st.input i (T.seat k m s) (T.strs E) (T.wit k m.st.input (m.st.heard ++ [])) →
      fall b s [] = none → blk.step T.ft s [] [] = .ok (s', 0) →
      T.Form (b + 1) k s' m ∧ T.rides (b + 1) m.st.input s' ∧ T.keeps b s s') :
    BehindS T Said b :=
  behindS_quiet T Said hblk hr fun k s m E s' hA hs =>
    hm k s m E s' hA (thr_item_at T hA.1 hi []) (hg s [] [] s' 0 hs) hs

/-- **THE EXCHANGE, FROM AN OPEN ITEM THAT IS SAID UNDER «NO FALL»**: at each continuation of the
challenges heard. -/
theorem exchangeS_item (hblk : T.bs[b]? = some blk) (hr : blk.rounds = [])
    (hg : FallGuards T.ft blk (fall b)) (i : T.ι) (hi : i ∈ T.opened b)
    (hm : ∀ k s m E s' ds, ThrS T Said b k s m E →
      T.means m.st.input i (T.seat k m s) (T.strs E) (T.wit k m.st.input (m.st.heard ++ ds)) →
      fall b s [] = none → blk.step T.ft s [] [] = .ok (s', 0) →
      T.ItemsAt (T.row b).owes k s' m E ds) : ExchangeS T Said b :=
  exchangeS_quiet T Said hblk hr fun k s m E s' hA hs ds =>
    hm k s m E s' ds hA (thr_item_at T hA.1 hi ds) (hg s [] [] s' 0 hs) hs

end

end ProofFile.Honest

#print axioms ProofFile.Honest.thr_item_at
#print axioms ProofFile.Honest.behindS_item
#print axioms ProofFile.Honest.exchangeS_item
