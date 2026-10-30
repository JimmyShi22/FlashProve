-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/PaidFlat.lean: kind K14: the premise AtEight of
Honest/K14/PaidAt.lean HOLDS WHERE THE THREAD's LIST HAS THE FORM OF THE SHARED CHAIN's LIST IN THE
IOP AS WRITTEN IN LEAN, UNDER FOUR MORE PREMISES (listed at atEight_of_flat). The form is FlatOf
(Johnson/Desc/K14/Honest/FlatForm.lean): a front sub-protocol, then the kind's eight, each with the
library's own rounds, oracle messages, place and decide function. That the shared chain's blocksInOrder list,
carried to another type of claims, has that form: flatOf_carried there.

  three_of_like   what AtEight asks of a member, of Like
  atEight_of_flat   AtEight holds at b0 := 1, where the list has the form FlatOf at the eight
                  sub-protocols that the library's blocks P returns (F, hb), the public data's shape
                  is the plan's (hA: A.S = P.S), and moreover the thread's halves stand at different
                  places (hn) and the kind's are among them (hh)
  flat_Play       **Plays at the members number 1, 4, 7 and 8 of such a thread**, under the same
                  premises, where the shape splits (hS) and the committed table has its columns
                  (hcol). No other file of this folder calls it

What is not claimed. That blocks P returns eight: a premise. Anything on the thread's halves: that
they stand at different places and that the kind's are among them are premises. That the committed
table has its columns: a premise. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.PaidAt
import Johnson.Desc.K14.Honest.FlatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open Desc.K14 (P14 St blocks)
open Desc.K14.Honest (FlatOf Like)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Ky X Pb : Type}

variable (T : Thread Bk St Cl Empty (Common W₀ Rc Ky) X Pb)

/-- What AtEight asks of a member, of Like. -/
theorem three_of_like {x : Block St Cl} {b : Block St Unit} (h : Like x b) :
    x.rounds = b.rounds ∧ x.oracles = b.oracles ∧ x.place = b.place :=
  ⟨h.rounds, h.oracles, h.place⟩

/-- **AtEight at b0 := 1, where the thread's list has the form FlatOf** at the eight sub-protocols
that blocks P returns (F, hb), the public data's shape is the plan's (hA), the thread's halves stand
at different places (hn) and the kind's halves are among them (hh). -/
theorem atEight_of_flat (P : P14) (A : Data) (weights : W₀ → Weights)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (c : OnBytes.Model.Verify.Chains)
    (F : FlatOf T.bs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hA : A.S = P.S) (hn : (T.hs.map (·.place)).Nodup)
    (hh : ∀ h ∈ (proverSidesOfSharedRounds A weights : List (Placed Empty (Common W₀ Rc Ky) X)), h ∈ T.hs) :
    AtEight T 1 P A weights :=
  ⟨hA, ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, fun i x hx blk hblk => by
    match i, hx, hblk with
    | 0, hx, hblk => obtain rfl := Option.some.inj hx; exact three_of_like (F.at1 hblk)
    | 1, hx, hblk => obtain rfl := Option.some.inj hx; exact three_of_like (F.at2 hblk)
    | 2, hx, hblk => obtain rfl := Option.some.inj hx; exact three_of_like (F.at3 hblk)
    | 3, hx, hblk => obtain rfl := Option.some.inj hx; exact three_of_like (F.at4 hblk)
    | 4, hx, hblk => obtain rfl := Option.some.inj hx; exact three_of_like (F.at5 hblk)
    | 5, hx, hblk => obtain rfl := Option.some.inj hx; exact three_of_like (F.at6 hblk)
    | 6, hx, hblk => obtain rfl := Option.some.inj hx; exact three_of_like (F.at7 hblk)
    | 7, hx, hblk => obtain rfl := Option.some.inj hx; exact three_of_like (F.at8 hblk)
    | n + 8, hx, _ => simp at hx⟩, hn, hh⟩

/-- **Plays at the members number 1, 4, 7 and 8 of such a thread**, under atEight_of_flat's premises
(hb, F, hA, hn, hh), where the shape splits (hS) and, at every valid input, the committed table that
"LOC" reads has a column of the declared width at every position below its length (hcol). -/
theorem flat_Play (P : P14) (A : Data) (weights : W₀ → Weights)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (c : OnBytes.Model.Verify.Chains)
    (F : FlatOf T.bs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hA : A.S = P.S) (hS : P.S.sharedSplitNeeded = true) (hn : (T.hs.map (·.place)).Nodup)
    (hh : ∀ h ∈ (proverSidesOfSharedRounds A weights : List (Placed Empty (Common W₀ Rc Ky) X)), h ∈ T.hs)
    (hcol : ∀ w, T.valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc P.S.fold P.item).sh.a,
      ∃ u, T.stored w (Desc.K14.readsAtLoc P.S.fold P.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc P.S.fold P.item).sh.W) :
    Plays T 1 ∧ Plays T 4 ∧ Plays T 7 ∧ Plays T 8 :=
  four_Play (atEight_of_flat T P A weights b1 b2 b3 b4 b5 b6 b7 b8 hb c F hA hn hh) hS hcol

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.three_of_like
#print axioms ProofFile.Honest.K14.atEight_of_flat
#print axioms ProofFile.Honest.K14.flat_Play
