-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/ThrBehind.lean: `BehindS T Said b` (Honest/Thread/PaysS.lean: the debt "behind", asked
from the pair of the thread and what is said) AT WHATEVER MEMBER, FROM NAMED PREMISES; AND, AT THE BATCHING's, THE PAYER
OF K9's CLAUSE. THE THREAD T AND THE LETTER Said ARE VARIABLES. Definitions, statements and proofs; no goal is stated.
  `moved_mid`       where the prover's side of a member's step is there at all (`Thread.Moved`): behind it the input
      is as it was, and the challenges heard are those in front and the step's own: THE FRAME's OWN `play_mid`
      (Honest/Law/Along.lean) AND `play_heard` (Honest/Thread/PaysLaw.lean), read at `Thread.Moved`: at every block
      and all challenges
  `seat_behind`     so what the thread's items are said of (`Thread.seat`) is, behind the member, what it is in front,
      at the state behind: what was handed to the chain does not turn (from (F): the challenges in front of the chain
      have all been heard)
`FormBy Said T b C`, `BehindBy Said T b C`   NAMED PREMISES ON T's LETTERS AT A MEMBER b, EACH IN A STRUCTURE,
over a clause C s s' on the state in front of the member and behind it: `form`: a state without a mark of failure has
the form behind · `formP`: FROM THE PAIR IN FRONT (`ThrS T Said b …`) and the clause: the sentence behind · `keeps`:
the clause gives T.keeps b · and, in `BehindBy` alone, `rides`: from the pair in front and the clause: the riders behind
  **`formKeeps_of`**, **`behindS_by`**   AT WHATEVER MEMBER: from these, a payer of the clause IN THE FRAME's ONE FORM
      (from `StepYes` of whatever block stands at b; `stepped_yes`: a member's step of the thread is such a yes), and
      "the clause holds no mark": behind each step: T.Form (b + 1) ∧ T.keeps b (THE SHARE WHICH THE FRAME's RULE ON
      RIDERS LEAVES TO A KIND WHOSE MEMBER LAYS NO RIDER: the premise hFK of its `behindS_of_keepsS`,
      Honest/Thread/SharesS.lean, and `behindS_of_keeps`, Riders.lean: neither imported here) · `BehindS T Said b` whole
  `SeatedFree.k9Keeps_yes`: at the batching's member, from K9's seat `SeatedFree` (Honest/K9/AtSeatAll.lean): the
      member's yes, in the frame's one form, pays K9's closed clause `K9Keeps` (Honest/K9/Keeps.lean): one call
WHICH CAN BE PAID BY UNFOLDING: `form`, where T.form reads the mark alone; `keeps`, where T.keeps b is laid as the
clause. `formP` AND `rides` ARE LAWS: whoever lays these two letters owes them, with the pair in front and the clause
in hand: what the member has LEFT comes off the clause by `K9Keeps.left` (under the library's head, field by field:
Honest/K9/SeatTied.lean); what it has TURNED comes off `BatBehind`, which the clause holds. No member. The two
structures and the two general theorems are spent in Honest/K9/ThrClose.lean; `moved_mid` also in
Honest/K9/TotalExchangeSeat.lean and EqExchangeHead.lean.
WHAT IS NOT CLAIMED. Any of the premises at any thread (at the frame's thread at the library's head `rides` can be
paid only under a premise that the rider's own border is not the one behind the member: the frame's hb₀ : b₀ ≠ b + 1).
`Exchange` (at the item totalB: `exchange_totalB_seat`, Honest/K9/TotalExchangeSeat.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.YesAll
import Johnson.Desc.ProofFile.Honest.K9.Keeps
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- Where the prover's run stands behind a member's step: the frame's `play_mid` and `play_heard`, read at
`Thread.Moved`. -/
theorem moved_mid {S' Cl : Type} (T : Thread Bk S' Cl V W X Pb) (blk : Block S' Cl) (k : Coins Bk) (m : Mid W X)
    (En : Env) (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List Desc.OpenedColumn)
    (hM : T.Moved blk k m En ds y cols) : y.2.st.input = m.st.input ∧ y.2.st.heard = m.st.heard ++ ds := by
  obtain ⟨⟨l, _, hp⟩, _⟩ := hM
  exact ⟨(play_mid l ds [] m y hp).1, play_heard l ds [] m y hp⟩

/-- What was handed to the chain does not turn. -/
theorem seat_behind {S' Cl : Type} (T : Thread Bk S' Cl V W X Pb) {b : ℕ} (k : Coins Bk) (m m' : Mid W X)
    (ds : List Fmt.Drawn) (s' : S') (hF : T.Fit b m) (hi : m'.st.input = m.st.input)
    (hh : m'.st.heard = m.st.heard ++ ds) : T.seat k m' s' = T.seat k m s' := by
  have hl : T.front ≤ m.st.heard.length := by
    rw [T.heard_length hF]
    exact Nat.le_add_right _ _
  unfold Thread.seat
  rw [hi, hh, List.take_append_of_le_length hl]

variable (Said : ℕ → Coins Bk → Mid W X → Prop)

/-- **Named premises on a thread's letters at a member**, over a clause on the state in front and behind: for the
form behind and for T.keeps. -/
structure FormBy (T : Thread Bk S Claim V W X Pb) (b : ℕ) (C : S → S → Prop) : Prop where
  form : ∀ a s', s'.failed = none → T.form (b + 1) (a, s') = true
  formP : ∀ κ s m En s', ThrS T Said b κ s m En → C s s' → T.formP (b + 1) (T.seat κ m s')
  keeps : ∀ s s', C s s' → T.keeps b s s'

/-- These, and the riders behind. -/
structure BehindBy (T : Thread Bk S Claim V W X Pb) (b : ℕ) (C : S → S → Prop) : Prop
    extends FormBy Said T b C where
  rides : ∀ κ s m En s', ThrS T Said b κ s m En → C s s' → T.rides (b + 1) m.st.input s'

variable {Said} {T : Thread Bk S Claim V W X Pb} {b : ℕ} {C : S → S → Prop}

/-- A member's step of the thread is a yes in the frame's one form. -/
theorem stepped_yes {blk : Block S Claim} {κ : Coins Bk} {s : S} {m : Mid W X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List Desc.OpenedColumn} {s' : S} (hS : T.Stepped blk κ s m En ds y cols s') :
    Johnson.Desc.First.Walk.Tied.StepYes T.ft blk s s' :=
  ⟨roundsOf y.1, cols, Sound.roundsFit_len _ _ ((Sound.step_ok_iff T.ft blk s s' _ cols _).1 hS.2).1, hS.2⟩

/-- **The form behind and T.keeps, at whatever member**: from the named premises, a payer of the clause at the member's
step, and "the clause holds no mark": in the form in which the frame's rule on riders takes a kind's share. -/
theorem formKeeps_of (B : FormBy Said T b C) (hmark : ∀ s s', C s s' → s'.failed = none)
    (pay : ∀ blk, T.bs[b]? = some blk → ∀ s s', Johnson.Desc.First.Walk.Tied.StepYes T.ft blk s s' → C s s') :
    ∀ blk, T.bs[b]? = some blk → ∀ κ s m En ds y cols s', ThrS T Said b κ s m En →
      drawsFit blk.rounds ds = true → T.Stepped blk κ s m En ds y cols s' →
      T.Form (b + 1) κ s' y.2 ∧ T.keeps b s s' := by
  intro blk hblk κ s m En ds y cols s' hT _ hS
  obtain ⟨hi, hh⟩ := moved_mid T blk κ m En ds y cols hS.1
  have K := pay blk hblk s s' (stepped_yes hS)
  refine ⟨⟨B.form _ s' (hmark s s' K), ?_⟩, B.keeps s s' K⟩
  rw [seat_behind T κ m y.2 ds s' hT.1.2.1 hi hh]
  exact B.formP κ s m En s' hT K

/-- **`BehindS` at whatever member.** -/
theorem behindS_by (B : BehindBy Said T b C) (hmark : ∀ s s', C s s' → s'.failed = none)
    (pay : ∀ blk, T.bs[b]? = some blk → ∀ s s', Johnson.Desc.First.Walk.Tied.StepYes T.ft blk s s' → C s s') :
    BehindS T Said b := by
  intro blk hblk κ s m En ds y cols s' hT hd hS
  obtain ⟨hF, hK⟩ := formKeeps_of B.toFormBy hmark pay blk hblk κ s m En ds y cols s' hT hd hS
  refine ⟨hF, ?_, hK⟩
  rw [(moved_mid T blk κ m En ds y cols hS.1).1]
  exact B.rides κ s m En s' hT (pay blk hblk s s' (stepped_yes hS))

variable {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
  {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- **The payer in the frame's one form, at the batching.** -/
theorem SeatedFree.k9Keeps_yes (Sd : SeatedFree c Z l k Lk p w) (ft : ℕ) (s s' : S)
    (h : Johnson.Desc.First.Walk.Tied.StepYes ft (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s s') :
    K9Keeps p (claimsInBy Lk.each Lk.hear Lk.order) s s' := by
  obtain ⟨R, cs, _, h⟩ := h
  exact k9Keeps_of_step Sd ft s s' R cs _ h

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.moved_mid
#print axioms ProofFile.Honest.K9.seat_behind
#print axioms ProofFile.Honest.K9.stepped_yes
#print axioms ProofFile.Honest.K9.formKeeps_of
#print axioms ProofFile.Honest.K9.behindS_by
#print axioms ProofFile.Honest.K9.SeatedFree.k9Keeps_yes
