-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LaysNext.lean: the kind "lookup" (K3): what a lookup's
member lays for a thread's rider (Honest/Thread/Riders.lean), each theorem stated for an arbitrary
clause. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the member number b of a thread T lays the clause c if c
holds behind the member's own accepted step: `LaysAt T b c` (Honest/Thread/Riders.lean).
`LaysAt T b c` reads of the clause c its sentence at the border b + 1 alone. So each theorem takes
any clause c and one implication `hc`, from what is shown behind the step of the lookup's member
into that sentence: however the clause is written, that implication connects it.

What is shown. Each conclusion is `LaysAt T b c`; the lines say what stands in front of the arrow in
`hc`.
  `lays_of_next`: behind a lookup, of whatever sort: the next free slot of the state's open ledger
    is the lookup's first slot plus its number of hidden values (`OnBytes.Model.Forest.elems` of its
    shape).
  `lays_of_nextHead`: the same said of the head's link's own ledger, at the lookup on the digits of
    that link.
  `lays_of_nextHeadCalls`: the same at the lookup on the calls of that link.
  `lays_of_claim`: at the lookup on the digits of the head's link: the claim on the weights is laid
    (the field claim of `HeadOwn`, Johnson/Desc/First/State.lean, is some value).
The equation has "=" where the lookup's promise behind has "≤":
Honest/K3/Law/Thread/NextBehind.lean.

Hypotheses that remain. The thread T is a variable.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hS`: the structure `K3AtSite` (Honest/K3/Law/Thread/AtThreadSite.lean). Of what it takes from the
    thread's relation the proofs use the field front: the lookup's promise in front holds. The proof
    of `lays_of_claim` does not use it.
  `hc`: the implication into the clause's sentence.
  `hd`, `hq`: at the digits of the head's link: which step without a round stands behind the lookup
    (a condition on public data).
  `hHere`: at the calls of the head's link: from the thread's relation, the chain stands in the
    head's link. The lookups' clause at the calls goes by the sort of the link and does not say
    which sort it is.

Imported, through Honest/K3/Law/Thread/RidersAtSite.lean. Files under Honest/Thread/.

Users. Honest/K3/Law/Thread/LaysNextLight.lean states the sentence of `lays_of_nextHead` under what
its proof uses. Honest/K3/Law/Thread/LaysStands.lean imports this file.

Limits. Nothing here shows that a thread with such a clause exists. No instance of these hypotheses
is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RidersAtSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.NextBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (quietAt quietHead)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {V W X Pb Wj : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)
  (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
  {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
  {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : W → Wj}
  (hS : K3AtSite T b Z Bs ch s lot J wit)
include O hS

/-- **Behind a lookup, of whatever sort: the ledger's next free slot.** No instance of these
hypotheses is exhibited in this file. -/
theorem lays_of_next (c : RiderCl W FS)
    (hc : ∀ w t, (∃ G, t.fork? = some G ∧
      G.next = s.p.first + OnBytes.Model.Forest.elems s.shape) → c.prop (b + 1) w t) :
    LaysAt T b c := by
  intro blk hblk k st m E ds y cols s' hA _ hSt
  exact hc _ _ (next_atSite o pol lay KL Fd Z Bs base ch A B O s hS.site hS.usedIs lot blk hS.inLot
    hS.lotPlace (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' _ _ cols
    (hS.front k st m E hA).1 hSt.2)

/-- **The same said of the head's link's own ledger, at that link's digits.** No instance of these
hypotheses is exhibited in this file. -/
theorem lays_of_nextHead (hd : s.digits = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (c : RiderCl W FS)
    (hc : ∀ w t, (∃ a, t.here = .head a ∧
      a.F.next = s.p.first + OnBytes.Model.Forest.elems s.shape) → c.prop (b + 1) w t) :
    LaysAt T b c := by
  intro blk hblk k st m E ds y cols s' hA _ hSt
  obtain ⟨G, hG, hn⟩ := next_atSite o pol lay KL Fd Z Bs base ch A B O s hS.site hS.usedIs lot blk
    hS.inLot hS.lotPlace (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' _ _
    cols (hS.front k st m E hA).1 hSt.2
  obtain ⟨_, tl, F, H, G', a₀, claim, _, _, _, _, e, _⟩ := k3Keeps_head o pol lay KL Fd Z Bs base ch
    A B O s hS.site hd lot blk hS.inLot hS.lotPlace (hS.mem blk hblk) (hS.place blk hblk)
    (hS.plan blk hblk) hq T.ft st s' _ _ cols hSt.2
  obtain ⟨a', hh⟩ : ∃ a', s'.here = .head a' := ⟨_, by rw [e]⟩
  exact hc _ _ ⟨a', hh, by rw [fork_head hh hG]; exact hn⟩

/-- **The same at that link's calls.** No instance of these hypotheses is exhibited in this file. It
is set aside: the files under Honest/Thread/ ask for the rider of span one behind the head's digits
alone. -/
theorem lays_of_nextHeadCalls (hd : s.digits = false)
    (hHere : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      ∃ a, st.here = .head a) (c : RiderCl W FS)
    (hc : ∀ w t, (∃ a, t.here = .head a ∧
      a.F.next = s.p.first + OnBytes.Model.Forest.elems s.shape) → c.prop (b + 1) w t) :
    LaysAt T b c := by
  intro blk hblk k st m E ds y cols s' hA _ hSt
  obtain ⟨G, hG, hn⟩ := next_atSite o pol lay KL Fd Z Bs base ch A B O s hS.site hS.usedIs lot blk
    hS.inLot hS.lotPlace (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' _ _
    cols (hS.front k st m E hA).1 hSt.2
  obtain ⟨a₀, ha₀⟩ := hHere k st m E hA
  obtain ⟨_, F, H, G', _, hC, _⟩ := k3Keeps_calls o pol lay KL Fd Z Bs base ch A B O s hS.site hd
    lot blk hS.inLot hS.lotPlace (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st
    s' _ _ cols hSt.2
  rcases hC with ⟨a, h1, _⟩ | ⟨a, h1, _⟩ | ⟨a, _, _, e⟩
  · rw [ha₀] at h1
    exact nomatch h1
  · rw [ha₀] at h1
    exact nomatch h1
  · obtain ⟨a', hh⟩ : ∃ a', s'.here = .head a' := ⟨_, by rw [e]⟩
    exact hc _ _ ⟨a', hh, by rw [fork_head hh hG]; exact hn⟩

/-- **At the head's digits: the claim on the weights is laid.** No instance of these hypotheses is
exhibited in this file. -/
theorem lays_of_claim (hd : s.digits = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (c : RiderCl W FS)
    (hc : ∀ w t, (∃ a, t.here = .head a ∧ a.claim.isSome = true) → c.prop (b + 1) w t) :
    LaysAt T b c := by
  intro blk hblk k st m E ds y cols s' hA hd' hSt
  exact hc _ _ (lays_claim T o pol lay KL Fd base A B O hS hd hq (b + 1) blk hblk k st m E ds y cols
    s' hA hd' hSt)

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.lays_of_next
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_of_nextHead
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_of_nextHeadCalls
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_of_claim
