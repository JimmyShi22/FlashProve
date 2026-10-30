-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LaysFold.lean: the kind "lookup" (K3): a clause of a
thread's rider that the lookup on the digits of the head's link lays: behind its member the
smallness test's structure in the head's link's own part of the state has foldDrawn = 1, where it
had 0 in front. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the member number b of a thread T lays the clause c if c
holds behind the member's own accepted step: `LaysAt T b c` (Honest/Thread/Riders.lean). The head's
link's own part of the state is `HeadOwn` (Johnson/Desc/First/State.lean); its field tl is the
smallness test's structure, and foldDrawn is a field of that (OnBytes/Model/Tail.lean).

What is shown.
  `lays_foldDrawn`: `LaysAt T b c`, at every clause c that holds at the border b + 1 wherever the
    chain stands in the head's link with foldDrawn = 1 (`hc`).
  `lays_foldDrawn_head`: the case of the clause `riderHead (b + 1) hi` (Honest/Thread/Riders.lean)
    with the sentence foldDrawn = 1.
From `LaysAt`, `laysAtS_of` (Honest/Thread/SharesS.lean) gives `LaysAtS`, the same sentence from the
pair of the thread's relation and what is said.

Hypotheses that remain. The thread T is a variable.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`: s is a site of the public part (`lookSites Z`).
  `hlp`: the sub-protocol lot stands at the site's place.
  `hM`: the structure `K3MemberAt` (Honest/K3/Law/Thread/K3KeepsStep.lean), of four fields.
  `hd`, `hq`: this is the lookup on the digits of the head's link.
  `hF`, foldDrawn is 0 in front: at every state at which the thread's relation `Thr T b` holds, if
    the chain stands in the head's link then foldDrawn is 0. This is a rider of another kind. It is
    a named hypothesis here and is not shown in this file.
The statements need nothing of the prover's halves and nothing of the step without a round behind
the lookup.

Imported. Files under Honest/Thread/.

Users. `lays_foldDrawn_thread` (Honest/K3/Law/Thread/HeadDigitsAtLink.lean) calls
`lays_foldDrawn_head`.

Limits. The conclusion is drawn from the step's acceptance alone. No instance of these hypotheses is
exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3KeepsStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (quietAt quietHead)
open VerifiableInference.Desc.First (S)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {V W X Pb : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)
  (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
  {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
  {lot : Block FS ProofFile.Cl} (hs : s ∈ lookSites Z) (hlp : lot.place = s.at_.place)
  (hM : K3MemberAt T b Z Bs ch lot)
include O hs hlp hM

/-- **Behind the member foldDrawn is 1**, at every clause c that follows from that sentence (`hc`).
Conditional on the hypotheses that the head of this file lists. No instance of these hypotheses is
exhibited in this file. -/
theorem lays_foldDrawn (hd : s.digits = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X))
    (hF : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      ∀ a, st.here = .head a → a.tl.foldDrawn = 0)
    (c : RiderCl W FS)
    (hc : ∀ w t, (∃ a, t.here = .head a ∧ a.tl.foldDrawn = 1) → c.prop (b + 1) w t) :
    LaysAt T b c := by
  intro blk hblk k st m E ds y cols s' hA _ hSt
  obtain ⟨_, hstep⟩ := hSt
  obtain ⟨_, tl, F, H, G, a₀, claim, htl, _, hh, ho, e, _⟩ := k3Keeps_head o pol lay KL Fd Z Bs base
    ch A B O s hs hd lot blk hM.inLot hlp (hM.mem blk hblk) (hM.place blk hblk) (hM.plan blk hblk)
    hq T.ft st s' _ _ cols hstep
  have h0 : a₀.tl.foldDrawn = 0 := hF k st m E hA a₀ hh
  have etl : a₀.tl = tl := by
    have := htl
    simp only [S.tl?, hh, ho, if_true] at this
    exact Option.some.inj this
  refine hc _ _ ⟨_, by rw [e], ?_⟩
  show tl.foldDrawn + 1 = 1
  rw [← etl, h0]

/-- The case of the clause `riderHead (b + 1) hi` (Honest/Thread/Riders.lean). -/
theorem lays_foldDrawn_head (hd : s.digits = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X))
    (hF : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      ∀ a, st.here = .head a → a.tl.foldDrawn = 0) (hi : Nat) :
    LaysAt T b (riderHead (b + 1) hi fun a => a.tl.foldDrawn = 1) :=
  lays_foldDrawn T o pol lay KL Fd base A B O hs hlp hM hd hq hF _ fun _ _ h => h

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.lays_foldDrawn
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_foldDrawn_head
