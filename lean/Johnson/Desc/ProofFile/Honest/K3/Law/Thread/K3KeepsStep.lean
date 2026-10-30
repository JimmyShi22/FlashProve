-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/K3KeepsStep.lean: the kind "lookup" (K3): the lookups'
clause of "keeps" by place (`k3KeepsAt`, Honest/K3/Law/Thread/K3KeepsAt.lean) in the form in which a
thread takes a kind's clause, and what the clause leaves of the own part of the head's link. The
thread is a variable, or no thread is named. One definition and theorems.

Terms. Honest/K3/GLOSSARY.md ("keeps"). In this file: "the member's step accepts" is the library's
`StepYes` (Johnson/Top/H0/Walk/Reach.lean). The own part of the head's link is `HeadOwn`
(Johnson/Desc/First/State.lean), of fifteen fields.

What is shown.
  `K3MemberAt`: what the proof of the clause reads of the member at a border: four fields of
    the structure `K3AtSite` (Honest/K3/Law/Thread/AtThreadSite.lean).
  `k3KeepsAt_stepYes`: the clause holds behind a member's step that accepts (`StepYes`), from
    `K3MemberAt`.
  `headField_ofPlace`: the clause leaves eleven of the fifteen fields of the own part of the head's
    link as they were: all but F, tl, lookHeard and claim.

Hypotheses that remain.
  `O`, `hM`: (in `k3KeepsAt_stepYes`) the description returns (`IM.Open`,
    Johnson/IMR/SeatOpen.lean); `K3MemberAt` at the border.
  `h`, `hs`, `ha`: (in `headField_ofPlace`) the clause at the site's place; the site; the state in
    front stands in the head's link.
  `hT3`: (in `headField_ofPlace`) one test with code on public data, on the slots in use.

Imported.
Honest/Thread/Thr.lean. This file
imports no file on the riders.

Users. `k3KeepsAt_stepYes` is called in Honest/K3/Law/Thread/KeepsThread.lean and
Honest/K3/Law/Thread/K3KeepsForms.lean [not in this library]. `headField_ofPlace` is meant for a
clause `riderHead lo hi P` whose P reads these eleven fields alone: there it shows the hypothesis of
`staysBy_head_of` (Honest/Thread/RidersStayH.lean). The theorem `staysBy_head`
(Honest/Thread/RidersStay.lean) asks "here is as it was", and no lookup leaves the field here as it
was. These two files are not imported.
Honest/K3/Law/Thread/LaysFold.lean
imports this file too.

Limits. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3KeepsAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietSorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (HeadOwn)
open Johnson.Desc.First.Walk.Tied (StepYes)

local notation "FS" => VerifiableInference.Desc.First.S

section
variable {Bk : ProverCoinCounts} {V W X Pb : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)

/-- **What the proof of the clause reads of the member at a border**: four fields of the structure
`K3AtSite` (Honest/K3/Law/Thread/AtThreadSite.lean), to the letter: a sub-protocol of the lookups'
lot; the thread's member at the border lies in the description's list, at that sub-protocol's place,
and its plan is in order. Nothing on the prover's halves, on the state in front, or on the head's
own return. -/
structure K3MemberAt (b : Nat) (Z : Pub) (Bs : PureBase) (ch : Chain FS ProofFile.Cl)
    (lot : Block FS ProofFile.Cl) : Prop where
  inLot : lot ∈ (K3Lot.lot Z).blocks Bs.G₀
  mem : ∀ blk, T.bs[b]? = some blk → blk ∈ ch.blocksInOrder
  place : ∀ blk, T.bs[b]? = some blk → blk.place = lot.place
  plan : ∀ blk, T.bs[b]? = some blk → blk.planOk = true

/-- **The clause holds behind a member's step that accepts**, in the form in which a thread takes a
kind's clause; the thread is a variable. No instance of these hypotheses is exhibited in this file.
-/
theorem k3KeepsAt_stepYes (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat}
    {lot : Block FS ProofFile.Cl} (hM : K3MemberAt T b Z Bs ch lot) :
    ∀ blk, T.bs[b]? = some blk → ∀ t t', StepYes T.ft blk t t' → k3KeepsAt Z blk.place t t' := by
  intro blk hblk t t' ⟨R, c, _, hstep⟩
  exact k3KeepsAt_pays o pol lay KL Fd Z Bs base ch A B O blk.place lot blk hM.inLot
    (hM.place blk hblk).symm (hM.mem blk hblk) (hM.place blk hblk) (hM.plan blk hblk) T.ft t t' _ R
    c hstep

end

/-- **The lookups' clause leaves eleven of the fifteen fields of the own part of the head's link.**
-/
theorem headField_ofPlace {Z : Pub} {s : Site} {st st' : FS}
    (h : k3KeepsAt Z s.at_.place st st') (hs : s ∈ lookSites Z)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true) {a : HeadOwn}
    (ha : st.here = .head a) :
    ∃ a', st'.here = .head a' ∧ a'.fr = a.fr ∧ a'.kept = a.kept ∧ a'.ids = a.ids ∧ a'.L = a.L ∧
      a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo ∧ a'.Fm = a.Fm ∧ a'.slot = a.slot ∧
      a'.squaresP = a.squaresP ∧ a'.opened = a.opened := by
  cases hd : s.digits with
  | false =>
    obtain ⟨_, F, H, G, _, hC, _⟩ := k3KeepsAt_calls h hs hd
    rcases hC with ⟨a₁, h1, _⟩ | ⟨a₁, h1, _⟩ | ⟨a₁, h1, _, e⟩
    · rw [ha] at h1
      exact nomatch h1
    · rw [ha] at h1
      exact nomatch h1
    · obtain rfl : a = a₁ := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans h1)
      subst e
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | true =>
    rcases quiet_sorts hs hd hT3 with hq | ⟨used, claims, hq⟩
    · obtain ⟨_, tl, F, H, G, a₁, claim, _, _, h1, _, e, _⟩ := k3KeepsAt_head h hs hd hq
      obtain rfl : a = a₁ := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans h1)
      subst e
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨_, tl, F, H, G, _, _, hA, _⟩ := k3KeepsAt_digits h hs hd hq
      rcases hA with ⟨a₁, h1, _⟩ | ⟨a₁, h1, _⟩ | ⟨a₁, h1, _, e⟩
      · rw [ha] at h1
        exact nomatch h1
      · rw [ha] at h1
        exact nomatch h1
      · obtain rfl : a = a₁ := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans h1)
        subst e
        exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.k3KeepsAt_stepYes
#print axioms ProofFile.Honest.K3.Law.AtThr.headField_ofPlace
