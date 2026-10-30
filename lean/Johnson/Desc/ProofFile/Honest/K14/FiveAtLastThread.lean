-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/FiveAtLastThread.lean: the linear claim's second part ("K14,
second part", the first member of a proof file's last chain): THE FIVE STATEMENTS ON ONE
SUB-PROTOCOL, AS THE STRUCTURE FiveAtBorder (Honest/Thread/FiveAtBorder.lean), AT THE MEMBER 0 OF
THE TERM lastThread (Honest/Thread/TheFirstThread.lean), at any filling.

  accepted_at_lastThread   AcceptedS there: second_acceptedS_last (Honest/K14/SecondDoor.lean) at
                      that term's letters, with its one premise hD
  five_at_lastThread  **FiveAtBorder there**: four_at_lastThread (Honest/K14/FourAtLastThread.lean)
                      and accepted_at_lastThread
  five_at_lastThread_door   **FiveAtBorder there, where rides is doorRider
                            (Honest/K14/DoorRider.lean: at
                      border 0 alone: secondDoor's eleven tests are true) and clauses that begin
                      at border 2 or later**: hD and three of the four premises on rides (h₀, hst,
                      hl) fall; hr stays, as the form of rides, and late comes: hD is read off the
                      invariant in front of the member, and no clause speaks on both sides of the
                      member or begins behind it. THE PRICE OF late: no clause may begin at border 0
                      or 1 and reach further, so a fact that is shown where the chain is entered and
                      read by a later member cannot ride; where rides holds such a clause this
                      theorem does not apply, and five_at_lastThread does. WHAT IS OWED MOVES TO
                      WHERE THE CHAIN IS ENTERED: whoever shows the invariant at border 0 shows the
                      clause there

TWO LIMITS THAT A READER MUST KNOW FIRST (Honest/K14/SecondFour.lean's head has them at length).
(1) NEITHER THIS FILE NOR ANY FILE THAT IT IMPORTS SHOWS THE ITEMS ev AND dot, which ExchangeS takes
from the invariant in front of the
member. (2) BehindS AND ExchangeS HOLD VACUOUSLY WHEREVER fillZ's TEST AT BORDER 0 IS FALSE, and
neither this file nor any file that it imports evaluates that test at a state.

WHAT STAYS A PREMISE. The eight of four_at_lastThread: hEv, hDot, hPin₁, hPin, hr, h₀, hst, hl. And
hD: under all that AcceptedS itself hands out (the invariant and `Said` in front of the member, no
stop, no fall, the prover has moved) the eleven tests of secondDoor (Honest/K14/SecondDoor.lean) are
true at the state in front. Files beside that one give these eleven from the invariants of the two
earlier chains at their last borders, the start's return, and where W's pad lies (second_door_thr,
Honest/K14/SecondAtRun.lean); neither this file nor any file that it imports ties these to a stand
of this thread. Of
five_at_lastThread_door: hEv, hDot, hPin₁, hPin, hr, late.

What is not claimed. That any premise holds. That the thread's invariant holds at any state. Nothing
on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import Johnson.Desc.ProofFile.Honest.K14.FourAtLastThread
import Johnson.Desc.ProofFile.Honest.K14.DoorRider
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K14
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Sound (wordsLast)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (RowsHold DotSem omWW wvW)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread)

variable {W₀ Rc Tr X₀ X : Type}

/-- **AcceptedS at the member 0 of lastThread**, at every `Said` and every `fall`. hD: under all
that AcceptedS itself hands out, the eleven tests of secondDoor are true at the state in front. -/
theorem accepted_at_lastThread {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    (hD : ∀ blk, (lastThread h first reads parts w).bs[0]? = some blk → ∀ k s m E ds y cols,
      ThrS (lastThread h first reads parts w) Said 0 k s m E → drawsFit blk.rounds ds = true →
      chainStopAt ((lastThread h first reads parts w).φ.sees m.st.input) [blk]
        (lastThread h first reads parts w).hs m.loc ds = none →
      fall 0 s ds = none → (lastThread h first reads parts w).Moved blk k m E ds y cols →
      ok (secondDoor (ToldDesc.p14At A.Z) s) = true) :
    AcceptedS (lastThread h first reads parts w) Said fall 0 :=
  second_acceptedS_last A.Z h.places h.firstChain A.H h.sharedNumbers parts.meaning h.lastMeaning
    h.lastForm _ parts.taken parts.ends _ parts.table parts.fixed 0 h.description.t₁
    h.description.t₂ _ parts.rides _ w Said fall hD

/-- **FiveAtBorder at the member 0 of lastThread.** BehindS and ExchangeS hold vacuously wherever
fillZ's test at border 0 is false; ExchangeS takes the items ev and dot from the invariant in front.
hEv, hDot, hPin₁, hPin, hr, h₀, hst, hl: four_at_lastThread's premises. hD:
accepted_at_lastThread's. -/
theorem five_at_lastThread {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    (hEv : ∀ inp a e s y v, h.lastForm.shape 0 a e s = true → (parts.meaning inp).ev a y v →
      RowsHold OnBytes.Model.Reading.gl s
        (wordsLast (P5J.At.arr A.Z) (treesFirst files) (treesShared files) s v))
    (hDot : ∀ inp a e s y v, h.lastForm.shape 0 a e s = true → (parts.meaning inp).dot a e y v →
      DotSem OnBytes.Model.Reading.gl (ToldDesc.p14At A.Z)
        (omWW (P5J.At.arr A.Z) (treesFirst files) (ToldDesc.p14At A.Z) (fun q => q.2)
          (a.1, a.2, e))
        (wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q => q.2) a) s v)
    (hPin₁ : ∀ inp a b q E ps v,
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs (E.add ps)) v)
    (hPin : ∀ inp a b e E ps v,
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs (E.add ps)) v)
    {R₀ : Nat → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop}
    {cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hr : ∀ b v s, parts.rides b v s ↔ R₀ b v s ∧ ridersOf cs b v s)
    (h₀ : ∀ blk, (lastThread h first reads parts w).bs[0]? = some blk → ∀ k s m E ds y cols s',
      ThrS (lastThread h first reads parts w) Said 0 k s m E → drawsFit blk.rounds ds = true →
      (lastThread h first reads parts w).Stepped blk k s m E ds y cols s' →
      R₀ (0 + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ 0 → 0 + 1 ≤ c.hi → StaysBy (lastThread h first reads parts w) 0 c)
    (hl : ∀ c ∈ cs, c.lo = 0 + 1 → LaysAtS (lastThread h first reads parts w) Said 0 c)
    (hD : ∀ blk, (lastThread h first reads parts w).bs[0]? = some blk → ∀ k s m E ds y cols,
      ThrS (lastThread h first reads parts w) Said 0 k s m E → drawsFit blk.rounds ds = true →
      chainStopAt ((lastThread h first reads parts w).φ.sees m.st.input) [blk]
        (lastThread h first reads parts w).hs m.loc ds = none →
      fall 0 s ds = none → (lastThread h first reads parts w).Moved blk k m E ds y cols →
      ok (secondDoor (ToldDesc.p14At A.Z) s) = true) :
    FiveAtBorder (lastThread h first reads parts w) Said fall 0 := by
  obtain ⟨p, bh, ex, rp⟩ :=
    four_at_lastThread h first reads parts w Said hEv hDot hPin₁ hPin hr h₀ hst hl
  exact ⟨p, bh, ex, rp, accepted_at_lastThread h first reads parts w Said fall hD⟩

/-- **FiveAtBorder at the member 0 of lastThread, where the field rides is doorRider and clauses
that begin at border 2 or later.** BehindS and ExchangeS hold vacuously wherever fillZ's test at
border 0 is false; ExchangeS takes the items ev and dot from the invariant in front, and AcceptedS
takes secondDoor's tests from it. hEv, hDot, hPin₁, hPin: four_at_lastThread's premises. hr, late:
the form of the field rides. -/
theorem five_at_lastThread_door {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    (hEv : ∀ inp a e s y v, h.lastForm.shape 0 a e s = true → (parts.meaning inp).ev a y v →
      RowsHold OnBytes.Model.Reading.gl s
        (wordsLast (P5J.At.arr A.Z) (treesFirst files) (treesShared files) s v))
    (hDot : ∀ inp a e s y v, h.lastForm.shape 0 a e s = true → (parts.meaning inp).dot a e y v →
      DotSem OnBytes.Model.Reading.gl (ToldDesc.p14At A.Z)
        (omWW (P5J.At.arr A.Z) (treesFirst files) (ToldDesc.p14At A.Z) (fun q => q.2)
          (a.1, a.2, e))
        (wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q => q.2) a) s v)
    (hPin₁ : ∀ inp a b q E ps v,
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs (E.add ps)) v)
    (hPin : ∀ inp a b e E ps v,
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs (E.add ps)) v)
    {cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hr : ∀ b v s, parts.rides b v s ↔ ridersOf (doorRider _ (ToldDesc.p14At A.Z) :: cs) b v s)
    (late : ∀ c ∈ cs, 2 ≤ c.lo) :
    FiveAtBorder (lastThread h first reads parts w) Said fall 0 := by
  refine five_at_lastThread h first reads parts w Said fall hEv hDot hPin₁ hPin
    (R₀ := fun _ _ _ => True) (cs := doorRider _ (ToldDesc.p14At A.Z) :: cs)
    (fun b v s => ⟨fun g => ⟨trivial, (hr b v s).1 g⟩, fun g => (hr b v s).2 g.2⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) (fun c hc g g' => ?_) (fun c hc g => ?_)
    (fun blk _ k s m E ds y cols hA _ _ _ _ => ?_)
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact absurd (show 0 + 1 ≤ 0 from g') (by omega)
    · exact absurd (late c hc) (by omega)
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact absurd (show (0 : Nat) = 0 + 1 from g) (by omega)
    · exact absurd (late c hc) (by omega)
  · exact riders_at ((hr 0 _ _).1 hA.1.2.2.2.2.2.1) (List.mem_cons_self ..) (Nat.le_refl 0)
      (Nat.le_refl 0)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.accepted_at_lastThread
#print axioms ProofFile.Honest.K14.five_at_lastThread
#print axioms ProofFile.Honest.K14.five_at_lastThread_door
