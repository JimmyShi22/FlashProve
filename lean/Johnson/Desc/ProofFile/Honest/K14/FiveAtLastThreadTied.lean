-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/FiveAtLastThreadTied.lean: the linear claim's second part ("K14,
second part", the first member of a proof file's last chain): THE STRUCTURE FiveAtBorder
(Johnson/Desc/ProofFile/Honest/Thread/FiveAtBorder.lean) AT THE MEMBER 0 OF THE TERM lastThread
(Honest/Thread/TheFirstThread.lean), WHERE THE FIELD rides HOLDS A CLAUSE AT BORDER 1 THAT THE
MEMBER HAS TO LAY: "the taken trees' sources are tied to the own test's declared rounds" (Tied,
Johnson/Desc/Third/Law/Sources.lean), which is what makes the member 1 say yes.

  lays_tied       **the member 0 lays that clause**: from the clause tiedAheadRider at border 0
                  (Honest/K14/TiedAhead.lean) and the member's own yes
  five_at_lastThread_tied   **the five**, where rides is: doorRider at border 0 · tiedAheadRider at
                            border
                  0 · the clause Tied at border 1 · clauses that begin at border 2 or later
  five_at_lastThread_laid_tied   the same where the items ev and dot are laid as evAll and dotI

THE PRICE. One more clause rides at border 0, and whoever enters the chain owes it: tiedAheadB at
the record that the chain's start returns. All limits of Honest/K14/FiveAtLastThread.lean bind here:
BehindS and ExchangeS hold vacuously wherever fillZ's test at border 0 is false; ExchangeS takes the
items ev and dot, and AcceptedS secondDoor's tests, from the invariant in front.

What is not claimed. That the invariant holds at any state; that tiedAheadB says yes at any record.
Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import Johnson.Desc.ProofFile.Honest.K14.FiveAtLastThreadLaid
import Johnson.Desc.ProofFile.Honest.K14.TiedAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (wordsLast wordsShared)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (RowsHold DotSem omWW wvW gOfS dotI Tied)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread)

variable {W₀ Rc Tr X₀ X : Type}

/-- The clause at border 1, at the own test's sub-protocol own. -/
def tiedClause (W : Type) {Cl : Type} (own : Block S₃ Cl) : RiderCl W S₃ :=
  ⟨1, 1, fun _ _ s => Tied own s⟩

/-- **The member 0 lays the clause at border 1.** hr: rides gives tiedAheadB at border 0. -/
theorem lays_tied {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc) (parts : LastThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {Cl : Type}
    (own : Block S₃ Cl)
    (hr : ∀ v s, parts.rides 0 v s → tiedAheadB own.rounds s = true) :
    LaysAtS (lastThread h first reads parts w) Said 0 (tiedClause _ own) := by
  intro blk hb k s m E ds y cols s' hA _ hS
  obtain ⟨gs, hd⟩ := Desc.K14.Law.step_decides _ blk s s' _ cols _ hS.2
  rw [(like_at_last A.Z h.places h.firstChain blk hb).decide] at hd
  exact tied_behind_yes own _ s s' _ gs hd (hr _ _ hA.1.2.2.2.2.2.1)

/-- **FiveAtBorder at the member 0 of lastThread, with the clause at border 1 laid.** hEv, hDot,
hPin₁, hPin: four_at_lastThread's premises. hr, late: the form of the field rides. -/
theorem five_at_lastThread_tied {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
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
    {Cl : Type} (own : Block S₃ Cl) {cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hr : ∀ b v s, parts.rides b v s ↔ ridersOf (doorRider _ (ToldDesc.p14At A.Z) ::
      tiedAheadRider _ own.rounds :: tiedClause _ own :: cs) b v s)
    (late : ∀ c ∈ cs, 2 ≤ c.lo) :
    FiveAtBorder (lastThread h first reads parts w) Said fall 0 := by
  refine five_at_lastThread h first reads parts w Said fall hEv hDot hPin₁ hPin
    (R₀ := fun _ _ _ => True) (cs := doorRider _ (ToldDesc.p14At A.Z) ::
      tiedAheadRider _ own.rounds :: tiedClause _ own :: cs)
    (fun b v s => ⟨fun g => ⟨trivial, (hr b v s).1 g⟩, fun g => (hr b v s).2 g.2⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) (fun c hc g g' => ?_) (fun c hc g => ?_)
    (fun blk _ k s m E ds y cols hA _ _ _ _ => ?_)
  · simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | hc
    · exact absurd (show 0 + 1 ≤ 0 from g') (by omega)
    · exact absurd (show 0 + 1 ≤ 0 from g') (by omega)
    · exact absurd (show 1 ≤ 0 from g) (by omega)
    · exact absurd (late c hc) (by omega)
  · simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | hc
    · exact absurd (show (0 : Nat) = 0 + 1 from g) (by omega)
    · exact absurd (show (0 : Nat) = 0 + 1 from g) (by omega)
    · exact lays_tied h first reads parts w Said own fun v s hv =>
        riders_at ((hr 0 v s).1 hv) (List.mem_cons_of_mem _ List.mem_cons_self) (Nat.le_refl 0)
          (Nat.le_refl 0)
    · exact absurd (late c hc) (by omega)
  · exact riders_at ((hr 0 _ _).1 hA.1.2.2.2.2.2.1) (List.mem_cons_self ..) (Nat.le_refl 0)
      (Nat.le_refl 0)

/-- **The same where ev is evAll and dot is dotI.** hE, hDt: the two layings. -/
theorem five_at_lastThread_laid_tied {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    (hE : ∀ inp, (parts.meaning inp).ev = evAll (P5J.At.arr A.Z) fun q => q.2)
    (hDt : ∀ inp, (parts.meaning inp).dot = dotI (ToldDesc.p14At A.Z).S (fun q => gOfS q.2)
      (fun d v => wordsShared (P5J.At.arr A.Z) (treesFirst files) d.st d.book v)
      (fun q => wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q => q.2) q))
    (hPin₁ : ∀ inp a b q E ps v,
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs (E.add ps)) v)
    (hPin : ∀ inp a b e E ps v,
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs (E.add ps)) v)
    {Cl : Type} (own : Block S₃ Cl) {cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hr : ∀ b v s, parts.rides b v s ↔ ridersOf (doorRider _ (ToldDesc.p14At A.Z) ::
      tiedAheadRider _ own.rounds :: tiedClause _ own :: cs) b v s)
    (late : ∀ c ∈ cs, 2 ≤ c.lo) :
    FiveAtBorder (lastThread h first reads parts w) Said fall 0 :=
  five_at_lastThread_tied h first reads parts w Said fall
    (second_hEv parts.meaning (ToldDesc.p14At A.Z) (LLT25.c2 h.places).rounds (fun q => q.2)
      (P5J.At.arr A.Z) (treesFirst files) (treesShared files) hE)
    (second_hDot parts.meaning (ToldDesc.p14At A.Z) (LLT25.c2 h.places).rounds (fun q => q.2)
      (P5J.At.arr A.Z) (treesFirst files) hDt)
    hPin₁ hPin own hr late

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.lays_tied
#print axioms ProofFile.Honest.K14.five_at_lastThread_tied
#print axioms ProofFile.Honest.K14.five_at_lastThread_laid_tied
