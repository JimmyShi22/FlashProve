-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Frames/LastAtValues.lean: THE STRUCTURE FiveAtBorder
(Johnson/Desc/ProofFile/Honest/Thread/FiveAtBorder.lean) AT THE MEMBER 1 OF A PROOF FILE's LAST
CHAIN ("the taken trees' sources"), AT THE THREAD lastThread AT lastParts, AT THE VALUES OF TWO OF
ITS LETTERS (Honest/Thread/TheLaterThreads.lean): the riders lastRiders, whose clause at border 1 is
Tied (tiedRider), and the clause keeps lastKeeps, which says that the state stays at the chain's two
frames. The member has no round and hands its state on as it is.

  tied_at_one        in front of the member the invariant holds Tied: it is the rider's clause there
  five_at_last_one   **FiveAtBorder at the member 1**: by last_one
                     (AtFullSide/Frames/LastChain.lean): of its five premises the two on pins are
                     shown outright, the three others under the premises named below
  five_at_last_one_late   the same where every later clause begins at border 3 or later: lays falls
  acceptedS_one_last   the fifth of the five alone: the member says yes

WHAT STAYS A PREMISE of five_at_last_one, on the letters: hrid: L's riders are lastRiders at a list
later · late: each clause of later begins at border 2 or later · lays: a clause of later that begins
AT border 2 holds there, at the state in front of the member, wherever the invariant holds in front
(the member turns no state, so it cannot make such a clause true: it has to be had from the
invariant) · hk: L's keeps is lastKeeps at a clause own · hown: own allows a state to stay at this
member's place, wherever the invariant holds in front.

Limits. Each of the five starts from the thread's invariant in front of the member, which brings
Tied from the rider. Tied IS the condition of the member's yes: SO THE YES IS MOVED, NOT PAID, HERE:
it counts only with the two laws named next, at the same letters L. That the member 0 lays that
clause is lays_tied (Johnson/Desc/ProofFile/Honest/K14/FiveAtLastThreadTied.lean), from a clause at
border 0 that is owed where the chain is entered (tied_ahead_at_terms,
AtFullSide/K14/TiedAheadAtTerms.lean). THAT THE INVARIANT HOLDS AT ANY BORDER OF ANY RUN IS NOT
SHOWN: no state is known here at which the five speak. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import AtFullSide.Frames.LastChain
import AtFullSide.K14.AtLastTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Frames
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (Tied)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K14 (tiedAheadRider doorRider)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **In front of the member 1 the invariant holds Tied**: the rider's clause at border 1. -/
theorem tied_at_one (h : HeadAtReturn files A) (first : FirstThreadParts A) (L : LastLetters A)
    (reads : IndexReaders W₀ Rc) (w : Local W₀ Rc ProofFile.Inst Tr)
    {later : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hrid : L.riders = lastRiders h.places later) {k : Coins A.B} {s : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hA : Thr (lastThread h first reads (lastParts h first L) w) 1 k s m E) :
    Tied (LLT25.c2 h.places) s := by
  have hr : ridersOf (doorRider _ (ToldDesc.p14At A.Z) :: L.riders) 1 m.st.input s :=
    hA.2.2.2.2.2.1
  rw [hrid] at hr
  exact hr (tiedRider _ h.places)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (Nat.le_refl 1)
    (Nat.le_refl 1)

/-- **FiveAtBorder at the member 1 of the last chain's thread at lastParts, at lastRiders and
lastKeeps.** hrid, late, lays: on L's riders. hk, hown: on L's keeps. -/
theorem five_at_last_one (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (L : LastLetters A) (reads : IndexReaders W₀ Rc) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    {later : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hrid : L.riders = lastRiders h.places later) (late : ∀ c ∈ later, 2 ≤ c.lo)
    (lays : ∀ c ∈ later, c.lo = 2 → ∀ k s m E,
      ThrS (lastThread h first reads (lastParts h first L) w) Said 1 k s m E →
      c.prop 2 m.st.input s)
    {own : Place → S₃ → S₃ → Prop} (hk : L.keeps = lastKeeps own)
    (hown : ∀ k s m E,
      ThrS (lastThread h first reads (lastParts h first L) w) Said 1 k s m E →
      own ⟨3, none, 1, .frame⟩ s s) :
    FiveAtBorder (lastThread h first reads (lastParts h first L) w) Said fall 1 := by
  have hnext2 : ∀ k s m E,
      ThrS (lastThread h first reads (lastParts h first L) w) Said 1 k s m E →
      (lastParts h first L).rides 2 m.st.input s := by
    intro k s m E hA
    show ridersOf (doorRider _ (ToldDesc.p14At A.Z) :: L.riders) 2 m.st.input s
    rw [hrid]
    intro c hc hlo hhi
    have hc' : c = doorRider _ (ToldDesc.p14At A.Z) ∨
        c = tiedAheadRider _ (LLT25.c2 h.places).rounds ∨ c = tiedRider _ h.places ∨
        c ∈ later := by
      simpa [lastRiders] using hc
    rcases hc' with rfl | rfl | rfl | hc'
    · exact absurd (show 2 ≤ 0 from hhi) (by omega)
    · exact absurd (show 2 ≤ 0 from hhi) (by omega)
    · exact absurd (show 2 ≤ 1 from hhi) (by omega)
    · exact lays c hc' (Nat.le_antisymm hlo (late c hc')) k s m E hA
  have hst : ∀ s s', (lastThread h first reads (lastParts h first L) w).keeps 1 s s' → s' = s := by
    intro s s' hK
    have e := hK ⟨3, none, 1, .frame⟩ rfl
    have e' : L.keeps ⟨3, none, 1, .frame⟩ s s' := by
      unfold ProofFile.Honest.K14.kpSecond at e
      rwa [if_neg (by decide)] at e
    rw [hk] at e'
    exact e'.1 (Or.inl rfl)
  obtain ⟨p1, p2, p3, p4, p5⟩ := last_one h first reads (lastParts h first L) w Said
    (fun inp a b q _ _ v hp => AtFullSide.K14.pin₁_lastParts h first L inp a b q _ _ v hp)
    (fun inp a b e _ _ v hp => AtFullSide.K14.pin_lastParts h first L inp a b e _ _ v hp)
    (fun s s' v hK hv => by rw [hst s s' hK]; exact hv)
    (fun k s m E hA => ⟨hnext2 k s m E hA, by
      show L.keeps ⟨3, none, 1, .frame⟩ s s
      rw [hk]
      exact ⟨fun _ => rfl, hown k s m E hA⟩⟩)
    (fun k s m E hA => tied_at_one h first L reads w hrid hA.1) fall
  exact ⟨p1, p2, p3, p4, p5⟩

/-- **The same where every later clause begins at border 3 or later.** -/
theorem five_at_last_one_late (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (L : LastLetters A) (reads : IndexReaders W₀ Rc) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    {later : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hrid : L.riders = lastRiders h.places later) (late : ∀ c ∈ later, 3 ≤ c.lo)
    {own : Place → S₃ → S₃ → Prop} (hk : L.keeps = lastKeeps own)
    (hown : ∀ k s m E,
      ThrS (lastThread h first reads (lastParts h first L) w) Said 1 k s m E →
      own ⟨3, none, 1, .frame⟩ s s) :
    FiveAtBorder (lastThread h first reads (lastParts h first L) w) Said fall 1 :=
  five_at_last_one h first L reads w Said fall hrid
    (fun c hc => Nat.le_of_succ_le (late c hc))
    (fun c hc e => absurd (late c hc) (by omega)) hk hown

/-- **The member 1 says yes**, wherever the invariant holds in front of it: hrid alone is asked. -/
theorem acceptedS_one_last (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (L : LastLetters A) (reads : IndexReaders W₀ Rc) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    {later : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hrid : L.riders = lastRiders h.places later) :
    AcceptedS (lastThread h first reads (lastParts h first L) w) Said fall 1 :=
  acceptedS_takenSources _ Said rfl fun _ _ _ _ hA => tied_at_one h first L reads w hrid hA.1

end AtFullSide.Frames

#print axioms AtFullSide.Frames.tied_at_one
#print axioms AtFullSide.Frames.five_at_last_one
#print axioms AtFullSide.Frames.five_at_last_one_late
#print axioms AtFullSide.Frames.acceptedS_one_last
