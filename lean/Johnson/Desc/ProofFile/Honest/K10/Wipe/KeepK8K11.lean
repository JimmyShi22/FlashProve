-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK8K11.lean: the closing of a segment (K10): the smallness test's block (kind
K8, Johnson/Desc/First/K8/Whole.lean: whole) and the block that merges the claims on the weights at the head's link
(kind K11, Johnson/Desc/First/Fork/MergeKind.lean: headClaimMergeKind) do alike at two states of the first chain that are one
once wiped. One structure of type Prop; the rest are theorems.

Words. wipeS sets to zero the targets of the rows that a state of the first chain holds (Honest/K10/WipeS.lean says
which). Two states are one under w where w s = w s'. A reader does not see w where it returns at w s what it returns
at s. A writer goes through w where it returns at w s the image under w of what it returns at s. Two outcomes are
alike where both refuse with the same word, or both return and the values are one under w (AlikeE, Wipe/Alike.lean). A
block does alike (Whole2 w) where its decide, each of its runs of claims and each of its runs behind the batching have
like outcomes at two states that are one under w; the claims of a run are then equal.

What is proved.
  K8Blind w L     what is asked of a seat L of K8's hearing: its eight readers do not see w; its laying goes through w
  hear_whole2     K8Blind w L ⊢ Whole2 w (K8.approximateRangeProofDrawKind L p), at any type of state
  k8AtS_blind     K8Blind wipeS K8.atS
  k8Get_blind, k8Set_wipe, atRecord_comm   the part of the state that K8's three runs read does not see the wiping;
                  its laying goes through the wiping; so does any run at the part that atRecord lays at the state
  **k8_keeps**      Whole2 wipeS (K8.whole p): the field k8 of SeatKeeps2 (Wipe/Lots2.lean)
  headMergeDecide_wiped, headMergeClaim_wiped   K11's decide, and its one run of claims, have like outcomes at wipeS s
                  and at s
  **k11_keeps**     Whole2 wipeS (headClaimMergeKind P): the field k11

By what. K8's hearing is a ladder of tests on the seat's readers, then the seat's laying: one AlikeE.iteB
(Wipe/KeepBase.lean) for each rung. The three runs' texts are not opened: they are handed the part, which is equal.
K11's two texts are typed at the first chain's state: the state is taken apart; outside the head's link both refuse
with one word; inside it the text at wipeS s and the text at s make the same calls, one after the other
(AlikeE.head'), and the state that the first returns is the second's, wiped (alike_of_wiped).

Limits. Nothing is said of what K8's runs or K11's mergeHear compute. No property of the protocol is claimed: nothing
is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepBase
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (K8Part k8PartP)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headMergeClaim headClaimMergeKind)

/-! ## 1 K8's hearing, at any type of state -/

/-- What is asked of a seat of K8's hearing: the readers do not see w; the laying goes through w. -/
structure K8Blind {T : Type} (w : T → T) (L : K8.Seat T) : Prop where
  closed : ∀ s, L.closed (w s) = L.closed s
  nothingOwed : ∀ s, L.nothingOwed (w s) = L.nothingOwed s
  drawn : ∀ s, L.drawn (w s) = L.drawn s
  matrices : ∀ s, L.matrices (w s) = L.matrices s
  ks : ∀ s, L.ks (w s) = L.ks s
  ms : ∀ s, L.ms (w s) = L.ms s
  tau : ∀ s, L.tau (w s) = L.tau s
  tabs : ∀ s, L.tabs (w s) = L.tabs s
  lay : ∀ s m first, L.lay (w s) m first = (L.lay s m first).map w

/-- **K8's hearing does alike at a seat whose readers do not see w and whose laying goes through w.** -/
theorem hear_whole2 {T Cl : Type} {w : T → T} {L : K8.Seat T} (h : K8Blind w L) (p : K8.Par) :
    Whole2 w (K8.approximateRangeProofDrawKind (Cl := Cl) L p) := by
  refine whole2_bare (fun s s' rs gs gs' hs _ => ?_) rfl rfl
  rcases rs with _ | ⟨r, _ | ⟨r', rest⟩⟩
  · exact AlikeE.error _
  · have e : AlikeE w (L.lay s r.drawn.trits.toArray (K8.firstColumns p))
        (L.lay s' r.drawn.trits.toArray (K8.firstColumns p)) := by
      have e' : (L.lay s r.drawn.trits.toArray (K8.firstColumns p)).map w =
          (L.lay s' r.drawn.trits.toArray (K8.firstColumns p)).map w := by
        rw [← h.lay s, ← h.lay s', hs]
      exact e'
    simp only [K8.approximateRangeProofDrawKind]
    refine AlikeE.iteB (by rw [blind2 (f := L.closed) h.closed hs]) (AlikeE.error _) ?_
    refine AlikeE.iteB (by rw [blind2 (f := L.nothingOwed) h.nothingOwed hs]) (AlikeE.error _) ?_
    refine AlikeE.iteB (by rw [blind2 (f := L.drawn) h.drawn hs]) (AlikeE.error _) ?_
    refine AlikeE.iteB (by rw [blind2 (f := L.matrices) h.matrices hs]) (AlikeE.error _) ?_
    refine AlikeE.iteB (by rw [blind2 (f := L.ks) h.ks hs]) (AlikeE.error _) ?_
    refine AlikeE.iteB (by rw [blind2 (f := L.ms) h.ms hs]) (AlikeE.error _) ?_
    refine AlikeE.iteB (by rw [blind2 (f := L.tau) h.tau hs]) (AlikeE.error _) ?_
    exact AlikeE.iteB (by rw [blind2 (f := L.tabs) h.tabs hs]) (AlikeE.error _) e
  · exact AlikeE.error _

/-! ## 2 K8 at the first chain's state -/

/-- The seat of K8's hearing at the first chain's state: its readers do not see the wiping; its laying goes through
it. -/
theorem k8AtS_blind : K8Blind wipeS K8.atS where
  closed s := by
    show (((wipeS s).tl?.map (·.funClosed)).getD false) = ((s.tl?.map (·.funClosed)).getD false)
    rw [tl?_wipe]
  nothingOwed _ := rfl
  drawn s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl
  matrices s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl
  ks s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl
  ms s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl
  tau s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl
  tabs s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl
  lay s m first := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- The part of the state that K8's three runs read is the same at the wiped state and at the state. -/
theorem k8Get_blind (s : S) : k8PartP.get? (wipeS s) = k8PartP.get? s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- The laying of that part goes through the wiping. -/
theorem k8Set_wipe (s : S) (q : K8Part) : k8PartP.set (wipeS s) q = wipeS (k8PartP.set s q) := by
  show ((wipeS s).putTl q.tl).putFork q.F = wipeS ((s.putTl q.tl).putFork q.F)
  rw [putFork_wipe, putTl_wipe]

/-- Any run at the part, as atRecord lays it at the state, goes through the wiping. -/
theorem atRecord_comm {α : Type} (f : K8Part → Except String (α × K8Part)) (s : S) :
    K8.atRecord f (wipeS s) = (K8.atRecord f s).map fun y => (y.1, wipeS y.2) := by
  unfold K8.atRecord
  rw [k8Get_blind]
  cases k8PartP.get? s with
  | none => rfl
  | some q =>
    show (f q).map (fun x => (x.1, k8PartP.set (wipeS s) x.2)) =
      ((f q).map fun x => (x.1, k8PartP.set s x.2)).map fun y => (y.1, wipeS y.2)
    cases f q with
    | error e => rfl
    | ok x =>
      show (Except.ok (x.1, k8PartP.set (wipeS s) x.2) : Except String (α × S)) =
        Except.ok (x.1, wipeS (k8PartP.set s x.2))
      rw [k8Set_wipe]

/-- **Kind K8's block does alike at two states that are one once wiped.** -/
theorem k8_keeps (p : K8.ParW) : Whole2 wipeS (K8.whole p) := by
  refine ⟨(hear_whole2 (Cl := Claim) k8AtS_blind p.toPar).1, fun c hc n => ?_, fun c hc => ?_⟩
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    exact FnCl2.of_comm fun s => atRecord_comm _ s
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    exact Fn2.of_comm fun s => snd_comm (atRecord_comm _ s)

/-! ## 3 K11 -/

/-- K11's decide has like outcomes at the wiped state and at the state. -/
theorem headMergeDecide_wiped (P : HeadMergeP) (s : S) (rs : List Fmt.RoundView) :
    AlikeE wipeS (headMergeDecide P (wipeS s) rs) (headMergeDecide P s rs) := by
  obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s
  cases here with
  | between => exact AlikeE.error _
  | lay a => exact AlikeE.error _
  | att a => exact AlikeE.error _
  | fin a => exact AlikeE.error _
  | mem a => exact AlikeE.error _
  | head a =>
    unfold headMergeDecide wipeS wipeHere
    dsimp only
    refine AlikeE.head' fun _ => ?_
    refine AlikeE.head' fun _ => ?_
    refine AlikeE.head' fun t => ?_
    refine AlikeE.head' fun claim => ?_
    refine AlikeE.head' fun x => ?_
    refine AlikeE.head' fun y => ?_
    obtain ⟨wo, F, t'⟩ := y
    refine AlikeE.head' fun _ => ?_
    refine AlikeE.head' fun _ => ?_
    exact AlikeE.ok (alike_of_wiped rfl)

/-- K11's one run of claims has like outcomes, with equal claims, at the wiped state and at the state. -/
theorem headMergeClaim_wiped (n : Nat) (s : S) :
    AlikeE (wCl wipeS) (headMergeClaim n (wipeS s)) (headMergeClaim n s) := by
  obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s
  cases here with
  | between => exact AlikeE.error _
  | lay a => exact AlikeE.error _
  | att a => exact AlikeE.error _
  | fin a => exact AlikeE.error _
  | mem a => exact AlikeE.error _
  | head a =>
    unfold headMergeClaim wipeS wipeHere
    dsimp only
    refine AlikeE.head' fun wo => ?_
    refine AlikeE.head' fun x => ?_
    exact AlikeE.ok (alikeCl_of_wiped rfl)

/-- **Kind K11's block does alike at two states that are one once wiped.** -/
theorem k11_keeps (P : HeadMergeP) : Whole2 wipeS (headClaimMergeKind P) := by
  refine ⟨Decides2.of_wiped (fun _ _ _ _ => rfl) fun s rs _ => headMergeDecide_wiped P s rs,
    fun c hc n => ?_, (fun _ hc => nomatch hc)⟩
  obtain rfl := List.mem_singleton.1 hc
  exact FnCl2.of_wiped fun s => headMergeClaim_wiped n s

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.K8Blind
#print axioms ProofFile.Honest.K10.hear_whole2
#print axioms ProofFile.Honest.K10.k8AtS_blind
#print axioms ProofFile.Honest.K10.k8Get_blind
#print axioms ProofFile.Honest.K10.k8Set_wipe
#print axioms ProofFile.Honest.K10.atRecord_comm
#print axioms ProofFile.Honest.K10.k8_keeps
#print axioms ProofFile.Honest.K10.headMergeDecide_wiped
#print axioms ProofFile.Honest.K10.headMergeClaim_wiped
#print axioms ProofFile.Honest.K10.k11_keeps
