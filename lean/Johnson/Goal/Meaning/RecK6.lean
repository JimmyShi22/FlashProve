-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecK6.lean: the output head's own block at the first chain's record (kind K6:
Johnson/Desc/Kinds/HeadKind.lean, HeadCaller.lean; its seat: Johnson/Stored/HeadSeatAt.lean) writes
neither the statement nor a copy of the frame of the links: it is Quiet
(Johnson/Goal/Meaning/RecQuiet.lean): so it hands RecAll on, and the statement grows.

  k6_whole: A GENERAL RULE, at any seat L and any reflexive and transitive relation R that the
    seat's four layings keep (setLedger, setHeard, setWeightClaim, setKeyForms): Whole R of the
    kind.
    The decision by its own text (decideBy, Johnson/Desc/Kinds/HeadFrame.lean), taken apart here.
  k6Join_whole: the like of the kind with its run "join", where the lookup's seat's mark keeps R.
  seatAt's four layings are Quiet.
  blockAt_quiet, blockOf_quiet: Whole Quiet of the kind's block at the record.
Not claimed: that this is the block that a seated description lays at the head's link.
OBJECT: the makers' blocks and steps that are named above. USERS: through whole_rec |
recRel_of_quiet the walk (Johnson/Goal/Meaning/RecWalk.lean: recAll_border, at the letters cs and
sh); through whole_grows | groundKeeps_grows the owed premise of Johnson/Desc/StatementGrows.lean
(ChainKeeps (GrowsBy st) c). Neither calls them yet. Which maker stands at which place of a seated
text is not said here.
-/
import Johnson.Goal.Meaning.RecK5K8
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole)
open VerifiableInference.Desc.Kinds.Head

variable {T Cl : Type}

/-- **The kind, at any seat.** -/
theorem k6_whole (R : T → T → Prop) (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (L : Seat T) (h1 : ∀ s F s', L.setLedger s F = .ok s' → R s s')
    (h2 : ∀ s H s', L.setHeard s H = .ok s' → R s s') (h3 : ∀ s w, R s (L.setWeightClaim s w))
    (h4 : ∀ s k, R s (L.setKeyForms s k)) (cl : Kinds.Form → Cl) (link piece : Nat)
    (p : Kinds.Head.Par) :
    Whole R (kind cl L link piece p) := by
  refine ⟨fun s rs gs s' h => ?_, fun c hc n s y h => ?_, (fun _ hc => nomatch hc)⟩
  · have h' := h
    simp only [kind] at h'
    unfold decideBy at h'
    obtain ⟨g, -, h'⟩ := bindE h'
    obtain ⟨_, -, h'⟩ := bindE h'
    obtain ⟨⟨H, F, left⟩, -, h'⟩ := bindE h'
    obtain ⟨_, -, h'⟩ := bindE h'
    obtain ⟨s1, e1, h'⟩ := bindE h'
    obtain ⟨s2, e2, h'⟩ := bindE h'
    cases h'
    exact ht _ _ _ (ht _ _ _ (h1 _ _ _ e1) (h2 _ _ _ e2)) (h3 _ _)
  · have hc' : c ∈ runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
        (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) cl p L := hc
    unfold runsBy at hc'
    obtain ⟨name, -, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨⟨g, b, x⟩, -, h⟩ := bindE h
    obtain ⟨fs, -, h⟩ := bindE h
    cases h
    dsimp only
    split
    · exact h4 _ _
    · exact hr _

/-- **The kind with its run "join".** -/
theorem k6Join_whole (R : T → T → Prop) (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (look : K3.Seat T Cl) (hm : ∀ s G, R s (look.mark s G)) (L : Seat T)
    (h1 : ∀ s F s', L.setLedger s F = .ok s' → R s s')
    (h2 : ∀ s H s', L.setHeard s H = .ok s' → R s s') (h3 : ∀ s w, R s (L.setWeightClaim s w))
    (h4 : ∀ s k, R s (L.setKeyForms s k)) (link piece : Nat) (p : Kinds.Head.Par) :
    Whole R (kindWithJoin look L link piece p) := by
  have W := k6_whole R hr ht L h1 h2 h3 h4 look.claim link piece p
  refine ⟨W.1, fun c hc => ?_, W.2.2⟩
  have hc' : c ∈ (kind look.claim L link piece p).claims.take 1 ++
      [("join", K3.joinRun look (callerKeys p L))] ++
      (kind look.claim L link piece p).claims.drop 1 := hc
  rcases List.mem_append.1 hc' with h | h
  · rcases List.mem_append.1 h with h | h
    · exact W.2.1 c (List.mem_of_mem_take h)
    · obtain rfl := List.mem_singleton.1 h
      exact fun n => joinRun_keep R look hm _ n
  · exact W.2.1 c (List.mem_of_mem_drop h)

/-! ## At the record -/

theorem seatAt_ledger (h : Model.Head.Shape) (iU3 : Nat) (s : S) (F : Fork) (s' : S)
    (e : (seatAt h iU3).setLedger s F = .ok s') : Quiet s s' := by
  have e' : s.putFork? F = .ok s' := e
  unfold S.putFork? at e'
  split at e'
  · rw [quiet_unmarked e']
    exact quiet_putFork s F
  · cases e'

theorem seatAt_heard (h : Model.Head.Shape) (iU3 : Nat) (s : S) (H : HeardAll) (s' : S)
    (e : (seatAt h iU3).setHeard s H = .ok s') : Quiet s s' := by
  simp only [seatAt] at e
  split at e
  · rename_i o ho
    split at e
    · cases e
      refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩,
        by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun w => w, fun _ e => e⟩
      unfold framesIn at hf ⊢
      rw [ho]
      exact hf
    · cases e
  · cases e

/-- **The output head's own block at the record is Quiet.** -/
theorem blockAt_quiet (h : Model.Head.Shape) (iU3 work l : Nat) :
    Whole Quiet (Kinds.Head.blockAt h iU3 work l) :=
  k6Join_whole Quiet quiet_refl quiet_trans _ (seatCalls_mark _) (seatAt h iU3)
    (seatAt_ledger h iU3) (seatAt_heard h iU3) (fun s _ => quiet_refl s) (fun s _ => quiet_refl s)
    l 4 (parOf h work)

theorem blockOf_quiet {W : Verify.Public} {l : Nat} {b : Block S Unit}
    (hb : Kinds.Head.blockOf W l = some b) : Whole Quiet b := by
  unfold Kinds.Head.blockOf at hb
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact blockAt_quiet _ _ _ _

#print axioms k6_whole
#print axioms k6Join_whole
#print axioms blockAt_quiet
#print axioms blockOf_quiet

end Meaning.K2
