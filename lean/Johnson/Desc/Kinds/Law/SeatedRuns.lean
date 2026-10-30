-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SeatedRuns.lean.
WHAT IT DOES NOT SHOW. No soundness. NOTHING ON WHAT A CLAIM IS WORTH: which function stands under
which name, and no more. Nothing on the guard that a chain lays around a run.
LETTERS. Under "there is": iU3: pinned by W.H.tl.ix.U.getD 2 none = some iU3.
OBJECT. The block as a lot seats it (Stored/HeadAddsAtS.lean: seatedClaims W l ms): its field
claims.
USER. The laws on the kind's own three runs and on "join", which are stated at the kind's block
(kind asClaim (seatAt h iU3) l 4 p) and at the term K3.joinRun ...: they pass to the seated block.
WHAT IT IS. THE SEATED BLOCK's FOUR RUNS ARE THE KIND's OWN THREE, UNDER THEIR NAMES, AND THE
LOOKUP's "join" AT THE HEAD's KEY VECTORS.
  seated_claims     the list, written out: the kind's first run, "join", the kind's other runs.
  seated_run        a run that is looked up under a name other than "join" is the kind's run of that
                    name.
  seated_join       the run that is looked up under "join" is K3.joinRun at the head's key vectors.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.SeatedBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)

/-- The bits of work that the block reads off the public record. -/
abbrev workAtW (W : Model.Verify.Public) : Nat :=
  (Params.settingOf W.P.frame).workOf .field .request

/-- **The seated block's list of runs, written out.** -/
theorem seated_claims {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) :
    ∃ iU3, W.H.tl.ix.U.getD 2 none = some iU3 ∧
      b.claims = (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workAtW W))).claims.take 1 ++
        [("join", K3.joinRun (K3.seatCalls asClaim)
          (callerKeys (parOf W.hS (workAtW W)) (seatAt W.hS iU3)))] ++
        (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workAtW W))).claims.drop 1 := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨iU3, hU, rfl⟩ := Option.map_eq_some_iff.mp h0
  exact ⟨iU3, hU, rfl⟩

/-- The kind's own list of runs has the three names. -/
theorem kind_names {Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par) :
    (kind cl L link piece p).claims.map (·.1) = ["norm", "policy", "logits"] := rfl

/-- **A run under a name other than "join" is the kind's run of that name.** -/
theorem seated_run {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) {name : String}
    {run : Nat → S → Except String (List Claim × S)} (hr : b.claims.lookup name = some run)
    (hn : name ≠ "join") :
    ∃ iU3, W.H.tl.ix.U.getD 2 none = some iU3 ∧
      (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workAtW W))).claims.lookup name
        = some run := by
  obtain ⟨iU3, hU, e⟩ := seated_claims h
  refine ⟨iU3, hU, ?_⟩
  rw [e] at hr
  have hj : (name == "join") = false := by simpa using hn
  have e3 : (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workAtW W))).claims =
      (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workAtW W))).claims.take 1 ++
        (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workAtW W))).claims.drop 1 :=
    (List.take_append_drop 1 _).symm
  rw [e3]
  generalize (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workAtW W))).claims.take 1 = A at hr ⊢
  generalize (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workAtW W))).claims.drop 1 = B at hr ⊢
  induction A with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.lookup_cons, hj] at hr
    exact hr
  | cons a A ih =>
    rw [List.cons_append, List.cons_append, List.lookup_cons] at hr
    rw [List.cons_append, List.lookup_cons]
    cases hk : name == a.1 with
    | true =>
      rw [hk] at hr
      exact hr
    | false =>
      rw [hk] at hr
      exact ih hr

/-- **The run under "join".** -/
theorem seated_join {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b)
    {run : Nat → S → Except String (List Claim × S)} (hr : b.claims.lookup "join" = some run) :
    ∃ iU3, W.H.tl.ix.U.getD 2 none = some iU3 ∧
      run = K3.joinRun (K3.seatCalls asClaim)
        (callerKeys (parOf W.hS (workAtW W)) (seatAt W.hS iU3)) := by
  obtain ⟨iU3, hU, e⟩ := seated_claims h
  refine ⟨iU3, hU, ?_⟩
  rw [e] at hr
  exact (Option.some.inj hr).symm

end VerifiableInference.Desc.Kinds.Head.Law
