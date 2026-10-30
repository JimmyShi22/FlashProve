-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06Runs.lean: THE KIND's OWN RUNS ARE `claims` (for K06_law: so that the laws of
K06Statement.lean, which name Head.lean's `claims`, speak of the block's own list). `k6_run_spec`:
where a named run of `kind …`.claims returns at a record, the letters are there (`lettersAt`), and the
claims that it makes are the forms that `claims`, under these letters, holds under that name, each
through the map from a form to a claim. By unfolding HeadFrame.lean's runsBy. No Mathlib.
WHAT IT DOES NOT SAY: what the letters are (that is `lettersAt`'s text: the lookup's points by
HeadIn.lean's fromLookup; what was heard and the reads' places off the record).
-/
import Johnson.Desc.Kinds.HeadKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

theorem lookup_map_self {β : Type} (F : String → β) : ∀ (names : List String) (name : String) (r : β),
    (names.map fun a => (a, F a)).lookup name = some r → r = F name
  | [], _, _, h => by simp at h
  | a :: as, name, r, h => by
    simp only [List.map_cons, List.lookup_cons] at h
    split at h
    · rename_i he
      have : name = a := by simpa using he
      subst this
      exact (Option.some.inj h).symm
    · exact lookup_map_self F as name r h

/-- **The kind's own runs are `claims`.** -/
theorem k6_run_spec {S Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (par : Par)
    (name : String) (run : Nat → S → Except String (List Cl × S)) (n : Nat) (s s' : S)
    (cls : List Cl) (h1 : (kind cl L link piece par).claims.lookup name = some run)
    (h2 : run n s = .ok (cls, s')) :
    ∃ (g : Given) (b : Behind) (x : Places) (fs : List Form),
      lettersAt par L s = .ok (g, b, x) ∧
      ((fun (_ : Given) (_ : Behind) (_ : Places) => claims) g b x).lookup name = some fs ∧
      cls = fs.map cl := by
  have h1' : (runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
      (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) cl par L).lookup name = some run := h1
  unfold runsBy at h1'
  have hr := lookup_map_self _ _ _ _ h1'
  subst hr
  simp only [bind, Except.bind, pure, Except.pure] at h2
  split at h2
  · simp at h2
  · rename_i v hv
    obtain ⟨g, b, x⟩ := v
    split at h2
    · simp at h2
    · rename_i fs hfs
      simp only [Except.ok.injEq, Prod.mk.injEq] at h2
      refine ⟨g, b, x, fs, hv, ?_, h2.1.symm⟩
      unfold named at hfs
      split at hfs
      · rename_i y hy
        simp only [Except.ok.injEq] at hfs
        rw [← hfs]; exact hy
      · simp at hfs

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_run_spec
