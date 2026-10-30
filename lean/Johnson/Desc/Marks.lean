-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Marks.lean: NO NEW MARK: a relation on statements beside "a statement only grows"
(Johnson/Desc/Grows.lean). Grows lets a step lay the mark inRun on a group; this relation forbids
it: it is owed by every step but the beginning of a proximity test. Definitions and theorems.

  NoNewMark T T'       a group that bears the mark in T' stood in T at that number and bore it
                       there.
  NoNewMark.refl, NoNewMark.trans
  noNew_modGroup, noNew_oracles   a change of one group that lays no mark; of the messages alone.
  noNew_stSent · noNew_withGroup · noNew_admitted · noNew_joined · noNew_withRow ·
  noNew_closeLedgers   the plain changes of a statement, but for the beginning of a test.
  unmarked_of          along NoNewMark a group without the mark stays without it: so where a mark is
                       found at the end, some step that does not keep NoNewMark has laid it.
WHAT OF `verify-on-bytes` IS USED: as in Johnson/Desc/Grows.lean.
What is not claimed. That the step which lays the mark has run a test: that is the proximity test's
own law. NOTHING ON ROWS.

-/
import Johnson.Desc.Grows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Slice

/-- A group that bears the mark behind stood at that number in front and bore it there. -/
def NoNewMark (T T' : Statement) : Prop :=
  ∀ (i : Nat) G', T'.groups[i]? = some G' → G'.inRun = true →
    ∃ G, T.groups[i]? = some G ∧ G.inRun = true

/-- A statement lays no new mark on itself. -/
theorem NoNewMark.refl (T : Statement) : NoNewMark T T := fun _ G h m => ⟨G, h, m⟩

/-- No new mark, twice over, is no new mark. -/
theorem NoNewMark.trans {A B C : Statement} (h : NoNewMark A B) (k : NoNewMark B C) :
    NoNewMark A C := by
  intro i G hG m
  obtain ⟨G', h1, m1⟩ := k i G hG m
  exact h i G' h1 m1

/-- A change of one group that lays no mark. -/
theorem noNew_modGroup (T : Statement) (k : Nat) (f : Group → Group)
    (hf : ∀ G, (f G).inRun = G.inRun) : NoNewMark T { T with groups := T.groups.modify k f } := by
  intro i G' h m
  have h' : (T.groups.modify k f)[i]? = some G' := h
  rw [Array.getElem?_modify] at h'
  split at h'
  · cases hg : T.groups[i]? with
    | none => simp [hg] at h'
    | some G =>
      simp only [hg, Option.map_some, Option.some.injEq] at h'
      subst h'
      exact ⟨G, rfl, (hf G) ▸ m⟩
  · exact ⟨G', h', m⟩

/-- A change of the oracle messages alone. -/
theorem noNew_oracles (T : Statement) (os : Array OnBytes.Oracle) :
    NoNewMark T { T with oracles := os } :=
  fun _ G h m => ⟨G, h, m⟩

/-- Messages are received: no new mark. -/
theorem noNew_stSent (T : Statement) (sent : Array OracleNotice) : NoNewMark T (stSent T sent) :=
  noNew_oracles T _

/-- A new group bears no mark. -/
theorem noNew_withGroup (T : Statement) (code maskCode : Nat) :
    NoNewMark T (withGroup T code maskCode) := by
  intro i G' h m
  have h' : (T.groups.push { code := code, maskCode := maskCode })[i]? = some G' := h
  rw [Array.getElem?_push] at h'
  split at h'
  · cases h'
    cases m
  · exact ⟨G', h', m⟩

/-- A message's sample is admitted: no new mark. -/
theorem noNew_admitted (T : Statement) (o : Nat) (s : OracleShape) (p : List PadPlace)
    (rows : Array OnBytes.Row) : NoNewMark T (admitted T o s p rows) := noNew_oracles T _

/-- A message joins a group: no new mark. -/
theorem noNew_joined (T : Statement) (g o : Nat) (kept : Bool) (G : Group) :
    NoNewMark T (withMessageInGroup T g o kept G) :=
  (noNew_modGroup T g (fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept })
    fun _ => rfl).trans (noNew_oracles _ _)

/-- A row is added to a group: no new mark. -/
theorem noNew_withRow (T : Statement) (g : Nat) (row : OnBytes.Row) :
    NoNewMark T (withRow T g row) :=
  noNew_modGroup T g (fun G => { G with rows := G.rows.push row }) fun _ => rfl

/-- Ledgers of mask entries are closed: no new mark. -/
theorem noNew_closeLedgers (l : List Nat) : ∀ T : Statement, NoNewMark T (closeLedgers T l) := by
  induction l with
  | nil => exact NoNewMark.refl
  | cons o l ih =>
    intro T
    exact (noNew_oracles T _).trans (ih _)

/-- Along NoNewMark a group without the mark stays without it. -/
theorem unmarked_of (T T' : Statement) (h : NoNewMark T T') (i : Nat) (G G' : Group)
    (hG : T.groups[i]? = some G) (hG' : T'.groups[i]? = some G') (hm : G.inRun = false) :
    G'.inRun = false := by
  cases hx : G'.inRun with
  | false => rfl
  | true =>
    obtain ⟨G₀, h0, m0⟩ := h i G' hG' hx
    rw [hG] at h0
    cases h0
    rw [hm] at m0
    cases m0

end VerifiableInference.Desc
