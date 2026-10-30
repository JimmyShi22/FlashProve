--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/OwnGroup.lean: a group that is made and then filled, member by member: what
stays true of the statement on the way. Statements with their proofs.

Behind W's commitment kind K13's text makes the request's own group and lets the messages of the
claim's masks, W and, where the shape asks it, the split's message join it. Each joining is tested
at the statement as the joinings before have left it. This file carries the tests back to the
statement in front of the new group, so that a caller has to show them there alone.
Main names:
  `CanJoin S c z o`: the message o is there, its OOD sample is answered (the mark `sampled`), and
    its rows are under the codes c and z.
  `Built S₀ S g c z M`: five facts that hold where S comes from S₀ by making the group g under the
    codes c and z and by joinings to it: the codes and the tables are those of S₀; each message has
    its shape, its mark `sampled` and its pad as in S₀; no test has begun on g; the members of g are
    the numbers with M.
  `Built.start`: behind the making of the group, with no member.
  `Built.step`: one joining returns, and the statement behind it is `Built`, with one member more.
  `Built.steps`: the same of the text `joinAll`, for a list without repeats.
That a single joining returns, and that it leaves the tables, is `joinP_of` and `alike_joined`
(Johnson/Desc/K14/Honest/YesState.lean).

What is not claimed. That a message can join at any statement. Nothing on soundness, on an honest
prover's values or on hiding.

-/
import Johnson.Desc.K13.Law.AtM4
import Johnson.Desc.K14.Honest.YesState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.K13.Law

/-- The message o can join a group under the codes c and z. -/
def CanJoin (S : Statement) (c z o : ℕ) : Prop :=
  ∃ x : OnBytes.Oracle, S.oracles[o]? = some x ∧ x.sampled = true ∧
    (x.shape.mainRows = 0 ∨ x.shape.code = c) ∧ (x.shape.maskRows = 0 ∨ x.shape.maskCode = z)

/-- Five facts on S against S₀, which hold where S comes from S₀ by making the group g and by
joinings to it. M: which numbers are members. -/
structure Built (S₀ S : Statement) (g c z : ℕ) (M : ℕ → Prop) : Prop where
  codes : S.codes = S₀.codes
  orc : ∀ (o : ℕ) (x : OnBytes.Oracle), S₀.oracles[o]? = some x →
    ∃ x' : OnBytes.Oracle, S.oracles[o]? = some x' ∧ x'.shape = x.shape ∧
      x'.sampled = x.sampled ∧ x'.pad = x.pad
  bits : ∀ (o : ℕ) (part : OnBytes.Part), S.tableBits o part = S₀.tableBits o part
  tables : ∀ (o : ℕ) (part : OnBytes.Part), S.has o part = S₀.has o part
  grp : ∃ G : Group, S.groups[g]? = some G ∧ G.code = c ∧ G.maskCode = z ∧ G.inRun = false ∧
    ∀ o, o ∈ G.members.toList ↔ M o

variable {S₀ S : Statement} {g c z : ℕ} {M M' : ℕ → Prop}

/-- The members may be said in other words. -/
theorem Built.iff (h : Built S₀ S g c z M) (e : ∀ o, M o ↔ M' o) : Built S₀ S g c z M' := by
  obtain ⟨G, h1, h2, h3, h4, h5⟩ := h.grp
  exact ⟨h.codes, h.orc, h.bits, h.tables, G, h1, h2, h3, h4, fun o => (h5 o).trans (e o)⟩

/-- **Behind the making of the group**: no member. -/
theorem Built.start (S : Statement) (c z : ℕ) :
    Built S (Ground.withGroup S c z) S.groups.size c z fun _ => False :=
  ⟨rfl, fun _ x hx => ⟨x, hx, rfl, rfl, rfl⟩, fun _ _ => tableBits_congr rfl rfl _ _,
    fun _ _ => rfl,
    { code := c, maskCode := z }, by simp [Ground.withGroup], rfl, rfl, rfl, fun o => by simp⟩

/-- **One joining.** -/
theorem Built.step {o : ℕ} (d : St) (h : Built S₀ d.st g c z M) (ho : CanJoin S₀ c z o)
    (hn : ¬ M o) :
    ∃ d' : St, Ground.joinP d g o false = some d' ∧
      Built S₀ d'.st g c z fun o' => o' = o ∨ M o' := by
  obtain ⟨G, hG, hc, hz, hr, hm⟩ := h.grp
  obtain ⟨x, hx, h1, h3, h4⟩ := ho
  obtain ⟨x', hx', e1, e2, _⟩ := h.orc o x hx
  have h5 : G.members.contains o = false := by
    cases hcon : G.members.contains o with
    | false => rfl
    | true => exact absurd ((hm o).1 (by simpa using hcon)) hn
  have hpos : (G.members.filter (· < o)).size ≤ G.members.toList.length := by
    rw [Array.length_toList]
    exact Array.size_filter_le
  refine ⟨{ d with st := withMessageInGroup d.st g o false G },
    _root_.Desc.K14.Honest.joinP_of d g o G x' hG hx' (by rw [e2]; exact h1) hr
      (by rw [e1, hc]; exact h3) (by rw [e1, hz]; exact h4) h5, ?_⟩
  refine ⟨h.codes, fun o' y hy => ?_, fun o' part => ?_, fun o' part => ?_, ?_⟩
  · obtain ⟨y', hy', f1, f2, f3⟩ := h.orc o' y hy
    by_cases e : o = o'
    · subst e
      exact ⟨{ y' with groups := y'.groups ++ [g] }, joined_same _ _ _ _ _ _ hy', f1, f2, f3⟩
    · exact ⟨y', (joined_other _ _ _ _ _ _ e).trans hy', f1, f2, f3⟩
  · exact ((_root_.Desc.K14.Honest.alike_joined _ _ _ _ _).tableBits_eq o' part).trans
      (h.bits o' part)
  · exact ((_root_.Desc.K14.Honest.alike_joined _ _ _ _ _).has_eq o' part).trans (h.tables o' part)
  · refine ⟨_, joined_group _ _ _ _ _ hG, hc, hz, hr, fun o' => ?_⟩
    show o' ∈ (G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o).toList ↔ _
    rw [OnBytes.Means.toList_insertIdxIfInBounds, List.mem_insertIdx hpos, hm o']

/-- **Joinings in a row**, as the kind's text makes them. -/
theorem Built.steps : ∀ (l : List ℕ) (d : St) (M : ℕ → Prop), Built S₀ d.st g c z M →
    (∀ o ∈ l, CanJoin S₀ c z o) → l.Nodup → (∀ o ∈ l, ¬ M o) →
    ∃ d' : St, K13.joinAll g l d = .ok d' ∧ Built S₀ d'.st g c z fun o' => o' ∈ l ∨ M o'
  | [], d, _, h, _, _, _ =>
    ⟨d, rfl, h.iff fun _ => ⟨Or.inr, fun h' => h'.elim (fun h'' => absurd h'' List.not_mem_nil) id⟩⟩
  | o :: l, d, M, h, hc, hnd, hn => by
    obtain ⟨d₁, hj, h₁⟩ := Built.step d h (hc o List.mem_cons_self) (hn o List.mem_cons_self)
    have hnd' := List.nodup_cons.1 hnd
    obtain ⟨d', hd', h'⟩ := Built.steps l d₁ _ h₁
      (fun o' ho' => hc o' (List.mem_cons_of_mem _ ho')) hnd'.2
      (fun o' ho' hM => hM.elim (fun e => hnd'.1 (e ▸ ho')) (hn o' (List.mem_cons_of_mem _ ho')))
    refine ⟨d', ?_, h'.iff fun o' => ?_⟩
    · simp only [K13.joinAll, Law.bind_ok, Law.there_ok]
      exact ⟨d₁, hj, hd'⟩
    · show (o' ∈ l ∨ (o' = o ∨ M o')) ↔ (o' ∈ o :: l ∨ M o')
      rw [List.mem_cons]
      tauto

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.Built.iff
#print axioms VerifiableInference.Desc.K13.Honest.Built.start
#print axioms VerifiableInference.Desc.K13.Honest.Built.step
#print axioms VerifiableInference.Desc.K13.Honest.Built.steps
