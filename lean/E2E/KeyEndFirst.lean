--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyEndFirst.lean: THE LAST SUB-PROTOCOL OF THE KEY FILE's FIRST CHAIN ("seal") ACCEPTS, FROM THE
BOOK-KEEPING OF THE STATE IN FRONT OF IT; and what that book-keeping hands to the third chain's end.
The seal has one round, in which nothing is sent, and no part of a prover. It asks three tests on
the carried state: no count of rows is owed; a proximity test has begun on every group but the own
one; every sampled message is a member of the own group or in a tested group. Statements and proofs.
Single tests of the verifier's: NOTHING IS SHOWN OF ANY PROVER: no completeness, nothing on what a
view shows.

The direction is that of E2E/KeyEnds.lean: the book-keeping in front GIVES the acceptance.

`End₁ n a s`: THE BOOK-KEEPING THAT IS SPENT, clause by clause; n: the number of stages of the
proximity test on the ranges; a: the answers to a sample. Message 0 holds the index masks, 1 is the
lookups' own message, 2 the mask of that test's first fold; each later stage has a sampled message
alone in a group and a spent mask; behind them W and the mask of the own test's first fold. Group 0
is the ranges', the last group the own one.
WHAT OF IT THE LIBRARY's TEST ON THIS CHAIN's BOOK-KEEPING HOLDS (`shape₁` at its border 18,
Johnson/Desc/Key/KeyShape.lean with Johnson/RunOne/KeyReaders1.lean), by a reading of its text: the
counts; the own group, its two members and that it is the last; W's number; that the groups FROM
THE RANGES' GROUP ON but the last have begun their tests. WHAT IT DOES NOT HOLD: that the ranges'
group is group 0; that group's member behind the test; which of the later stages' messages are
sampled and in which groups they lie; that no count of rows is owed; `Joined`. No theorem here ties
`End₁` to `shape₁`.

What is shown.
  **`butOwn_ok`**: for any state of the first chain whose claim names an own group, with `Joined`:
    if every group but the own one has begun its test, and every message has no sample, or is a
    member of the own group, or of a group whose test has begun: the seal's two tests on the
    statement accept.
  `End₁.begun`, `End₁.home`: these two premises, from `End₁`.
  **`seal_passes`**: where the state in front has `End₁` and `Joined`, the seal accepts and hands
    the state on as it is.
  **`older_of_end₁`**: `End₁` gives `Older` (E2E/KeyEnds.lean) at the same statement: what the third
    chain's end wants of the first chain's messages and groups.
  `toy₁`, `toy₁_member`: a member: `End₁` and `Joined` hold together. A toy of two stages.

Limits.
- That a run's state in front of the seal has `End₁` and `Joined` is not shown.
- `older_of_end₁` speaks of the first chain's LAST statement. The third chain's end reads its own
  statement, which the third chain's sub-protocols have made of that one: that they keep `Older` is
  not shown here.
- The numbers are those of three messages and one group in front of the ranges' test: the form of
  the library's own counts.


-/
import E2E.KeyEnds
import Johnson.Desc.Key.Chain1

set_option autoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes
open VerifiableInference.Desc.Key (ChainState untestedButOwn firstChainEnd Pieces)
open LKFU.Shape23 (grpIs msgIs towerIs)

/-- **The seal's two tests on the statement accept.** -/
theorem butOwn_ok {β : Type} (s : ChainState β) (L : LinFirst) (hl : s.lin = some L)
    (hj : Joined s.d.st)
    (hg : ∀ (g : Nat) (G : OnBytes.Group), s.d.st.groups[g]? = some G → G.inRun = true ∨ g = L.own)
    (ho : ∀ (o : Nat) (x : Oracle), s.d.st.oracles[o]? = some x → x.sampled = false ∨
      (∃ G : OnBytes.Group, s.d.st.groups[L.own]? = some G ∧ o ∈ G.members.toList) ∨
      ∃ (g : Nat) (G : OnBytes.Group), s.d.st.groups[g]? = some G ∧ o ∈ G.members.toList ∧
        G.inRun = true) :
    ∀ c ∈ untestedButOwn s, c.2 = true := by
  intro c hc
  unfold untestedButOwn at hc
  simp only [hl, Option.map_some] at hc
  rcases List.mem_cons.1 hc with rfl | hc
  · refine List.all_eq_true.2 fun y hy => ?_
    have e := List.mem_zipIdx_iff_getElem?.1 hy
    rw [Array.getElem?_toList] at e
    show (y.1.inRun || some L.own == some y.2) = true
    rcases hg y.2 y.1 e with r | r
    · rw [r]
      rfl
    · rw [r]
      exact Bool.or_eq_true_iff.2 (Or.inr (beq_self_eq_true _))
  · rcases List.mem_cons.1 hc with rfl | hc
    · refine List.all_eq_true.2 fun y hy => ?_
      have e := List.mem_zipIdx_iff_getElem?.1 hy
      rw [Array.getElem?_toList] at e
      show (!y.1.sampled ||
          ((some L.own).bind fun g => s.d.st.groups[g]?).any (·.members.contains y.2) ||
          y.1.groups.any fun g => (s.d.st.groups[g]?).any (·.inRun)) = true
      rcases ho y.2 y.1 e with r | ⟨G, hG, hm⟩ | ⟨g, G, hG, hm, r⟩
      · rw [r]
        rfl
      · have hm' : G.members.contains y.2 = true :=
          Array.contains_iff_mem.2 (Array.mem_toList_iff.1 hm)
        have t : (((some L.own).bind fun g => s.d.st.groups[g]?).any
            (·.members.contains y.2)) = true := by
          show (s.d.st.groups[L.own]?).any (·.members.contains y.2) = true
          rw [hG]
          exact hm'
        rw [t]
        simp only [Bool.or_true, Bool.true_or]
      · have t : (y.1.groups.any fun g => (s.d.st.groups[g]?).any (·.inRun)) = true :=
          List.any_eq_true.2 ⟨g, hj g G y.2 y.1 hG hm e, by rw [hG]; exact r⟩
        rw [t]
        simp only [Bool.or_true]
    · cases hc

/-- **The book-keeping in front of the seal that is spent.** n: the stages of the proximity test on
the ranges; a: the answers to a sample. -/
structure End₁ {β : Type} (n a : Nat) (s : ChainState β) : Prop where
  stages : 1 ≤ n
  waits : s.noneWaits = true
  own : ∃ L : LinFirst, s.lin = some L ∧ L.own = n
  msgs : s.d.st.oracles.size = 3 + 2 * (n - 1) + 2
  grps : s.d.st.groups.size = n + 1
  ranges : grpIs s.d.st 0 [1] 0 0 true = true
  rider : msgIs s.d.st 2 none true = true
  tower : towerIs s.d.st 3 1 n a = true
  group : grpIs s.d.st n [0, 3 + 2 * (n - 1)] 1 0 false = true
  mask : msgIs s.d.st (3 + 2 * (n - 1) + 1) none false = true

section End1
variable {β : Type} {n a : Nat} {s : ChainState β} (h : End₁ n a s)
include h

/-- Every group but the last has begun its test. -/
theorem End₁.begun (g : Nat) (hg : g < n) :
    ∃ G : OnBytes.Group, s.d.st.groups[g]? = some G ∧ G.inRun = true := by
  by_cases c0 : g = 0
  · subst c0
    obtain ⟨G, e, -, r⟩ := grpIs_spec h.ranges
    exact ⟨G, e, r⟩
  · obtain ⟨-, -, t⟩ := towerIs_spec h.tower (g - 1) (by omega)
    obtain ⟨G, e, -, r⟩ := grpIs_spec t
    have i : 1 + (g - 1) = g := by omega
    rw [i] at e
    exact ⟨G, e, r⟩

/-- Every message has no sample, or is a member of the own group, or of a group whose test has
begun. -/
theorem End₁.home (o : Nat) (ho : o < s.d.st.oracles.size) :
    (∃ x : Oracle, s.d.st.oracles[o]? = some x ∧ x.sampled = false) ∨
      (∃ G : OnBytes.Group, s.d.st.groups[n]? = some G ∧ o ∈ G.members.toList) ∨
      ∃ (g : Nat) (G : OnBytes.Group), s.d.st.groups[g]? = some G ∧ o ∈ G.members.toList ∧
        G.inRun = true := by
  rw [h.msgs] at ho
  obtain ⟨GO, eO, mO, -⟩ := grpIs_spec h.group
  by_cases c0 : o = 0
  · subst c0
    exact Or.inr (Or.inl ⟨GO, eO, by rw [mO]; simp⟩)
  by_cases c1 : o = 1
  · subst c1
    obtain ⟨G, e, m, r⟩ := grpIs_spec h.ranges
    exact Or.inr (Or.inr ⟨0, G, e, by rw [m]; simp, r⟩)
  by_cases c2 : o = 2
  · subst c2
    exact Or.inl (msgIs_bare h.rider)
  by_cases c3 : o < 3 + 2 * (n - 1)
  · obtain ⟨-, b, c⟩ := towerIs_spec h.tower ((o - 3) / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one (o - 3) with hp | hp
    · obtain ⟨G, e, m, r⟩ := grpIs_spec c
      refine Or.inr (Or.inr ⟨_, G, e, ?_, r⟩)
      rw [m]
      exact List.mem_singleton.2 (by omega)
    · have i : 3 + 2 * ((o - 3) / 2) + 1 = o := by omega
      rw [i] at b
      exact Or.inl (msgIs_bare b)
  by_cases c4 : o = 3 + 2 * (n - 1)
  · subst c4
    exact Or.inr (Or.inl ⟨GO, eO, by rw [mO]; simp⟩)
  · have i : o = 3 + 2 * (n - 1) + 1 := by omega
    subst i
    exact Or.inl (msgIs_bare h.mask)

/-- **What the third chain's end wants of the first chain's messages and groups**, at the first
chain's last statement. -/
theorem older_of_end₁ : Older (3 + 2 * (n - 1) + 2) (n + 1) s.d.st := by
  refine ⟨by omega, by omega, fun j hj => h.begun j (by omega), fun o ho => ?_⟩
  rcases h.home o (by rw [h.msgs]; omega) with c | ⟨G, e, m⟩ | ⟨g, G, e, m, -⟩
  · exact Or.inl c
  · exact Or.inr ⟨_, G, e, m⟩
  · exact Or.inr ⟨g, G, e, m⟩

end End1

/-- **The seal accepts and hands the state on as it is.** -/
theorem seal_passes {β Cl : Type} (n a : Nat) (s : ChainState β) (h : End₁ n a s)
    (hj : Joined s.d.st) (N : Pieces) (inFront : List Fmt.DeclaredRound) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (firstChainEnd (Cl := Cl) N inFront).decide s rs gs = .ok s := by
  obtain ⟨L, hl, hn⟩ := h.own
  have t : VerifiableInference.Desc.ChainEnd.refuse
      ([("end: no count of rows is owed", s.noneWaits)] ++ untestedButOwn s) = .ok () := by
    refine refuse_ok _ fun c hc => ?_
    rcases List.mem_append.1 hc with hc | hc
    · obtain rfl := List.mem_singleton.1 hc
      exact h.waits
    · refine butOwn_ok s L hl hj (fun g G e => ?_) (fun o x e => ?_) c hc
      · have lt := (Array.getElem?_eq_some_iff.1 e).1
        rw [h.grps] at lt
        by_cases c0 : g = n
        · exact Or.inr (c0.trans hn.symm)
        · obtain ⟨G', e', r⟩ := h.begun g (by omega)
          rw [e] at e'
          obtain rfl := Option.some.inj e'
          exact Or.inl r
      · rw [hn]
        rcases h.home o (Array.getElem?_eq_some_iff.1 e).1 with ⟨x', e', r⟩ | c | c
        · rw [e] at e'
          obtain rfl := Option.some.inj e'
          exact Or.inl r
        · exact Or.inr (Or.inl c)
        · exact Or.inr (Or.inr c)
  show (VerifiableInference.Desc.ChainEnd.refuse
    ([("end: no count of rows is owed", s.noneWaits)] ++ untestedButOwn s)).map (fun _ => s) = .ok s
  rw [t]
  rfl

/-! ## A member -/

/-- A message without a sample, not spent. -/
def toyFresh : Oracle := { shape := {} }

/-- The own group: two members, one open row, its test not begun. -/
def toyOwn (ms : Array Nat) : OnBytes.Group := { code := 0, members := ms, rows := #[default] }

/-- A state of the first chain: seven messages, three groups; two stages. -/
def toy₁ : ChainState Unit :=
  { base := ()
    d := { st := { oracles := #[toySampled [2], toySampled [0], toyMask, toySampled [1], toyMask,
                     toySampled [2], toyFresh]
                   groups := #[toyGroup #[1], toyGroup #[3], toyOwn #[0, 5]] }
           book := { trees := #[], place := #[] }, roots := 0, opened := [], loc := () }
    lin := some { own := 2 } }

/-- **A member**: the book-keeping that is spent and `Joined` hold together. A toy. -/
theorem toy₁_member : End₁ 2 0 toy₁ ∧ Joined toy₁.d.st :=
  ⟨⟨by omega, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, joined_of_B _ rfl⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.butOwn_ok
#print axioms AtPublicFiles.AtFiles.End₁.begun
#print axioms AtPublicFiles.AtFiles.End₁.home
#print axioms AtPublicFiles.AtFiles.older_of_end₁
#print axioms AtPublicFiles.AtFiles.seal_passes
#print axioms AtPublicFiles.AtFiles.toy₁_member
