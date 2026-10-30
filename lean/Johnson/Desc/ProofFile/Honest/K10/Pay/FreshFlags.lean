-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/FreshFlags.lean: two relations on statements that meet `StMild` (FreshMild.lean), so that every
sub-protocol in front of the last segment's end keeps them.

  `Answered T`        every message of T that bears the flag "sampled" has a shape that counts an answer
  `AnsweredStays`     if it holds in front, it holds behind; `stMild_answered`
  `MarkedAt T g`      group g is there and bears the mark "its proximity test has begun"
  `NoSpend A B`       every message that is spent as a mask in B is there and spent in A
  `Calm A B`          no mark is taken off; and if no group has gained the mark, then `NoSpend A B`; `stMild_calm`

Why the second holds at a closing: the closing marks a group that bore no mark, so its second half asks nothing there.

Limits. General laws on statements: no chain and no state is named here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.FreshMild

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Ground (GroundMild)
open VerifiableInference.Desc.K13.Law (StMild)
open VerifiableInference.Desc.First.Close (spent)

/-! ## 1 A sampled message counts an answer -/

/-- Every message that bears the flag "sampled" has a shape that counts an answer. -/
def Answered (T : Statement) : Prop :=
  ∀ (o : Nat) (x : OnBytes.Oracle), T.oracles[o]? = some x → x.sampled = true → 1 ≤ x.shape.answers

/-- If it holds in front, it holds behind. -/
def AnsweredStays (A B : Statement) : Prop := Answered A → Answered B

theorem answered_same {A B : Statement} (h : B.oracles = A.oracles) : AnsweredStays A B := by
  intro hA o x hx
  rw [h] at hx
  exact hA o x hx

theorem answered_modify {A B : Statement} (o : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (h : B.oracles = A.oracles.modify o f)
    (hf : ∀ x, A.oracles[o]? = some x → (x.sampled = true → 1 ≤ x.shape.answers) →
      (f x).sampled = true → 1 ≤ (f x).shape.answers) : AnsweredStays A B := by
  intro hA o' x' hx'
  rw [h, Array.getElem?_modify] at hx'
  by_cases c : o = o'
  · rw [if_pos c] at hx'
    obtain ⟨x, h1, rfl⟩ := Option.map_eq_some_iff.1 hx'
    subst c
    exact hf x h1 (hA o x h1)
  · rw [if_neg c] at hx'
    exact hA o' x' hx'

theorem answered_sent (A : Statement) (sent : Array OracleNotice) :
    AnsweredStays A (stSent A sent) := by
  intro hA o x hx hs
  have hx' : (A.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[o]? = some x :=
    hx
  rw [Array.getElem?_append] at hx'
  split at hx'
  · exact hA o x hx' hs
  · rw [Array.getElem?_map] at hx'
    obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.1 hx'
    exact absurd hs (by simp)

theorem answered_closeLedgers : ∀ (l : List Nat) (T : Statement),
    AnsweredStays T (closeLedgers T l)
  | [], _ => fun h => h
  | o :: l, T => by
    intro h
    have h1 : Answered { T with oracles := T.oracles.modify o fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } } } :=
      answered_modify (A := T) o (fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } }) rfl (fun _ _ k => k) h
    exact answered_closeLedgers l _ h1

theorem groundMild_answered : GroundMild AnsweredStays where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := by
    intro L d d' code maskCode n h
    unfold VerifiableInference.Desc.Ground.newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact answered_same rfl
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold VerifiableInference.Desc.Ground.recvP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact answered_sent d.st sent
    · cases h
  admit := by
    intro L d d' o rows h
    unfold VerifiableInference.Desc.Ground.admitP at h
    split at h
    · rename_i hok
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨pl, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain rfl := Option.some.inj h
      have ha : 1 ≤ x.shape.answers := by
        simp only [VerifiableInference.Desc.Ground.ok, VerifiableInference.Desc.Ground.admitL,
          List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at hok
        obtain ⟨-, -, -, -, h5⟩ := hok
        rw [hx] at h5
        simpa [VerifiableInference.Desc.Ground.has] using h5
      refine answered_modify o (fun y => { y with
        sampled := true, sampleRows := rows, pad := pl.map fun p => (p.part, p.index),
        ledger := freshLedger d.st.codes x.shape }) rfl (fun y hy _ _ => ?_)
      obtain rfl := Option.some.inj (hx.symm.trans hy)
      exact ha
    · cases h
  join := by
    intro L d d' g o kept h
    unfold VerifiableInference.Desc.Ground.joinP at h
    split at h
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact answered_modify o (fun x => { x with groups := x.groups ++ [g] }) rfl (fun _ _ k => k)
    · cases h
  addRow := by
    intro L d d' g row h
    unfold VerifiableInference.Desc.Ground.addRowP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact answered_same rfl
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold VerifiableInference.Desc.Ground.takeMaskP at h
    split at h
    · obtain ⟨l, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact answered_modify o (fun x => { x with ledger := some { l with
        next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 } }) rfl (fun _ _ k => k)
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold VerifiableInference.Desc.Ground.closeLedgerP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact answered_closeLedgers [o] d.st
    · cases h

/-- **"A sampled message counts an answer" is kept by all that `StMild` names.** -/
theorem stMild_answered : StMild AnsweredStays where
  ground := groundMild_answered
  closed := by
    intro T g G id _ _ h
    have h1 := answered_closeLedgers G.members.toList T h
    have h2 : Answered (begun T g G) := answered_same (A := closeLedgers T G.members.toList) rfl h1
    exact answered_modify (A := begun T g G) id (fun x => { x with spentAsMask := true }) rfl
      (fun _ _ k => k) h2

/-! ## 2 Where no group gains the mark, nobody is spent -/

/-- Group g is there and bears the mark "its proximity test has begun". -/
def MarkedAt (T : Statement) (g : Nat) : Prop := ∃ G, T.groups[g]? = some G ∧ G.inRun = true

/-- Every message that is spent as a mask in B is there and spent in A. -/
def NoSpend (A B : Statement) : Prop :=
  ∀ (o : Nat) (x' : OnBytes.Oracle), B.oracles[o]? = some x' → x'.spentAsMask = true →
    ∃ x, A.oracles[o]? = some x ∧ x.spentAsMask = true

/-- No mark is taken off; and if no group has gained the mark, nobody was spent. -/
def Calm (A B : Statement) : Prop :=
  (∀ g, MarkedAt A g → MarkedAt B g) ∧ ((∀ g, MarkedAt B g → MarkedAt A g) → NoSpend A B)

theorem noSpend_trans {A B C : Statement} (a : NoSpend A B) (b : NoSpend B C) : NoSpend A C := by
  intro o x'' h s
  obtain ⟨x', h', s'⟩ := b o x'' h s
  exact a o x' h' s'

theorem noSpend_same {A B : Statement} (h : B.oracles = A.oracles) : NoSpend A B := by
  intro o x hx hs
  rw [h] at hx
  exact ⟨x, hx, hs⟩

theorem noSpend_modify {A B : Statement} (o : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (h : B.oracles = A.oracles.modify o f) (hf : ∀ x, (f x).spentAsMask = x.spentAsMask) :
    NoSpend A B := by
  intro o' x' hx' hs
  rw [h, Array.getElem?_modify] at hx'
  by_cases c : o = o'
  · rw [if_pos c] at hx'
    obtain ⟨x, h1, rfl⟩ := Option.map_eq_some_iff.1 hx'
    exact ⟨x, h1, (hf x).symm.trans hs⟩
  · rw [if_neg c] at hx'
    exact ⟨x', hx', hs⟩

theorem noSpend_sent (A : Statement) (sent : Array OracleNotice) : NoSpend A (stSent A sent) := by
  intro o x hx hs
  have hx' : (A.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[o]? = some x :=
    hx
  rw [Array.getElem?_append] at hx'
  split at hx'
  · exact ⟨x, hx', hs⟩
  · rw [Array.getElem?_map] at hx'
    obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.1 hx'
    exact absurd hs (by simp)

theorem noSpend_closeLedgers : ∀ (l : List Nat) (T : Statement), NoSpend T (closeLedgers T l)
  | [], _ => noSpend_same rfl
  | o :: l, T => by
    have h1 : NoSpend T { T with oracles := T.oracles.modify o fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } } } :=
      noSpend_modify o (fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } }) rfl (fun _ => rfl)
    exact noSpend_trans h1 (noSpend_closeLedgers l _)

theorem marks_same {A B : Statement} (h : B.groups = A.groups) (g : Nat) :
    MarkedAt B g ↔ MarkedAt A g := by
  unfold MarkedAt
  rw [h]

theorem marks_modify {A B : Statement} (j : Nat) (f : Group → Group)
    (h : B.groups = A.groups.modify j f) (hf : ∀ G, (f G).inRun = G.inRun) (g : Nat) :
    MarkedAt B g ↔ MarkedAt A g := by
  unfold MarkedAt
  rw [h, Array.getElem?_modify]
  by_cases c : j = g
  · rw [if_pos c]
    constructor
    · rintro ⟨G', h1, h2⟩
      obtain ⟨G, h3, rfl⟩ := Option.map_eq_some_iff.1 h1
      exact ⟨G, h3, (hf G).symm.trans h2⟩
    · rintro ⟨G, h1, h2⟩
      exact ⟨f G, by rw [h1]; rfl, (hf G).trans h2⟩
  · rw [if_neg c]

theorem marks_push {A B : Statement} (G₀ : Group) (h : B.groups = A.groups.push G₀)
    (h0 : G₀.inRun = false) (g : Nat) : MarkedAt B g ↔ MarkedAt A g := by
  unfold MarkedAt
  rw [h, Array.getElem?_push]
  split
  · rename_i c
    constructor
    · rintro ⟨G', h1, h2⟩
      obtain rfl := Option.some.inj h1
      rw [h0] at h2
      cases h2
    · rintro ⟨G, h1, -⟩
      rw [c] at h1
      simp at h1
  · exact Iff.rfl

theorem calm_of {A B : Statement} (hm : ∀ g, MarkedAt B g ↔ MarkedAt A g) (hs : NoSpend A B) :
    Calm A B := ⟨fun g h => (hm g).2 h, fun _ => hs⟩

theorem calm_trans {A B C : Statement} (h : Calm A B) (k : Calm B C) : Calm A C :=
  ⟨fun g m => k.1 g (h.1 g m), fun hb =>
    noSpend_trans (h.2 fun g m => hb g (k.1 g m)) (k.2 fun g m => h.1 g (hb g m))⟩

theorem groundMild_calm : GroundMild Calm where
  refl := fun _ => calm_of (fun _ => Iff.rfl) (noSpend_same rfl)
  trans := calm_trans
  newGroup := by
    intro L d d' code maskCode n h
    unfold VerifiableInference.Desc.Ground.newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact calm_of (marks_push { code := code, maskCode := maskCode } rfl rfl) (noSpend_same rfl)
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold VerifiableInference.Desc.Ground.recvP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact calm_of (marks_same rfl) (noSpend_sent d.st sent)
    · cases h
  admit := by
    intro L d d' o rows h
    unfold VerifiableInference.Desc.Ground.admitP at h
    split at h
    · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨pl, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain rfl := Option.some.inj h
      exact calm_of (marks_same rfl) (noSpend_modify o (fun y => { y with
        sampled := true, sampleRows := rows, pad := pl.map fun p => (p.part, p.index),
        ledger := freshLedger d.st.codes x.shape }) rfl (fun _ => rfl))
    · cases h
  join := by
    intro L d d' g o kept h
    unfold VerifiableInference.Desc.Ground.joinP at h
    split at h
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact calm_of
        (marks_modify g (fun G' => { G' with
          members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
          kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept }) rfl
          (fun _ => rfl))
        (noSpend_modify o (fun x => { x with groups := x.groups ++ [g] }) rfl (fun _ => rfl))
    · cases h
  addRow := by
    intro L d d' g row h
    unfold VerifiableInference.Desc.Ground.addRowP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact calm_of (marks_modify g (fun G => { G with rows := G.rows.push row }) rfl
        (fun _ => rfl)) (noSpend_same rfl)
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold VerifiableInference.Desc.Ground.takeMaskP at h
    split at h
    · obtain ⟨l, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact calm_of (marks_same rfl) (noSpend_modify o (fun x => { x with ledger := some { l with
        next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 } }) rfl (fun _ => rfl))
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold VerifiableInference.Desc.Ground.closeLedgerP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact calm_of (marks_same (OnBytes.Means.closeLedgers_groups [o] d.st))
        (noSpend_closeLedgers [o] d.st)
    · cases h

/-- **"Where no group gains the mark, nobody is spent" is kept by all that `StMild` names.** -/
theorem stMild_calm : StMild Calm where
  ground := groundMild_calm
  closed := by
    intro T g G id hG hu
    have e : (spent (begun T g G) id).groups =
        T.groups.modify g (fun G' => { G' with inRun := true, rows := #[] }) := by
      have e0 : (spent (begun T g G) id).groups =
          (closeLedgers T G.members.toList).groups.modify g
            (fun G' => { G' with inRun := true, rows := #[] }) := rfl
      rw [e0, OnBytes.Means.closeLedgers_groups]
    have hg : MarkedAt (spent (begun T g G) id) g :=
      ⟨{ G with inRun := true, rows := #[] },
        VerifiableInference.Desc.First.Close.behind_group T g G id hG, rfl⟩
    refine ⟨fun g' m => ?_, fun hb => ?_⟩
    · by_cases c : g = g'
      · subst c
        exact hg
      · obtain ⟨G', h1, h2⟩ := m
        exact ⟨G', by rw [e, Array.getElem?_modify, if_neg c]; exact h1, h2⟩
    · obtain ⟨G2, h1, h2⟩ := hb g hg
      obtain rfl := Option.some.inj (hG.symm.trans h1)
      rw [hu] at h2
      cases h2

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.answered_same
#print axioms ProofFile.Honest.K10.answered_modify
#print axioms ProofFile.Honest.K10.answered_sent
#print axioms ProofFile.Honest.K10.answered_closeLedgers
#print axioms ProofFile.Honest.K10.groundMild_answered
#print axioms ProofFile.Honest.K10.stMild_answered
#print axioms ProofFile.Honest.K10.noSpend_trans
#print axioms ProofFile.Honest.K10.noSpend_same
#print axioms ProofFile.Honest.K10.noSpend_modify
#print axioms ProofFile.Honest.K10.noSpend_sent
#print axioms ProofFile.Honest.K10.noSpend_closeLedgers
#print axioms ProofFile.Honest.K10.marks_same
#print axioms ProofFile.Honest.K10.marks_modify
#print axioms ProofFile.Honest.K10.marks_push
#print axioms ProofFile.Honest.K10.calm_of
#print axioms ProofFile.Honest.K10.calm_trans
#print axioms ProofFile.Honest.K10.groundMild_calm
#print axioms ProofFile.Honest.K10.stMild_calm
