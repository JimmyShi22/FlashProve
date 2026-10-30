-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/SubSame.lean: what is produced where no part is called, on
the two sides. After a rejection the prover of Honest/Walk.lean produces each round's fixed
substitute (Honest/Law/Rule/WalkLaw.lean: `subPlayed`), and a session produces `Stretch.sub`
(Honest/Law/Rule/Session.lean). At a place without a list of parts `play`, with no stored run to
fall back on, produces rounds without an item and without a table, and a session produces
`Stretch.bare`. Each time, what the first show is the second (`sub_pairs`, `bare_pairs`).

  1  `sent_shown`, `sub_shown`   what a round shows whose tables are a message's own
  2  `subsOf`, `subsOf_append`, `sub_pairs`   a stretch of substitutes
  3  `none_shown`, `bare_pairs`   a stretch of rounds at a place without a list of parts

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartLaw
import Johnson.Desc.ProofFile.Honest.Law.Rule.WalkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place Oracle)

variable {W Y : Type}

/-! ## 1 A round whose tables are a message's own -/

/-- A round as produced whose items and tables are a message's shows what the message shows, at the
positions read of its trees. -/
theorem sent_shown (tree : Nat → List Nat) (n : Nat) (p : Played) (x : Sending)
    (hv : p.vals = x.vals.map Said.got) (ht : p.tables = x.tables.map some) :
    p.shownBy tree n = x.shownAt ((List.range x.tables.length).map fun i => tree (n + i)) := by
  unfold Played.shownBy Sending.shownAt
  rw [hv, ht, List.length_map]
  refine congrArg (Shown.mk (x.vals.map Said.got)) ?_
  have h := zipIdx_range (fun (T : Option Table) (i : Nat) =>
    colsOfT T ((((List.range x.tables.length).map fun i => tree (n + i))[i]?).getD [])) x.tables 0
  refine Eq.trans (List.map_congr_left fun i hi => ?_) h.symm
  show colsOfT (((x.tables.map some)[i]?).join) (tree (n + i)) = colsOfT x.tables[i]?
    ((((List.range x.tables.length).map fun i => tree (n + i))[0 + i]?).getD [])
  rw [Nat.zero_add, getD_range (fun i => tree (n + i)) (List.mem_range.1 hi), List.getElem?_map]
  cases x.tables[i]? <;> rfl

theorem sub_shown (tree : Nat → List Nat) (n : Nat) (s : Step W Y) (d : Fmt.Drawn) :
    (subPlayed s d).shownBy tree n = (subSending s.decl s.oracles).shownAt
      ((List.range s.oracles.length).map fun i => tree (n + i)) := by
  have h := sent_shown tree n (subPlayed s d) (subSending s.decl s.oracles) rfl rfl
  have hl : (subSending s.decl s.oracles).tables.length = s.oracles.length := by
    show (s.oracles.map substituteZeroTable).length = _
    rw [List.length_map]
  rw [hl] at h
  exact h

/-! ## 2 A stretch of substitutes -/

/-- The substitutes of `Step`s, as rounds that are produced. As many as the shorter of the two lists
has. -/
def subsOf (ss : List (Step W Y)) (ds : List Fmt.Drawn) : List Played :=
  (ss.zip ds).map fun u => subPlayed u.1 u.2

theorem subsOf_append (l₁ l₂ : List (Step W Y)) (d₁ d₂ : List Fmt.Drawn)
    (h : l₁.length = d₁.length) :
    subsOf (l₁ ++ l₂) (d₁ ++ d₂) = subsOf l₁ d₁ ++ subsOf l₂ d₂ := by
  unfold subsOf
  rw [List.zip_append h, List.map_append]

/-- **A stretch of substitutes shows what a session produces after a rejection.** The right side is
the body of `Stretch.sub` written out, at the `Step`s' declared rounds, the positions of `asksFrom`
and the challenges. -/
theorem sub_pairs (tree : Nat → List Nat) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (n : Nat), pairsBy tree (subsOf ss ds) n =
      (((ss.map fun s => (s.decl, s.oracles)).zip
        (asksFrom tree (ss.map (·.oracles.length)) n)).map fun z =>
          (subSending z.1.1 z.1.2).shownAt z.2).zip ds
  | [], _, _ => rfl
  | _ :: _, [], _ => by simp [subsOf, pairsBy]
  | s :: ss, d :: ds, n => by
    have ih := sub_pairs tree ss ds (n + s.oracles.length)
    have hl : (subPlayed s d).tables.length = s.oracles.length := by
      show ((s.oracles.map substituteZeroTable).map some).length = _
      rw [List.length_map, List.length_map]
    show ((subPlayed s d).shownBy tree n, d) ::
        pairsBy tree (subsOf ss ds) (n + (subPlayed s d).tables.length) =
      ((subSending s.decl s.oracles).shownAt
          ((List.range s.oracles.length).map fun i => tree (n + i)), d) ::
        (((ss.map fun s => (s.decl, s.oracles)).zip
          (asksFrom tree (ss.map (·.oracles.length)) (n + s.oracles.length))).map fun z =>
            (subSending z.1.1 z.1.2).shownAt z.2).zip ds
    rw [hl, ih, sub_shown]

/-! ## 3 A place without a list of parts -/

/-- A round without an item and without an available table shows no item, and an empty list of
columns for each root. -/
theorem none_shown (tree : Nat → List Nat) (n r : Nat) (p : Played) (hv : p.vals = [])
    (ht : p.tables = List.replicate r none) : p.shownBy tree n = ⟨[], List.replicate r []⟩ := by
  unfold Played.shownBy
  rw [hv, ht, List.length_replicate]
  refine congrArg (Shown.mk []) ?_
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
  rw [List.getElem?_replicate, if_pos (List.mem_range.1 hi)]
  rfl

/-- **Rounds that `play` has played, with no stored run to fall back on (its third argument is
`[]`), at `Step`s without a move that declare as many oracle messages as their entry counts roots,
show what a session produces at a place without a list of parts.** The right side is the body of
`Stretch.bare` written out, at the `Step`s' declared rounds and the challenges. -/
theorem bare_pairs (tree : Nat → List Nat) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (m : Mid W Y) (y : List Played × Mid W Y) (n : Nat), play ss ds [] m = .ok y →
    (∀ s ∈ ss, s.move.isSome = false) → (∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) →
    pairsBy tree y.1 n =
      (ss.map fun s => (⟨[], List.replicate s.oracles.length []⟩ : Shown)).zip ds
  | [], [], m, y, n, h, _, _ => by
    simp only [play] at h
    cases h
    rfl
  | [], _ :: _, _, _, _, h, _, _ => by simp [play] at h
  | _ :: _, [], _, _, _, h, _, _ => by simp [play] at h
  | s :: ss, d :: ds, m, y, n, h, hm, hs => by
    obtain ⟨x, m', z, hx, -, hz, rfl⟩ := play_cons_ok h
    obtain ⟨-, -, t3⟩ := tell_yields hx
    obtain ⟨v1, v2⟩ := t3 (hm s (List.mem_cons.2 (Or.inl rfl)))
    have hr := hs s (List.mem_cons.2 (Or.inl rfl))
    have hz' : play ss ds [] m' = .ok z := hz
    have ih := bare_pairs tree ss ds m' z (n + x.tables.length) hz'
      (fun t ht => hm t (List.mem_cons_of_mem _ ht)) fun t ht => hs t (List.mem_cons_of_mem _ ht)
    show ((⟨s.name, s.addr.place, if x.told then s.addr.part else 0, x.told, x.vals, x.tables,
        d⟩ : Played).shownBy tree n, d) :: pairsBy tree z.1 (n + x.tables.length) =
      ((⟨[], List.replicate s.oracles.length []⟩ : Shown), d) ::
        (ss.map fun s => (⟨[], List.replicate s.oracles.length []⟩ : Shown)).zip ds
    have hsn := none_shown tree n s.decl.entry.roots (⟨s.name, s.addr.place,
      if x.told then s.addr.part else 0, x.told, x.vals, x.tables, d⟩ : Played) v1 v2
    rw [ih, hsn, hr]

end ProofFile.Honest

#print axioms ProofFile.Honest.sent_shown
#print axioms ProofFile.Honest.sub_shown
#print axioms ProofFile.Honest.subsOf_append
#print axioms ProofFile.Honest.sub_pairs
#print axioms ProofFile.Honest.none_shown
#print axioms ProofFile.Honest.bare_pairs
