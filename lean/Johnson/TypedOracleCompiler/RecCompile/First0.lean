-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/First0.lean: the first query of a chain stands in round 0.

`ours_first` (OnBytes/TypedOracleCompiler/Compile/Batch/OursFirst.lean) says that every query of our own chain is,
or has before it in the trace, a query with a head (F1) that holds our list. Here the same with one
word more: that query's number of the round is 0 (`ours_first0`). It is wanted where queries with a
head (F1) in another round are told apart from the first queries of chains.

The text is that of `StartsWith`, `Data.Good`, `good_viaTail`, `rooted_good`
(OnBytes/TypedOracleCompiler/Compile/Batch/Facts.lean) and of `first_of_startsWith`, `ours_first`, copied by a
program, with the clause on the round written in.

Limits: soundness alone; typed oracles.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.OursFirst

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {t : Tag}

/-- the first record is a first query of a chain, with these external roots and this instance, in
round 0 -/
def StartsWith0 (cms : List (Dig lam)) (x : Option X) (l : List (Rec lam K L t)) : Prop :=
  ∃ q1 a1 rest salt, l = (Item.lo q1, a1) :: rest ∧ q1.head = Head.f1 cms x salt ∧ q1.round = 0

/-- A list that starts so still does when records are appended. -/
theorem StartsWith0.append {cms : List (Dig lam)} {x : Option X} {l : List (Rec lam K L t)}
    (h : StartsWith0 cms x l) (l' : List (Rec lam K L t)) : StartsWith0 cms x (l ++ l') := by
  obtain ⟨q1, a1, rest, salt, rfl, hq⟩ := h
  exact ⟨q1, a1, rest ++ l', salt, rfl, hq⟩

/-- What the data of a rooted query of round i with the head h look like. -/
def Data.Good0 (pre : Trace (typedOracleFamily lam K L)) (i : ℕ) (h : Head lam X) : Data lam K L t → Prop
  | .locV cms x l =>
    l.length = i ∧ AllLo l ∧ (∀ rc ∈ l, RecIn pre rc) ∧
    ((l = [] ∧ ∃ salt, h = .f1 cms x salt) ∨ StartsWith0 cms x l)
  | .locA cms x l => (∀ rc ∈ l, RecIn pre rc) ∧ StartsWith0 cms x l
  | .shd cms _ slot sh =>
    (∀ p ∈ sh, fbE t p.1 p.2 ∈ pre) ∧
    ∃ iJ,
      iJ + sh.length = i ∧
      ∀ c sd, slot c = some sd →
        sd.recs.length = iJ ∧ AllLo sd.recs ∧ (∀ rc ∈ sd.recs, RecIn pre rc) ∧
        (∃ c', gE t sd.gq c' ∈ pre) ∧ StartsWith0 cms sd.x sd.recs

/-- The step of `rooted_good0` at a tail: if the data of every rooted query of round i are good, so
are the data that `viaTail` gives for round i + 1. -/
theorem good0_viaTail {pre : Trace (typedOracleFamily lam K L)} {i : ℕ}
    (ih : ∀ h D, rooted t pre i h = some D → D.Good0 pre i h) {ρ : Bits} {D : Data lam K L t}
    (hD : viaTail (rooted t pre i) pre i ρ = some D) (xl : Option X := none) :
    D.Good0 pre (i + 1) (.f2 xl ρ) := by
  obtain ⟨p, hp, ⟨cms, x, l, hr, rfl⟩ | ⟨cms, x, l, hr, rfl⟩⟩ := viaTail_eq_some hD
  · obtain ⟨h1, h2, h3, h4⟩ := ih _ _ hr
    refine ⟨by simp [h1], ?_, ?_, Or.inr ?_⟩
    · intro rc hrc
      rcases List.mem_append.1 hrc with h | h
      · exact h2 rc h
      · rw [List.mem_singleton.1 h]; exact ⟨_, rfl⟩
    · intro rc hrc
      rcases List.mem_append.1 hrc with h | h
      · exact h3 rc h
      · rw [List.mem_singleton.1 h]; exact (predF_spec hp).1
    · rcases h4 with ⟨rfl, salt, hs⟩ | h4
      · exact ⟨p.1, p.2, [], salt, rfl, hs, (predF_spec hp).2.1.trans h1.symm⟩
      · exact h4.append _
  · obtain ⟨h3, h4⟩ := ih _ _ hr
    refine ⟨?_, h4.append _⟩
    intro rc hrc
    rcases List.mem_append.1 hrc with h | h
    · exact h3 rc h
    · rw [List.mem_singleton.1 h]; exact (predF_spec hp).1

/-- The data of every rooted query are good (`Data.Good0`). -/
theorem rooted_good0 (pre : Trace (typedOracleFamily lam K L)) : ∀ (i : ℕ) (h : Head lam X) (D : Data lam K L t),
    rooted t pre i h = some D → D.Good0 pre i h
  | 0, h, D, hD => by
      cases h with
      | f1 cms x salt =>
        cases Option.some.inj hD
        exact ⟨rfl,
          fun _ h => absurd h (List.not_mem_nil),
          fun _ h => absurd h (List.not_mem_nil),
          Or.inl ⟨rfl, salt, rfl⟩⟩
      | f2 xl ρ => cases hD
      | f3 ρ c => cases hD
      | f4 cms r => cases hD
      | f5 ρ => cases hD
  | i + 1, h, D, hD => by
      have ih := rooted_good0 pre i
      cases h with
      | f1 cms x salt => cases hD
      | f2 xl ρ => exact good0_viaTail ih hD xl
      | f4 cms rtreq =>
        cases Option.some.inj hD
        refine ⟨fun _ h => absurd h (List.not_mem_nil), i + 1, rfl, fun c sd hsd => ?_⟩
        obtain ⟨g, hg, hv, hgq⟩ := slotFn_eq_some hsd
        obtain ⟨h1, h2, h3, h4⟩ := good0_viaTail ih hv
        refine ⟨h1, h2, h3, ⟨g.2, hgq ▸ (predG_spec hg).1⟩, ?_⟩
        rcases h4 with ⟨h5, -⟩ | h4
        · rw [h5] at h1; cases h1
        · exact h4
      | f5 ρ0 =>
        obtain ⟨p, cms, rtreq, slot, sh, hp, hr, rfl⟩ := rooted_f5_eq_some hD
        obtain ⟨h1, iJ, h2, h3⟩ := ih _ _ hr
        refine ⟨?_, iJ,
          by simp only [List.length_append, List.length_cons, List.length_nil]; omega, h3⟩
        intro z hz
        rcases List.mem_append.1 hz with h | h
        · exact h1 z h
        · rw [List.mem_singleton.1 h]; exact (predF_spec hp).1
      | f3 ρ0 c =>
        obtain ⟨p, cms, rtreq, slot, sh, sd, l, hp, hr, hs, hl, rfl⟩ := rooted_f3_eq_some hD
        obtain ⟨h1, iJ, h2, h3⟩ := ih _ _ hr
        obtain ⟨-, -, h6, h7, h8⟩ := h3 c sd hs
        have hall : ∀ z ∈ sh ++ [p], fbE t z.1 z.2 ∈ pre := by
          intro z hz
          rcases List.mem_append.1 hz with h | h
          · exact h1 z h
          · rw [List.mem_singleton.1 h]; exact (predF_spec hp).1
        cases hsh : sh ++ [p] with
        | nil => rw [hsh] at hl; cases hl
        | cons p4 rest =>
          rw [hsh] at hl hall
          cases Option.some.inj hl
          refine ⟨?_, h8.append _⟩
          intro rc hrc
          rcases List.mem_append.1 hrc with h | h
          · exact h6 rc h
          · rcases List.mem_cons.1 h with rfl | h
            · exact ⟨h7, hall p4 List.mem_cons_self⟩
            · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 h
              exact hall z (List.mem_cons_of_mem _ hz)

/-- If a list starts so and all its records stand in the trace, the trace holds a first query with
these roots and this instance, in round 0. -/
theorem first0_of_startsWith {K : ℕ} {t : Tag} {pre : Trace (typedOracleFamily lam K L)} {cms : List (Dig lam)}
    {x : Option X}
    {l : List (Rec lam K L t)} (h : StartsWith0 cms x l) (hin : ∀ rc ∈ l, RecIn pre rc) :
    ∃ q1 a1 salt, fbE t q1 a1 ∈ pre ∧ q1.head = Head.f1 cms x salt ∧ q1.round = 0 := by
  obtain ⟨q1, a1, rest, salt, rfl, hq⟩ := h
  exact ⟨q1, a1, salt, hin _ List.mem_cons_self, hq⟩

/-- Every query that is ours is, or has before it, a first query with our outer roots and our early
instance, in round 0. -/
theorem ours_first0 {W : QueryLayout lam L} (C : Ctx W) {pre : Tc W} {q : FbIn lam L C.t}
    {l : List (Rec lam W.K L C.t)}
    {cur : Item lam L C.t} (h : Ours C pre q l cur) :
    ((∃ salt, q.head = Head.f1 C.cms C.xo salt) ∧ q.round = 0) ∨
      ∃ q1 a1 salt, fbE C.t q1 a1 ∈ pre ∧ q1.head = Head.f1 C.cms C.xo salt ∧ q1.round = 0 := by
  rcases h with ⟨h1 | h1, -⟩ | ⟨slot, sh, c', sd, hr, -, hs, hx, -⟩
  · obtain ⟨h0, -, h3, h4⟩ := rooted_good0 pre _ _ _ h1
    rcases h4 with ⟨rfl, salt, hq⟩ | h4
    · exact Or.inl ⟨⟨salt, hq⟩, h0.symm⟩
    · exact Or.inr (first0_of_startsWith h4 h3)
  · obtain ⟨h3, h4⟩ := rooted_good0 pre _ _ _ h1
    exact Or.inr (first0_of_startsWith h4 h3)
  · obtain ⟨-, iJ, -, hslot⟩ := rooted_good0 pre _ _ _ hr
    obtain ⟨-, -, h6, -, h8⟩ := hslot c' sd hs
    rw [hx] at h8
    exact Or.inr (first0_of_startsWith h8 h6)

end TypedOracleCompiler.Compile.Batch
