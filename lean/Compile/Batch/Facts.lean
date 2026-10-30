-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Facts.lean: facts about rooted queries (`rooted`, Compile/Batch/Rooted.lean), and the
bound for one query on the event E'_S (`Lane.step`, Compile/Batch/Rooted.lean): a new rooted query
whose answer turns the state of a transcript from 0 to 1. A query of round i, with the head h, is
rooted if its data can be read from h and the earlier entries pre of the trace (`rooted t pre i h`).

  Part 1  How the data of a rooted query arise: lemmas for each of the clauses (R2) to (R5) of
          `rooted`.
  Part 2  The form of these data (`Data.Good`): the numbers of records; the records before the
          joining round are of local rounds (`AllLo`); the queries of a record are entries of the
          trace (`RecIn`); the first record names the external roots (`StartsWith`).
  Part 3  The data only grow with the trace (`rooted_mono`).
  Part 4  Each query causes E'_S with probability at most εs: `Lane.pr_step_le` (under `Lane.OK`,
          `Err.Below`, N = 2^depthReq).

Notation: `t`: a `Tag` (Compile/Oracles.lean); in `Lane`, a protocol's tag; `ℓ`: a `Lane W`
(Compile/Batch/Rooted.lean): one protocol in the analysis; `N`: a natural number; in `JointLaw N`
(Iop/Batch.lean) the slots are numbered by `Fin N`; `εs`: an `ℝ≥0∞`, the second argument of
`Err.Below` (Iop/InteractiveOracleProof.lean); a record: a `Rec` (Compile/Batch/Rooted.lean): an item with the answer
that gives the verifier message of its round; `locV`, `shd`, `locA`: the constructors of `Data`
(Compile/Batch/Rooted.lean): the data of a rooted query of a local round before the shared rounds,
of a shared round, of a local round after them; `Head.f1` to `.f5`: the five formats (F1) to (F5) of
a Fiat-Shamir query (Compile/Batch/Oracles.lean).

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.Joint

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {t : Tag}

/-! ## Part 1. Inversion -/

theorem viaTail_eq_some {rec : Head lam X → Option (Data lam K L t)} {pre : Trace (spec lam K L)}
    {i : ℕ} {ρ : Bits} {D : Data lam K L t} (h : viaTail rec pre i ρ = some D) :
    ∃ p,
      predF t pre i ρ = some p ∧
      ((∃ cms x l, rec p.1.head = some (.locV cms x l) ∧ D = .locV cms x (l ++ [(.lo p.1, p.2)])) ∨
        (∃ cms x l,
          rec p.1.head = some (.locA cms x l) ∧ D = .locA cms x (l ++ [(.lo p.1, p.2)]))) := by
  obtain ⟨p, hp, h1⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨D₀, hD₀, h2⟩ := Option.bind_eq_some_iff.1 h1
  refine ⟨p, hp, ?_⟩
  cases D₀ with
  | locV cms x l => exact Or.inl ⟨cms, x, l, hD₀, (Option.some.inj h2).symm⟩
  | locA cms x l => exact Or.inr ⟨cms, x, l, hD₀, (Option.some.inj h2).symm⟩
  | shd cms rtreq slot sh => cases h2

theorem viaTail_locV {rec : Head lam X → Option (Data lam K L t)} {pre : Trace (spec lam K L)}
    {i : ℕ} {ρ : Bits} {p : FbIn lam L t × FsAns lam K} {cms : List (Dig lam)} {x : Option X}
    {l : List (Rec lam K L t)} (hp : predF t pre i ρ = some p)
    (hr : rec p.1.head = some (.locV cms x l)) :
    viaTail rec pre i ρ = some (.locV cms x (l ++ [(.lo p.1, p.2)])) := by
  simp only [viaTail, hp, hr, Option.bind_some]

theorem viaTail_locA {rec : Head lam X → Option (Data lam K L t)} {pre : Trace (spec lam K L)}
    {i : ℕ} {ρ : Bits} {p : FbIn lam L t × FsAns lam K} {cms : List (Dig lam)} {x : Option X}
    {l : List (Rec lam K L t)} (hp : predF t pre i ρ = some p)
    (hr : rec p.1.head = some (.locA cms x l)) :
    viaTail rec pre i ρ = some (.locA cms x (l ++ [(.lo p.1, p.2)])) := by
  simp only [viaTail, hp, hr, Option.bind_some]

theorem slotFn_eq_some {rec : Head lam X → Option (Data lam K L t)} {pre : Trace (spec lam K L)}
    {i : ℕ} {cms : List (Dig lam)} {c : Bits} {sd : SlotD lam K L t}
    (h : slotFn rec pre i cms c = some sd) :
    ∃ g,
      predG t pre (i + 1) c = some g ∧
      viaTail rec pre i g.1.ρ = some (.locV cms sd.x sd.recs) ∧
      sd.gq = g.1 := by
  obtain ⟨g, hg, h1⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨D, hD, h2⟩ := Option.bind_eq_some_iff.1 h1
  refine ⟨g, hg, ?_⟩
  cases D with
  | locV cms' x l =>
    by_cases hc : cms' = cms
    · have h3 : some (⟨x, l, g.1⟩ : SlotD lam K L t) = some sd := by
        rw [← h2]; exact (if_pos hc).symm
      cases h3
      exact ⟨hc ▸ hD, rfl⟩
    · have h3 : (none : Option (SlotD lam K L t)) = some sd := by rw [← h2]; exact (if_neg hc).symm
      cases h3
  | locA cms' x l => cases h2
  | shd cms' rtreq slot sh => cases h2

theorem slotFn_of {rec : Head lam X → Option (Data lam K L t)} {pre : Trace (spec lam K L)} {i : ℕ}
    {cms : List (Dig lam)} {c : Bits} {g : JoiningRoundQuery lam L t × Dig lam} {x : Option X}
    {l : List (Rec lam K L t)} (hg : predG t pre (i + 1) c = some g)
    (hv : viaTail rec pre i g.1.ρ = some (.locV cms x l)) :
    slotFn rec pre i cms c = some ⟨x, l, g.1⟩ := by
  simp only [slotFn, hg, hv, Option.bind_some, if_true]

theorem rooted_f5_eq_some {pre : Trace (spec lam K L)} {i : ℕ} {ρ0 : Bits}
    {D : Data lam K L t} (h : rooted t pre (i + 1) (.f5 ρ0) = some D) :
    ∃ p cms rtreq slot sh,
      predF t pre i ρ0 = some p ∧
      rooted t pre i p.1.head = some (.shd cms rtreq slot sh) ∧
      D = .shd cms rtreq slot (sh ++ [p]) := by
  obtain ⟨p, hp, h1⟩ := Option.bind_eq_some_iff.1 (show (predF t pre i ρ0).bind _ = some D from h)
  obtain ⟨D₀, hD₀, h2⟩ := Option.bind_eq_some_iff.1 h1
  cases D₀ with
  | locV cms' x l => cases h2
  | locA cms' x l => cases h2
  | shd cms rtreq slot sh => exact ⟨p, cms, rtreq, slot, sh, hp, hD₀, (Option.some.inj h2).symm⟩

theorem rooted_f5_of {pre : Trace (spec lam K L)} {i : ℕ} {cms : List (Dig lam)} {ρ0 : Bits}
    {p : FbIn lam L t × FsAns lam K} {rtreq : Bits} {slot : Bits → Option (SlotD lam K L t)}
    {sh : List (FbIn lam L t × FsAns lam K)} (hp : predF t pre i ρ0 = some p)
    (hr : rooted t pre i p.1.head = some (.shd cms rtreq slot sh)) :
    rooted t pre (i + 1) (.f5 ρ0) = some (.shd cms rtreq slot (sh ++ [p])) := by
  simp only [rooted, hp, hr, Option.bind_some]

theorem rooted_f3_eq_some {pre : Trace (spec lam K L)} {i : ℕ} {ρ0 c : Bits} {D : Data lam K L t}
    (h : rooted t pre (i + 1) (.f3 ρ0 c) = some D) :
    ∃ p cms rtreq slot sh sd l,
      predF t pre i ρ0 = some p ∧
      rooted t pre i p.1.head = some (.shd cms rtreq slot sh) ∧
      slot c = some sd ∧
      joinRecs sd (sh ++ [p]) = some l ∧
      D = .locA cms sd.x l := by
  obtain ⟨p, hp, h1⟩ := Option.bind_eq_some_iff.1 (show (predF t pre i ρ0).bind _ = some D from h)
  obtain ⟨D₀, hD₀, h2⟩ := Option.bind_eq_some_iff.1 h1
  cases D₀ with
  | locV cms' x l => cases h2
  | locA cms' x l => cases h2
  | shd cms rtreq slot sh =>
    obtain ⟨sd, hsd, h3⟩ := Option.bind_eq_some_iff.1 h2
    obtain ⟨l, hl, h4⟩ := Option.map_eq_some_iff.1 h3
    exact ⟨p, cms, rtreq, slot, sh, sd, l, hp, hD₀, hsd, hl, h4.symm⟩

theorem rooted_f3_of {pre : Trace (spec lam K L)} {i : ℕ} {ρ0 c : Bits}
    {p : FbIn lam L t × FsAns lam K} {cms : List (Dig lam)} {rtreq : Bits}
    {slot : Bits → Option (SlotD lam K L t)} {sh : List (FbIn lam L t × FsAns lam K)}
    {sd : SlotD lam K L t} {l : List (Rec lam K L t)} (hp : predF t pre i ρ0 = some p)
    (hr : rooted t pre i p.1.head = some (.shd cms rtreq slot sh)) (hs : slot c = some sd)
    (hl : joinRecs sd (sh ++ [p]) = some l) :
    rooted t pre (i + 1) (.f3 ρ0 c) = some (.locA cms sd.x l) := by
  simp only [rooted, hp, hr, hs, hl, Option.bind_some, Option.map_some]

/-- The records of a slot after one more shared query. -/
theorem joinRecs_concat (sd : SlotD lam K L t)
    (sh : List (FbIn lam L t × FsAns lam K)) (p : FbIn lam L t × FsAns lam K) :
    joinRecs sd (sh ++ [p]) = some ((slotTr sd sh p.1).1 ++ [((slotTr sd sh p.1).2, p.2)]) := by
  cases sh with
  | nil => rfl
  | cons p4 rest =>
    show some
        (sd.recs ++ (Item.jn sd.gq p4.1, p4.2) :: (rest ++ [p]).map fun z => (Item.sh z.1, z.2)) = _
    simp [slotTr, joinRecs]

/-! ## Part 2. The form of the data -/

/-- all records are records of local rounds -/
def AllLo (l : List (Rec lam K L t)) : Prop := ∀ rc ∈ l, ∃ q, rc.1 = Item.lo q

/-- the queries of a record are entries of the trace -/
def RecIn (pre : Trace (spec lam K L)) (rc : Rec lam K L t) : Prop :=
  match rc.1 with
  | .lo q => fbE t q rc.2 ∈ pre
  | .jn gq q => (∃ c, gE t gq c ∈ pre) ∧ fbE t q rc.2 ∈ pre
  | .sh q => fbE t q rc.2 ∈ pre

/-- the first record is a first query of a chain, with these external roots and this instance -/
def StartsWith (cms : List (Dig lam)) (x : Option X) (l : List (Rec lam K L t)) : Prop :=
  ∃ q1 a1 rest salt, l = (Item.lo q1, a1) :: rest ∧ q1.head = Head.f1 cms x salt

theorem StartsWith.append {cms : List (Dig lam)} {x : Option X} {l : List (Rec lam K L t)}
    (h : StartsWith cms x l) (l' : List (Rec lam K L t)) : StartsWith cms x (l ++ l') := by
  obtain ⟨q1, a1, rest, salt, rfl, hq⟩ := h
  exact ⟨q1, a1, rest ++ l', salt, rfl, hq⟩

/-- The form of the data of a rooted query of round i with the header h. -/
def Data.Good (pre : Trace (spec lam K L)) (i : ℕ) (h : Head lam X) : Data lam K L t → Prop
  | .locV cms x l =>
    l.length = i ∧ AllLo l ∧ (∀ rc ∈ l, RecIn pre rc) ∧
    ((l = [] ∧ ∃ salt, h = .f1 cms x salt) ∨ StartsWith cms x l)
  | .locA cms x l => (∀ rc ∈ l, RecIn pre rc) ∧ StartsWith cms x l
  | .shd cms _ slot sh =>
    (∀ p ∈ sh, fbE t p.1 p.2 ∈ pre) ∧
    ∃ iJ,
      iJ + sh.length = i ∧
      ∀ c sd, slot c = some sd →
        sd.recs.length = iJ ∧ AllLo sd.recs ∧ (∀ rc ∈ sd.recs, RecIn pre rc) ∧
        (∃ c', gE t sd.gq c' ∈ pre) ∧ StartsWith cms sd.x sd.recs

theorem good_viaTail {pre : Trace (spec lam K L)} {i : ℕ}
    (ih : ∀ h D, rooted t pre i h = some D → D.Good pre i h) {ρ : Bits} {D : Data lam K L t}
    (hD : viaTail (rooted t pre i) pre i ρ = some D) (xl : Option X := none) :
    D.Good pre (i + 1) (.f2 xl ρ) := by
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
      · exact ⟨p.1, p.2, [], salt, rfl, hs⟩
      · exact h4.append _
  · obtain ⟨h3, h4⟩ := ih _ _ hr
    refine ⟨?_, h4.append _⟩
    intro rc hrc
    rcases List.mem_append.1 hrc with h | h
    · exact h3 rc h
    · rw [List.mem_singleton.1 h]; exact (predF_spec hp).1

theorem rooted_good (pre : Trace (spec lam K L)) : ∀ (i : ℕ) (h : Head lam X) (D : Data lam K L t),
    rooted t pre i h = some D → D.Good pre i h
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
      have ih := rooted_good pre i
      cases h with
      | f1 cms x salt => cases hD
      | f2 xl ρ => exact good_viaTail ih hD xl
      | f4 cms rtreq =>
        cases Option.some.inj hD
        refine ⟨fun _ h => absurd h (List.not_mem_nil), i + 1, rfl, fun c sd hsd => ?_⟩
        obtain ⟨g, hg, hv, hgq⟩ := slotFn_eq_some hsd
        obtain ⟨h1, h2, h3, h4⟩ := good_viaTail ih hv
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

/-! ## Part 3. The data only grow with the trace -/

/-- D' holds what D holds; for a rooted query of a shared round, `slot` of D' may be defined at more
slot values -/
def Data.le : Data lam K L t → Data lam K L t → Prop
  | .locV cms x l, D' => D' = .locV cms x l
  | .locA cms x l, D' => D' = .locA cms x l
  | .shd cms rtreq slot sh, D' =>
    ∃ slot', D' = .shd cms rtreq slot' sh ∧ ∀ c sd, slot c = some sd → slot' c = some sd

theorem viaTail_mono {pre : Trace (spec lam K L)} (more : Trace (spec lam K L))
    {rec rec' : Head lam X → Option (Data lam K L t)}
    (hrec : ∀ h D, rec h = some D → ∃ D', rec' h = some D' ∧ D.le D') {i : ℕ} {ρ : Bits}
    {D : Data lam K L t} (hD : viaTail rec pre i ρ = some D) :
    viaTail rec' (pre ++ more) i ρ = some D := by
  obtain ⟨p, hp, ⟨cms, x, l, hr, rfl⟩ | ⟨cms, x, l, hr, rfl⟩⟩ := viaTail_eq_some hD
  · obtain ⟨D', h1, h2⟩ := hrec _ _ hr
    cases (show D' = .locV cms x l from h2)
    exact viaTail_locV (firstWith_append hp more) h1
  · obtain ⟨D', h1, h2⟩ := hrec _ _ hr
    cases (show D' = .locA cms x l from h2)
    exact viaTail_locA (firstWith_append hp more) h1

theorem rooted_mono {pre : Trace (spec lam K L)} (more : Trace (spec lam K L)) :
    ∀ (i : ℕ) (h : Head lam X) (D : Data lam K L t),
      rooted t pre i h = some D → ∃ D', rooted t (pre ++ more) i h = some D' ∧ D.le D'
  | 0, h, D, hD => by
      cases h with
      | f1 cms x salt =>
        cases Option.some.inj hD
        exact ⟨_, rfl, rfl⟩
      | f2 xl ρ => cases hD
      | f3 ρ c => cases hD
      | f4 cms r => cases hD
      | f5 ρ => cases hD
  | i + 1, h, D, hD => by
      have ih := rooted_mono (pre := pre) more i
      cases h with
      | f1 cms x salt => cases hD
      | f2 xl ρ =>
        have h1 : rooted t (pre ++ more) (i + 1) (.f2 xl ρ) = some D := viaTail_mono more ih hD
        refine ⟨D, h1, ?_⟩
        obtain ⟨p, -, ⟨cms, x, l, -, rfl⟩ | ⟨cms, x, l, -, rfl⟩⟩ := viaTail_eq_some hD <;> rfl
      | f4 cms rtreq =>
        cases Option.some.inj hD
        refine ⟨_, rfl, _, rfl, fun c sd hsd => ?_⟩
        obtain ⟨g, hg, hv, hgq⟩ := slotFn_eq_some hsd
        have := slotFn_of (firstWith_append hg more) (viaTail_mono more ih hv)
        rw [this, ← hgq]
      | f5 ρ0 =>
        obtain ⟨p, cms, rtreq, slot, sh, hp, hr, rfl⟩ := rooted_f5_eq_some hD
        obtain ⟨D', h1, slot', rfl, h2⟩ := ih _ _ hr
        exact ⟨_, rooted_f5_of (firstWith_append hp more) h1, slot', rfl, h2⟩
      | f3 ρ0 c =>
        obtain ⟨p, cms, rtreq, slot, sh, sd, l, hp, hr, hs, hl, rfl⟩ := rooted_f3_eq_some hD
        obtain ⟨D', h1, slot', rfl, h2⟩ := ih _ _ hr
        exact ⟨_, rooted_f3_of (firstWith_append hp more) h1 (h2 c sd hs) hl, rfl⟩

/-! ## Part 4. The bound on E'_S for one query -/

theorem slotTr_nil (sd : SlotD lam K L t) (q : FbIn lam L t) :
    slotTr sd [] q = (sd.recs, .jn sd.gq q) := rfl

theorem slotTr_cons (sd : SlotD lam K L t) (p4 : FbIn lam L t × FsAns lam K)
    (rest : List (FbIn lam L t × FsAns lam K)) (q : FbIn lam L t) :
    slotTr sd (p4 :: rest) q =
      (sd.recs ++ (.jn sd.gq p4.1, p4.2) :: rest.map fun z => (.sh z.1, z.2), .sh q) := rfl

theorem map_shPart_of_allLo :
    ∀ {l : List (Rec lam K L t)}, AllLo l → l.map shPart = List.replicate l.length (none, none)
  | [], _ => rfl
  | rc :: l, h => by
      obtain ⟨q, hq⟩ := h rc List.mem_cons_self
      have h1 : shPart rc = (none, none) := by
        unfold shPart
        rw [hq]
        rfl
      rw [List.map_cons, h1, map_shPart_of_allLo fun z hz => h z (List.mem_cons_of_mem _ hz)]
      rfl

variable {W : QueryLayout lam L}

/-- What the analysis needs of a protocol: well-formed wire records (`RoundsQueryLayout.OKG`); and, for its
state function and for every instance vector, the condition on verifier messages (`JointLaw`,
Iop/Batch.lean) of (Snd-B): in each round at most ε_i (of `ℓ.ε`) values of the verifier message turn
a slot's state from 0 to 1, in a shared round for all slots jointly. -/
structure Lane.OK (ℓ : Lane W) (N : ℕ) : Prop where
  ws : RoundsQueryLayout.OKG ℓ.s ℓ.A ℓ.ws
  joint : ∀ (pre : Tc W) (cms : List (Dig lam)) (xs : Fin N → Option (Option X)),
    JointLaw N ℓ.s ℓ.A ℓ.ε fun j => (xs j).bind (ℓ.state pre cms)

/-- Under the hypotheses below: a uniform answer turns the state of one slot's transcript from 0 to
1 (`Lane.flips`) with probability at most εs. -/
theorem Lane.pr_flips_le (ℓ : Lane W) {N : ℕ} (hN : 0 < N) (hOK : ℓ.OK N) {εs : ℝ≥0∞}
    (hε : Err.Below ℓ.ε εs) (pre : Tc W) (cms : List (Dig lam)) (x : Option X)
    (l : List (Rec lam W.K L ℓ.t)) (cur : Item lam L ℓ.t) :
    pr (unif (FsAns lam W.K)) {a | ℓ.flips pre cms x l cur a} ≤ εs := by
  cases hS : ℓ.state pre cms x with
  | none =>
    refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
    rintro a - ⟨S, τ, h, -⟩
    rw [hS] at h; cases h
  | some S =>
    cases hτ : trOf pre ℓ.t ℓ.s ℓ.A ℓ.ws ℓ.prjS ℓ.prjP l cur with
    | none =>
      refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
      rintro a - ⟨S', τ, -, h, -⟩
      rw [hτ] at h; cases h
    | some τ =>
      by_cases h0 : S (.atV τ) = false
      · refine le_trans (pr_mono _ ?_)
          (pr_flip_le hOK.ws hε (hOK.joint pre cms fun _ => some x) ⟨0, hN⟩ S hS τ h0)
        rintro a ⟨S', τ', h1, h2, -, h4⟩
        rw [hS] at h1; cases h1
        rw [hτ] at h2; cases h2
        exact h4
      · refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
        rintro a - ⟨S', τ', h1, h2, h3, -⟩
        rw [hS] at h1; cases h1
        rw [hτ] at h2; cases h2
        exact h0 h3

/-- The same for a rooted query with its data. -/
theorem Lane.pr_flipsAt_le (ℓ : Lane W) {N : ℕ} (hN : N = 2 ^ W.depthReq) (hOK : ℓ.OK N) {εs : ℝ≥0∞}
    (hε : Err.Below ℓ.ε εs) (pre : Tc W) (q : FbIn lam L ℓ.t) (D : Data lam W.K L ℓ.t)
    (hD : rooted ℓ.t pre q.round q.head = some D) :
    pr (unif (FsAns lam W.K)) {a | ℓ.flipsAt pre q a D} ≤ εs := by
  have hpos : 0 < N := by rw [hN]; exact Nat.pow_pos (by decide)
  cases D with
  | locV cms x l => exact ℓ.pr_flips_le hpos hOK hε pre cms _ l (.lo q)
  | locA cms x l => exact ℓ.pr_flips_le hpos hOK hε pre cms _ l (.lo q)
  | shd cms rtreq slot sh =>
    obtain ⟨-, iJ, hi, hslot⟩ := rooted_good pre _ _ _ hD
    let sdOf : Fin N → Option (SlotD lam W.K L ℓ.t) := fun j =>
      (digOf rtreq).bind fun rt => (extReq pre W.depthReq rt j.val).bind slot
    have hlive : ∀ j sd, sdOf j = some sd → ∃ c, slot c = some sd := by
      intro j sd h
      obtain ⟨rt, -, h1⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨c, -, h2⟩ := Option.bind_eq_some_iff.1 h1
      exact ⟨c, h2⟩
    have hcompat : Compat (fun j => (sdOf j).map fun sd => slotTr sd sh q) q.round := by
      refine ⟨fun j d hd => ?_, fun j j' d d' hd hd' => ?_, fun j d hd => ?_⟩
      · obtain ⟨sd, h1, rfl⟩ := Option.map_eq_some_iff.1 hd
        obtain ⟨c, hc⟩ := hlive j sd h1
        have h2 := (hslot c sd hc).1
        cases sh with
        | nil => rw [slotTr_nil]; simpa [h2] using hi
        | cons p4 rest =>
          rw [slotTr_cons]
          simp only [List.length_append, List.length_cons, List.length_map] at hi ⊢
          omega
      · obtain ⟨sd, h1, rfl⟩ := Option.map_eq_some_iff.1 hd
        obtain ⟨sd', h1', rfl⟩ := Option.map_eq_some_iff.1 hd'
        obtain ⟨c, hc⟩ := hlive j sd h1
        obtain ⟨c', hc'⟩ := hlive j' sd' h1'
        obtain ⟨h2, h3, -⟩ := hslot c sd hc
        obtain ⟨h2', h3', -⟩ := hslot c' sd' hc'
        have h4 : sd.recs.map shPart = sd'.recs.map shPart := by
          rw [map_shPart_of_allLo h3, map_shPart_of_allLo h3', h2, h2']
        cases sh with
        | nil => exact ⟨h4, rfl⟩
        | cons p4 rest =>
          refine ⟨?_, rfl⟩
          rw [slotTr_cons, slotTr_cons]
          simp only [List.map_append, List.map_cons, h4]
          rfl
      · obtain ⟨sd, h1, rfl⟩ := Option.map_eq_some_iff.1 hd
        cases sh <;> rfl
    refine le_trans (pr_mono _ ?_)
      (joint_le pre ℓ.s ℓ.A ℓ.ws hOK.ws ℓ.ε hε ℓ.prjS ℓ.prjP _
        (hOK.joint pre cms fun j =>
          (sdOf j).map fun sd => lastX sd.x (slotTr sd sh q).1 (slotTr sd sh q).2)
        q.round _ hcompat)
    rintro a ⟨j, hj, rt, c, sd, hrt, hc, hsd, S, τ, hS, hτ, h0, h1⟩
    have hsdj : sdOf ⟨j, hN ▸ hj⟩ = some sd := by
      show (digOf rtreq).bind (fun rt => (extReq pre W.depthReq rt j).bind slot) = some sd
      rw [hrt, Option.bind_some, hc, Option.bind_some, hsd]
    refine ⟨⟨j, hN ▸ hj⟩, S, slotTr sd sh q, τ, ?_, ?_, hτ, h0, h1⟩
    · show ((sdOf ⟨j, hN ▸ hj⟩).map fun sd => lastX sd.x (slotTr sd sh q).1 (slotTr sd sh q).2).bind
          (ℓ.state pre cms) = some S
      rw [hsdj]
      exact hS
    · show (sdOf ⟨j, hN ▸ hj⟩).map (fun sd => slotTr sd sh q) = _
      rw [hsdj]
      rfl

/-- Under the hypotheses below: given the entries before it, a query causes E'_S with probability at
most εs. -/
theorem Lane.pr_step_le (ℓ : Lane W) {N : ℕ} (hN : N = 2 ^ W.depthReq) (hOK : ℓ.OK N) {εs : ℝ≥0∞}
    (hε : Err.Below ℓ.ε εs) (pre : Tc W) (q : FbIn lam L ℓ.t) :
    pr (unif (FsAns lam W.K)) {a | ℓ.step pre (fbE ℓ.t q a)} ≤ εs := by
  cases h : rooted ℓ.t pre q.round q.head with
  | none =>
    refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
    rintro a - ⟨-, q', a', D, he, hr, -⟩
    obtain ⟨rfl, rfl⟩ := fbE_inj he
    rw [h] at hr; cases hr
  | some D =>
    refine le_trans (pr_mono _ ?_) (ℓ.pr_flipsAt_le hN hOK hε pre q D h)
    rintro a ⟨-, q', a', D', he, hr, hf⟩
    obtain ⟨rfl, rfl⟩ := fbE_inj he
    rw [h] at hr; cases hr
    exact hf

end Compile.Batch
