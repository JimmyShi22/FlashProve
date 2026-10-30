-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxReadAs.lean: the format's reader of an opening said yes at every opening of a
chain that the strict reader has read: `ReadAs` (OnBytes/TypedOracleCompiler/Slice/Batch3SRead.lean) for every
member of the typing's list, from the reader's equation
`Fmt.readChainX h S seen b i = some (o, j)`.

Main names (h: any hash; S: any description):
  `ReadAt h S o y`: what is said of an opening y = (shape, places, what was read): either it is a
    stored table's: some round of S lists a stored table t with that shape, and the reader of an
    opening returned it from the start `S.base.cfg`; or it is a tree's of the chain: some round of S
    opens a tree x with that shape, and the reader returned it from that tree's own start
    (`startOf o.run x.2`, OnBytes/Tie/TraceStrict.lean: the chain's run value for a tree of its
    own).
  `readAt_of_chain`: every opening of every round as read has it.
  `readAs_of_chain`: so every member of `opsOf 1 o`.
  `readAs_run`: where every tree that S opens is the chain's own, and the chain has the run value
    `run`: a tree's opening was read from `run`.
  `own_unmarked`, `stored_flags`: of a description in order: a stored table's tree has the mark
    "stored"; a tree of the chain's own that is opened has not.
  `readAs_own`, `readAs_sto`: the split by the shape's mark "stored", there: an opening without the
    mark is a tree's of the chain, one with the mark a stored table's.
  `readAs_own_at`, `readAs_sto_at`: at the entry's description `entryXD G c`, any statement, at the
    format's own oracle.

Hypotheses: the reader's equation; for `readAs_run`, `readAs_own`, `readAs_sto`: every tree that S
opens is the chain's own; for the first two: the chain's run value; for the last two names:
`PQ.ok (entryXD G c).base`.

Limits: values alone. Nothing on roots, on leaves' digests at a family of oracles, or on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.Asm
import OnBytes.Tie.StoredMain
import OnBytes.Tie.SpecXBase
import Run.OneIsTypedTop
import Fmt.Rules8Ok

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie TypedOracleCompiler.Slice
open _root_.Run (HId)

/-- What is said of an opening as read. -/
def ReadAt (h : HId) (S : Fmt.SpecX) (o : Fmt.ChainOut)
    (y : Fmt.Shape × List ℕ × Fmt.OpenOut) : Prop :=
  (∃ t ∈ S.stored.flatten, y.1 = t.sh ∧
    ReadAs h S.base.cfg S.base.cfg ⟨1, 0, 0, y.1, y.2.1, y.2.2⟩) ∨
  ∃ r ∈ S.base.rounds, ∃ x ∈ r.opens, y.1 = x.1 ∧ ∃ start, startOf o.run x.2 = some start ∧
    ReadAs h S.base.cfg start ⟨1, 0, 0, y.1, y.2.1, y.2.2⟩

section
variable {h : HId} {S : Fmt.SpecX} {seen : Fmt.Seen} {b : ByteArray} {i : ℕ} {o : Fmt.ChainOut}
  {j : ℕ} (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j))

include e in
/-- Every opening of every round as read. -/
theorem readAt_of_chain : ∀ r ∈ o.rounds.toList, ∀ y ∈ r.opens, ReadAt h S o y := by
  obtain ⟨hok, -, rc, g1, g2, -, g5⟩ := readX_trace h S seen b i o j e
  have hlen : S.stored.length = S.base.rounds.length := by
    have := hok
    simp only [Fmt.SpecX.ok, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.2
  have hzp : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (by omega)
  have sh1 := List.forall₂_map_right_iff.1 (shapes_of_trace h S.base.plan _ _ _ _ g2)
  rw [← hzp] at sh1
  have all := forall₂_and (List.forall₂_map_left_iff.1 sh1) g5
  intro r hr y hy
  rw [g1] at hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  obtain ⟨x, hx, hs, -, hown, hsto⟩ := forall₂_mem_right all p hp
  have hs' : List.Forall₂ (fun a c => c.1 = a.1) x.1.opens p.1.opens :=
    List.forall₂_map_right_iff.1 hs
  rcases List.mem_append.1 (show y ∈ p.2 ++ p.1.opens from hy) with hy | hy
  · obtain ⟨t, ht, hf, i', hrd⟩ := forall₂_mem_right hsto y hy
    exact .inl ⟨t, List.mem_flatten.2 ⟨x.2, (List.of_mem_zip hx).2, ht⟩, hf.sh,
      ⟨S.base.plan.field, t.salt, b, i', by rw [hf.sh]; exact hrd⟩,
      given32_of_read h _ _ _ _ _ _ _ _ _ hrd⟩
  · obtain ⟨a, ha, hsh, start, i', hst, hrd, -⟩ := forall₂_mem_right (forall₂_and hs' hown) y hy
    exact .inr ⟨x.1, (List.of_mem_zip hx).1, a, ha, hsh, start, hst,
      ⟨S.base.plan.field, S.base.plan.salt, b, i', by rw [hsh]; exact hrd⟩,
      given32_of_read h _ _ _ _ _ _ _ _ _ hrd⟩

include e in
/-- Every member of the typing's list. -/
theorem readAs_of_chain : ∀ op ∈ opsOf 1 o,
    (∃ t ∈ S.stored.flatten, op.sh = t.sh ∧ ReadAs h S.base.cfg S.base.cfg op) ∨
    ∃ r ∈ S.base.rounds, ∃ x ∈ r.opens, op.sh = x.1 ∧ ∃ start, startOf o.run x.2 = some start ∧
      ReadAs h S.base.cfg start op := fun op hop => by
  rcases ops1_all (ReadAt h S o) o (readAt_of_chain e) op hop with
    ⟨t, ht, hs, R⟩ | ⟨r, hr, x, hx, hs, start, hst, R⟩
  · exact .inl ⟨t, ht, hs, R.read, R.given32⟩
  · exact .inr ⟨r, hr, x, hx, hs, start, hst, R.read, R.given32⟩

include e in
/-- Where every tree that the description opens is the chain's own: from the chain's run value. -/
theorem readAs_run (hown : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    {run : ByteArray} (hrun : o.run = some run) : ∀ op ∈ opsOf 1 o,
    (∃ t ∈ S.stored.flatten, op.sh = t.sh ∧ ReadAs h S.base.cfg S.base.cfg op) ∨
    ∃ r ∈ S.base.rounds, ∃ x ∈ r.opens, op.sh = x.1 ∧ ReadAs h S.base.cfg run op := fun op hop => by
  rcases readAs_of_chain e op hop with hs | ⟨r, hr, x, hx, hs, start, hst, R⟩
  · exact .inl hs
  · obtain ⟨n, hn⟩ := hown r hr x hx
    rw [hn, hrun] at hst
    obtain rfl : run = start := Option.some.inj hst
    exact .inr ⟨r, hr, x, hx, hs, R⟩

/-- A tree of the chain's own that a description in order opens has no mark "stored". -/
theorem own_unmarked (hS : S.ok = true) : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens,
    (∃ n, x.2 = .own n) → x.1.stored = false := by
  intro r hr x hx ⟨n, hn⟩
  obtain ⟨after, sent, hk⟩ := _root_.Run.PQ.roundsOk_mem _ _ _ _ _ _
    (Fmt.ok_rounds (specX_base S hS)) r hr
  simp only [Fmt.Round.ok, Bool.and_eq_true, and_assoc, List.all_eq_true] at hk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ho⟩ := hk
  have h2 := (ho x hx).2
  rw [hn] at h2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
  exact h2.1.2

/-- The two marks, of a description in order: a stored table's tree has the mark "stored"; a tree of
the chain's own that is opened has not. -/
theorem stored_flags (S : Fmt.SpecX) (hS : S.ok = true) :
    (∀ t ∈ S.stored.flatten, t.sh.stored = true) ∧
    ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, (∃ n, x.2 = .own n) → x.1.stored = false :=
  ⟨fun t ht => (specX_shape S hS t ht).1, own_unmarked hS⟩

include e in
/-- An opening without the mark "stored" is a tree's of the chain, read from the run value. -/
theorem readAs_own (hown : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    {run : ByteArray} (hrun : o.run = some run) :
    ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      ∃ r ∈ S.base.rounds, ∃ x ∈ r.opens, op.sh = x.1 ∧ ReadAs h S.base.cfg run op := by
  intro op hop
  obtain ⟨hop, hf⟩ := List.mem_filter.1 hop
  rcases readAs_run e hown hrun op hop with ⟨t, ht, hs, -⟩ | hr
  · have hS := (readX_trace h S seen b i o j e).1
    rw [hs, (specX_shape S hS t ht).1] at hf
    cases hf
  · exact hr

include e in
/-- An opening with the mark "stored" is a stored table's, read from the configuration's
digest. -/
theorem readAs_sto (hown : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n) :
    ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      ∃ t ∈ S.stored.flatten, op.sh = t.sh ∧ ReadAs h S.base.cfg S.base.cfg op := by
  intro op hop
  obtain ⟨hop, hf⟩ := List.mem_filter.1 hop
  rcases readAs_of_chain e op hop with hs | ⟨r, hr, x, hx, hs, -⟩
  · exact hs
  · have hS := (readX_trace h S seen b i o j e).1
    rw [hs, own_unmarked hS r hr x hx (hown r hr x hx)] at hf
    cases hf

end

/-- Every tree that a description within the typing's limits opens is the chain's own. -/
theorem opens_own {S₀ : Fmt.Spec} (hok : TypedOracleCompiler.Run.PQ.ok S₀ = true) :
    ∀ r ∈ S₀.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n := by
  intro r hr x hx
  simp only [TypedOracleCompiler.Run.PQ.ok, Bool.and_eq_true, List.all_eq_true] at hok
  have h1 := hok.1.1.2 x (List.mem_flatMap.2 ⟨r, hr, hx⟩)
  obtain ⟨sh, src⟩ := x
  cases src with
  | own n => exact ⟨n, rfl⟩
  | given _ _ => cases h1

section
variable (G : EntryGround) (c st : ByteArray)
  (hok : TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true) {seen : Fmt.Seen} {b : ByteArray}
  {i : ℕ} {o : Fmt.ChainOut} {j : ℕ}
  (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
    (TypedOracleCompiler.Run.PQ.withStatement (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) st)
    seen b i = some (o, j))

include hok e in
/-- At the entry's description: an opening without the mark. -/
theorem readAs_own_at {run : ByteArray} (hrun : o.run = some run) :
    ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      ∃ r ∈ (entryXD G c).base.rounds, ∃ x ∈ r.opens, op.sh = x.1 ∧
        ReadAs (Fmt.HO Fmt.oracle) (entryXD G c).base.cfg run op :=
  readAs_own e (opens_own (S₀ := (entryXD G c).base) hok) hrun

include hok e in
/-- At the entry's description: an opening with the mark. -/
theorem readAs_sto_at :
    ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      ∃ t ∈ (entryXD G c).stored.flatten, op.sh = t.sh ∧
        ReadAs (Fmt.HO Fmt.oracle) (entryXD G c).base.cfg (entryXD G c).base.cfg op :=
  readAs_sto e (opens_own (S₀ := (entryXD G c).base) hok)

end
end OnBytes.K.Left
