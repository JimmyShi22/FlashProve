-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Holes.lean: the four fields of the page (OnBytes/Maker/Page/Frame.lean, `PageJ`)
that are taken as they are from the codes of the entry file's chain, of the seeds' two queries and
of the entry file's leaves; where these codes and the page's own rows meet.

The page asks the taken spellings first (`takenJ`). So a law on the page's own row at a typed query
asks that the taken spelling writes nothing there, or writes the same string (for the leaves:
OnBytes/Maker/Page/LeafAgree.lean).

Main names.
  `withHoles P ...`: the page P with `link`, `seeds` and `leafX` laid from a code of the link's
    chain queries (`SeedPage.LinkCode`), the code of the seeds' two queries (`SeedPoints.fbSeeds`)
    and a code of leaves (`PageG.Leaves`); `other` writes nothing.
  `seeds_writes`: the seeds' code writes at its two forms of query alone: `q0 cm` at the last block,
    `q1 v`.
  `seeds_none`: at a query of neither form it writes nothing. `seeds_silent`: so at a chain query
    that a file's own row spells, unless the query is of round 2, has no root and bears the plain
    part p1.
  `seeds_meet`: at `q1 v` both write, if the file's first chain has two written rounds: one typed
    query, two spellings.

Limits: the codes of the link's chain and of the leaves are letters: whether a code of leaves agrees
with the page's own call where it writes is shown of none. `gJ P O` is a function of the typed
query, no one-to-one coding. Nothing on soundness.


-/
import OnBytes.Maker.Page.LeafAgree
import OnBytes.TypedOracleCompiler.Run.SeedPage

set_option autoImplicit false

namespace OnBytes.Maker.Page
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.SeamAt TypedOracleCompiler.Run.PageG
open TypedOracleCompiler.Run.SeedPoints TypedOracleCompiler.Run.SeedPage
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes.Flat

variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (p0 p1 : PBt L .test) (isP0 isP1 : PBt L .test → Bool)
  (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (K : ℕ)

/-- The page with the four fields laid. -/
def withHoles (P : PageJ L K) (Lk : LinkCode L K) (V : Leaves L) : PageJ L K :=
  { P with
    link := Lk.pL.put
    seeds := (fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put
    leafX := V.lf.put
    other := fun _ => none }

/-- The seeds' code writes at its two forms of query alone. -/
theorem seeds_writes (x : FbIn 256 L .test × Fin (K + 1)) (s : List Bool)
    (h : (fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put x = some s) :
    (∃ cm, x = (q0 L .test p0 cfgL sh cm, Fin.last K)) ∨ (∃ v, x.1 = q1 L .test p1 v) := by
  rcases split_put _ _ _ _ x s h with h1 | h1
  · left
    obtain ⟨h2, hj⟩ := tailP_put _ K x s h1
    obtain ⟨a, ha, -⟩ := PCode.pull_put _ _ _ _ _ x.1 s h2
    obtain ⟨cm, hq, -⟩ := sel0_some L .test p0 isP0 cfgL sh hp0 x.1 a ha
    exact ⟨cm, Prod.ext hq hj⟩
  · right
    obtain ⟨y, hy, -⟩ := PCode.pull_put _ _ _ _ _ x s h1
    obtain ⟨v, hx, -⟩ := sel1_some L .test p1 isP1 hp1 K x y hy
    exact ⟨v, congrArg Prod.fst hx⟩

/-- At a query of neither form the seeds' code writes nothing. -/
theorem seeds_none (q : FbIn 256 L .test) (j : Fin (K + 1))
    (h0 : ∀ cm, q ≠ q0 L .test p0 cfgL sh cm) (h1 : ∀ v, q ≠ q1 L .test p1 v) :
    (fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put (q, j) = none := by
  cases hs : (fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put (q, j) with
  | none => rfl
  | some s =>
    rcases seeds_writes L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K (q, j) s hs with ⟨cm, e⟩ | ⟨v, e⟩
    · exact absurd (congrArg Prod.fst e) (h0 cm)
    · exact absurd e (h1 v)

/-- At a chain query that a file's own row spells the seeds' code writes nothing, unless the query
is of round 2, has no root and bears the plain part p1. -/
theorem seeds_silent (F : FileJ L .test) (q : FbIn 256 L .test) (j : Fin (K + 1)) (c : Fmt.OQ)
    (hc : fbCallJ F K q j = some c) (hp : q.round = 2 → q.rt = [] → q.plain ≠ p1) :
    (fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put (q, j) = none := by
  cases hs : (fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put (q, j) with
  | none => rfl
  | some s =>
    exfalso
    rcases seeds_writes L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K (q, j) s hs with ⟨cm, e⟩ | ⟨v, e⟩
    · have eq : q = q0 L .test p0 cfgL sh cm := congrArg Prod.fst e
      rw [eq] at hc
      have hn : fbCallJ F K (q0 L .test p0 cfgL sh cm) j = none := by
        unfold fbCallJ q0
        simp
      rw [hn] at hc
      cases hc
    · have eq : q = q1 L .test p1 v := e
      exact hp (by rw [eq]; rfl) (by rw [eq]; rfl) (by rw [eq]; rfl)

/-- At the seeds' second query both write, if the file's first chain has two written rounds. -/
theorem seeds_meet (F : FileJ L .test) (h2 : 2 ≤ F.n₁) (hK : K < 2 ^ 48) (v : Bits)
    (hv : v.length = 256) (j : Fin (K + 1)) :
    (fbCallJ F K (q1 L .test p1 v) j).isSome = true ∧
      ((fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put
        (q1 L .test p1 v, j)).isSome = true := by
  constructor
  · show (if 1 ≤ 2 ∧ 2 ≤ F.n₁ then some _ else _ : Option Fmt.OQ).isSome = true
    rw [if_pos ⟨by decide, h2⟩]
    rfl
  · rw [fbSeeds_q1 L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K hK v hv j]
    rfl

end OnBytes.Maker.Page
