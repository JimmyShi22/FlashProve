-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ShownRounds.lean: THE ROUNDS THAT A BLOCK'S `decide` IS SHOWN ARE THE STRETCH'S
OWN ROUNDS AS THE LIBRARY MAKES THEM OF THE TRANSCRIPT. A small law on the frame, for every kind; no
probability in it.

Why. A piece's reduction (`Piece.ior`, Johnson/Desc/Sound/ChainRule.lean) shows the block's `decide`
the view's rounds WITHOUT THE SEALED DIGEST (`Block.step`: `rs.map noDigest`). A kind's tie to the
library (for the lookup: K3DecideHears and K3ClaimsGiveOut, Johnson/Top/H/) speaks of `decide`
at `rvT C ds τ`, the rounds as the library makes them of a written transcript. Between the two
stands one equation: where no round of the stretch is the sealing round, no round holds a digest,
and taking it away changes nothing.

Main theorems:
  `collect_noSeal`, `dsOf_noSeal`, `dr_noDigest`: what a round draws whose kind is not "sealed"
    holds no digest (at the challenges as hash blocks: `ckP`).
  `rvSL_noDigest`: the like along written rounds. `shown_is_rvT`: **the equation**, for a piece
    behind whose stretch no round is put.

Silly members: an equation on the frame's view: it holds of every block: it claims nothing of what a
block decides.

Limits: the premise (no round of the stretch has the kind "sealed") is not shown of any stretch
here: for a plan's written rounds it is read off the plan. The first chain's last block, behind
which the empty sealing round is put, is not covered. It calls the library's `Run.outAll`,
`Run.Vals`, `Fmt.collect`, `Fmt.dsOf`, `rvSL`, `sView`: pure functions.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ChainRule
import Run.PlanPull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat
open _root_.Run (ckP)

/-- Draws among which none is the sealed digest give a record without a digest. -/
theorem collect_noSeal (f : Fmt.Fld) : ∀ (ds : List Fmt.Draw) (v : _root_.Run.Vals f ds),
    Fmt.Draw.sealed ∉ ds → (Fmt.collect (_root_.Run.outAll f ds v)).digest = none
  | [], _, _ => rfl
  | d :: ds, v, h => by
    have ih := collect_noSeal f ds v.2 fun hm => h (List.mem_cons_of_mem _ hm)
    cases d with
    | elem => exact ih
    | elemNZ => exact ih
    | pos k => exact ih
    | trits n => exact ih
    | sealed => exact absurd List.mem_cons_self h

/-- A round whose kind is not "sealed" has no sealed digest among its draws. -/
theorem dsOf_noSeal (e : Fmt.Entry) (k : Fmt.Kind) (hk : k ≠ .sealed) :
    Fmt.Draw.sealed ∉ Fmt.dsOf e k := by
  unfold Fmt.dsOf Fmt.dsElems Fmt.dsSeeds
  rw [if_neg hk]
  split <;> simp [List.mem_replicate, List.mem_flatten]

/-- **What such a round draws holds no digest.** -/
theorem dr_noDigest (f : Fmt.Fld) (e : Fmt.Entry) (k : Fmt.Kind) (hk : k ≠ .sealed)
    (u : (ckP f).Ch e k) : ((ckP f).dr e k u).digest = none :=
  collect_noSeal f _ _ (dsOf_noSeal e k hk)

theorem noDigest_of_none (r : Fmt.RoundView) (h : r.drawn.digest = none) : noDigest r = r := by
  obtain ⟨vals, ⟨a, b, c, d⟩⟩ := r
  cases h
  rfl

/-- The like along written rounds (the library's plain form). -/
theorem rvSL_noDigest (f : Fmt.Fld) : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD)
    (τ : Iop.Tr (TypedOracleCompiler.Run.PQ.uL (ckP f) ds)), (∀ d ∈ ds, d.kind ≠ .sealed) →
    (TypedOracleCompiler.Run.PQ.rvSL (ckP f) ds τ).map noDigest = TypedOracleCompiler.Run.PQ.rvSL (ckP f) ds τ
  | [], _, _ => rfl
  | d :: ds, (m, c, τ), h => by
    show noDigest _ :: (TypedOracleCompiler.Run.PQ.rvSL (ckP f) ds τ).map noDigest = _ :: _
    rw [rvSL_noDigest f ds τ fun d' hd => h d' (List.mem_cons_of_mem _ hd),
      noDigest_of_none _ (dr_noDigest f d.entry d.kind (h d List.mem_cons_self) _)]

/-- **THE ROUNDS THAT A BLOCK'S `decide` IS SHOWN ARE THE STRETCH'S OWN ROUNDS AS THE LIBRARY MAKES
THEM OF THE TRANSCRIPT**, where no round of the stretch is the sealing round and none is put behind.
-/
theorem shown_is_rvT {S Cl W : Type} {F : Frame} (f : Fmt.Fld) (p : Piece (ckP f) F S Cl W)
    (hk : ∀ d ∈ toRDs p.ds, d.kind ≠ .sealed) (hb : p.back = []) (y : F.E.Str)
    (τ : Iop.Tr (uLT (ckP f) p.ds)) :
    ((sView (ckP f) p.stage y τ).rounds ++ p.back).map noDigest = rvT (ckP f) p.ds τ := by
  rw [hb, List.append_nil]
  exact rvSL_noDigest f (toRDs p.ds) τ hk

end VerifiableInference.Desc.Sound
