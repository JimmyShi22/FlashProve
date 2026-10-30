-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Opened.lean: the openings that the compiled prover lays (OnBytes/Prover/Defs.lean)
meet what the verifier's strict format asks of openings (`Opened`, `OpenedE`,
OnBytes/TypedOracleCompiler/Joined/K/YesRead.lean), if what is kept of the rounds meets the invariant
(OnBytes/Prover/Inv.lean) and the outer trees are kept rightly.

Main names:
  `extK_read`, `extK_some`   an opening of the external strings stands at each read position, and
                 there alone
  `opened_at`    the openings at the rounds: only where read, under a root, with a salt of sMT
                 bits; none that is read lacks; each path is as long as its tree is deep
  `openedE_at`   the same for the external strings

Limits: lengths and places alone: nothing on hashing (that is OnBytes/Prover/Walks.lean), nothing
on probability. Nothing says that a prover's run meets the invariant: that is
OnBytes/Prover/Chain.lean. Salts are spoken of by their lengths alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Tree

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The external strings' openings -/

/-- at a read position stands the opening out of that position's tree -/
theorem extK_read {E : ExtSpec} (we : WireE E) (y : E.Str) (xt : ℕ → TreeK lam L)
    (rd : E.Pos → Bool) {p : E.Pos} (h : rd p = true) :
    extK we y xt rd p = some ((xt (we.which p)).opening (we.leaf p) (E.rd y p)) :=
  if_pos h

/-- an opening stands at a read position alone -/
theorem extK_some {E : ExtSpec} (we : WireE E) (y : E.Str) (xt : ℕ → TreeK lam L)
    (rd : E.Pos → Bool) {p : E.Pos} {op : Opening lam E.Sym} (h : extK we y xt rd p = some op) :
    rd p = true := by
  by_contra hn
  have e : extK we y xt rd p = none := if_neg hn
  rw [e] at h
  cases h

/-! ## What the strict format asks -/

/-- **The openings at the rounds.** -/
theorem opened_at : ∀ (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L) (kp : Kept lam L s)
    (R : RootsOfChain lam s) (rd : OPos s → Bool),
  RoundsAt g sMT s A W embS kp R → RoundsQueryLayout.OKG s A W →
    Opened sMT s A W R rd (opensK s A W kp rd) := by
  intro g sMT s A W embS kp R rd hR hW
  refine ⟨fun p op h => ?_, fun p hp => ?_, fun p op d c hp h ht => ?_⟩
  · have hp := opensK_some s A W kp rd p op h
    obtain ⟨T, d, ht, -, -, ho, -, hs⟩ := look s A W embS kp R rd hR hW p hp
    rw [ho] at h
    obtain rfl := Option.some.inj h
    exact ⟨hp, hs, Option.isSome_iff_exists.2 ⟨_, ht⟩⟩
  · obtain ⟨T, d, -, -, -, ho, -, -⟩ := look s A W embS kp R rd hR hW p hp
    exact Option.isSome_iff_exists.2 ⟨_, ho⟩
  · obtain ⟨T, d', ht', hA, -, ho, -, -⟩ := look s A W embS kp R rd hR hW p hp
    rw [ho] at h
    obtain rfl := Option.some.inj h
    rw [ht'] at ht
    obtain rfl : d' = d := congrArg Prod.fst (Option.some.inj ht)
    exact hA.length_path _

/-- **The openings of the external strings.** -/
theorem openedE_at : ∀ (g : Fam (typedOracleFamily lam K L)) (sMT m : ℕ) (E : ExtSpec) (we : WireE E)
    (embE : E.Sym → Body L) (cms : List (Dig lam)) (y : E.Str) (xt : ℕ → TreeK lam L)
    (rd : E.Pos → Bool),
  ExtAt g sMT we embE cms y xt → we.depth ≤ m → OpenedE sMT m we rd (extK we y xt rd) := by
  intro g sMT m E we embE cms y xt rd hx hm
  refine ⟨fun p _ op h => ?_, fun p _ hp => ?_, fun p _ op hp h => ?_, hx.leaf, hm⟩
  · have hp := extK_some we y xt rd h
    rw [extK_read we y xt rd hp] at h
    obtain rfl := Option.some.inj h
    exact ⟨hp, hx.salt p⟩
  · exact Option.isSome_iff_exists.2 ⟨_, extK_read we y xt rd hp⟩
  · rw [extK_read we y xt rd hp] at h
    obtain rfl := Option.some.inj h
    exact (hx.tree p).length_path _

end OnBytes.Prover

