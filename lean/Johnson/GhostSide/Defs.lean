-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/GhostSide/Defs.lean: the names fbw t k of the later tries of a search, for the compiler's
second form: the exchange of queries, and what it means that a program is routed. Definitions and
statements; the proofs are in Johnson/GhostSide/Generic.lean.

General statements on the second form's oracles. This file states no goal of the release. A DEVICE
OF A PROOF: the names fbw t k, the exchange of queries and "routed" stand in no statement on the
scheme.

The definitions and the three statements are those of Compile/Batch/SpecGhost.lean, typed again over
the second form's oracles (OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean). That file's head says why there
are such names: in a round with a test the honest prover asks the Fiat-Shamir oracle fb t once for
each nonce that it tries, all these queries hold one secret string, and the lemma on deferred
programming allows one charge for each secret string and oracle. So a token program writes try
number k + 1 as a query to a further oracle, fbw t k, at the same input; the scheme has fb t written
back (realQ).

Main names (namespace OnBytes.GhostSide).
  clsPB, shW, cls   the number for which the nonce in a plain part, or in a Fiat-Shamir query,
                    stands; 0 if the component has no test.
  ghost W           the exchange: (fb t, q) with the nonce for k + 1 ↔ (fbw t k, q); all other
                    queries stay. Spec.ghostPerm: a bijection, and its own inverse, for every wire.
  Routed, RoutedT   an oracle algorithm, a token program (Johnson/TokenSide/Split.lean: StT), asks
                    fb t only where the input holds the nonce for 0, and fbw t k only where it holds
                    the nonce for k + 1. A recursion on the term.
  Spec.realQ_via    for a routed algorithm realQ is the translation by ghost W.
  Spec.routedErase  what erase makes of a routed token program is routed.

Limits: those of Compile/Batch/SpecGhost.lean. Nothing is said here on any program.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Split
import Compile.Star
import Rom.SpecVia

set_option autoImplicit false

noncomputable section

namespace OnBytes.GhostSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch OnBytes.TokenSide Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- the number for which the nonce in a plain part stands; 0 if the component has no test -/
def clsPB {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → PlainPart s A → ℕ
  | [], _, _, z => nomatch z
  | _ :: _, (_, _), (w, _), .inl (.inl α) => match w.gr0 with
      | none => 0
      | some g => g.get α
  | _ :: _, (_, _), (w, _), .inl (.inr α) => match w.grJ with
      | none => 0
      | some g => g.get α
  | _ :: s, (_, A), (_, W), .inr z => clsPB s A W z

/-- the wires of the rounds of a protocol, by its tag -/
def shW (W : QueryLayout lam L) : (t : Tag) → RoundsQueryLayout lam W.K (shapeOf L t) (annOf L t)
  | .test => W.T.sh
  | .link => W.Lk.sh
  | .onl => W.B.sh

/-- the number for which the nonce of a Fiat-Shamir query stands -/
def cls (W : QueryLayout lam L) (t : Tag) (q : FbIn lam L t) : ℕ := clsPB _ _ (shW W t) q.plain

/-- The exchange of queries: (fb t, q) with the nonce for k + 1 ↔ (fbw t k, q). All other queries
stay. -/
def ghost (W : QueryLayout lam L) : QMap (typedOracleFamily lam W.K L)
  | .fb t, q => match cls W t q with
      | 0 => ⟨.fb t, q, id⟩
      | k + 1 => ⟨.fbw t k, q, id⟩
  | .fbw t k, q => if cls W t q = k + 1 then ⟨.fb t, q, id⟩ else ⟨.fbw t k, q, id⟩
  | .leaf, q => ⟨.leaf, q, id⟩
  | .node, q => ⟨.node, q, id⟩
  | .rleaf, q => ⟨.rleaf, q, id⟩
  | .rnode, q => ⟨.rnode, q, id⟩
  | .g t, q => ⟨.g t, q, id⟩
  | .ann, q => ⟨.ann, q, id⟩
  | .other, q => ⟨.other, q, id⟩

/-- Routed: fb t is asked only where the input holds the nonce for 0, and fbw t k only where it
holds the nonce for k + 1. -/
def Routed (W : QueryLayout lam L) {α : Type} : TypedOracleComputation lam W.K L α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, Routed W (k r)
  | .query (.fb t) q k => cls W t q = 0 ∧ ∀ r, Routed W (k r)
  | .query (.fbw t j) q k => cls W t q = j + 1 ∧ ∀ r, Routed W (k r)
  | .query _ _ k => ∀ r, Routed W (k r)

/-- Routed, for a token program: whatever strings its tokens stand for. -/
def RoutedT (W : QueryLayout lam L) {α : Type} : StT lam W.K L α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, RoutedT W (k r)
  | .plain (.fb t) q k => cls W t q = 0 ∧ ∀ r, RoutedT W (k r)
  | .plain (.fbw t j) q k => cls W t q = j + 1 ∧ ∀ r, RoutedT W (k r)
  | .plain _ _ k => ∀ r, RoutedT W (k r)
  | .fresh _ k => ∀ u, RoutedT W (k u)
  | .marked (.fb t) _ _ pt _ k => (∀ v vs, cls W t (pt v vs) = 0) ∧ ∀ v u, RoutedT W (k v u)
  | .marked (.fbw t j) _ _ pt _ k => (∀ v vs, cls W t (pt v vs) = j + 1) ∧ ∀ v u, RoutedT W (k v u)
  | .marked _ _ _ _ _ k => ∀ v u, RoutedT W (k v u)
  | .reveal _ k => ∀ vs, RoutedT W (k vs)

namespace Spec

def ghostPerm : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocolWithLeafBody I X) (W : QueryLayout lam L), QMap.Perm (ghost W) (ghost W)

def realQ_via : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocolWithLeafBody I X) (W : QueryLayout lam L) (α : Type) (c : TypedOracleComputation lam W.K L α),
    Routed W c → realQ c = c.via (ghost W)

def routedErase : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocolWithLeafBody I X) (W : QueryLayout lam L) (α : Type)
      (c : StT lam W.K L α) (vs : List Bits),
    RoutedT W c → Routed W (erase c vs)

end Spec
end OnBytes.GhostSide
