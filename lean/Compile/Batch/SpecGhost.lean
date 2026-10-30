-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecGhost.lean: the ghost names `fbw t k`, and how statements about them are carried
back to the scheme. Definitions and statements. The proofs: Compile/Batch/Ghost.lean,
Compile/Batch/GhostRouted.lean. (Words of this library: lean/GLOSSARY.md.)

Why there are ghost names. In a round with proof-of-work bits (Iop/BatchWire.lean: `GrW`) the honest
prover queries the Fiat-Shamir oracle `fb t` of its protocol once for each nonce 0, 1, 2, .. that it
tries (an attempt). All these queries hold the same secret string (the chaining value of the chain),
and differ in the nonce alone. The lemma on deferred programming (Rom/Defer.lean) allows one charge
for each secret string and oracle. So the token programs (Compile/Batch/Prover.lean: `fbTG`) make
attempt number k + 1 as a query to a further oracle, `fbw t k`, with the same input. The scheme has
these programs with `fb t` put back (Compile/Batch/Oracles.lean: `realQ`; Compile/Batch/Star.lean:
C, P). V, the extractor and every cheating party know `fb t` only; a query to a ghost name `fbw t k`
is, for them, a query to a further oracle that has nothing to do with the scheme.

The way back. Exchange the query (fb t, q), for an input q whose plain part holds the nonce for k +
1, with the query (fbw t k, q); leave all other queries as they are. That is a bijection of the
queries of the family of oracles which is its own inverse (`ghost W`). For a well-formed wire record
(`W.OKG`) the honest programs are routed: they query `fb t` only where the input holds the nonce for
0 (or in rounds without proof-of-work bits), and `fbw t k` only where it holds the nonce for k + 1.
For a routed program `realQ` is the translation by `ghost W` (`Spec.realQ_via`). By Rom/SpecVia.lean
an adversary A against the scheme sees what `A.via (ghost W)` sees against `argBT`, whose C and P
query the ghost names. So privacy of `argBT`, with a simulating challenger Sm, gives privacy of the
scheme with the simulating challenger that answers a query by Sm's answer at the exchanged query.

Part 1 (generic in the family of oracles and in the scheme)
  `Spec.closeVia`   closeness of the real challenger of A to a simulating challenger Sm gives
                    closeness of the real challenger of `viaCP φ A` to `Sm.pre ψ`, if φ and ψ are
                    inverse bijections (`QMap.Perm`), with the same bound ζ t n, t the number of all
                    queries of the adversary
  `Spec.gadmVia`   an admissible adversary stays admissible under a translation

Part 2 (the compiled scheme)
  `ghost`   `ghost W`: the exchange of queries; `Spec.ghostPerm`: it is a bijection and its own
            inverse, for every wire record (no condition on it is used)
  `Routed`, `RoutedT`   the property, for an oracle algorithm and for a token program: a recursion
                        on the term, so Lean checks it of the very terms `Cp`, `Pp`
  `Spec.routedErase`   what `erase` makes of a routed program is routed
  `Spec.routedCp`, `Spec.routedPp`
      the committer's and the prover's programs are routed, for every well-formed wire record
      (`W.OKG`)
  `argBT`   the scheme whose C and P query the ghost names. An object of the analysis only
  `Spec.argB_via`   see its doc comment

Notation: `t`: in `fb t`, `fbw t k`, `cls W t q`: a `Tag` (`.test`, `.link`, `.onl`:
Compile/Oracles.lean; they stand for `L.offline`, `L.link`, `L.onlineBatch`: `shapeOf`,
Compile/Batch/Oracles.lean); in ζ t n and in "budget t": a natural number: in `Close`
(Compile/Batch/SpecGlue.lean): `D.TotalBound t (n + 1)`; `k`: a natural number; `A`: in `viaCP` and
`Spec.closeVia` a scheme (`Gen.Arg`, ZKCP/Gen.lean), elsewhere in this header an adversary; `gr0`,
`grJ`: fields of `WireRB` (Iop/BatchWire.lean), each an `Option` of a `GrW`; token program: a term
of `St` (Compile/Batch/TokTree.lean; `Step`, Rom/Defer.lean); `erase`: Compile/Star.lean; `Cp`,
`Pp`: Compile/Batch/Star.lean; `WP`: a `WireBP L` (Iop/BatchWireP.lean); `p`: a `Params`
(Compile/Star.lean).

Limits.
* Nothing is said about completeness, index binding or any other form of binding of `argBT`: its V
  queries `fb t` where its P queried `fbw t k`, so as a rule V rejects a proof whose final attempt is not the first.
* The `fbw t k` remain oracles of the family `spec`, over which the scheme is typed. A step to one
  hash function must give their queries strings (Compile/Batch/ImplOf.lean); the scheme never
  queries them. "An object of the analysis only" is said of `argBT`, not of these oracles.
* The bound ζ of `Spec.closeVia` is in the adversary's total number of queries. `A.via (ghost W)`
  queries `fbw t k` where A queried `fb t`: in the proof of privacy for `argBT` the adversary's
  budget at each ghost name `fbw t k` has to be taken as its whole budget t. That is where the
  number of attempts, as a factor in the hash term of ζ, comes from (Compile/Batch/SpecGrind.lean;
  `xFbG`: Compile/Batch/Counts.lean).
* Other provers have programs of their own. That its program is routed is stated for the prover that
  makes no query for an empty slot (Compile/Batch/GhostRoutedU.lean); for any other program
  Compile/Batch/PubProgVia.lean assumes it; for the forms with a seed Compile/Batch/SeedGhost.lean
  proves, if the seed's oracle is no ghost name, that the provers query no ghost name.
-/
import Compile.Batch.Star
import Compile.Batch.SpecGlue
import Rom.SpecVia

noncomputable section

/-! ## Part 1: generic -/

namespace Compile.GlueB
open Rom Prob ZKCP
open scoped ENNReal

variable {S : OSpec} {I X Wn PP IVK ISK Pf : Type}

/-- the scheme with C and P translated, and V as it is -/
def viaCP (φ : QMap S) (A : Gen.Arg S I X Wn IVK ISK Pf) : Gen.Arg S I X Wn IVK ISK Pf where
  C := fun i => (A.C i).via φ
  P := fun k b => (A.P k b).via φ
  V := A.V

def Spec.gadmVia : Prop :=
  ∀ (S : OSpec) (X Wn IVK Pf α : Type) (ψ : QMap S) (ok : Gen.Batch X Wn → Prop)
      (D : Adv S (GCall X Wn) (GIn IVK Pf) α) (b : Bool) (n : ℕ),
    GAdm ok D b n → GAdm ok (D.via ψ) b n

/-- Privacy at the level of challengers (`Close`) carries over along a bijection of the queries. -/
def Spec.closeVia : Prop :=
  ∀ (S : OSpec) (I X Wn PP IVK ISK Pf : Type) (R : Gen.RelPair I X Wn PP)
      (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ) (Sm : World S (SCall X) (GIn IVK Pf)) (s₀ : Sm.σ)
      (ζ : ℕ → ℕ → ℝ≥0∞) (φ ψ : QMap S),
    QMap.Perm φ ψ → Close R A B (asW Wn Sm) s₀ ζ → Close R (viaCP φ A) B (asW Wn (Sm.pre ψ)) s₀ ζ

end Compile.GlueB

/-! ## Part 2: the compiled scheme -/

namespace Compile.Batch
open Iop Rom Compile.GlueB

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the number that the nonce in a plain part denotes; 0 if the component has no proof-of-work bits
-/
def clsPB {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → PlainPart s A → ℕ
  | [], _, _, z => nomatch z
  | _ :: _, (_, _), (w, _), .inl (.inl α) => match w.gr0 with
      | none => 0
      | some g => g.get α
  | _ :: _, (_, _), (w, _), .inl (.inr α) => match w.grJ with
      | none => 0
      | some g => g.get α
  | _ :: s, (_, A), (_, W), .inr z => clsPB s A W z

/-- the wire records of the rounds of a protocol -/
def shW (W : QueryLayout lam L) : (t : Tag) → RoundsQueryLayout lam W.K (shapeOf L t) (annOf L t)
  | .test => W.T.sh
  | .link => W.Lk.sh
  | .onl => W.B.sh

/-- the number that the nonce of a Fiat-Shamir query denotes -/
def cls (W : QueryLayout lam L) (t : Tag) (q : FbIn lam L t) : ℕ := clsPB _ _ (shW W t) q.plain

/-- The exchange of queries: (fb t, q) with the nonce for k + 1 ↔ (fbw t k, q). All other queries
stay. -/
def ghost (W : QueryLayout lam L) : QMap (spec lam W.K L)
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

def Spec.ghostPerm : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L), QMap.Perm (ghost W) (ghost W)

/-- Routed: fb t is queried only where the input holds the nonce for 0, and fbw t k only where it
holds the nonce for k + 1. -/
def Routed (W : QueryLayout lam L) {α : Type} : TypedOracleComputation lam W.K L α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, Routed W (k r)
  | .query (.fb t) q k => cls W t q = 0 ∧ ∀ r, Routed W (k r)
  | .query (.fbw t j) q k => cls W t q = j + 1 ∧ ∀ r, Routed W (k r)
  | .query _ _ k => ∀ r, Routed W (k r)

/-- `Routed` for a token program: whatever strings its tokens denote -/
def RoutedT (W : QueryLayout lam L) {α : Type} : St lam W.K L α → Prop
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

def Spec.realQ_via : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (α : Type) (c : TypedOracleComputation lam W.K L α),
    Routed W c → realQ c = c.via (ghost W)

def Spec.routedErase : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (α : Type)
      (c : St lam W.K L α) (vs : List Bits),
    RoutedT W c → Routed W (erase c vs)

def Spec.routedCp : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I),
    W.OKG → RoutedT W (Cp W WP p i)

def Spec.routedPp : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (k : IskH lam L) (fr : ℕ → Bool) (xs : List X),
    W.OKG → RoutedT W (Pp W WP p k fr xs)

/-- The scheme whose C and P are what `erase` makes of the programs, queries to the ghost names
included. An object of the analysis of privacy only. -/
def argBT (W : QueryLayout lam L) (WP : WireBP L) (p : Params) :
    ZKCP.Gen.Arg (spec lam W.K L) I X Unit (IVK lam L) (ISK lam L) (Prf lam L) where
  C := fun i => (erase (Cp W WP p i) []).bind fun o => pure (o.1.1, (o.1.2, o.2))
  P := fun k b =>
    (erase (Pp W WP p k.1 (fun _ => true) (b.map Prod.fst)) k.2).bind fun o =>
      pure (fitLen ⟨0, default, none, none⟩ b.length o.1)
  V := V W p

/-- Under `W.OKG`: the scheme `argB` is `argBT` with C and P translated by the exchange of queries.
-/
def Spec.argB_via : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params),
    W.OKG → argB W WP p = viaCP (ghost W) (argBT W WP p)

end Compile.Batch
