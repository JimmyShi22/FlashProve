-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecDiscipline.lean: the rules of deferred programming for the token programs of the
compiled scheme: definitions and statements. (Words of this library: lean/GLOSSARY.md.)

Words used below: token, marked query (there: "marked evaluation"), charged, reveal, shown, mode I:
the head of Rom/Defer.lean; slot value, chaining value, the formats (F1) to (F5): the head of
Compile/Batch/Oracles.lean; token tree: `TTree`, Compile/Batch/TokTree.lean.

The committer `Cp` and the prover `Pp` (Compile/Batch/Star.lean) are token programs (`Step`,
Rom/Defer.lean). The lemma on deferred programming (`Rom.Spec.defer`) requires of every run in mode
I: no violation of the rules, bounds on the numbers of ordinary (`Step.plain`) and of marked queries
to each oracle, marked queries only at the oracles of a given set, and a lower bound on the length
of every charged token (`Rom.DSt.Within`).

A marked query may hold further tokens (`others`): an inner node of a token tree is charged to its
left child and holds its right child; a Fiat-Shamir query holds the root of the tree over its
component, if the component has one, and in format (F3) (`Head.f3`, Compile/Batch/Oracles.lean) also
the last shared chaining value. And one token may be charged at two oracles (a slot value: at the
leaf oracle of request trees and, in format (F3), at the Fiat-Shamir oracle). So:
* `FreeAt d o t`: the token t can be charged at the oracle o: it exists, is not shown, and no
  earlier query to o holds it (charged or among the others). This is what the check of
  `Rom.Step.run` asks of t, but for t ∉ us, the others of the same query (a clause of its own in
  `SafeO`).
* `ClosedO d ts`: the tokens ts can be revealed together: they exist, and the tail (`Ev.tail`,
  Rom/Defer.lean) and all others of every query that is charged to one of them are among them or are
  shown already.
* `SafeO Rl c d Q`: a weakest precondition, by recursion on the program c. From the state d,
  whatever the coins, the oracle answers and the tables are, every plain query is allowed by
  `Rl.Pl`; every marked query is charged to a token t that is `FreeAt` its oracle o and not among
  its others, has at least `Rl.bits o` bits, and the query is allowed by `Rl.Mk`; every reveal is
  `ClosedO`; and at the end Q holds of the result and the state. `TidyO Rl d`: the state is orderly;
  it implies d.viol = false. `GrowsO`: what a run may have added. The intermediate states are
  `afterPlain`, `afterFresh`, `afterMark`, `afterReveal` (Compile/SpecDiscipline.lean).

The statements on the scheme, each under the hypotheses in its docstring: `Spec.safeCB`,
`Spec.safePB`, `Spec.sumB` (the sum of that lemma over the ten oracles `osB` is at most explicit
terms in `xTree`, `xFb`, `xReq` of Compile/Batch/Counts.lean), `Spec.zeroBG` (outside these oracles
and the ghost names the count `mAllB` is 0).
-/
import Compile.SpecDiscipline
import Compile.Batch.Counts

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules markBad markDue afterPlain afterFresh afterMark afterReveal nEv)
open scoped ENNReal

/-! ## 1. Generic in the family of oracles -/

section Generic
variable {S : OSpec} {sp : Split S} {α : Type}

/-- A marked query to the oracle o can be charged to the token t. -/
structure FreeAt (d : DSt S) (o : S.ι) (t : Tok) : Prop where
  lt : t < d.vals.length
  not_shown : t ∉ d.shown
  fresh : ∀ e ∈ d.evs, e.o = o → e.charged ≠ t ∧ t ∉ e.others

/-- The tokens ts can be revealed together. -/
structure ClosedO (d : DSt S) (ts : List Tok) : Prop where
  lt : ∀ t ∈ ts, t < d.vals.length
  tail : ∀ e ∈ d.evs, e.charged ∈ ts → e.tail ∈ ts ∨ e.tail ∈ d.shown
  others : ∀ e ∈ d.evs, e.charged ∈ ts → ∀ u ∈ e.others, u ∈ ts ∨ u ∈ d.shown

/-- The program c obeys the rules from the state d, and ends in Q, whatever the coins, the answers
and the tables are. (Rl.Term is not used.) -/
def SafeO (Rl : Rules S) : Step S sp α → DSt S → (α → DSt S → Prop) → Prop
  | .pure a, d, Q => Q a d
  | .sample _ k, d, Q => ∀ r, SafeO Rl (k r) d Q
  | .plain o q k, d, Q => Rl.Pl o q ∧ ∀ r T, SafeO Rl (k r) (afterPlain d o T) Q
  | .fresh ℓ k, d, Q => ∀ u : Fin ℓ → Bool, SafeO Rl (k d.vals.length) (afterFresh d (List.ofFn u)) Q
  | .marked o t us pt _ k, d, Q =>
      (∀ u ∈ us, u < d.vals.length) ∧ t ∉ us ∧ FreeAt d o t ∧
      Rl.bits o ≤ (d.val t).length ∧ Rl.Mk o (pt (d.val t) (us.map d.val)) ∧
      ∀ r T, SafeO Rl (k (sp.split o r).1 d.vals.length)
        (afterMark sp d o t us (pt (d.val t) (us.map d.val)) r T) Q
  | .reveal ts k, d, Q => ClosedO d ts ∧ ∀ T, SafeO Rl (k (ts.map d.val)) (afterReveal d ts T) Q

/-- The state is well-formed. -/
structure TidyO (Rl : Rules S) (d : DSt S) : Prop where
  viol : d.viol = false
  shown_lt : ∀ t ∈ d.shown, t < d.vals.length
  charged_lt : ∀ e ∈ d.evs, e.charged < d.vals.length
  tail_lt : ∀ e ∈ d.evs, e.tail < d.vals.length
  others_lt : ∀ e ∈ d.evs, ∀ u ∈ e.others, u < d.vals.length
  /-- a marked query whose charged token is shown has been released -/
  released : ∀ e ∈ d.evs, e.charged ∈ d.shown → e.released = true
  /-- a released query has its `tail` and its others shown -/
  closed_tail : ∀ e ∈ d.evs, e.released = true → e.tail ∈ d.shown
  closed_others : ∀ e ∈ d.evs, e.released = true → ∀ u ∈ e.others, u ∈ d.shown
  bits : ∀ e ∈ d.evs, Rl.bits e.o ≤ (d.val e.charged).length
  point : ∀ e ∈ d.evs, Rl.Mk e.o e.pt

/-- What a run may have added on the way from d to d'. Ch: the tokens of d that its marked queries
may hold (charged or among the others); R: the tokens of d that it may have shown; e o and
M o: how many ordinary and marked queries to o it may have added. -/
structure GrowsO (Ch R : Tok → Prop) (e M : S.ι → ℕ) (d d' : DSt S) : Prop where
  vals : d.vals <+: d'.vals
  shown_old : ∀ t ∈ d.shown, t ∈ d'.shown
  shown : ∀ t ∈ d'.shown, t ∈ d.shown ∨ R t ∨ d.vals.length ≤ t
  /-- a marked query of d' is one of d (perhaps released by now), or new: then its `tail` is a new
  token, and every token that it holds is new or in Ch -/
  evs : ∀ e' ∈ d'.evs,
    (∃ e₀ ∈ d.evs,
      e₀.o = e'.o ∧ e₀.charged = e'.charged ∧ e₀.others = e'.others ∧ e₀.tail = e'.tail) ∨
    (d.vals.length ≤ e'.tail ∧
      (Ch e'.charged ∨ d.vals.length ≤ e'.charged) ∧
      ∀ u ∈ e'.others, Ch u ∨ d.vals.length ≤ u)
  plain : ∀ o, d'.nPlain o ≤ d.nPlain o + e o
  marked : ∀ o, nEv d' o ≤ nEv d o + M o

namespace Spec

/-- Under `SafeO Rl c d Q` every result of `Rom.Step.run`, in both modes, satisfies Q. -/
def safeRunO : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α : Type) (Rl : Rules S) (c : Step S sp α) (d : DSt S)
      (Q : α → DSt S → Prop) (m : Bool),
    SafeO Rl c d Q → ∀ x ∈ (c.run m d).support, Q x.1 x.2


/-- Under `TidyO` and the counts e, M: `DSt.Within`, if outside os M allows no marked query. -/
def withinO' : Prop :=
  ∀ (S : OSpec) (Rl : Rules S) (d : DSt S) (e M : S.ι → ℕ) (os : Finset S.ι), TidyO Rl d →
    (∀ o, o ∉ os → M o = 0) → (∀ o, d.nPlain o ≤ e o) →
    (∀ o, nEv d o ≤ M o) → d.Within e M Rl.bits os

end Spec

end Generic

/-! ## 2. The compiled scheme -/

section Scheme
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the ten oracles with marked queries beside the ghost names fbw t k -/
def osB : Finset OracleName :=
  {OracleName.leaf, OracleName.node, OracleName.rleaf, OracleName.rnode, OracleName.fb Tag.test, OracleName.fb Tag.link, OracleName.fb Tag.onl,
   OracleName.g Tag.test, OracleName.g Tag.link, OracleName.g Tag.onl}

/-- `osB` with the ghost names fbw t k, k < m -/
def osBG (m : ℕ) : Finset OracleName :=
  osB ∪ ((Finset.range m).image (OracleName.fbw Tag.test) ∪ (Finset.range m).image (OracleName.fbw Tag.link) ∪
      (Finset.range m).image (OracleName.fbw Tag.onl))

/-- The rules of the scheme. `Pl` and `Mk` restrict the oracle alone, not the query; what the
programs ask there: Ordinary queries: the padding leaves and the inner nodes of the trees over
encoded indices. Marked queries: leaves, charged to a salt of sMT bits; inner nodes of token trees,
leaves and inner nodes of request trees, and g, charged to a digest, a slot value or a chaining
value, of lam bits; Fiat-Shamir queries, charged to a chain's salt of sFS bits or to a token of lam
bits; the same at the ghost names fbw t k (the later attempts of a round with proof-of-work bits).
The rules allow every ghost name fbw t k; that only finitely many occur is said by the counts
(mProveB is 0 from maxMore on). -/
def rulesB (K : ℕ) (L : BatchProtocol I X) (lam : ℕ) (p : Params) : Rules (spec lam K L) where
  Term := fun _ => False
  Pl := fun o _ => o = OracleName.leaf ∨ o = OracleName.node
  Mk := fun o _ => o ∈ osB ∨ ∃ t k, o = OracleName.fbw t k
  bits := fun o => match o with
    | .leaf => p.sMT
    | .fb _ => min p.sFS lam
    | .fbw _ _ => min p.sFS lam
    | .node => lam
    | .rleaf => lam
    | .rnode => lam
    | .g _ => lam
    | _ => 0

/-- The tokens of a tree over an encoded index can be revealed: each pair (salt, digest) is
closed. -/
def TreeOKB {K : ℕ} (d : DSt (spec lam K L)) (t : TreeH lam) : Prop :=
  ∀ s s', some (s, s') ∈ t.salts → ClosedO d [s, s']

/-- The tokens of isk can be revealed. -/
def IskOKB {K : ℕ} (d : DSt (spec lam K L)) (k : IskH lam L) : Prop :=
  TreeOKB d k.root.tree ∧ ∀ lf ∈ k.leaves, TreeOKB d lf.node.tree

/-- u is one of the tokens of isk -/
def IskTokB (k : IskH lam L) (u : Tok) : Prop :=
  Compile.Disc.TreeTok k.root.tree u ∨ ∃ lf ∈ k.leaves, Compile.Disc.TreeTok lf.node.tree u

/-- 1 if the chains of an execution can join (there is a shared round), else 0 -/
def joins : (s : Shape) → RoundSplits s → ℕ
  | [], _ => 0
  | _ :: s, (a, A) => match a.kind with
    | .sh => 1
    | .lo => joins s A

/-- ordinary and marked queries of one tree over an encoded index (bounds) -/
def eTreeE (depth : ℕ) (f : ℕ → Bool) : OracleName → ℕ
  | .leaf => Compile.Disc.cntLeaves depth (fun j => !f j)
  | .node => 2 ^ depth
  | _ => 0
def mTreeE (depth : ℕ) (f : ℕ → Bool) : OracleName → ℕ
  | .leaf => Compile.Disc.cntLeaves depth f
  | _ => 0

/-- marked queries of one execution of the protocol with the tag t, with Ns slots (bounds); it makes
no ordinary query -/
def mProveB {K : ℕ} (t : Tag) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (Ns : ℕ) : OracleName → ℕ
  | .leaf => cTrees s A W Ns
  | .node => cTrees s A W Ns
  | .rleaf => joins s A * Ns
  | .rnode => joins s A * Ns
  | .fb t' => if t' = t then (Ns + 1) * s.length else 0
  | .fbw t' k => if t' = t then cTry k Ns s A W else 0
  | .g t' => if t' = t then joins s A * Ns else 0
  | _ => 0

variable (W : QueryLayout lam L) (p : Params)

def eNodeB : OracleName → ℕ := eTreeE W.depth fun j => decide (j < L.wordLength)
def mNodeB : OracleName → ℕ := mTreeE W.depth fun j => decide (j < L.wordLength)

/-- The counts of the committer: the first encoding with Test, and M + 1 copies with Link. -/
def eCB : OracleName → ℕ := fun o => eNodeB W o + (p.M + 1) * eNodeB W o
def mCB : OracleName → ℕ := fun o => mNodeB W o + mProveB Tag.test L.offline.shape _ W.T.sh 1 o
  + (p.M + 1) * (mNodeB W o + mProveB Tag.link L.link.shape _ W.Lk.sh 1 o)
/-- The counts of one batch. -/
def ePB : OracleName → ℕ := fun _ => 0
def mPB : OracleName → ℕ := mProveB Tag.onl L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh L.maxBatchSize

/-- the counts of the setup and n batches -/
def eAllB (n : ℕ) : OracleName → ℕ := fun o => eCB W p o + n * ePB o
def mAllB (n : ℕ) : OracleName → ℕ := fun o => mCB W p o + n * mPB W o

namespace Spec

/-- The committer obeys the rules, from every state with `TidyO`; its marked queries hold, and it
shows, only tokens that it has made; the tokens of the isk that it outputs can be revealed. -/
def safeCB : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (i : I) (d : DSt (spec lam W.K L)),
    TidyO (rulesB W.K L lam p) d → SafeO (rulesB W.K L lam p) (Cp W WP p i) d fun out d' =>
      TidyO (rulesB W.K L lam p) d' ∧
      IskOKB d' out.2 ∧
      GrowsO (fun _ => False) (fun _ => False) (eCB W p) (mCB W p) d d'

/-- The prover obeys the rules, from every state with `TidyO` in which the tokens of isk can be
revealed, if the number of slots is 2^depthReq; its marked queries hold only tokens that it has
made, and it shows only such tokens and tokens of isk; the tokens of isk can still be revealed
afterwards. For all flags and all lists of requests. -/
def safePB : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (d : DSt (spec lam W.K L)),
    L.maxBatchSize = 2 ^ W.depthReq → TidyO (rulesB W.K L lam p) d → IskOKB d k →
    SafeO (rulesB W.K L lam p) (Pp W WP p k fr xs) d fun _ d' =>
      TidyO (rulesB W.K L lam p) d' ∧
      IskOKB d' k ∧
      GrowsO (fun _ => False) (IskTokB k) ePB (mPB W) d d'

/-- The sum of the lemma on deferred programming, over the oracles `osB`, is at most the four terms
below, for an adversary with at most T queries to each oracle. -/
def sumB : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (p : Params)
      (n : ℕ) (t : OracleName → ℕ) (T : ℕ),
    (∀ o, t o ≤ T) →
    ∑ o ∈ osB, (mAllB W p n o : ℝ≥0∞) * (t o + eAllB W p n o + mAllB W p n o : ℕ) /
        2 ^ (rulesB W.K L lam p).bits o ≤
      (xTree W p n : ℝ≥0∞) * (T + xTree W p n : ℕ) / 2 ^ p.sMT +
        (xTree W p n : ℝ≥0∞) * (T + xTree W p n : ℕ) / 2 ^ lam +
        (xFb (L := L) p n : ℝ≥0∞) * (T + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) +
        3 * ((xReq L n : ℝ≥0∞) * (T + xReq L n : ℕ) / 2 ^ lam)

/-- outside osBG (maxMoreB W) the count `mAllB` allows no marked query -/
def zeroBG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (p : Params) (n : ℕ) (o : OracleName),
    o ∉ osBG (maxMoreB W) → mAllB W p n o = 0

end Spec

end Scheme

end Compile.Batch.Disc
