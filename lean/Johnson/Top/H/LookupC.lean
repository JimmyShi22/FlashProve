-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LookupC.lean: the lookup inside a sub-proof of the model (and inside a sub-proof's
test of smallness on digits) as a kind of block.

What the file states.
 - sizesLookupC: a written list of twelve records of public numbers (OnBytes.Model.Forest.Shape).
   CLookupC, a closed proposition: the test FoNums.ok holds at each; cLookupC proves it.
 - LookupCCaller: who calls such a lookup: the record of public numbers h and what the sub-proof
   around the lookup fixes: its state, the entries of its committed messages, where the keys, the
   bits of the counts and the mask row lie among them, its signature, its own joint. Data alone:
   no field is a proof.
 - kLookupC L: the kind of block at a list L of callers. The reduction is Cb.Fo.forB over the
   challenge field, with the short sumcheck filled by the named V₀ and V₀C; the committed messages
   are those of the caller's signature. What is claimed before the block (Cb.Fo.forIn): the
   caller's own joint, and for every call each of its 2^n keys, its padding places included, is
   one of the 2^k rows of that call's own table. What is claimed behind it (Cb.Fo.forOut): the
   caller's own joint at the caller's old state, one masked claim on the joint shifted keys, and
   that all rows put out hold of the entries. The claim behind does not hold the claim before.
 - HLookupC, a closed proposition: for every list of callers whose records are of the written
   list, round-by-round knowledge soundness of each block, for every tuple of committed messages,
   at the block's own errors. hLookupC_of : CLookupC → HLookupC, and hLookupC : HLookupC.
 - HLookupCEvery, hLookupCEvery: the same for every list of callers whose records pass the test
   FoNums.ok. So another list of sizes needs that test at its members and nothing else.
 - lookupC_knowAt, lookupC_point, lookupC_local, lookupC_onOut: all four facts of a block, and the
   three on the verifier alone; lookupC_good: the four together, over the caller's signature.
 - lookupC_small: each round's number of bad challenges is below the number of its challenges.
 - lookupC_plan: the block's rounds are those that the verifier's planner plans for the forest's
   sizes, in the three of an entry's twelve fields that a typed round bears, and its errors over
   its own challenge sets are the plan's ratios, round by round.
 - lookupC_eq0: at each of the block's own sumchecks every variable's weights sum to 1, the
   condition under which the short sumcheck's verifier rejects nothing.
 - CopyLookupC, PassLookupC, closed propositions, stated here and not proved here: the block hands
   on the oracle string that it was given, and the caller's state. No statement of this library
   concludes either.

Which statement reaches the verifier's own records. HLookupCEvery has no list: it speaks of every
caller whose record passes the test FoNums.ok. HLookupC and CLookupC speak of the written list
alone, and membership is equality of whole records: a record that differs from a member in any
field (the numbers of padding keys, a table, a call's name, fields that the block never reads) is
no member. So HLookupC may speak of no record that the verifier makes from a real file, and of
the two only HLookupCEvery is of use there.

Where the list comes from, and what is made up in it. Each member is made by the verifier's own
Forest.shape from each call's three numbers (the logarithm of the number of keys, that of the number
of rows, the padding row) and the cap on a tree's depth. These numbers and the sums of the padding
are written by hand, after the lookups of the two public configurations; no statement here ties them
to those configurations. Made up: the tables are range tables where a configuration has written
ones, and the sum of the padding is spread evenly over the trees. By an evaluation, in a test file
that is [not in this library], against the records that Verify.publicOf returns at the library's two
written configurations: the sizes (dT, kT, NT, rK, NC, cK, iota, first, callOf, and each call's n,
k, t0, kappa) and the sums of the padding agree at all twelve; the padding itself, tree by tree,
agrees at the six tests of smallness on digits and differs at the six calls' lookups (a layer
group's, attention's, the head's). So at least these six members are no records that the verifier
makes of these configurations. An evaluation is no theorem.

What the file does not say: that the block's verifier as a whole refuses nothing (knowledge
soundness alone does not shut out a verifier that refuses; lookupC_eq0 is the condition at the
sumchecks, not that conclusion); that a file's whole plan holds the forest's plan at the lookup's
place (lookupC_plan speaks of the plan of the forest alone); that the list holds the sizes at which
the verifier runs a lookup; that FoNums.ok follows from the success of Forest.shape and
Forest.pubAsk (Johnson/Top/H/LookupCShape.lean has it: okLookupC_of_made); that a caller exists
whose data are a sub-proof's own, or how its joints meet a neighbour's.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.KindKnowAt
import Cb.Pv.Lookup.Know.AsmKV0
import OnBytes.Tie.Pv.Lookup.Forest.FoSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwRound TwPlan TwErr TwLaw OnBytes.G4
open Cb.Fo
open OnBytes.Params (Setting Scope Planned finish planForest)
open OnBytes.Model (Forest.Shape Forest.shape Forest.pubAsk Call)

/-! ### the written list of sizes -/

/-- A record of public numbers, by the verifier's own Forest.shape, from each call's (n, k, t0),
the cap on a tree's depth, and the sum of the padding, which is spread evenly over the trees. -/
def shapeLookupC (calls : List (Nat × Nat × Nat)) (lid sumPub : Nat) : Option Forest.Shape :=
  (Forest.shape
    (calls.map fun c => ({ n := c.1, k := c.2.1, t0 := c.2.2, kappa := 5 } : Call)).toArray
    lid).toOption.bind fun h0 =>
    let pub := (Array.range h0.NT).map fun y =>
      sumPub / h0.NT + if y = 0 then sumPub % h0.NT else 0
    if (Forest.pubAsk h0 pub).toBool then some { h0 with pub := pub } else none

/-- Twelve rows: the calls' (n, k, t0), the cap, the sum of the padding. Written by hand for the
full configuration (the first six) and the small one (the last six); in each six: a layer group's
lookup, attention's, the head's, then the three tests of smallness on digits in the same order. The
padding keys are spread evenly over the trees (shapeLookupC); the records that the verifier makes of
the two written configurations spread them otherwise at the calls' lookups (the sums agree). -/
def rowsLookupC : List (List (Nat × Nat × Nat) × Nat × Nat) :=
  [([(27, 16, 0), (27, 16, 0), (27, 16, 0), (28, 8, 0), (27, 16, 32768), (27, 16, 32768),
      (26, 16, 32768), (26, 16, 0)], 28, 225941504),
   ([(27, 16, 0), (27, 16, 2307), (26, 16, 0), (25, 16, 0)], 28, 117276672),
   ([(28, 16, 0), (28, 16, 0), (28, 8, 0), (27, 16, 0), (27, 16, 0), (27, 16, 32768)], 28,
      364519424),
   ([(26, 10, 0), (26, 8, 0)], 28, 6291456),
   ([(25, 10, 0), (25, 8, 0)], 28, 10485760),
   ([(26, 10, 0), (26, 8, 0)], 28, 35651584),
   ([(20, 16, 0), (20, 16, 0), (20, 16, 0), (21, 8, 0), (20, 16, 32768), (20, 16, 32768),
      (20, 16, 32768), (20, 16, 0)], 24, 5122944),
   ([(20, 16, 0), (20, 16, 2307), (20, 16, 0), (20, 16, 0)], 24, 3701760),
   ([(20, 16, 0), (20, 16, 0), (20, 8, 0), (20, 16, 0), (20, 16, 0), (20, 16, 32768)], 24,
      6054400),
   ([(23, 10, 0), (23, 8, 0)], 24, 0),
   ([(22, 10, 0), (22, 8, 0)], 24, 524288),
   ([(23, 10, 0), (23, 8, 0)], 24, 6291456)]

/-- The sizes of the kind: the records that Forest.shape and Forest.pubAsk make of the rows. -/
def sizesLookupC : List Forest.Shape :=
  rowsLookupC.filterMap fun r => shapeLookupC r.1 r.2.1 r.2.2

/-- Forest.shape and Forest.pubAsk refuse none of the twelve. -/
theorem sizesLookupC_length : sizesLookupC.length = 12 := by decide +kernel

/-- The condition on public data: the test FoNums.ok holds at each size of the written list. -/
def CLookupC : Prop := ∀ h ∈ sizesLookupC, FoNums.ok h = true

/-- It holds, by evaluation. -/
theorem cLookupC : CLookupC :=
  List.all_eq_true.1 (by decide +kernel : sizesLookupC.all FoNums.ok = true)

/-! ### the caller -/

/-- Who calls a lookup of a sub-proof: data alone. -/
structure LookupCCaller : Type 1 where
  /-- the record of public numbers -/
  h    : Forest.Shape
  /-- the caller's state -/
  St₀  : Type
  /-- the entries of the committed messages that the lookup reads -/
  J₀   : Type
  finJ : Fintype J₀
  decJ : DecidableEq J₀
  /-- where the keys, the bits of the counts and the mask row lie -/
  L    : Lay Cb.Gl.E St₀ J₀
  /-- the oracles beside the block -/
  Ex   : ExtSpec
  Kc   : Type
  /-- the further witness -/
  Wp   : Type
  /-- the signature: the committed messages are its messages -/
  Sg   : Sig Cb.Gl.E
  /-- the caller's own joint, which rides along -/
  R0   : Rels Kc St₀ Ex (Sg.Msg × Wp)
  /-- the entries, read off the committed messages -/
  msg₀ : Sg.Msg → J₀ → Cb.Gl.E

attribute [instance] LookupCCaller.finJ LookupCCaller.decJ

/-! ### the kind -/

/-- The lookup of a sub-proof as a kind of block, at a written list of callers. -/
@[reducible] noncomputable def kLookupC (L : List LookupCCaller) : BaseKind.{1} Cb.Gl.E where
  Size := LookupCCaller
  sizes := L
  Sg := fun c => c.Sg
  Kc := fun c => c.Kc
  St := fun c => c.St₀
  St' := fun c => TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)
  Wp := fun c => c.Wp
  Wp' := fun c => c.Wp
  E₀ := fun c => c.Ex
  E₀' := fun c => c.Ex
  R := fun c => (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R
  A := fun c => forIn Cb.Gl.E c.h c.L c.R0 c.msg₀
  B := fun c => forOut Cb.Gl.E c.h c.L c.R0 c.msg₀
  ext := fun _ _ _ _ wp => wp
  ε := fun c => (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e

/-- Every caller's record of public numbers is of the written list. -/
def AtSizesLookupC (L : List LookupCCaller) : Prop := ∀ c ∈ L, c.h ∈ sizesLookupC

/-- Every caller's record of public numbers passes the test. -/
def OkLookupC (L : List LookupCCaller) : Prop := ∀ c ∈ L, FoNums.ok c.h = true

theorem okLookupC_of (hC : CLookupC) {L : List LookupCCaller} (hL : AtSizesLookupC L) :
    OkLookupC L := fun c hc => hC c.h (hL c hc)

/-- All four facts of a block, at every caller whose record passes the test. -/
theorem lookupC_knowAt (L : List LookupCCaller) (hL : OkLookupC L) : (kLookupC L).KnowAtAll :=
  fun c hc => holeCgl c.St₀ c.J₀ c.h c.L c.Ex c.Kc c.Sg.Msg c.Wp c.R0 c.msg₀ (hL c hc)

/-- The statement of HLookupCEvery for the lists of callers whose records of public numbers are
members of the written list sizesLookupC. -/
def HLookupC : Prop := ∀ L : List LookupCCaller, AtSizesLookupC L → (kLookupC L).Know

/-- For every list of callers whose records of public numbers pass the test FoNums.ok, each lookup
block is round-by-round knowledge sound at its own errors, for every tuple of committed messages:
from «one masked claim on the joint shifted keys and all rows put out hold» back to «each call's
keys all lie in that call's own table», the caller's own joint riding along. -/
def HLookupCEvery : Prop := ∀ L : List LookupCCaller, OkLookupC L → (kLookupC L).Know

/-- It holds: Cb.Fo.holeCgl at each caller. -/
theorem hLookupCEvery : HLookupCEvery := fun L hL =>
  BaseKind.know_of_knowAt (lookupC_knowAt L hL)

/-- From the condition on public data. -/
theorem hLookupC_of : CLookupC → HLookupC := fun hC L hL => hLookupCEvery L (okLookupC_of hC hL)

theorem hLookupC : HLookupC := hLookupC_of cLookupC

/-! ### the three facts on the verifier alone; the four together -/

theorem lookupC_point (L : List LookupCCaller) (hL : OkLookupC L) : (kLookupC L).Point :=
  BaseKind.point_of_knowAt (lookupC_knowAt L hL)

theorem lookupC_local (L : List LookupCCaller) (hL : OkLookupC L) : (kLookupC L).Local :=
  BaseKind.local_of_knowAt (lookupC_knowAt L hL)

theorem lookupC_onOut (L : List LookupCCaller) (hL : OkLookupC L) : (kLookupC L).OnOut :=
  BaseKind.onOut_of_knowAt (lookupC_knowAt L hL)

/-- Over its caller's signature every block of the kind has the property of a block. -/
theorem lookupC_good (L : List LookupCCaller) (hL : OkLookupC L) :
    ∀ c ∈ L, ((kLookupC L).toKind.block c).Good :=
  BaseKind.good_of_knowAt (lookupC_knowAt L hL)

/-! ### the arithmetic -/

/-- Each round's number of bad challenges is below the number of that round's challenges. -/
theorem lookupC_small (L : List LookupCCaller) (hL : OkLookupC L) : ∀ c ∈ L,
    List.Forall₂ (· < ·) (errList ((kLookupC L).ε c))
      (((kLookupC L).R c).shape.map fun r => Nat.card r.Chal) :=
  fun c hc => forB_small_gl c.h c.L c.Ex (hL c hc)

/-- The rounds are the planner's, and the errors over the block's own challenge sets are the
plan's ratios, for every setting over the prime with extension degree 3 and every plan that the
verifier's planner makes of the forest's sizes. -/
theorem lookupC_plan (L : List LookupCCaller) (hL : OkLookupC L) (c : LookupCCaller)
    (hc : c ∈ L) (s : Setting) (sc : Scope) (hp : s.p = Cb.Gl.p ∧ s.degree = 3) (P : Planned)
    (hf : finish s sc (planForest (OnBytes.Model.forestSize c.h)) = .ok P) :
    ShapeIs Cb.Gl.E ((kLookupC L).R c).shape (P.rounds.map (·.entry)) ∧
    ∃ Q : List Quad,
      Q.map (·.1) = errList ((kLookupC L).ε c) ∧
      Q.map (·.2.1) = ((kLookupC L).R c).shape.map (fun r => Nat.card r.Chal) ∧
      Q.map (fun x => errOf s sc x.2.2) = P.rounds.map (·.error) ∧
      ∀ x ∈ Q, x.1 * bOf s.cardE x.2.2.2 = x.2.2.1 * x.2.1 :=
  (forB_four_gl c.h c.L c.Ex c.Kc c.Sg.Msg c.Wp c.R0 c.msg₀ (hL c hc) s sc hp P hf).2

/-! ### the sumchecks' weights -/

/-- At each of the block's own sumchecks every variable's weights sum to 1. -/
theorem lookupC_eq0 (c : LookupCCaller) :
    (∀ l, Eq0 ((forA Cb.Gl.E c.h c.L).H.tie.lv l).T.par) ∧
    (∀ l, Eq0 (((forA Cb.Gl.E c.h c.L).IK.setV ((forA Cb.Gl.E c.h c.L).v' + 1)).DK.lv l).T.par) ∧
    (∀ l, Eq0 ((forA Cb.Gl.E c.h c.L).D.lv l).T.par) ∧ Eq0 (forA Cb.Gl.E c.h c.L).En.par ∧
    Eq0 (forA Cb.Gl.E c.h c.L).Bt.zc.next.par :=
  asmK_eq0 Cb.Gl.E (forA Cb.Gl.E c.h c.L)

/-! ### what is handed on -/

/-- Whatever the transcript, the block hands on the oracle string that it was given. -/
def CopyLookupC : Prop :=
  ∀ (c : LookupCCaller) (y : c.Ex.Str) (τ : Tr ((kLookupC [c]).R c).shape),
    ((kLookupC [c]).R c).imp y τ = y

/-- Whenever the verifier puts out a statement, the caller's state in it is the one given. -/
def PassLookupC : Prop :=
  ∀ (c : LookupCCaller) (x : c.St₀) (y : c.Ex.Str) (τ : Tr ((kLookupC [c]).R c).shape)
    (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)),
    ((kLookupC [c]).R c).out x y τ = some b → b.1.1 = x

#print axioms VerifiableInference.OnPublicFiles.sizesLookupC_length
#print axioms VerifiableInference.OnPublicFiles.cLookupC
#print axioms VerifiableInference.OnPublicFiles.okLookupC_of
#print axioms VerifiableInference.OnPublicFiles.hLookupC_of
#print axioms VerifiableInference.OnPublicFiles.hLookupC
#print axioms VerifiableInference.OnPublicFiles.hLookupCEvery
#print axioms VerifiableInference.OnPublicFiles.lookupC_knowAt
#print axioms VerifiableInference.OnPublicFiles.lookupC_point
#print axioms VerifiableInference.OnPublicFiles.lookupC_local
#print axioms VerifiableInference.OnPublicFiles.lookupC_onOut
#print axioms VerifiableInference.OnPublicFiles.lookupC_good
#print axioms VerifiableInference.OnPublicFiles.lookupC_small
#print axioms VerifiableInference.OnPublicFiles.lookupC_plan
#print axioms VerifiableInference.OnPublicFiles.lookupC_eq0

end VerifiableInference.OnPublicFiles
