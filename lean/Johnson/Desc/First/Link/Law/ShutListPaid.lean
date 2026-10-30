-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/ShutListPaid.lean: PAYMENTS BENEATH THE SHUTTING's LIST OF DEBTS
(`ShutList`,
ShutList.lean): TWO THEOREMS, EACH ENDING IN A FIELD's TYPE: hNH and hS. General in the numbers Nm
and the meaning Mg (the list asks them at 𝔇.N and mgAll 𝔇 mgBase).

  `carriesAt k`, `carries_shut`: BY THE KERNEL, AT ALL 25 SEGMENTS: at the shutting of segment m
just
    one "carry" rides: "carry m".
  `shutStandB`, `shutStand_full`: by the kernel: at the shuttings of the segments 0 .. 23 the chain
is to
    stand in a layers' or an attention segment.
  `notHead_of_stand`: a state that stands so does not stand at the head's link.
  `hNH_paid`: **THE FIELD hNH**: from the promise's own test on where the chain stands (`shapeAt`,
by
    `onT_bools`, FromPromise.lean) at m < 24; at m = 24 from ONE FACT ON THE PLAN, a premise: the
    switch that spends "carry 24" does not stand at the head.
  `size_of_onTR`: the promise's test on the book: the book holds just the plan's count of trees.
  `hS_paid`: **THE FIELD hS**: by `shutFacts_of_fold` (ShutFactsPaid.lean), with size paid here.
WHAT IS LEFT. Of hNH: h24 : (ProofFile.pAtK2 Zc 24).stands ≠ .head. Of hS: FoldFacts at the list's own
"reached" with d.ft = 0; Zc is made by the proof file's maker; the piece's first tree is the plan's
count at the place (`row_base_at`, Johnson/P5J/K09Cap.lean); rows: the letter of the field rowsSent
of
FoldFacts (Johnson/Desc/First/FoldFacts.lean), taken as a premise.
Limits. FoldFacts' fields are shown in Johnson/P5J/FoldJ3Whole.lean (P5J.foldFacts_at_head') at the
letters fun a => a.1 · At.foldD Zp cF L · At.reqW · At.links · At.ps, under h : P5J.AtMg at secondHashFunction,
hR, hl, hs and hB; NO MEMBER is shown there; that these are the list's
own letters (what «WHAT IS LEFT» asks) is not shown here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.ShutFactsPaid
import Johnson.Desc.First.Link.Law.FromPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers FoldFacts FoldData shapeAt bookAt
  standOf standAt)

/-- The numbers m' of the items "carry m'" that ride at place k. -/
def carriesAt (k : ℕ) : List ℕ :=
  (ridersAt k).filterMap fun i => match i with
    | .carry m => some m
    | _ => none

set_option maxRecDepth 1000000 in
/-- **At the shutting of segment m just "carry m" rides.** -/
theorem carries_shut :
    ((List.range 25).all fun m => carriesAt (batchIx m + 4) == [m]) = true := by decide +kernel

/-- At the shuttings of the segments 0 .. 23 the chain is to stand in a layers' or an attention
segment. -/
def shutStandB : Bool :=
  (List.range 24).all fun m => (plF[batchIx m + 4]?).any fun p =>
    decide (standAt linksFull p = .link .layers) || decide (standAt linksFull p = .link .attention)

set_option maxRecDepth 1000000 in
theorem shutStand_full : shutStandB = true := by decide +kernel

theorem notHead_of_stand {s : S}
    (h : standOf s = .link .layers ∨ standOf s = .link .attention) : ∀ x, s.here ≠ .head x := by
  intro x hx
  unfold standOf at h
  rw [hx] at h
  dsimp only at h
  split at h
  · rcases h with h | h <;> exact nomatch h
  · rcases h with h | h <;> exact nomatch h

theorem carry_is {m m' : ℕ} (hm : m < 25) (h : Item.carry m' ∈ ridersAt (batchIx m + 4)) :
    m' = m := by
  have h1 : m' ∈ carriesAt (batchIx m + 4) := List.mem_filterMap.2 ⟨_, h, rfl⟩
  have h2 := List.all_eq_true.1 carries_shut m (List.mem_range.2 hm)
  rw [beq_iff_eq.1 h2] at h1
  exact List.mem_singleton.1 h1

variable {P W : Type} {F : Sound.Frame}

/-- **THE FIELD hNH.** -/
theorem hNH_paid (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ) (hm : m < 25) (hlinks : links = linksFull)
    (hpl : pl = plF) (hk : k = batchIx m + 4) (Zc : ProofFile.Pub)
    (h24 : (ProofFile.pAtK2 Zc 24).stands ≠ .head) :
    ∀ m', openAfter (insQ links pl) (outsQ links pl) (· ∈ First.start links) k (.carry m') →
      ¬ insQ links pl k (.carry m') → (ProofFile.pAtK2 Zc m').stands = .head →
      ∀ a, onTR Nm Mg links pl (fun s : S => (z, s)) Rz k a → ∀ x, a.1.here ≠ .head x := by
  subst hlinks hpl hk
  intro m' h1 h2 hs a ha
  obtain rfl : m' = m := carry_is hm (rider_mem (quietAt_le (shut_mem hm)) h1 h2)
  by_cases e : m' = 24
  · subst e
    exact absurd hs h24
  · have hlt : m' < 24 := by omega
    have hb := List.all_eq_true.1 shutStand_full m' (List.mem_range.2 hlt)
    have hsh := (onT_bools Nm Mg linksFull plF z (batchIx m' + 4) a ha.1).1
    cases hp : plF[batchIx m' + 4]? with
    | none =>
      rw [hp] at hb
      cases hb
    | some p =>
      rw [hp] at hb hsh
      have h' : (standOf a.1 == standAt linksFull p &&
          (a.1.noneWaits || First.mayWait linksFull p) &&
          a.1.link?.all fun L => p.link == some L.link) = true := hsh
      have h3 : standOf a.1 = standAt linksFull p := by
        have := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h').1).1
        simpa using this
      refine notHead_of_stand ?_
      rw [h3]
      simpa using hb

/-- The promise's test on the book: the book holds just the plan's count of trees. -/
theorem size_of_onTR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ) (a : S × F.E.Str)
    (ha : onTR Nm Mg links pl (fun s : S => (z, s)) Rz k a) :
    a.1.book.trees.size = Nm.treesAt pl[k]? := by
  have h := (onT_bools Nm Mg links pl z k a ha.1).2.2.2.2.2
  unfold bookAt at h
  have := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).1
  simpa using this

/-- **THE FIELD hS.** -/
theorem hS_paid (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ) {d : FoldData} {reqW : P → Array UInt32}
    {linksF : List ModelPart} {psF : List Place}
    (FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) d reqW linksF psF) (hft : d.ft = 0)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Zc : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Zc) (base : ℕ) (hbase : base = Nm.treesAt pl[k]?)
    (hrows : ∀ k a, Rz k a → a.1.failed = none →
      ∀ o ∈ singleRowsOracles a.1.live.frame.rows, o < a.1.book.place.size) :
    ∀ a, onTR Nm Mg links pl (fun s : S => (z, s)) Rz k a → ShutFacts Zc base a.1 := by
  intro a ha
  have hu : a.1.failed = none := not_not.1 ha.1.2
  exact shutFacts_of_fold FF hft hZ ha.2 hu base (hrows k a ha.2 hu)
    (by rw [hbase]; exact Nat.le_of_eq (size_of_onTR Nm Mg links pl z Rz k a ha))

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.carries_shut
#print axioms VerifiableInference.Desc.LinkJoin.shutStand_full
#print axioms VerifiableInference.Desc.LinkJoin.notHead_of_stand
#print axioms VerifiableInference.Desc.LinkJoin.carry_is
#print axioms VerifiableInference.Desc.LinkJoin.size_of_onTR
#print axioms VerifiableInference.Desc.LinkJoin.hNH_paid
#print axioms VerifiableInference.Desc.LinkJoin.hS_paid
