-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadG.lean: more clauses for the condition `keeps` of the
first chain's invariant at the full size, beside `fHeadF` (FHeadF.lean). An item `forms` that passes
over K1's commitment to the digits, or over the lookup on the digits (K3), needs relations between
the states before and after the step that the clauses of `fHead` (FHead.lean) do not say. They are
laid beside `fHeadF`. FHead.lean and FHeadF.lean are not changed, and what is proved at them carries
over (KeepsMono.lean, KeepsFree.lean, FormShare.lean).

  1  `readersStayAt`, `k1RelsAt`, `relsHead`, `fHeadG`   the four definitions
  2  `rels_no_more`, `rels_none_missed`   two tests on the written list of the 358 places: the
     pieces that `relsHead` names, at the kinds K1 and K3, stand at the 25 + 25 numbers that are
     meant and at no other; and each of these numbers has such a piece. The statements have no free
     variable. They are decided by the kernel's evaluation (`decide +kernel`), so they are counted
     apart
  3  `rels_no_more_control`, `rels_none_missed_control`   each test can fail
  4  `rels_k1_number`, `rels_k3_number`   the first test, read at one place
  5  `relsHead_other`, `kpBy_fHeadG`   at every other kind the clause is "True"; `fHeadG` implies
     `fHeadF`

Limits.
  * Definitions, tests on a written list, and unfoldings. Nothing shows that a clause holds at any
    step. The lemmas that prove these clauses from an accepting step (PayersAt.lean) stand at
    `SaidOk` (SaidOk.lean) alone, so the column `hK` at `fHeadG` can be proved at `SaidOk` alone.
  * K8 has no clause here. Whether an item `forms` that passes over K8 needs one is not settled in
    this file.
  * Full size only.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadF
import Johnson.Desc.Reads.FormsPass
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.K1.Law.GoAtLaterForms
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.First.Look.K3Base
import Johnson.IMR.K1Scope
import Johnson.IMR.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First (Item borderOf)
open VerifiableInference.Desc.K1 (noL)
open VerifiableInference.OnPublicFiles (k3K)
open P5J (TS)

/-! ## 1 The definitions -/

/-- The readers' answers at the runs of an item `forms` that is open on both sides of the
sub-protocol at the place `p` are after the step what they were before it. `Fwd` is the library's
(Johnson/Desc/Reads/FormsPass.lean). It is a definition: a part of a clause of `keeps`. -/
def readersStayAt (D : VerifiableInference.Desc.First.PubData) (p : Place) (s s' : TS) : Prop :=
  ∀ mm kk ρ, Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps (borderOf P5J.At.ps (some p)) →
    Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps (borderOf P5J.At.ps (some p) + 1) →
    ∀ q ∈ D.runs mm kk ρ, VerifiableInference.Reads.Pass.Fwd (D.Rd mm) q.1 q.2 s s'

/-- Three relations of the library between the states before and after K1's commitment to the
digits in segment `l` (`RecRides`, `AheadMeets`, `ReadersStay`: Johnson/Desc/K1/Law/). It is a
definition: a part of a clause of `keeps`. -/
def k1RelsAt (D : VerifiableInference.Desc.First.PubData) (l : Nat) (p : Place) (s s' : TS) :
    Prop :=
  ∃ new, VerifiableInference.Desc.K1.RecRides new s s' ∧
    VerifiableInference.Desc.K1.AheadMeets (D.N.sent l) (D.N.group l) new s s' ∧
    ∀ mm kk ρ, Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps (borderOf P5J.At.ps (some p)) →
      mm = l ∧ VerifiableInference.Desc.K1.ReadersStay D mm kk ρ s s'

/-- What the items `forms` need of `keeps` beyond `fHeadF`, kind by kind. At K1 it speaks at the
commitment to the digits (pieces 6 and 7 of a segment), at K3 at the lookup on the digits (pieces 7
and 8); everywhere else it is "True". There are two piece numbers at each kind because the output
head's segment has one sub-protocol more in front than the other 24 segments, so its pieces are one
higher. `rels_no_more` and `rels_none_missed` hold these numbers against the written list of
places. It is a definition: a part of a clause of `keeps`. -/
def relsHead (D : VerifiableInference.Desc.First.PubData) : KindName → Place → TS → TS → Prop
  | .K1 => fun p s s' => ∀ l, p.link = some l → p.piece = 6 ∨ p.piece = 7 → k1RelsAt D l p s s'
  | .K3 => fun p s s' => p.piece = 7 ∨ p.piece = 8 → readersStayAt D p s s'
  | _ => fun _ _ _ => True

/-- `fHeadF` with these relations beside it. It is a definition: it fills an argument of the
invariant. -/
def fHeadG (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (D : VerifiableInference.Desc.First.PubData) :
    KindName → Place → TS → TS → Prop :=
  fun κ p s s' => fHeadF Zp cF G take P11 p12 P13 D κ p s s' ∧ relsHead D κ p s s'

/-! ## 2 The piece numbers, held against the written list of places -/

set_option maxRecDepth 1000000 in
/-- The pieces that `relsHead` names stand at the numbers that are meant, and at no other. -/
theorem rels_no_more :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      (!(p.kind == KindName.K1 && p.link.isSome && (p.piece == 6 || p.piece == 7)) ||
        (decide (p.link.getD 25 < 25) && b == noL (p.link.getD 25) true)) &&
      (!(p.kind == KindName.K3 && (p.piece == 7 || p.piece == 8)) ||
        (decide (p.link.getD 25 < 25) && b == k3K (p.link.getD 25) true))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with piece 4 named too at K1, the same test fails. -/
theorem rels_no_more_control :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      (!(p.kind == KindName.K1 && p.link.isSome &&
          (p.piece == 4 || p.piece == 6 || p.piece == 7)) ||
        (decide (p.link.getD 25 < 25) && b == noL (p.link.getD 25) true)) &&
      (!(p.kind == KindName.K3 && (p.piece == 7 || p.piece == 8)) ||
        (decide (p.link.getD 25 < 25) && b == k3K (p.link.getD 25) true))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Each of the 25 + 25 numbers that are meant has such a piece. -/
theorem rels_none_missed :
    ((List.range 25).all fun l =>
      P5J.At.ps[noL l true]? == some (IM.k1PlaceL l true) &&
      ((IM.k1PlaceL l true).piece == 6 || (IM.k1PlaceL l true).piece == 7) &&
      P5J.At.ps[k3K l true]? == some (IM.k3Place l true) &&
      ((IM.k3Place l true).piece == 7 || (IM.k3Place l true).piece == 8)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at 26 segments the same test fails. -/
theorem rels_none_missed_control :
    ((List.range 26).all fun l =>
      P5J.At.ps[noL l true]? == some (IM.k1PlaceL l true) &&
      ((IM.k1PlaceL l true).piece == 6 || (IM.k1PlaceL l true).piece == 7) &&
      P5J.At.ps[k3K l true]? == some (IM.k3Place l true) &&
      ((IM.k3Place l true).piece == 7 || (IM.k3Place l true).piece == 8)) = false := by
  decide +kernel

/-- The first test at a place of the kind K1. -/
theorem rels_k1_number {b l : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K1) (hl : p.link = some l) (hc : p.piece = 6 ∨ p.piece = 7) :
    l < 25 ∧ b = noL l true := by
  have t := List.all_eq_true.1 rels_no_more b (List.mem_range.2 hb)
  rw [hp, Option.all_some] at t
  have t1 := (Bool.and_eq_true_iff.1 t).1
  rw [hk, hl] at t1
  rcases hc with hc | hc <;> rw [hc] at t1 <;> simpa using t1

/-- The first test at a place of the kind K3. -/
theorem rels_k3_number {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K3) (hc : p.piece = 7 ∨ p.piece = 8) :
    p.link.getD 25 < 25 ∧ b = k3K (p.link.getD 25) true := by
  have t := List.all_eq_true.1 rels_no_more b (List.mem_range.2 hb)
  rw [hp, Option.all_some] at t
  have t2 := (Bool.and_eq_true_iff.1 t).2
  rw [hk] at t2
  rcases hc with hc | hc <;> rw [hc] at t2 <;> simpa using t2

/-! ## 3 Unfoldings -/

/-- At every kind other than K1 and K3 the clause is "True". -/
theorem relsHead_other (D : VerifiableInference.Desc.First.PubData) {κ : KindName}
    (h1 : κ ≠ KindName.K1) (h3 : κ ≠ KindName.K3) (p : Place) (s s' : TS) :
    relsHead D κ p s s' := by
  cases κ <;> trivial

/-- `fHeadG` implies `fHeadF`. -/
theorem kpBy_fHeadG {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (Dp : VerifiableInference.Desc.First.PubData) :
    ∀ p s s', kpBy (fHeadG Zp cF G take P11 p12 P13 Dp) p s s' →
      kpBy (fHeadF Zp cF G take P11 p12 P13 Dp) p s s' :=
  fun _ _ _ hk => hk.1

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rels_no_more
#print axioms ProofFile.Honest.FirstThread.rels_no_more_control
#print axioms ProofFile.Honest.FirstThread.rels_none_missed
#print axioms ProofFile.Honest.FirstThread.rels_none_missed_control
#print axioms ProofFile.Honest.FirstThread.rels_k1_number
#print axioms ProofFile.Honest.FirstThread.rels_k3_number
#print axioms ProofFile.Honest.FirstThread.relsHead_other
#print axioms ProofFile.Honest.FirstThread.kpBy_fHeadG
