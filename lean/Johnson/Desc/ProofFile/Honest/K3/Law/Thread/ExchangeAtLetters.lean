-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeAtLetters.lean: the honest side of the kind
"lookup" (K3): THE PREMISES "OF THE FILLING" of `allOpenings_digitsLookup`, `all_attention`, `all_layers`
(Honest/K3/Law/Thread/ExchangeAll.lean) and `all_head` (ExchangeHeadAll.lean), AT THE FIRST CHAIN'S
LETTERS LAID AT THE LIBRARY'S OWN (`lettersAt`, Honest/Thread/FirstAt.lean): where these theorems
will be spent. Theorems with proofs; no definition.

These letters' meaning of the items is the library's one filling at data THAT HANG ON THE INPUT, in
two fields. The premises bind their letters in front of "at every input". So each is held here at
letters of the library's own data, which do not hang on the input; Lean says that the two fields are
not read.

  `formsT_lettersAt`        the field formsT has the text that is asked, at every input
  `k3At_lettersAt`          `K3At` at every input
  `headSuffices_lettersAt`  `HeadSuffices` at every input; the head's place is the head's own clause
  `ah_objects`, `ah_guests`   the text's test on what is ahead rejects both runs
  `runs_calls`, `runs_digits`  the name "objects" stands for the runs "objects" and "guests" of one
                            piece, at a segment of a sort: CONDITIONAL ON the data's list of sorts
                            holding that sort at the segment's number; no instance of that
                            hypothesis is exhibited in this file

The like for the field forms: `formsText_lettersAt` (Honest/K3/Law/Thread/FormsAtLetters.lean).

NOT HELD HERE, AND WHY. The readers' two answers and the public test for the promise speak of the
STATE that the sub-protocol leaves, not of the filling alone: they want what the library shows of a
link's runs in the goals' scope, from an opening, and the promise behind.

Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it. Beside it the library has `head_exists_at_name`
(Johnson/P5J/HeadExistsAtName.lean), under four hypotheses on public files.

Limits. AT THE FULL SIZE ALONE (the letters stand there alone). The head h is a premise.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeAtMgAll
import Johnson.Desc.Sound.MgAt.K3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.First (ModelPart shift)
open VerifiableInference.Desc.Sound (MsgT seatTab formsTQ)
open VerifiableInference.OnPublicFiles (K3At k3At_mgAll k3SizesAt k3PolicyAt k3AdrAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt WtF Script)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-! ## 1 Facts of the data alone -/

/-- The text's test on what is ahead rejects the run "objects". -/
theorem ah_objects (piece : Nat) : h.𝔇.ah piece "objects" = false := by
  show ("objects" == "K8.equations") = false
  decide

/-- The text's test on what is ahead rejects the run "guests". -/
theorem ah_guests (piece : Nat) : h.𝔇.ah piece "guests" = false := by
  show ("guests" == "K8.equations") = false
  decide

/-- **At the calls' piece the name "objects" stands for two runs.** CONDITIONAL ON the segment's
sort; no instance of that hypothesis is exhibited in this file. -/
theorem runs_calls (m : Nat) (sub : ModelPart) (hs : h.𝔇.links[m]? = some sub) :
    h.𝔇.runs m (2 + shift sub) "objects" =
      [(1 + shift sub, "objects"), (1 + shift sub, "guests")] := by
  show ((h.𝔇.links[m]?).map fun sub => VerifiableInference.Desc.First.runsOf sub _ _).getD [] = _
  rw [hs]
  cases sub <;> rfl

/-- **At the digits' piece the name "objects" stands for two runs.** CONDITIONAL ON the segment's
sort; no instance of that hypothesis is exhibited in this file. -/
theorem runs_digits (m : Nat) (sub : ModelPart) (hs : h.𝔇.links[m]? = some sub) :
    h.𝔇.runs m (7 + shift sub) "objects" =
      [(6 + shift sub, "objects"), (6 + shift sub, "guests")] := by
  show ((h.𝔇.links[m]?).map fun sub => VerifiableInference.Desc.First.runsOf sub _ _).getD [] = _
  rw [hs]
  cases sub <;> rfl

/-! ## 2 At every input -/

variable {Bk : ProverCoinCounts} {W₀ Rc Tr Xo : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The field formsT has the text that is asked, at every input, at the letters of the library's
own data.** -/
theorem formsT_lettersAt :
    ((lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Mg w).formsT =
      fun m k r a y v =>
        (∀ p ∈ h.𝔇.runs m k r,
          formsTQ (h.𝔇.Rd m) h.𝔇.St ((fun m => h.𝔇.N.sent m 0) m) p.1 p.2 a.2
            (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) ∧ (r = "weights" → h.𝔇.wt m a y v) :=
  formsT_mgAll _ _

/-- **`K3At` at every input**, at what the library's own data send and at their letters. -/
theorem k3At_lettersAt :
    K3At (P5J.At.X Zp) h.𝔇.sent h.𝔇.l3
      ((lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Mg w) :=
  k3At_mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells w), cr1 := carryX }
    VerifiableInference.Desc.Sound.mgBase

/-- **`HeadSuffices` at every input**, at the library's own sizes, policy, addresses and
requests. -/
theorem headSuffices_lettersAt :
    @HeadSuffices (k3SizesAt (P5J.At.X Zp)) (k3PolicyAt (P5J.At.X Zp)) _ _ _ (P5J.At.X Zp) h.𝔇.sent
      h.𝔇.l3 (k3AdrAt (P5J.At.X Zp)) h.𝔇.rq x
      ((lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Mg w) :=
  headSuffices_mgAll _ _ h.headAt

#print axioms ProofFile.Honest.K3.Law.Exchange.ah_objects
#print axioms ProofFile.Honest.K3.Law.Exchange.ah_guests
#print axioms ProofFile.Honest.K3.Law.Exchange.runs_calls
#print axioms ProofFile.Honest.K3.Law.Exchange.runs_digits
#print axioms ProofFile.Honest.K3.Law.Exchange.formsT_lettersAt
#print axioms ProofFile.Honest.K3.Law.Exchange.k3At_lettersAt
#print axioms ProofFile.Honest.K3.Law.Exchange.headSuffices_lettersAt

end ProofFile.Honest.K3.Law.Exchange
