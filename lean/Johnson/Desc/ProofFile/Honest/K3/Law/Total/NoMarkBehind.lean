-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/NoMarkBehind.lean: the kind "lookup" (K3). Conditional
(the first two theorems on the goals' scope, the reading of the files and the description's return;
the four step theorems under the library's hypothesis `P5J.AtMgA`):
behind the acceptance alone of the step of one of the lookups' 50 members of the first chain the
state bears no mark; hence the step theorems of Honest/K3/Law/Total/StepWhole.lean without their
hypothesis "no mark at the state behind"; and the same with all six of the table's Boolean tests on
both sides. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a state s bears no mark if `s.failed = none`. The
lookups' 50 members stand at the numbers `k3K l d` of the flat list
(Johnson/Desc/First/Look/K3Base.lean): l < 25 is the link; d is false for the lookup on the calls
and true for the lookup on the digits. The step's acceptance alone from s to s' is `IM.Yes 0 b s s'`
(Johnson/IMR/HandsDef.lean). The table is the table of borders (Johnson/Desc/First/Borders.lean).
The five tests are `IM.XK` (HandsDef.lean) at the public items' test alone; the six tests are
`IM.XK` at `P1K2.EQ` (Johnson/P1K2R/TieTwo.lean), which is "in order" and the public items' test.
The item leftOn l is the public item `Pub.leftOn l` (Borders.lean). EP, SP and OP in the statements
are local notations, as in StepWhole.lean, whose head tells them.

What is shown.
  `member_alone_k3`: the member at the number `k3K l d` is the kind's own stated sub-protocol
    (`IM.k3At`) at the address `IM.k3Place l d`, laid alone (`IM.LaidAlone`).
  `noMark_next`: behind the acceptance alone of that member's step the state bears no mark. No
    hypothesis is made on the state in front.
  `step_calls_all`, `step_digits_all`: `step_calls_whole` and `step_digits_whole` (StepWhole.lean)
    without the hypothesis "no mark behind", and with "no mark behind" as the first conjunct of the
    conclusion.
  `xk_ep_of_eq`, `xk_eq_of_ep`: the six tests give the five tests and "in order", and these give the
    six; for every meaning.
  `step_calls_top`, `step_digits_top`: the same step with the six tests in front and the six behind.
    The open sets are written `IM.openAt` and `P1K2.pubAt`.
So, at each of the 50 members: suppose that the state in front is reached by the wrapped
sub-protocols' steps, that it bears no mark, that the five tests hold there (in the last two
theorems: the six), that the samples are held there, at the digits besides that what every public
item open there says holds, and that the member's step accepts. Then behind: no mark; the same tests
hold; the samples are held; what every open public item says holds.

Hypotheses that remain.
  `hS`, `hR`, `O`: (in `member_alone_k3` and `noMark_next`) the public files are in the goals' scope
    (`VerifierAndGoals.InScope`); their reading returns (`VerifierAndGoals.readFiles`); the proof file's description
    returns (`IM.Open`, Johnson/IMR/SeatOpen.lean). These two theorems do not assume `h`; nor do
    `xk_ep_of_eq` and `xk_eq_of_ep`.
  `h`: (in the four step theorems) the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hl`, `hb`: the link is below 25; b is the member at the number `k3K l d`.
  `hy`: the step's acceptance alone, from s to s'.
  `hf`: s is reached by the wrapped sub-protocols' steps (`IM.RB`, Johnson/IMR/GrownRch.lean).
  `h0`: s bears no mark.
  `hx`: the five tests hold at s; in the last two theorems the six.
  `hi`: (in `xk_eq_of_ep`) the test "in order" holds.
  `hS`: (in the four step theorems) the samples are held at s (`samplesHeld`).
  `hQ`: (at the digits) what every public item that is open at s says holds (the field pubP). Of
    these sentences only those of the items left m and leftOn m read a state (the head of
    Honest/K3/Law/Total/SaidBehind.lean); the item leftOn l is open in front of the digits of link l
    (the head of StepWhole.lean), so `hQ` holds its sentence.

Imported. Honest/K3/Law/Total/StepWhole.lean, beneath which lie thirteen more files of
Honest/K3/Law/Total/: the files on the library's `IM.MadeOwed` (Johnson/IMR/MadeOwed.lean: "the debt
of a kind's authors at one of its places"), of which this file is the topmost. Besides,
Johnson/P1K2R/TieTwo.lean. No module under Johnson/Goal/ is imported directly.

How the proof goes. `member_alone_k3` is the library's `IM.k3_of` (Johnson/IMR/K3Seat.lean), read at
the flat list's number by `hear_flat` (Johnson/IMR/FrameAt.lean) and `hear_flat24`
(Johnson/IMR/FrameAll.lean); its proof repeats the first lines of `calls_hd_of_yes`
(Honest/K3/Law/Total/CallsYesAt.lean) and of `digits_hd_of_yes`
(Honest/K3/Law/Total/MadeOwedDigits.lean), by cases on d. For `noMark_next`: a sub-protocol that is
laid alone accepts only where the kind's own accepts, the state behind bears no mark, and the reply
is as it was: the second conjunct of the library's `IM.k3_yes` (K3Seat.lean). The two theorems on
the tests unfold the definitions. In the last two, "in order" has one value at all states
(`inOrder_same`, StepWhole.lean).

Users. The last two theorems are stated for `form_behind_of_xk` (Honest/Thread/FormXK.lean).
That lemma asks four things of the state behind: no
mark; the six tests at `P1K2.EQ`; `samplesHeld` at `IM.openAt`; pubP of every item of `P1K2.pubAt`.
The four conclusions of the last two theorems are these four, at that file's letters N, links, ps,
mgP := `P5J.At.N Zp cF`, `P5J.At.links`, `P5J.At.ps`, `P5J.mgAtAll h`. Its `xk_of_form` gives the
six tests in front.

Options. `maxRecDepth` is raised to 100000 for the file; `quotPrecheck` is off at three local
notations. These raise limits on Lean's own work or switch off a check on a notation's names: none
loosens a check on a proof.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
In particular no state is exhibited at which a member's step accepts; `P5J.AtMgA` is a hypothesis.
At the full size alone. That the state is reached (`hf`) is assumed in front and is not among the
conclusions behind.
Not shown here, as the head of StepWhole.lean says: anything on the witness, on strings or on
decoding; and anything on the four members between a link's two lookups, the first of which makes
the item leftOn l.
That the conclusions meet `form_behind_of_xk` is not shown in this file: nothing under
Honest/Thread/ is imported here. The composition stands in Honest/Thread/K3FormBehind.lean; that
composition is not made here. Three things that the composition needs are
not shown here: that the letters of these files at `P5J.AtMgA` are these four (Lean takes the four
as they stand in Honest/Thread/K3FormBehind.lean); that the thread's list of members there
is the flat list, and its border the number `k3K l d` (the lookup's files on the site and the border
at the thread assume it, for instance `SiteAt`, Honest/K3/Law/Thread/SiteThr.lean, in its fields
flat and place; it is not combined with them here); that the thread's state in front satisfies
`IM.RB` (which is for the files under Honest/Thread/ to show). `k3_form_behind_calls` and
`k3_form_behind_digits` (Honest/Thread/K3FormBehind.lean) import this file and make the composition
over both theorems; their hypotheses are
`P5J.AtMgA`, a link below 25, the member at the number, the thread's invariant in front of the step
together with `SaidOk`, and the step.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.StepWhole
import Johnson.P1K2R.TieTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (pubSets openSets start ePubAt samplesHeld)
open P5J

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {c : Chain TS ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The flat list's member at a lookup's number is the kind's own stated sub-protocol, laid
alone.** Here d is false for the lookup on the calls and true for the lookup on the digits.
Conditional on the goals' scope, the reading of the files, the return of the description, and b
being the member at the number. No instance of these hypotheses is exhibited in this file. -/
theorem member_alone_k3 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) (d : Bool)
    {b : Block TS ProofFile.Cl} (hb : c.blocksInOrder[k3K l d]? = some b) :
    ∃ b', IM.k3At Bs.G₀.W Z (IM.k3Place l d) = some b' ∧
      IM.LaidAlone ProofFile.sameReply b b' b.name (IM.k3Place l d) := by
  obtain ⟨Lk, b0, b', e1, e2, hat, hla⟩ := IM.k3_of hS hR O l hl d
  cases d with
  | false =>
    have hbb : b0 = b := by
      by_cases h24 : l = 24
      · subst h24
        obtain ⟨Lk', e1', -, hj⟩ := Meaning.K2.hear_flat24 hS hR O
        obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
        obtain ⟨b1, f1, f2⟩ := hj 2 (by decide)
        have g1 : b0 = b1 := Option.some.inj (e2.symm.trans f1)
        exact g1.trans (Option.some.inj (f2.symm.trans hb))
      · obtain ⟨Lk', e1', hj⟩ := Meaning.K2.hear_flat hS hR O (l := l) (by omega)
        obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
        obtain ⟨b1, f1, f2⟩ := hj 1 (by decide)
        have hix : IM.k3Ix l false = 1 := by
          show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = 1
          rw [if_neg h24]
          rfl
        have hk : k3K l false = 14 * l + 2 + 1 := by
          show 14 * l + IM.k3Ix l false + 2 = _
          rw [hix]
        rw [hix] at e2
        rw [hk] at hb
        have g1 : b0 = b1 := Option.some.inj (e2.symm.trans f1)
        exact g1.trans (Option.some.inj (f2.symm.trans hb))
    subst hbb
    exact ⟨b', hat, hla⟩
  | true =>
    have hbb : b0 = b := by
      by_cases h24 : l = 24
      · subst h24
        obtain ⟨Lk', e1', -, hj⟩ := Meaning.K2.hear_flat24 hS hR O
        obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
        obtain ⟨b1, f1, f2⟩ := hj 7 (by decide)
        have g1 : b0 = b1 := Option.some.inj (e2.symm.trans f1)
        exact g1.trans (Option.some.inj (f2.symm.trans hb))
      · obtain ⟨Lk', e1', hj⟩ := Meaning.K2.hear_flat hS hR O (l := l) (by omega)
        obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
        obtain ⟨b1, f1, f2⟩ := hj 6 (by decide)
        have hix : IM.k3Ix l true = 6 := by
          show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
          rw [if_neg h24]
          rfl
        have hk : k3K l true = 14 * l + 2 + 6 := by
          show 14 * l + IM.k3Ix l true + 2 = _
          rw [hix]
        rw [hix] at e2
        rw [hk] at hb
        have g1 : b0 = b1 := Option.some.inj (e2.symm.trans f1)
        exact g1.trans (Option.some.inj (f2.symm.trans hb))
    subst hbb
    exact ⟨b', hat, hla⟩

/-- **Behind the step's acceptance alone the state bears no mark.** Conditional on the goals' scope,
the reading of the files, the return of the description, b being the member at the number, and the
acceptance alone of its step from s to s'. No instance of these hypotheses is exhibited in this
file. -/
theorem noMark_next (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) (d : Bool)
    {b : Block TS ProofFile.Cl} (hb : c.blocksInOrder[k3K l d]? = some b) {s s' : TS} (hy : IM.Yes 0 b s s') :
    s'.failed = none := by
  obtain ⟨b', -, hla⟩ := member_alone_k3 hS hR O hl d hb
  obtain ⟨rs, cols, n, hst⟩ := hy
  have hd0 := ((Desc.Sound.step_ok_iff 0 b s s' rs cols n).1 hst).2.2.2
  exact ((IM.k3_yes hla s s' _ _).1 hd0).2.1

end

section
variable {Pz W : Type} (N : Desc.First.Numbers) (Mg : Desc.First.Meaning Pz W)
  (links : List Desc.First.ModelPart) (ps : List Desc.Place) (z : Pz) (k : ℕ) (s : TS)

/-- **The six Boolean tests give the five and "in order".** Conditional on the six at s. No instance
of these hypotheses is exhibited in this file. -/
theorem xk_ep_of_eq (hx : IM.XK N links ps (P1K2.EQ Mg links ps z) k s = true) :
    IM.XK N links ps (fun k s => ePubAt Mg.pub Mg.more links ps k (z, s)) k s = true ∧
      Mg.inOrder (z, s) = true := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := IM.xk_parts hx
  unfold P1K2.EQ at c5
  rw [Bool.and_eq_true] at c5
  have c6 : ePubAt Mg.pub Mg.more links ps k (z, s) = true := c5.2
  refine ⟨?_, c5.1⟩
  unfold IM.XK IM.BK
  rw [c1, c2, c3, c4]
  show (true && true && true && true && ePubAt Mg.pub Mg.more links ps k (z, s)) = true
  rw [c6]
  rfl

/-- **The five Boolean tests and "in order" give the six.** Conditional on these at s. No instance
of these hypotheses is exhibited in this file. -/
theorem xk_eq_of_ep
    (hx : IM.XK N links ps (fun k s => ePubAt Mg.pub Mg.more links ps k (z, s)) k s = true)
    (hi : Mg.inOrder (z, s) = true) : IM.XK N links ps (P1K2.EQ Mg links ps z) k s = true := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := IM.xk_parts hx
  have c6 : Desc.First.pubHeld Mg (IM.openAt links ps k) (P1K2.pubAt Mg links ps k) (z, s) =
      true := c5
  unfold IM.XK IM.BK P1K2.EQ
  rw [c1, c2, c3, c4, hi, c6]
  rfl

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

set_option quotPrecheck false in
local notation "EP" => fun (z : ProofFile.InstPub) (k : ℕ) (s : TS) =>
  ePubAt (mgAtAll h).pub (mgAtAll h).more At.links At.ps k (z, s)
set_option quotPrecheck false in
local notation "SP" => fun (k : ℕ) => (pubSets (mgAtAll h).more At.links At.ps)[k]?.getD []
set_option quotPrecheck false in
local notation "OP" => fun (k : ℕ) => (openSets At.links At.ps (start At.links))[k]?.getD []

/-- **The whole step at the calls, with "no mark behind" among its conclusions.** Conditional on
`P5J.AtMgA`; a link below 25; b being the member at the number; s being reached by the wrapped
sub-protocols' steps; the step's acceptance alone from s to s'; no mark at s; the five tests and
"the samples are held" at s. No instance of these hypotheses is exhibited in this file. -/
theorem step_calls_all {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) {s s' : TS}
    (hf : IM.RB cF Zp z (k3K l false) s) (hy : IM.Yes 0 b s s') (h0 : s.failed = none)
    (hx : IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l false) s = true)
    (hS : samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l false)) (z, s) = true) :
    s'.failed = none ∧
      IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l false + 1) s' = true ∧
      samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l false + 1)) (z, s') = true ∧
      ∀ p ∈ SP (k3K l false + 1), (mgAtAll h).pubP p (z, s') := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have h1 := noMark_next h.scope h.reads O hl false hb hy
  exact ⟨h1, step_calls_whole h hl hb z hf hy h0 h1 hx hS⟩

/-- **The whole step at the digits, with "no mark behind" among its conclusions.** Conditional on
`P5J.AtMgA`; a link below 25; b being the member at the number; s being reached by the wrapped
sub-protocols' steps; the step's acceptance alone from s to s'; no mark at s; the five tests, "the
samples are held" and what every open public item says, at s. No instance of these hypotheses is
exhibited in this file. -/
theorem step_digits_all {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l true]? = some b) (z : ProofFile.InstPub) {s s' : TS}
    (hf : IM.RB cF Zp z (k3K l true) s) (hy : IM.Yes 0 b s s') (h0 : s.failed = none)
    (hx : IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l true) s = true)
    (hS : samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l true)) (z, s) = true)
    (hQ : ∀ p ∈ SP (k3K l true), (mgAtAll h).pubP p (z, s)) :
    s'.failed = none ∧
      IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l true + 1) s' = true ∧
      samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l true + 1)) (z, s') = true ∧
      ∀ p ∈ SP (k3K l true + 1), (mgAtAll h).pubP p (z, s') := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have h1 := noMark_next h.scope h.reads O hl true hb hy
  exact ⟨h1, step_digits_whole h hl hb z hf hy h0 h1 hx hS hQ⟩

/-- **The step at the calls with all six tests on both sides.** Conditional on `P5J.AtMgA`; a link
below 25; b being the member at the number; s being reached by the wrapped sub-protocols' steps; the
step's acceptance alone from s to s'; no mark at s; the six tests and "the samples are held" at s.
No instance of these hypotheses is exhibited in this file. -/
theorem step_calls_top {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) {s s' : TS}
    (hf : IM.RB cF Zp z (k3K l false) s) (hy : IM.Yes 0 b s s') (h0 : s.failed = none)
    (hx : IM.XK (At.N Zp cF) At.links At.ps (P1K2.EQ (mgAtAll h) At.links At.ps z)
      (k3K l false) s = true)
    (hS : samplesHeld (At.N Zp cF) (mgAtAll h) (IM.openAt At.links At.ps (k3K l false)) (z, s) =
      true) :
    s'.failed = none ∧
    IM.XK (At.N Zp cF) At.links At.ps (P1K2.EQ (mgAtAll h) At.links At.ps z)
      (k3K l false + 1) s' = true ∧
    samplesHeld (At.N Zp cF) (mgAtAll h) (IM.openAt At.links At.ps (k3K l false + 1)) (z, s') =
      true ∧
    ∀ q ∈ P1K2.pubAt (mgAtAll h) At.links At.ps (k3K l false + 1),
      (mgAtAll h).pubP q (z, s') := by
  obtain ⟨hxe, hio⟩ := xk_ep_of_eq _ _ _ _ z _ s hx
  obtain ⟨h1, a1, a2, a3⟩ := step_calls_all h hl hb z hf hy h0 hxe hS
  exact ⟨h1, xk_eq_of_ep _ _ _ _ z _ s' a1 ((inOrder_same h z s s').trans hio), a2, a3⟩

/-- **The step at the digits with all six tests on both sides.** Conditional on `P5J.AtMgA`; a link
below 25; b being the member at the number; s being reached by the wrapped sub-protocols' steps; the
step's acceptance alone from s to s'; no mark at s; the six tests, "the samples are held" and what
every open public item says, at s. No instance of these hypotheses is exhibited in this file. -/
theorem step_digits_top {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l true]? = some b) (z : ProofFile.InstPub) {s s' : TS}
    (hf : IM.RB cF Zp z (k3K l true) s) (hy : IM.Yes 0 b s s') (h0 : s.failed = none)
    (hx : IM.XK (At.N Zp cF) At.links At.ps (P1K2.EQ (mgAtAll h) At.links At.ps z)
      (k3K l true) s = true)
    (hS : samplesHeld (At.N Zp cF) (mgAtAll h) (IM.openAt At.links At.ps (k3K l true)) (z, s) =
      true)
    (hQ : ∀ q ∈ P1K2.pubAt (mgAtAll h) At.links At.ps (k3K l true), (mgAtAll h).pubP q (z, s)) :
    s'.failed = none ∧
    IM.XK (At.N Zp cF) At.links At.ps (P1K2.EQ (mgAtAll h) At.links At.ps z)
      (k3K l true + 1) s' = true ∧
    samplesHeld (At.N Zp cF) (mgAtAll h) (IM.openAt At.links At.ps (k3K l true + 1)) (z, s') =
      true ∧
    ∀ q ∈ P1K2.pubAt (mgAtAll h) At.links At.ps (k3K l true + 1),
      (mgAtAll h).pubP q (z, s') := by
  obtain ⟨hxe, hio⟩ := xk_ep_of_eq _ _ _ _ z _ s hx
  obtain ⟨h1, a1, a2, a3⟩ := step_digits_all h hl hb z hf hy h0 hxe hS hQ
  exact ⟨h1, xk_eq_of_ep _ _ _ _ z _ s' a1 ((inOrder_same h z s s').trans hio), a2, a3⟩

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.member_alone_k3
#print axioms ProofFile.Honest.K3.Law.Total.noMark_next
#print axioms ProofFile.Honest.K3.Law.Total.xk_ep_of_eq
#print axioms ProofFile.Honest.K3.Law.Total.xk_eq_of_ep
#print axioms ProofFile.Honest.K3.Law.Total.step_calls_all
#print axioms ProofFile.Honest.K3.Law.Total.step_digits_all
#print axioms ProofFile.Honest.K3.Law.Total.step_calls_top
#print axioms ProofFile.Honest.K3.Law.Total.step_digits_top
