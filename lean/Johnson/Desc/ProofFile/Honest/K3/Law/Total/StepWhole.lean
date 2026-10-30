-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/StepWhole.lean: the kind "lookup" (K3). Conditional,
under the library's hypothesis `P5J.AtMgA`: at each of the lookups' 50 members of the first chain
(on the calls and on the digits of the 25 links) three things pass together over the acceptance
alone of the member's step: the table's five Boolean tests (`IM.XK`), "the samples are held"
(`samplesHeld`), and what every open public item says beside its test (the field pubP). Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a state s bears no mark if `s.failed = none`. The
lookups' 50 members stand at the numbers `k3K l d` of the flat list
(Johnson/Desc/First/Look/K3Base.lean): l < 25 is the link; d is false for the lookup on the calls
and true for the lookup on the digits. The step's acceptance alone from s to s' is `IM.Yes 0 b s s'`
(Johnson/IMR/HandsDef.lean). The table is the table of borders (Johnson/Desc/First/Borders.lean).
The five tests are `IM.XK` (HandsDef.lean) at the public items' test alone; "in order" is the
table's sixth test. A row of the table is quiet if no pin and no class of rows opens or closes in
it. The item leftOn l is the public item `Pub.leftOn l` (Borders.lean). In the statements EP, SP and
OP are local notations: EP z k s is the public items' test at border k (`ePubAt`), SP k the set of
public items that are open at border k (`pubSets`), OP k the set of items that are open there
(`openSets`). Beyond the lists' ends SP k and OP k are empty: there a sentence on every open item
holds idly.

What is shown.
  `samples_sameBut`: "the samples are held" passes from s to s' wherever the lookups' relation
    `SameBut s s'` holds (Johnson/Desc/First/Look/K3CallsTurns.lean). It is stated for every value
    of the composed meaning's data and does not assume `h`.
  `inOrder_same`: "in order" has one value at all states.
  `samples_next_calls`, `samples_next_digits`: "the samples are held" passes over the acceptance
    alone of the member's step.
  `step_calls_whole`, `step_digits_whole`: the three things together.
The last two assume of the state in front: it is reached by the wrapped sub-protocols' steps; it
bears no mark; the five tests hold; the samples are held; at the digits besides, what every
public item that is open there says holds. Of the state behind they assume: no mark. The item
leftOn l is open in front of the digits at all 25 links, by a closed test of the library that the
kernel evaluates (`planesFront_mgMore`, Johnson/Desc/Sound/MgAt/K3DigitsPlanesIt.lean, its second
half); so the sentence that `xk_next_digits` assumes is among those that `hQ` gives.
The statements are in the terms `P5J.At.N Zp cF`, `P5J.At.links`, `P5J.At.ps`, `P5J.mgAtAll h`. They
speak of the verifier's states alone: no thread, prover, coin, string, piece or transcript occurs in
them.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean); in `inOrder_same` for its
    letters alone.
  `T`: (in `samples_sameBut`) `SameBut s s'`.
  `hl`, `hb`: the link is below 25; b is the member at the number `k3K l d`.
  `hy`: the step's acceptance alone, from s to s'.
  `hf`: s is reached by the wrapped sub-protocols' steps (`IM.RB`, Johnson/IMR/GrownRch.lean).
  `h0`, `h1`: s bears no mark; s' bears no mark.
  `hx`: the five tests hold at s.
  `hS`: the samples are held at s.
  `hQ`: (at the digits) what every public item that is open at s says holds.

Imported. Honest/K3/Law/Total/SaidBehind.lean, beneath which lie twelve more files of
Honest/K3/Law/Total/: the files on the library's `IM.MadeOwed` (Johnson/IMR/MadeOwed.lean: "the debt
of a kind's authors at one of its places"). Besides, files of the library. No module under
Johnson/Goal/ is imported directly.

How the proof goes. `samples_sameBut`: of the verifier's state "held" reads two fields alone, st and
book, which `SameBut` keeps (the library's `heldReads_mgAll`, Johnson/Desc/Sound/MgAt/K3At.lean, and
`held_sameBut`, Johnson/Desc/First/Look/K3FillDigits.lean). `inOrder_same`: over the library's
closed meaning beneath, "in order" is a test on the instance's public part and reads nothing of the
verifier's state (the library's `mgAll_inOrder_base`, Johnson/Desc/Sound/MgBase.lean, is `rfl`; so
is this). `samples_next_calls`, `samples_next_digits`: the lookups' two rows of the table are quiet
(`calls_quiet`, Johnson/Desc/First/Look/K3CallsBehind.lean; `digits_row`,
Johnson/Desc/Sound/DigitsRow.lean), so the sampled tenants behind are those in front
(`samplesHeld_step`, Johnson/Desc/First/BordersKeep.lean). The last two combine these with
`xk_next_calls` (Honest/K3/Law/Total/HandsCalls.lean), `xk_next_digits`
(Honest/K3/Law/Total/MadeOwedDigits.lean), `said_next_calls` and `said_next_digits`
(SaidBehind.lean).

Users. `step_calls_all` and `step_digits_all` (Honest/K3/Law/Total/NoMarkBehind.lean) call the last
two. These are stated so as to meet what, for the files under Honest/Thread/,
a kind's lemma may assume of the state in front: no mark; the Boolean tests; the samples; pubP of
every public item that is open there. The terms `P5J.At.N Zp cF`, `P5J.At.links`, `P5J.At.ps` and
`P5J.mgAtAll h` are those in which the statements were asked for.

Options. `maxRecDepth` is raised to 100000 for the file; `maxHeartbeats` to 4000000 in front of one
theorem; `quotPrecheck` is off at four local notations. These raise limits on Lean's own work or
switch off a check on a notation's names: none loosens a check on a proof.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
`P5J.AtMgA` is a hypothesis; no state is shown to be reached. At the full size alone. That the state
is reached (`hf`) is assumed in front and is not among the conclusions behind. Of what the open
public items say, only the sentences of the items left m and leftOn m read a state (the head of
SaidBehind.lean).
Not shown here: anything on the witness, on strings or on decoding; and anything on the four members
that stand between a link's two lookups, the first of which makes the item leftOn l by the table's
own text. These four are not the lookups'. Whoever chains these steps along the flat list needs the
like of the last two theorems at every other member.
The files under Honest/Thread/ are not imported here;
see the head of Honest/K3/Law/Total/NoMarkBehind.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.SaidBehind
import Johnson.Desc.First.BordersKeep
import Johnson.Desc.First.BordersSucc
import Johnson.Desc.Sound.DigitsRow
import Johnson.Desc.First.Look.K3CallsBehind
import Johnson.Desc.First.Look.K3FillDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning Numbers Item shift pubSets openSets start ePubAt
  samplesHeld quietRow)
open P5J

section
variable {Xi Pz Tok : Type} {rows cols₀ nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi Pz Tok rows cols₀ nR X)
  (Mg : Meaning Pz (Desc.Wit (CellsQ rows cols₀) Tok MsgT))

/-- **"The samples are held" passes wherever `SameBut` holds.** Conditional on that relation and on
the test at s. No instance of these hypotheses is exhibited in this file. -/
theorem samples_sameBut (N : Numbers) (O : List Item) {s s' : Desc.First.S} (T : SameBut s s')
    (z : Pz) (hS : samplesHeld N (mgAll Dm Mg) O (z, s) = true) :
    samplesHeld N (mgAll Dm Mg) O (z, s') = true := by
  unfold samplesHeld at hS ⊢
  rw [List.all_eq_true] at hS ⊢
  exact fun x hx => held_sameBut (heldReads_mgAll Dm Mg) T x.1 x.2 z (hS x hx)

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "𝔐" => AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)
local notation "baseP" => Desc.First.Meaning.pub (mgBase : Desc.First.Meaning ProofFile.InstPub
  (Desc.Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
set_option quotPrecheck false in
local notation "EP" => fun (z : ProofFile.InstPub) (k : ℕ) (s : TS) =>
  ePubAt (mgAtAll h).pub (mgAtAll h).more At.links At.ps k (z, s)
set_option quotPrecheck false in
local notation "SP" => fun (k : ℕ) => (pubSets (mgAtAll h).more At.links At.ps)[k]?.getD []
set_option quotPrecheck false in
local notation "OP" => fun (k : ℕ) => (openSets At.links At.ps (start At.links))[k]?.getD []

/-- **"In order" has one value at all states.** At this meaning it is a test on the instance's
public part, not on the state: no member makes it and none can lose it. Nothing is said on whether
it holds. Conditional on `P5J.AtMgA` (for its letters alone). No instance of these hypotheses is
exhibited in this file. -/
theorem inOrder_same (z : ProofFile.InstPub) (s s' : TS) :
    (mgAtAll h).inOrder (z, s') = (mgAtAll h).inOrder (z, s) := rfl

/-- **"The samples are held" passes over the step's acceptance alone, at the calls.** Conditional on
`P5J.AtMgA`; a link below 25; b being the member at the number; the acceptance alone of its step;
the test at s. No instance of these hypotheses is exhibited in this file. -/
theorem samples_next_calls {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) {s s' : TS} (hy : IM.Yes 0 b s s')
    (hS : samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l false)) (z, s) = true) :
    samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l false + 1)) (z, s') = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, P', sent, laid, rs, gs, -, hd⟩ :=
    calls_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy
  have T := k3_calls_sameBut K3Lot.ofForm _ laid sent P' [] s s' rs gs hd
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full l hl
  show samplesHeld (At.N Zp cF) (mgAll (𝔐) mgBase)
    ((openSets linksFull PS (start linksFull))[k3K l false + 1]?.getD []) (z, s') = true
  rw [Desc.First.openSets_succ linksFull PS (start linksFull) (k3K l false) (IM.k3Place l false)
    (K3Lot.k03_at_full l hl false),
    Desc.First.samplesHeld_step (At.N Zp cF) _ _ _ (calls_quiet rfl hs' hpc)]
  exact samples_sameBut (𝔐) mgBase _ _ T z hS

set_option maxHeartbeats 4000000 in
/-- **"The samples are held" passes over the step's acceptance alone, at the digits.** Conditional
on `P5J.AtMgA`; a link below 25; b being the member at the number; the acceptance alone of its step;
the five Boolean tests and the test at s. No instance of these hypotheses is exhibited in this file.
-/
theorem samples_next_digits {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l true]? = some b) (z : ProofFile.InstPub) {s s' : TS} (hy : IM.Yes 0 b s s')
    (hx : IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l true) s = true)
    (hS : samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l true)) (z, s) = true) :
    samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l true + 1)) (z, s') = true := by
  rw [ep_is_ew h z, ← linksW_at, ← placesW_at] at hx
  have hfront : ∀ q ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub q (z, s) = true :=
    front_of_xk (At.N Zp cF) (𝔐).pubD baseP z (k3K l true) s hx
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', rs, gs, hat, hOk, hd⟩ :=
    digits_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy
  rw [O.W] at hat
  obtain ⟨sub, hsub, -, hpcT⟩ := K3Lot.k03_sub_full l hl
  obtain ⟨hpc, x, hlook, hIn, -⟩ := dig_front h hl hsub hat z hfront
  obtain ⟨hs, hsh⟩ : ∃ hs,
      (Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) true x).shape = some hs := by
    cases e : (Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) true x).shape with
    | none =>
      unfold Desc.K3.k3OnIn at hIn
      rw [e] at hIn
      cases hIn
    | some hs => exact ⟨hs, rfl⟩
  have T := (k3_digits_step_turns K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place l true) b' hat hOk l rfl hpc hlook hsh s s' rs gs
    hd).1
  have hrow := digits_row linksFull (IM.k3Place l true) l sub rfl hsub hpcT
  have hq : quietRow (Desc.First.rowOf linksFull (IM.k3Place l true)) = true := by
    unfold quietRow
    rw [hrow.1, hrow.2.1]
    rfl
  show samplesHeld (At.N Zp cF) (mgAll (𝔐) mgBase)
    ((openSets linksFull PS (start linksFull))[k3K l true + 1]?.getD []) (z, s') = true
  rw [Desc.First.openSets_succ linksFull PS (start linksFull) (k3K l true) (IM.k3Place l true)
    (K3Lot.k03_at_full l hl true), Desc.First.samplesHeld_step (At.N Zp cF) _ _ _ hq]
  exact samples_sameBut (𝔐) mgBase _ _ T z hS

/-- **The whole step at the calls.** Conditional on `P5J.AtMgA`; a link below 25; b being the member
at the number; s being reached by the wrapped sub-protocols' steps; the step's acceptance alone from
s to s'; no mark at either; the five tests and "the samples are held" at s. No instance of these
hypotheses is exhibited in this file. -/
theorem step_calls_whole {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) {s s' : TS}
    (hf : IM.RB cF Zp z (k3K l false) s) (hy : IM.Yes 0 b s s') (h0 : s.failed = none)
    (h1 : s'.failed = none)
    (hx : IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l false) s = true)
    (hS : samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l false)) (z, s) = true) :
    IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l false + 1) s' = true ∧
      samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l false + 1)) (z, s') = true ∧
      ∀ p ∈ SP (k3K l false + 1), (mgAtAll h).pubP p (z, s') :=
  ⟨xk_next_calls h hl hb z hf hy h0 h1 hx, samples_next_calls h hl hb z hy hS,
    said_next_calls h hl hb z hy hx⟩

/-- **The whole step at the digits.** Conditional on `P5J.AtMgA`; a link below 25; b being the
member at the number; s being reached by the wrapped sub-protocols' steps; the step's acceptance
alone from s to s'; no mark at either; the five tests, "the samples are held" and what every open
public item says, at s. No instance of these hypotheses is exhibited in this file. -/
theorem step_digits_whole {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l true]? = some b) (z : ProofFile.InstPub) {s s' : TS}
    (hf : IM.RB cF Zp z (k3K l true) s) (hy : IM.Yes 0 b s s') (h0 : s.failed = none)
    (h1 : s'.failed = none)
    (hx : IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l true) s = true)
    (hS : samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l true)) (z, s) = true)
    (hQ : ∀ p ∈ SP (k3K l true), (mgAtAll h).pubP p (z, s)) :
    IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l true + 1) s' = true ∧
      samplesHeld (At.N Zp cF) (mgAtAll h) (OP (k3K l true + 1)) (z, s') = true ∧
      ∀ p ∈ SP (k3K l true + 1), (mgAtAll h).pubP p (z, s') := by
  have hFr := List.all_eq_true.1 planesFront_mgMore l (List.mem_range.2 hl)
  unfold planesFrontRowB at hFr
  rw [Bool.and_eq_true] at hFr
  have m2 : Desc.First.Pub.leftOn l ∈ (pubSets mgMore linksFull PS)[k3K l true]?.getD [] := by
    simpa using hFr.2
  have hLeft : (mgAtAll h).pubP (.leftOn l) (z, s) := hQ _ (by
    have e : (mgAtAll h).more = mgMore := mgAll_more_closed (𝔐) mgBase rfl
    rw [e]
    exact m2)
  exact ⟨xk_next_digits h hl hb z hf hLeft hy h0 h1 hx, samples_next_digits h hl hb z hy hx hS,
    said_next_digits h hl hb z hy hx hQ⟩

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.samples_sameBut
#print axioms ProofFile.Honest.K3.Law.Total.inOrder_same
#print axioms ProofFile.Honest.K3.Law.Total.samples_next_calls
#print axioms ProofFile.Honest.K3.Law.Total.samples_next_digits
#print axioms ProofFile.Honest.K3.Law.Total.step_calls_whole
#print axioms ProofFile.Honest.K3.Law.Total.step_digits_whole
