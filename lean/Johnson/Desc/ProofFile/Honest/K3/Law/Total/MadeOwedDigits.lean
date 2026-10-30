-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/MadeOwedDigits.lean: the kind "lookup" (K3). Conditional,
under the library's hypothesis `P5J.AtMgA`: the library's `IM.MadeOwed` (Johnson/IMR/MadeOwed.lean:
"the debt of a kind's authors at one of its places") and, with it, `IM.HandsR`
(Johnson/IMR/HandsFence.lean), at the lookup on the digits of every one of the 25 links. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a state s bears no mark if `s.failed = none`. The
lookups' 50 members stand at the numbers `k3K l d` of the flat list
(Johnson/Desc/First/Look/K3Base.lean): l < 25 is the link; d is false for the lookup on the calls
and true for the lookup on the digits. The step's acceptance alone from s to s' is `IM.Yes 0 b s s'`
(Johnson/IMR/HandsDef.lean). The table is the table of borders (Johnson/Desc/First/Borders.lean).
What the debt `IM.MadeOwed` is stands in the head of Honest/K3/Law/Total/MadeOwedCalls.lean. A fence
is the letter Fk of `IM.MadeOwed` and `IM.HandsR`: a condition on the state in front. The five tests
are `IM.XK` (HandsDef.lean) at the public items' test alone. The item leftOn l is the public item
`Pub.leftOn l` (Borders.lean); its sentence is what it says beside its test: the library's
`k3LeftOnItemAt` (Johnson/Desc/First/Look/K3LeftItem.lean), which is the composed meaning's field
pubP at that item. In the statements EP is a local notation: EP z k s is the public items' test at
border k (`ePubAt`). Three more local notations: PS is `flatPlacesOf linksFull true`, the written
list of places; 𝔐 is `AtMg.𝔇` at the head h (the composed meaning's data there); baseP is the field
pub of `mgBase`.

What is shown.
  `digits_hd_of_yes`: the acceptance alone of the step of the chain's member at the digits' number
    is an acceptance of the decision of the kind's own stated sub-protocol there. In the goals'
    scope; it does not assume `h`.
  `forms_dig_at`: every test "formsIn" of the two written lists (`keptDigits`, `newDigits`,
    Johnson/Desc/Sound/MgAt/K3DigitsSorted.lean) holds behind that acceptance.
  `madeOwed_digits`: the debt, at any fence inside the narrow one that is described below.
  `handsR_digits`: `IM.HandsR`, all six fields, at that narrow fence, at the test `LPFK9.HandsAt.EW`
    (Johnson/LPFK9R/SharesAtE.lean), at the written lists `IM.linksW` and `IM.placesW`
    (Johnson/IMR/WrittenList.lean), at the first tree 0. The fence names l: there are 25 fences, not
    one.
  `xk_next_digits`: the five tests pass over the acceptance alone of the member's step, at
    `P5J.At.N Zp cF`, `P5J.At.links`, `P5J.At.ps` and the public items' test of `P5J.mgAtAll h`; the
    sentence of leftOn l is assumed in the form of that meaning's field pubP.
The fence is narrower than at the calls. There "reached by the wrapped sub-protocols' steps" is
enough. Here the fenced state, where it bears no mark, must besides meet the sentence of leftOn l: a
sentence on what the lookup on the calls left, as it stands at every later state. Of a state with a
mark nothing is asked beside "reached": the debt gives "no mark" before the proof uses the sentence,
and the table's own promise gives its sentences only where no mark stands. By the table's own text
the lookups do not make that sentence: the lookup on the calls makes the item left l; the calling
kind's own member behind it drops that item and makes leftOn l. The table's Boolean tests do not
hold the sentence: the item's test is "true" by the meaning's own text. The proofs use it at the run
"planes" (attention's twelve links and the head's) and at the run "own" (the twelve layers' links):
so at all 25. Whoever calls these theorems must give it at the state in front; it is not shown in
this file.
The item leftOn l is among the public items that are open in front of the digits, at all 25 links,
by a closed test of the library that the kernel evaluates (`planesFront_mgMore`,
Johnson/Desc/Sound/MgAt/K3DigitsPlanesIt.lean, its second half). So a hypothesis "pubP of every
public item that is open in front" holds the sentence.
The statements stand at the composed meaning's own data. They speak of the verifier's states alone:
no thread, prover, coin, string, piece or transcript occurs in them. The file is the fellow of
Honest/K3/Law/Total/MadeOwedCallsHead.lean and Honest/K3/Law/Total/HandsCalls.lean at the calls.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hl`, `hb`: the link is below 25; b is the member at the number `k3K l true`.
  `hFk`: (in `madeOwed_digits`) every state of the fence is reached (`Reach`,
    Johnson/Top/H0/Walk/Reach.lean) and, where it bears no mark, meets the sentence of leftOn l.
  `hf`, `hLeft`, `hy`, `h0`, `h1`, `hx`: (in `xk_next_digits`) s is reached by the wrapped
    sub-protocols' steps (`IM.RB`, Johnson/IMR/GrownRch.lean); the sentence of leftOn l holds at s;
    the step's acceptance alone from s to s'; s bears no mark; s' bears no mark; the five tests hold
    at s. No other hypothesis is made on a state.
  `hS`, `hR`, `O`, `hF`: (in `digits_hd_of_yes`) the goals' scope; the reading of the files; the
    return of the description (`IM.Open`, Johnson/IMR/SeatOpen.lean); the description's test on the
    plan.
  `hsub`, `hb`, `hOk`, `hd`, `hfront`, `hshape`, `hbook`, `hr`, `hf`, `hLeft`: (in `forms_dig_at`)
    the link's sort; b' is the stated sub-protocol (`k3Const`, K3Base.lean); its test on the plan;
    the acceptance of its decision from s to s'; the public tests in front (`frontDig`,
    K3DigitsSorted.lean); the first and the fourth of the book-keeping's tests in front; s is
    reached; s bears no mark; the sentence of leftOn l holds at s.

Imported. Five files of Honest/K3/Law/Total/ directly (DigitsBehindState.lean, DigitsFormsOwn.lean,
DigitsFormsNew.lean, DigitsFormsLay.lean, HandsCalls.lean), beneath which lie six more: the files on
the library's `IM.MadeOwed`. Besides, files of the library. No module under Johnson/Goal/ is
imported directly.
Follows. The way from `IM.MadeOwed` to `IM.HandsR` by the library's `IM.rows_at_rch`
(Johnson/IMR/RowsAtRch.lean) and `IM.rows_at_plan` (Johnson/IMR/RowsAtPaid.lean) was pointed out in
the work on K11's files.

How the proof goes. `forms_dig_at` is the library's `forms_of_live`
(Johnson/Desc/Sound/MgAt/K3DigitsFormsLive.lean) over the live items: four at a layers' link, six at
an attention link, six at the head's. Nine theorems of Honest/K3/Law/Total/DigitsFormsFour.lean,
DigitsFormsOwn.lean, DigitsFormsNew.lean and DigitsFormsLay.lean bear the sixteen. `handsR_digits`
is one call of `IM.rows_at_plan`, which takes any fence inside "reached".

Users. `step_digits_whole` (Honest/K3/Law/Total/StepWhole.lean) calls `xk_next_digits`;
`member_alone_k3` (Honest/K3/Law/Total/NoMarkBehind.lean) repeats the first lines of
`digits_hd_of_yes`. `xk_next_digits` is stated so as to meet a lemma of the files
under Honest/Thread/ on "the five Boolean tests at a test that gives the public items' test", and
what, for these files, a kind's lemma may assume, of the state in front: pubP of a public item
that is open there. The terms `P5J.At.N Zp cF`, `P5J.At.links`, `P5J.At.ps` and `P5J.mgAtAll h`
are those in which it was asked for.

Options. `maxRecDepth` is raised to 100000 for the file; `maxHeartbeats` to 4000000 in front of two
theorems; `quotPrecheck` is off at two local notations. These raise limits on Lean's own work or
switch off a check on a notation's names: none loosens a check on a proof.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
`P5J.AtMgA` is a hypothesis; no state is shown to be reached, none to meet the sentence of leftOn l.
The fence is narrower than at the calls, and whoever calls these theorems must give the sentence of
leftOn l in front: see the paragraph on the fence under "What is shown". The Boolean tests alone:
nothing on what a public item says behind the acceptance, on the samples, on "in order" or on the
witness. At the full size alone.
`handsR_digits` stands at the test `LPFK9.HandsAt.EW`, which is the public items' test alone, not at
`P1K2.EQ` (Johnson/P1K2R/TieTwo.lean), which has "in order" besides. The table's own row of the
lookup on the digits (`pubRowOf`, Borders.lean) does not ask leftOn l.
The files under Honest/Thread/ are not imported here;
see the head of Honest/K3/Law/Total/NoMarkBehind.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.DigitsBehindState
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.DigitsFormsOwn
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.DigitsFormsNew
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.DigitsFormsLay
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.HandsCalls
import Johnson.IMR.RowsAtPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift bookAt ePubAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {c : Chain TS ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The acceptance alone of the step of the chain's member at the digits' number is an acceptance
of the stated sub-protocol's decision.** Conditional on the goals' scope, the reading of the files,
the return of the description, its test on the plan, b being the member at the number, and the
acceptance of its step from s to s'. No instance of these hypotheses is exhibited in this file. rs
and gs are bound by "∃" and held by what functions return at them alone: some values: not said to be
the step's own. -/
theorem digits_hd_of_yes (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true) {l : ℕ}
    (hl : l < 25) {b : Block TS ProofFile.Cl} (hb : c.blocksInOrder[k3K l true]? = some b) {s s' : TS}
    (hy : IM.Yes 0 b s s') :
    ∃ b' rs gs, IM.k3At Bs.G₀.W Z (IM.k3Place l true) = some b' ∧ b'.planOk = true ∧
      b'.decide s rs gs = .ok s' := by
  obtain ⟨Lk, b0, b', e1, e2, hat, hla⟩ := IM.k3_of hS hR O l hl true
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
  obtain ⟨rs, cols, n, hst⟩ := hy
  have hd0 := ((Desc.Sound.step_ok_iff 0 b0 s s' rs cols n).1 hst).2.2.2
  obtain ⟨hd1, -, -⟩ := (IM.k3_yes hla s s' _ _).1 hd0
  have hOkb : b0.planOk = true :=
    Meaning.K2.planOk_of_blocksOk (IM.blocksOk_of_planOk O hF) b0 (List.mem_of_getElem? hb)
  exact ⟨b', _, _, hat, by rw [← IM.alone_planOk hla]; exact hOkb, hd1⟩

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

set_option maxHeartbeats 4000000 in
/-- **Every test "formsIn" of the two written lists holds behind the acceptance.** Conditional on
`P5J.AtMgA`; the acceptance of the stated sub-protocol's decision; the public tests and the first
and fourth of the book-keeping's Boolean tests in front; s being reached and without a mark; what
the item leftOn l says of s. No instance of these hypotheses is exhibited in this file. -/
theorem forms_dig_at {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hOk : b'.planOk = true) {s s' : TS} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : b'.decide s rs gs = .ok s') (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, s) = true)
    (hshape : Desc.First.shapeAt linksFull PS[k3K l true]? s = true)
    (hbook : bookAt (𝔐).N PS[k3K l true]? s = true)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l true) (z, s))
    (hf : s.failed = none) (hLeft : k3LeftOnItemAt (At.X Zp) l s) :
    ∀ r ∈ keptDigits l sub ++ newDigits l sub, (∃ pc nm, r = .formsIn l pc nm) →
      (mgAll (𝔐) mgBase).pub r (z, s') = true := by
  have hK := objectsKept_dig_at h hl hsub hb hOk hd z hfront
  have hSm := small_dig_at h hl hsub hb hOk hd z hfront
  have hNew := objectsNew_dig_at h hl hsub hb hOk hd z hfront hshape hr hf hbook
  refine forms_of_live (𝔐) mgBase rfl hsub (z, s') fun q hq => ?_
  cases sub with
  | layers =>
    simp only [liveForms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hK
    · exact own_dig_lay h hl hsub hb hOk hd z hfront hr hLeft
    · exact hSm
    · exact hNew
  | attention =>
    simp only [liveForms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hK
    · exact planes_dig_at h hl hsub hb hOk hd z hfront (by decide) hshape hLeft
    · exact join_dig_att h hl hsub hb hOk hd z hfront hshape
    · exact own_dig_att h hl hsub hb hOk hd z hfront hshape
    · exact hSm
    · exact hNew
  | head =>
    obtain rfl : l = 24 := (P5J.k03_sorts_full l hl).2 hsub
    simp only [liveForms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hK
    · exact planes_dig_at h hl hsub hb hOk hd z hfront (by decide) hshape hLeft
    · exact join_dig_head h hb hOk hd z hfront hshape hr
    · exact own_dig_head h hb hOk hd z hfront hshape hr
    · exact hSm
    · exact hNew

set_option maxHeartbeats 4000000 in
/-- **The debt `IM.MadeOwed` at the digits of every link.** Conditional on `P5J.AtMgA`; a link below
25; b being the member at the number; a fence whose states are reached and, where they bear no mark,
meet what the item leftOn l says. No instance of these hypotheses is exhibited in this file. -/
theorem madeOwed_digits {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l true]? = some b) (z : ProofFile.InstPub) (Fk : ℕ → TS → Prop)
    (hFk : ∀ s, Fk (k3K l true) s →
      Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l true) (z, s) ∧
        (s.failed = none → k3LeftOnItemAt (At.X Zp) l s)) :
    IM.MadeOwed Fk (𝔐).N IM.linksW IM.placesW (𝔐).pubD baseP z 0 (k3K l true) b b.place := by
  intro s s' hF hy' h0 _ hx q hq
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', rs, gs, hat, hOk, hd⟩ :=
    digits_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy'
  rw [O.W] at hat
  obtain ⟨sub, hsub, -, -⟩ := K3Lot.k03_sub_full l hl
  obtain ⟨hr, hLeft0⟩ := hFk s hF
  have hLeft := hLeft0 h0
  have hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, s) = true :=
    front_of_xk _ _ _ z (k3K l true) s hx
  have hshape : Desc.First.shapeAt linksFull PS[k3K l true]? s = true := by
    have h1 := (IM.xk_parts hx).1
    rw [IM.linksW_full, IM.placesW_full] at h1
    exact h1
  have hbook : bookAt (𝔐).N PS[k3K l true]? s = true := by
    have h4 := (IM.xk_parts hx).2.2.2.1
    rw [IM.placesW_full] at h4
    exact h4
  have hpl : b.place = IM.k3Place l true := by
    have e1 := IM.place_at h.scope h.reads O hb
    rw [IM.placesW_full, K3Lot.k03_at_full l hl true] at e1
    exact (Option.some.inj e1).symm
  have hq' := behind_of_made _ _ _ _ q hq
  rw [hpl] at hq'
  obtain ⟨-, x, hlook, -⟩ := dig_front h hl hsub hat z hfront
  exact behind_dig_state (𝔐) mgBase Zp.first.codes Zp.first.shape rfl rfl (fun _ _ _ _ => rfl) hl
    hsub hlook b' hat hOk s s' rs gs hd z hfront
    (forms_dig_at h hl hsub hat hOk hd z hfront hshape hbook hr h0 hLeft) q hq'

/-- **`IM.HandsR` at the digits of every link, at the narrow fence with the sentence of leftOn l.**
Conditional on `P5J.AtMgA`; a link below 25; b being the member at the number. No instance of these
hypotheses is exhibited in this file. -/
theorem handsR_digits {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l true]? = some b) (z : ProofFile.InstPub) :
    IM.HandsR (fun k s => IM.RB cF Zp z k s ∧ (s.failed = none → k3LeftOnItemAt (At.X Zp) l s))
      (At.N Zp cF) IM.linksW IM.placesW (LPFK9.HandsAt.EW (𝔐).pubD baseP z) 0 (k3K l true) b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hpl : b.place = IM.k3Place l true := by
    have e1 := IM.place_at h.scope h.reads O hb
    rw [IM.placesW_full, K3Lot.k03_at_full l hl true] at e1
    exact (Option.some.inj e1).symm
  have M := madeOwed_digits h hl hb z
    (fun k s => IM.RB cF Zp z k s ∧ (s.failed = none → k3LeftOnItemAt (At.X Zp) l s))
    (fun _ hs => hs)
  have M' : IM.MadeOwed
      (fun k s => IM.RB cF Zp z k s ∧ (s.failed = none → k3LeftOnItemAt (At.X Zp) l s))
      (At.N Zp cF) IM.linksW IM.placesW (𝔐).pubD baseP z 0 (k3K l true) b b.place := M
  rw [← N₀_told Zp cF] at M' ⊢
  exact IM.rows_at_plan (p := z) h.scope h.reads O h.laid.planOk _ (fun _ _ _ => rfl) hb
    (by rw [hpl]; rfl) (fun s hs => IM.rb_wide s hs.1) M'

/-- **The five Boolean tests pass over the step's acceptance alone at the digits**, in the terms of
the files under Honest/Thread/. Conditional on `P5J.AtMgA`; a link below 25; b being the member at
the number; s being reached by the wrapped sub-protocols' steps; what the composed meaning's field
pubP says at leftOn l of s; the step's acceptance alone from s to s'; no mark at either; the five
tests at s. No instance of these hypotheses is exhibited in this file. -/
theorem xk_next_digits {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l true]? = some b) (z : ProofFile.InstPub) {s s' : TS}
    (hf : IM.RB cF Zp z (k3K l true) s) (hLeft : (mgAtAll h).pubP (.leftOn l) (z, s))
    (hy : IM.Yes 0 b s s') (h0 : s.failed = none) (h1 : s'.failed = none)
    (hx : IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l true) s = true) :
    IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l true + 1) s' = true := by
  have hL : k3LeftOnItemAt (At.X Zp) l s := by
    have h2 : (mgAll (𝔐) mgBase).pubP (.leftOn l) (z, s) := hLeft
    rw [(k3At_mgAll (𝔐) mgBase).pLeftOn] at h2
    exact h2
  rw [ep_is_ew h z, ← linksW_at, ← placesW_at] at hx ⊢
  exact (handsR_digits h hl hb z).step ⟨hf, fun _ => hL⟩ hy h0 h1 hx

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.digits_hd_of_yes
#print axioms ProofFile.Honest.K3.Law.Total.forms_dig_at
#print axioms ProofFile.Honest.K3.Law.Total.madeOwed_digits
#print axioms ProofFile.Honest.K3.Law.Total.handsR_digits
#print axioms ProofFile.Honest.K3.Law.Total.xk_next_digits
