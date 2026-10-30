-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/SaidBehind.lean: the kind "lookup" (K3). Conditional,
under the library's hypothesis `P5J.AtMgA`: what the public items say beside their Boolean tests
(the composed meaning's field pubP) holds behind the acceptance alone of the member's step, of every
public item that is open behind: at the lookup on the calls and at the lookup on the digits of every
one of the 25 links. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a state s bears no mark if `s.failed = none`. The
lookups' 50 members stand at the numbers `k3K l d` of the flat list
(Johnson/Desc/First/Look/K3Base.lean): l < 25 is the link; d is false for the lookup on the calls
and true for the lookup on the digits. The step's acceptance alone from s to s' is
`IM.Yes 0 b s s'` (Johnson/IMR/HandsDef.lean). The table is the table of borders
(Johnson/Desc/First/Borders.lean). The five tests are `IM.XK` (HandsDef.lean) at the public items'
test alone. The sentence of a public item is what the item says beside its test: the value of pubP
at it. The items left m and leftOn m are the public items `Pub.left m` and `Pub.leftOn m`
(Borders.lean). In the statements EP and SP are local notations: EP z k s is the public items' test
at border k (`ePubAt`), SP k the set of public items that are open at border k (`pubSets`). Five
more local notations: theQ and theP are `P.ofPlace` at the public record's setting, at the calls
(theQ at the place x; theP takes the place as its argument); PS is `flatPlacesOf linksFull true`,
the written list of places; 𝔐 is `AtMg.𝔇` at the head h (the composed meaning's data there). baseP
is the field pub of `mgBase`.

What is shown.
  `leftQ_front`: in front of the calls the ledger has its sizes and the place's number of slots, and
    is free from its next slot on (`LeftQ`, Johnson/Desc/First/Look/K3LeftItem.lean). It is stated
    for every value of the composed meaning's data and does not assume `h`.
  `left_behind_calls`: behind the acceptance the sentence of left l holds.
  `said_next_calls`: the whole at the calls. Of the state in front it assumes the five tests alone:
    not that it is reached, not that it bears no mark, no sentence.
  `said_next_digits`: the whole at the digits. Of the state in front it assumes the five tests and
    the sentences of the items open there; of these its proof uses those of the items leftOn m
    alone.
Which items say anything. At the composed meaning over the library's closed meaning beneath, the
items left m and leftOn m say the lookups' two sentences (`k3LeftItemAt`, `k3LeftOnItemAt`,
K3LeftItem.lean). Where the composed meaning's table says "no sentence is meant" the sentence holds
outright (`pubP_of_said`, Johnson/Desc/Sound/MgAt/K3CallsSaid.lean; its one hypothesis, that the
meaning beneath says its sentence wherever the table means none, holds by the text of the closed
meaning beneath, as Lean checks). By closed tests that the kernel evaluates, at all 25 links: behind
the calls every open item is left l or one of these (`callsSaidB_mgMore`, K3CallsSaid.lean); behind
the digits every open item is a left m, a leftOn m or one of these (`digSaid_mgMore`,
Johnson/Desc/Sound/MgAt/K3DigitsSaid.lean), no left m stands there, and a leftOn m stands there only
where it stands in front (`digTableB`, Johnson/Desc/First/Look/K3DigitsBehind.lean).
The statements are in the terms `P5J.At.N Zp cF`, `P5J.At.links`, `P5J.At.ps`, `P5J.mgAtAll h`. They
speak of the verifier's states alone: no thread, prover, coin, string, piece or transcript occurs in
them. They are the fellows, for the sentences, of `xk_next_calls`
(Honest/K3/Law/Total/HandsCalls.lean) and `xk_next_digits`
(Honest/K3/Law/Total/MadeOwedDigits.lean), which are on the tests.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hl`, `hb`: the link is below 25; b is the member at the number `k3K l d`.
  `hy`: the step's acceptance alone, from s to s'.
  `hx`: the five tests hold at s.
  `hQ`: (in `said_next_digits`) the sentences of the public items that are open at s hold.
  `hsP`, `hIn`, `hns`, `hFree`: (in `leftQ_front`) the place's parameters make its shape; the
    lookup's promise in front (`k3OnIn`, Johnson/Desc/First/Look/K3Borders.lean) holds; the built
    link has the place's number of slots; the public item freeAbove l holds at s.
  `hlook`, `hsP`, `hns`, `hfront`: (in `left_behind_calls`) y is the lookup's place; its parameters
    make its shape; the built link has its number of slots; the public tests in front hold at s
    (`frontAtK`, Johnson/Desc/Sound/MgAt/K3CallsTable.lean).

Imported. Honest/K3/Law/Total/MadeOwedDigits.lean, beneath which lie eleven more files of
Honest/K3/Law/Total/: the files on the library's `IM.MadeOwed` (Johnson/IMR/MadeOwed.lean: "the debt
of a kind's authors at one of its places"). Besides, files of the library. No module under
Johnson/Goal/ is imported directly.
Follows. The proof of `leftQ_front` takes over, token for token but for the state's letter, the
library's own lines inside `othersPub_lay_mgAll` (Johnson/Desc/Sound/MgAt/K3CallsOthers.lean). The
proof of `said_next_digits` follows the library's own lines on the sentences in K3DigitsBehind.lean:
`leftOn_stays` (K3LeftItem.lean) over what the acceptance leaves (`k3_digits_step_leaves`,
Johnson/Desc/First/Look/K3DigitsStep.lean).

How the proof goes. `left_behind_calls` calls the library's `k3_calls_leftItem_anyWords`
(Johnson/Top/H/Keep/K3LeftAnyWords.lean), which holds whatever the rounds' words are.

Users. `step_calls_whole` and `step_digits_whole` (Honest/K3/Law/Total/StepWhole.lean) call
`said_next_calls` and `said_next_digits`. These are stated so as to meet what, for the
files under Honest/Thread/, a kind's lemma may assume of the state in front: no mark; the
Boolean tests; the samples; pubP of every public item that is open there. The terms
`P5J.At.N Zp cF`, `P5J.At.links`, `P5J.At.ps` and `P5J.mgAtAll h` are those in which the statements
were asked for.

Options. `maxRecDepth` is raised to 100000 for the file; `maxHeartbeats` to 4000000 in front of
three theorems; `quotPrecheck` is off at four local notations. These raise limits on Lean's own work
or switch off a check on a notation's names: none loosens a check on a proof.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
`P5J.AtMgA` is a hypothesis. Nothing on the samples, on "in order" or on the witness. At the full
size alone.
Not shown here: by the table's own text the lookup on the calls makes left l; the calling kind's own
member behind it drops that item and makes leftOn l; three more members stand between that one and
the lookup on the digits. That the sentence of leftOn l is made there and carried to the digits is
not shown here: these four members are not the lookups'. The table's own row of the lookup on the
digits (`pubRowOf`, Borders.lean) neither asks, makes nor drops leftOn m; `said_next_digits` assumes
its sentence in front all the same.
The files under Honest/Thread/ are not imported here;
see the head of Honest/K3/Law/Total/NoMarkBehind.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.MadeOwedDigits
import Johnson.Desc.Sound.MgAt.K3CallsSaid
import Johnson.Desc.Sound.MgAt.K3DigitsSaid
import Johnson.Top.H.Keep.K3LeftAnyWords
import Johnson.Desc.First.BordersSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning shift pubSets pubStep pubRowM ePubAt)
open P5J

section
variable {Xi Pz Tok : Type} {rows cols₀ nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi Pz Tok rows cols₀ nR X)
  (Mg : Meaning Pz (Desc.Wit (CellsQ rows cols₀) Tok MsgT)) {l : ℕ} {x : Desc.First.Look.Place}

local notation "theQ" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **In front of the calls the ledger has its sizes and the place's number of slots, and is free
from its next slot on.** Conditional on the place's shape, the lookup's promise and freeAbove in
front, and the built link having the place's number of slots. No instance of these hypotheses is
exhibited in this file. -/
theorem leftQ_front {s : Desc.First.S} (hsP : (theQ).shape = some x.fs)
    (hIn : Desc.K3.k3OnIn theQ s = true) (hns : (Dm.built[l]?).map (·.ns) = some (theQ).ns)
    (z : Pz) (hFree : (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true) :
    ∃ F, s.fork? = some F ∧ LeftQ (theQ).ns F := by
  obtain ⟨F, hF, hz, -, -⟩ := k3OnIn_free hsP hIn
  refine ⟨F, hF, ?_⟩
  have f1 : ((Dm.pubD.nsOf l).any fun n => Desc.First.freeAboveB n s) = true := hFree
  have hns' : Dm.pubD.nsOf l = some (theQ).ns := hns
  rw [hns', Option.any_some, freeAboveB_is] at f1
  unfold freeAboveAtB at f1
  simp only [Bool.and_eq_true] at f1
  have f2 := f1.2
  rw [hF] at f2
  simp only [Option.any_some, beq_iff_eq] at f2
  have f3 := f1.1
  unfold freeAboveB at f3
  rw [hF] at f3
  simp only [Option.any_some, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at f3
  refine ⟨hz, f2, fun j hj hlt => ?_⟩
  have q0 := f3 (j - F.next) (by omega)
  rw [show F.next + (j - F.next) = j by omega] at q0
  exact q0

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "𝔐" => AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)
set_option quotPrecheck false in
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) false
local notation "baseP" => Desc.First.Meaning.pub (mgBase : Desc.First.Meaning ProofFile.InstPub
  (Desc.Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
set_option quotPrecheck false in
local notation "EP" => fun (z : ProofFile.InstPub) (k : ℕ) (s : TS) =>
  ePubAt (mgAtAll h).pub (mgAtAll h).more At.links At.ps k (z, s)
set_option quotPrecheck false in
local notation "SP" => fun (k : ℕ) => (pubSets (mgAtAll h).more At.links At.ps)[k]?.getD []

set_option maxHeartbeats 4000000 in
/-- **Behind the step's acceptance alone, at the calls, the sentence of left l holds.** Conditional
on `P5J.AtMgA`; a link below 25; the place, its shape, its number of slots; b being the member at
the number; the acceptance alone of its step; the public tests in front. No instance of these
hypotheses is exhibited in this file. -/
theorem left_behind_calls {l : ℕ} (hl : l < 25) {y : Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l false = some y) (hsP : (theP y).shape = some y.fs)
    (hns : ((𝔐).built[l]?).map (·.ns) = some (theP y).ns) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) {s s' : TS} (hy : IM.Yes 0 b s s')
    (hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll (𝔐) mgBase).pub q (z, s) = true) :
    k3LeftItemAt (At.X Zp) l s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hpcW, P', sent, laid, rs, gs, hP, hd⟩ :=
    calls_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy
  rw [O.W] at hpcW hP
  have eP : P' = theP y := by
    have e0 : placeAt (At.X Zp) l false = some P' := hP
    unfold placeAt at e0
    rw [hlook] at e0
    exact (Option.some.inj e0).symm
  subst eP
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full l hl
  obtain ⟨hIn, hFree, -⟩ := front_three (𝔐) mgBase (a := IM.k3Place l false) s rfl hpcW hpc hl hs'
    (calls_tests hl).1 hlook rfl (hfit_mgAll (𝔐) mgBase rfl) z hfront
  obtain ⟨F, hF, hQ⟩ := leftQ_front (𝔐) mgBase hsP hIn hns z hFree
  exact ⟨_, hP, k3_calls_leftItem_anyWords K3Lot.ofForm _ laid sent _ [] s s' rs gs hsP hd hF hQ⟩

set_option maxHeartbeats 4000000 in
/-- **The sentences behind the calls.** Conditional on `P5J.AtMgA`; a link below 25; b being the
member at the number; the acceptance alone of its step from s to s'; the five Boolean tests at s.
No instance of these hypotheses is exhibited in this file. -/
theorem said_next_calls {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) {s s' : TS} (hy : IM.Yes 0 b s s')
    (hx : IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l false) s = true) :
    ∀ p ∈ SP (k3K l false + 1), (mgAtAll h).pubP p (z, s') := by
  intro p hp
  rw [ep_is_ew h z, ← linksW_at, ← placesW_at] at hx
  have ek : k3K l false = kOfCalls l := (kOfCalls_border l).symm
  have hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll (𝔐) mgBase).pub q (z, s) = true := by
    rw [← ek]
    exact front_of_xk (At.N Zp cF) (𝔐).pubD baseP z (k3K l false) s hx
  have hp1 : p ∈ (pubSets mgMore linksFull PS)[k3K l false + 1]?.getD [] := by
    have e : (mgAtAll h).more = mgMore := mgAll_more_closed (𝔐) mgBase rfl
    rw [e] at hp
    exact hp
  rw [Desc.First.pubSets_succ mgMore linksFull PS (k3K l false) (IM.k3Place l false)
    (K3Lot.k03_at_full l hl false), ek] at hp1
  have hrow := List.all_eq_true.1 callsSaidB_mgMore l (List.mem_range.2 hl)
  unfold callsSaidRowB at hrow
  rw [(calls_tests hl).1, Option.any_some] at hrow
  have h1 := List.all_eq_true.1 hrow p hp1
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · obtain rfl : p = .left l := eq_of_beq h1
    show (mgAll (𝔐) mgBase).pubP (.left l) (z, s')
    rw [(k3At_mgAll (𝔐) mgBase).pLeft]
    rcases Nat.lt_or_ge l 24 with h24 | h24
    · rcases Nat.mod_two_eq_zero_or_one l with he | ho
      · obtain ⟨y, _, hy', -⟩ := layAt_scope h.scope h.reads h.pubOne h24 he
        exact left_behind_calls h hl (k03_look_lay h hl hy') (k03_shape_lay hy')
          (k03_slots_lay h h24 hy') hb z hy hfront
      · obtain ⟨y, a, -, -, hy', -⟩ :=
          attAt_scope h.scope h.reads h.pubOne h24 ho (𝔐).sent (fun _ => 0)
        exact left_behind_calls h hl (k03_look_att h hl hy') (attAt_shape hy')
          (k03_slots_att h h24 hy') hb z hy hfront
    · obtain rfl : l = 24 := by omega
      exact left_behind_calls h hl (k03_look_head h) (k03_shape_head h) (k03_slots_head h) hb z hy
        hfront
  · exact pubP_of_said (𝔐) mgBase (fun _ _ hq => hq) p h1 (z, s')

set_option maxHeartbeats 4000000 in
/-- **The sentences behind the digits.** Conditional on `P5J.AtMgA`; a link below 25; b being the
member at the number; the acceptance alone of its step from s to s'; the five Boolean tests at s;
the sentences of the public items that are open at s. No instance of these hypotheses is exhibited
in this file. -/
theorem said_next_digits {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l true]? = some b) (z : ProofFile.InstPub) {s s' : TS} (hy : IM.Yes 0 b s s')
    (hx : IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l true) s = true)
    (hQ : ∀ p ∈ SP (k3K l true), (mgAtAll h).pubP p (z, s)) :
    ∀ p ∈ SP (k3K l true + 1), (mgAtAll h).pubP p (z, s') := by
  intro p hp
  rw [ep_is_ew h z, ← linksW_at, ← placesW_at] at hx
  have eM : (mgAtAll h).more = mgMore := mgAll_more_closed (𝔐) mgBase rfl
  have hfront : ∀ q ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub q (z, s) = true :=
    front_of_xk (At.N Zp cF) (𝔐).pubD baseP z (k3K l true) s hx
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', rs, gs, hat, hOk, hd⟩ :=
    digits_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy
  rw [O.W] at hat
  obtain ⟨sub, hsub, -, -⟩ := K3Lot.k03_sub_full l hl
  obtain ⟨hpc, -, -, -, F, hF, hSz⟩ := dig_front h hl hsub hat z hfront
  obtain ⟨F', Gk, hF', hG, hLk, hrest, -⟩ := k3_digits_step_leaves K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes Zp.first.shape (IM.k3Place l true) b' hat
    hOk l rfl hpc s s' rs gs hd
  obtain rfl : F' = F := Option.some.inj (hF'.symm.trans hF)
  obtain ⟨hLat, hSzG, -⟩ := hrest hSz
  have hp1 : p ∈ (pubSets mgMore linksFull PS)[k3K l true + 1]?.getD [] := by
    rw [eM] at hp
    exact hp
  rw [Desc.First.pubSets_succ mgMore linksFull PS (k3K l true) (IM.k3Place l true)
    (K3Lot.k03_at_full l hl true)] at hp1
  have hTab := hTab_mgAll (𝔐) mgBase rfl l hl sub hsub
  rw [mgAll_more_closed (𝔐) mgBase rfl] at hTab
  unfold digTableB at hTab
  rcases pubP_cases p with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨h1, h2⟩
  · have ht := List.all_eq_true.1 hTab _ (List.mem_append_left _ hp1)
    simp [k3Like, digAllowedB] at ht
  · have ht := List.all_eq_true.1 hTab _ (List.mem_append_left _ hp1)
    simp only [k3Like, Bool.not_true, Bool.false_or, digAllowedB, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ht
    have hQm : Desc.First.Pub.leftOn m ∈ (pubSets mgMore linksFull PS)[k3K l true]?.getD [] := by
      rcases ht with hc | ⟨hQm, -⟩
      · cases hc
      · exact hQm
    have hfp : (mgAll (𝔐) mgBase).pubP (.leftOn m) (z, s) := hQ _ (by
      rw [eM]
      exact hQm)
    rw [(k3At_mgAll (𝔐) mgBase).pLeftOn] at hfp
    obtain ⟨pp, hpp, Lp⟩ := hfp
    show (mgAll (𝔐) mgBase).pubP (.leftOn m) (z, s')
    rw [(k3At_mgAll (𝔐) mgBase).pLeftOn]
    exact ⟨pp, hpp, leftOn_stays hLk hF hG hLat hSzG Lp⟩
  · have hrow := List.all_eq_true.1 digSaid_mgMore l (List.mem_range.2 hl)
    unfold digSaidRowB at hrow
    have h0 := List.all_eq_true.1 hrow p hp1
    rw [Bool.or_eq_true] at h0
    rcases h0 with h0 | h0
    · cases p with
      | left m => exact absurd rfl (h1 m)
      | leftOn m => exact absurd rfl (h2 m)
      | _ => cases h0
    · exact pubP_of_said (𝔐) mgBase (fun _ _ hq => hq) p h0 (z, s')

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.leftQ_front
#print axioms ProofFile.Honest.K3.Law.Total.left_behind_calls
#print axioms ProofFile.Honest.K3.Law.Total.said_next_calls
#print axioms ProofFile.Honest.K3.Law.Total.said_next_digits
