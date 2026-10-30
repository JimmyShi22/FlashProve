-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/DigitsFormsLay.lean: the kind "lookup" (K3). Conditional,
under the library's hypothesis `P5J.AtMgA`: the kept public test formsIn l 3 "own" (the feed-forward
kind's two runs "front" and "back") holds behind an acceptance of the lookup on the digits of a
layers' link. Said of two states of the verifier. One theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: a test "formsIn" is the Boolean test of a public item
`Pub.formsIn l pc nm` (Johnson/Desc/First/Borders.lean), for the run of claims named nm at piece pc
of link l; a kept test is one of `keptDigits`, the new one is `newDigits`
(Johnson/Desc/Sound/MgAt/K3DigitsSorted.lean). The stated sub-protocol at the digits' address is
`k3Const … l true` (Johnson/Desc/First/Look/K3Base.lean). The tests in front are the list
`frontDig mgMore l` (K3DigitsSorted.lean). The sentence of the item leftOn l is the library's
`k3LeftOnItemAt` (Johnson/Desc/First/Look/K3LeftItem.lean).

What is shown.
  `own_dig_lay`: the kept "own" behind the acceptance, at a layers' link. It is the last of the live
    tests "formsIn": the fellow of those in Honest/K3/Law/Total/DigitsFormsFour.lean,
    Honest/K3/Law/Total/DigitsFormsOwn.lean and Honest/K3/Law/Total/DigitsFormsNew.lean.
The statement speaks of no thread, piece, transcript or string, nor of the table's promise as a
whole.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hb`, `hOk`, `hd`: b' is the stated sub-protocol at the digits' address; it passes its test on the
    plan; its decision accepts from s to s'.
  `hfront`: the public tests that are open or tied in front hold at s.
  `hl`, `hsub`: the link is below 25; it is a layers' link.
  `hr`: s is reached by the wrapped sub-protocols' steps (`Reach`, Johnson/Top/H0/Walk/Reach.lean).
  `hLeft`: what the item leftOn l says of s holds: a sentence, not a Boolean test.

Imported. DigitsFormsFour.lean and files of the library. No module under Johnson/Goal/ is imported
directly.
Follows. Two proofs of the library's are followed from the decision's acceptance on and set end
to end. (α) `hOwn_of_below_front` (Johnson/Desc/Sound/MgAt/K3DigitsStaysBelowFront.lean):
the two runs go forward over the acceptance. (β) `P5J.k03_ownIt_lay`
(Johnson/P5J/K03OwnItLayAt.lean): so the test passes. Both stand under the table's whole promise
in front, with strings; (β) at a piece's acceptance.

How the proof goes. What these two use of the promise in front, and what stands for it here: (1) two
of the feed-forward kind's three windows lie below the ledger's next slot, and what the lookup on
the calls was heard to return is what that kind's hearing bears: the library's own lemma for it does
not read the promise (`wins_reached`, Johnson/Road/K4/InT/WinsReached.lean): from "reached", `hr`;
(2) the test lookOut at the calls' piece: `hfront`; (3) what the item leftOn l says of the state in
front: `hLeft`; (4) the kept test itself in front: `hfront`; (5) the third window: (β) takes it from
the promise (`k03_win_front`, Johnson/P5J/K03WinAt.lean); here it comes with the two others out of
the library's `windows_of_leaves` (Johnson/Desc/Sound/MgAt/K3DigitsStaysBelow.lean), as in (α).

Users. `forms_dig_at` (Honest/K3/Law/Total/MadeOwedDigits.lean) calls it.

Options. `maxRecDepth` is raised to 100000 for the file; `maxHeartbeats` to 4000000 in front of one
theorem; `quotPrecheck` is off at one local notation. These raise limits on Lean's own work or
switch off a check on a notation's names: none loosens a check on a proof.

Limits. An implication. No instance of these hypotheses is exhibited in this file. At a layers'
link. At the full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.DigitsFormsFour
import Johnson.Desc.Sound.MgAt.K3DigitsStaysBelowFront
import Johnson.P5J.K03OwnItLayAt
import Johnson.P5J.K03MergeAt
import Johnson.Road.K4.InT.WinsReached

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift LayOwn)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink holesAt formsIn)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Road.K4.InT (k4_runSame_below StatesAt wins_reached)
open OnBytes.Model.Layer (Own)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "𝔐" => AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)

set_option maxHeartbeats 4000000 in
/-- **The kept "own" behind the acceptance, at a layers' link.** Conditional on `P5J.AtMgA`; the
acceptance of the stated sub-protocol's decision; the public tests in front; s being reached; what
the item leftOn l says of s. No instance of these hypotheses is exhibited in this file. -/
theorem own_dig_lay {l : ℕ} (hl : l < 25) (hsub : linksFull[l]? = some ModelPart.layers)
    {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hOk : b'.planOk = true) {s s' : TS} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : b'.decide s rs gs = .ok s') (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, s) = true)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l true) (z, s))
    (hLeft : k3LeftOnItemAt (At.X Zp) l s) :
    (mgAll (𝔐) mgBase).pub (.formsIn l 3 "own") (z, s') = true := by
  have he : l % 2 = 0 ∧ l < 24 := by
    rcases Nat.lt_or_ge l 24 with h24 | h24
    · rcases Nat.mod_two_eq_zero_or_one l with he | ho
      · exact ⟨he, h24⟩
      · exact absurd (hsub.symm.trans (links_att l h24 ho)) (by simp)
    · obtain rfl : l = 24 := by omega
      exact absurd hsub (by decide)
  obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
  have hg : g < 12 := by omega
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hpc, -⟩ := dig_front h hl hsub hb z hfront
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  -- (1) the windows, from "reached"
  have hr' := reach_raw hr
  rw [digits_number g hg] at hr'
  obtain ⟨al, o, hal, ho, hSz, w1, w3, hT⟩ :=
    wins_reached h.scope h.reads O h.laid.planOk hg hr'
  have hF : s.fork? = some al.F := by simp [Desc.First.S.fork?, hal]
  -- (2) (3) what the lookup on the calls left
  obtain ⟨s2, hs2, a2, a3⟩ := K3Lot.k03_sub_full (2 * g) hl
  have hFr := List.all_eq_true.1 planesFront_mgMore (2 * g) (List.mem_range.2 hl)
  unfold planesFrontRowB at hFr
  rw [Bool.and_eq_true] at hFr
  have m1 : Desc.First.Pub.lookOut (2 * g) (IM.k3Place (2 * g) false).piece ∈
      frontDig mgMore (2 * g) := by
    simpa using hFr.1
  have ePc : (IM.k3Place (2 * g) false).piece = Desc.K3.pieceAt (At.X Zp) (2 * g) false := by
    have a1 := pieceAt_calls (At.X Zp) (2 * g)
    omega
  obtain ⟨pc, hpcAt, hLf⟩ := hLeft
  have hO : Desc.K3.k3OnOut pc s = true := by
    have h0 := hfront _ m1
    rw [ePc] at h0
    have h1 := ((k3At_mgAll (𝔐) mgBase).lookOut (2 * g) false _).symm.trans h0
    unfold k3OnOutAt at h1
    rw [hpcAt] at h1
    exact h1
  have hdc : pc.digits = false := by
    unfold placeAt at hpcAt
    obtain ⟨y', -, rfl⟩ := Option.map_eq_some_iff.1 hpcAt
    rfl
  have hW := windows_of_leaves hdc hal hO hLf
    (fun o' ho' => by
      obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
      exact hT)
    (fun o' ho' => by
      obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
      exact ⟨w1, w3⟩)
  have Kb := k4StaysBelow_of_digits K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place (2 * g) true) b' hb hOk (2 * g) rfl hpc s s' rs gs hd
    hal hSz hW
  have W : ∀ (a : LayOwn) (o' : Own), s.here = .lay a → a.own = some o' →
      o'.H.tV.p.first + o'.H.tV.p.walk.1.length ≤ al.F.next ∧
      o'.H.fo.leaves.first + o'.H.fo.leaves.walk.1.length ≤ al.F.next ∧
      o'.wo.toWsMerged.p.first + o'.wo.toWsMerged.p.walk.1.length ≤ al.F.next := by
    intro a o' ha ho'
    obtain rfl : a = al := by
      have := ha.symm.trans hal
      injection this
    exact hW o' ho'
  obtain ⟨G, Pq⟩ := k3_digits_step_pass K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place (2 * g) true) b' hb hOk (2 * g) rfl hpc s s' rs gs hd
    hF hSz
  obtain ⟨Lk, hLk⟩ := k03_link_some h hl
  obtain ⟨pK, hSt⟩ := k03_states_lay h hg Lk hLk
  have hRd := k03_hlink h (2 * g) Lk hLk
  have hsil : ∀ (b : ℕ) (n : String) (t : TS),
      (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g) Lk).silent b n t = none := by
    intro b n t
    unfold holesAt
    rw [h24]
    dsimp only
    rw [if_neg (by rw [beq_iff_eq]; omega)]
  -- (α) the two runs go forward
  have fwd : ∀ name, name = "front" ∨ name = "back" → Fwd ((𝔐).Rd (2 * g)) 2 name s s' := by
    intro name hn
    rw [hRd]
    exact link_fwd _ Lk 2 (by rcases hn with rfl | rfl <;> decide) (hsil 2 name s)
      fun nm r hfr => by
        obtain ⟨y, runC, hy, hC, e1⟩ := hSt name hn s
        obtain ⟨y', runC', hy', hC', e2⟩ := hSt name hn s'
        obtain rfl : y = (nm, r) := Option.some.inj (hy.symm.trans hfr)
        obtain rfl : y' = (nm, r) := Option.some.inj (hy'.symm.trans hfr)
        obtain rfl : runC' = runC := Option.some.inj (hC'.symm.trans hC)
        exact runSame_congr e1 e2 (k4_runSame_below hn hC Kb)
  -- (β) so the test passes
  have key : ∀ name, name = "front" ∨ name = "back" →
      formsIn ((𝔐).Rd (2 * g)) ((𝔐).N.group (2 * g)) 2 name s = true →
      formsIn ((𝔐).Rd (2 * g)) ((𝔐).N.group (2 * g)) 2 name s' = true :=
    fun name hn hin => k3_formsIn_fwd Pq _ _ 2 name (fwd name hn)
      (fun R hR => by
        rw [hRd] at hR
        exact k4_low _ Lk 2 hn (hsil 2 name s) (hSt name hn s) hF hSz W hR) hin
  have mOwn : Desc.First.Pub.formsIn (2 * g) 3 "own" ∈ keptDigits (2 * g) .layers := by
    simp [keptDigits]
  have ht := hfront _ ((digits_sorted hl hsub).2 _ mOwn)
  have eR : (𝔐).pubD.runs (2 * g) 3 "own" = [(2, "front"), (2, "back")] := by
    show runsAt linksFull (2 * g) 3 "own" = _
    rw [runsAt_of linksFull (2 * g) .layers hsub]
    rfl
  rw [mgAll_pub, VerifiableInference.Desc.First.pubAll_formsIn, eR] at ht ⊢
  have tF := List.all_eq_true.1 ht (2, "front") (by simp)
  have tB := List.all_eq_true.1 ht (2, "back") (by simp)
  refine List.all_eq_true.2 fun p hp => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact key "front" (Or.inl rfl) tF
  · exact key "back" (Or.inr rfl) tB

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.own_dig_lay
