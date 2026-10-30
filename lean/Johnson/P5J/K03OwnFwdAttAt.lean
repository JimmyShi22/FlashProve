-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03OwnFwdAttAt.lean: THE KIND "LOOKUP" (K3), AT THE DIGITS' LOOKUPS OF THE TWELVE
ATTENTION SEGMENTS, AT THE COMPOSED MEANING's OWN PARAMETERS: THE CALLING KIND's OWN THREE RUNS
("first", "keys", "second") GO FORWARD ACROSS AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL. Two
theorems; no new lemma on the runs.
  `k03_fwd_att_front`: THE STRONGER FORM: FROM THE PROMISE IN FRONT, "REACHED" AND NO MARK: no
    hand on the state
    behind but the accept itself. (So the item "own" of the digits' public tests, which is a part of
    what shows the promise behind, may call it.)
  `k03_fwd_att`: the same in the form of `DigFwdR h (2 * g + 1) b' [(2, "first"),
    (2, "keys"), (2, "second")]` (Johnson/P5J/K03Due7.lean) UNFOLDED: the end is made by program off
    that abbreviation's text: = the lookup's files' premise hOwn
    (Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean) at these parameters. Its hand "the promise behind"
    is not spent.
THE ROAD. The plan A at group g (`IM.ground_tails`) · what the link states at its second
sub-protocol IS runsN A, the seat's guard struck:
`K05_states_raw_of_open` (Johnson/H2K5R/StatesRawAtOpen.lean) · the readers: `k03_hlink` · off the
head's link the second hole is silent (holesAt's text) · in front the part is an attention's
(`here_att_of_stand`, `k03_stand_dig`) and its ledger is there and sized (`led_mgAll`) · ACROSS THE
WHOLE SEATED ACCEPT: `k3_digits_step_attSame`, `k3_digits_step_pass` · `runsN_same`
(Johnson/Top/H/Keep/AttOwnSame.lean) · `link_fwd` (Johnson/Top/H/Keep/FormsPassK3.lean). NOT SPENT:
AttOwnSame.lean's `own_formsIn_pass` and `k3_digits_runsN_same` (the second stands at the decision's
own accept). WHAT STAYS A PREMISE: the head AtMgA · the filling with its three equations.
WHICH `here_att_of_stand`: VerifiableInference.Desc.K1's (Johnson/Desc/K1/Law/ArmAtReads.lean),
written in full in the proof; another file declares a constant of the same short name and sentence
(Johnson/Desc/Sound/MgAt/K3DigitsPlanesIt.lean).
Limits. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03RidesDigAt2
import Johnson.Top.H.Keep.AttOwnSame
import Johnson.Desc.First.Look.K3DigitsCallersStay
import Johnson.H2K5R.StatesRawAtOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart)
open VerifiableInference.Desc.K9 (holesAt statesOfLink readersOfLink)
open VerifiableInference.Desc.First.Att.P (runsN K05_states_raw_of_open)
open VerifiableInference.Reads.Pass (Fwd)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **THE CALLING KIND's OWN THREE RUNS GO FORWARD, AT ATTENTION's TWELVE: FROM THE PROMISE IN
FRONT, "REACHED" AND NO MARK.** -/
theorem k03_fwd_att_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ g < 12, ∀ b',
    k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g + 1) true = some b' →
    ∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g + 1) true) u →
      h.toAtMg.rch (k3K (2 * g + 1) true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "first"), (2, "keys"), (2, "second")],
        Fwd ((h.toAtMg.𝔇 h.𝔇).Rd (2 * g + 1)) p.1 p.2 u.1 v.1 := by
  intro g hg b' hb' z u v hu hr hm hR p hp
  have hl : 2 * g + 1 < 25 := by omega
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hsub : linksFull[2 * g + 1]? = some ModelPart.attention := by
    have h0 := List.all_eq_true.1 linksAttFull g (List.mem_range.2 hg)
    simpa using h0
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨hT, -⟩ := IM.ground_tails h.scope h.reads O.pub O.blank
  obtain ⟨-, A, -, -, -, hA, -⟩ := hT g hg
  obtain ⟨Lk, hLk, hSt⟩ := K05_states_raw_of_open O (by rw [hW]; exact hp4)
    (by rw [hW]; exact hN ▸ hg) hA
  obtain ⟨w₀, hw⟩ := VerifiableInference.Desc.K1.here_att_of_stand
    (k03_stand_dig h hl hsub z u hu (Classical.not_not.1 hm))
  obtain ⟨F, hF, hSz⟩ := led_mgAll (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch rfl hl hsub
    z u hu hr hm
  have eF : w₀.F = F := by
    have h0 := hF
    simp only [VerifiableInference.Desc.First.S.fork?, hw] at h0
    exact Option.some.inj h0
  obtain ⟨rs, gs, hd⟩ := id hR
  obtain ⟨w, hw', hg', h5, HS, hwd⟩ := k3_digits_step_attSame K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes Zp.first.shape
    (IM.k3Place (2 * g + 1) true) b' hb' (Pc.planOk (2 * g + 1) hl true b' hb') (2 * g + 1) rfl
    (k03_pieceAt_dig h.toAtMg (2 * g + 1)) u.1 v.1 rs gs hd hw (by rw [eF]; exact hSz)
  obtain ⟨G, Q⟩ := k3_digits_step_pass K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place (2 * g + 1) true) b' hb'
    (Pc.planOk (2 * g + 1) hl true b' hb') (2 * g + 1) rfl (k03_pieceAt_dig h.toAtMg (2 * g + 1))
    u.1 v.1 rs gs hd hF hSz
  have hsame := runsN_same A hw hw' hg' h5 HS hwd hF Q.behind Q.trees
  have hsil : ∀ (b : ℕ) (n : String) (s : VerifiableInference.Desc.First.S),
      (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g + 1) Lk).silent b n s = none := by
    intro b n s
    have hne : ¬ ((2 * g + 1 == 24) = true) := by
      rw [beq_iff_eq]
      omega
    unfold holesAt
    rw [h24]
    dsimp only
    rw [if_neg hne]
  have key : ∀ name : String, name ≠ "join" → (name == "K8.equations") = false →
      Fwd (readersOfLink (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g + 1) Lk) Lk) 2 name u.1
        v.1 := by
    intro name hj hn
    refine link_fwd _ Lk 2 hn (hsil 2 name u.1) fun nm r hfr => ?_
    rw [hSt] at hfr
    have hym := List.mem_of_find?_eq_some hfr
    have hyn : nm = name := by simpa using List.find?_some hfr
    exact hsame (nm, r) hym (hyn ▸ hj)
  rw [k03_hlink h (2 * g + 1) Lk hLk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact key "first" (by decide) (by decide)
  · exact key "keys" (by decide) (by decide)
  · exact key "second" (by decide) (by decide)

/-- **THE CALLING KIND's OWN THREE RUNS GO FORWARD, AT ATTENTION's TWELVE**: in the form of rides'
premise, whose hand "the promise behind" is not spent. -/
theorem k03_fwd_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ g < 12, ∀ b',
    k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g + 1) true = some b' →
    ∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g + 1) true) u →
      h.toAtMg.rch (k3K (2 * g + 1) true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g + 1) true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "first"), (2, "keys"), (2, "second")],
        Fwd ((h.toAtMg.𝔇 h.𝔇).Rd (2 * g + 1)) p.1 p.2 u.1 v.1 :=
  fun g hg b' hb' z u v hu hr hm _ hR =>
    k03_fwd_att_front h 𝔏 q₁ q₂ q₃ g hg b' hb' z u v hu hr hm hR

end P5J

#print axioms P5J.k03_fwd_att_front
#print axioms P5J.k03_fwd_att
