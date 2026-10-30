-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03RidesDigAt2.lean: THE KIND "LOOKUP" (K3): WHAT RIDES PAST THE LOOKUP ON A SEGMENT's
DIGITS, AT ATTENTION's TWELVE SEGMENTS AND AT THE OUTPUT HEAD's, AT THE CLOSED CONSTANT, FROM
PREMISES ON THE STATES THAT ARE NOT SHOWN AT THE CONSTANT: UNTIL THEY HAVE PAYERS THE THIRTEEN
ROWS BUY NOTHING. The sisters of `k03_rides_dig_layers` (Johnson/P5J/K03RidesDigAt.lean), by one
call each of `ridesAtR_digits_att` and `ridesAtR_digits_head`
(Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean). One closed test with code and six theorems: two by
the kernel (one a negative test), the others joinings.
  `linksAttFullB`, `linksAttFull`, `linksAttFull_control`: the odd segments below 24 of the
    written list are attention's; segment 0 is not.
  `k03_lk_at`: where the head's own chain has a link Lk at m, the parameters' reader of links
    answers it. `k03_stand_dig`: under the promise in front of a segment's digits, without a mark:
    the state stands in an open link of the segment's sort (so its own part is of that sort:
    `here_att_of_stand`, `here_head_of_stand`,
    Johnson/Desc/K1/Law/ArmAtReads.lean, ArmHeadJ.lean: called).
  `k03_rides_dig_att`, `k03_rides_dig_head`: the fields.
What is paid beyond the layers' list: which sort is open (hHere: the promise's own test on where
the state stands) · the find at "planes" (`k03_planes_raw`,
Johnson/Desc/First/Look/K03StatesRaw.lean, at the lot's readers: at attention by
`readersAt_att`, Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean; at the head by `public_third`,
Johnson/Desc/Kinds/Law/ReadsNamed.lean: the plan names the array of reads as array 0) · at
attention: the second hole's silence at four runs · the first hole is `smallReader` (by
unfolding).
WHAT STAYS IN FRONT, EACH IN THE TWO THEOREMS' OWN TEXT. AT ATTENTION, THREE: hfJ (what the link
states at block 2 under "join" is the lookup's run at the plan's keys) · hWin (the window of the
sumcheck over the leaves is free and ends at or below the ledger's next slot) · hOwn (the calling
kind's runs "first", "keys", "second" go forward). AT THE HEAD, SEVEN: hrO, hrG, hrP (the run
itself answers in front) · hWin · hJoin · hOwn ("norm", "policy", "logits") · hWt (the sentence on
the weights goes back: it reads the state). And that `digAt` answers, and at attention that the
plan is there: binders on public data.
Limits: joinings. The head h and the free letters' three equations are premises. The full size
alone. No soundness is claimed.

-/
import Johnson.P5J.K03RidesDigAt
import Johnson.Desc.Sound.MgAt.K3RidesDigFwd2
import Johnson.IMR.SeatOpen
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Desc.K1.Law.ArmAtReads
import Johnson.Desc.K1.Law.ArmHeadJ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Item ModelPart start standOf standAt shapeAt)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.K9 (holesAt smallReader statesOfLink readerOf)
open VerifiableInference.Desc.First.Att.P (readersOfO keysOfO)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)
open VerifiableInference.Reads.Pass (Fwd)

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- The odd segments below 24 of the written list are attention's. -/
def linksAttFullB : Bool :=
  (List.range 12).all fun g => linksFull[2 * g + 1]? == some ModelPart.attention

theorem linksAttFull : linksAttFullB = true := by decide +kernel

/-- **A negative test.** -/
theorem linksAttFull_control : (linksFull[0]? == some ModelPart.attention) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- The parameters' reader of links answers the head's own chain's. -/
theorem k03_lk_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (m : ℕ)
    (Lk : Link VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim)
    (hl : cF.links[m]? = some Lk) : (h.toAtMg.𝔇 h.𝔇).lk m = some Lk :=
  (h.laid.linkAt m).trans hl

/-- **Where the state stands in front of a segment's digits.** -/
theorem k03_stand_dig (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {sub : ModelPart} (hsub : linksFull[l]? = some sub) (z : ProofFile.InstPub)
    (u : VerifiableInference.Desc.First.S × (FrD).E.Str)
    (hu : onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
      (k3K l true) u) (hm : u.1.failed = none) : standOf u.1 = .link sub := by
  have OP := onParts_of_on _ _ _ _ (fun s : VerifiableInference.Desc.First.S => (z, s)) _ u hu hm
  have hs : shapeAt linksFull (PS)[k3K l true]? u.1 = true := OP.shape
  rw [K3Lot.k03_at_full l hl true] at hs
  unfold shapeAt at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  rw [hs.1.1]
  unfold standAt
  show (if (IM.k3Place l true).piece ≤ 1 then _ else _) = _
  have hp : ¬ (IM.k3Place l true).piece ≤ 1 := by
    show ¬ (if (true : Bool) = true then 6 else 1) + (if l = 24 then 1 else 0) + 1 ≤ 1
    simp
  rw [if_neg hp]
  show (if ((linksFull[l]?).getD .layers == .head && (IM.k3Place l true).piece == 2) = true then _
    else _) = _
  have hp2 : ((IM.k3Place l true).piece == 2) = false := by
    show ((if (true : Bool) = true then 6 else 1) + (if l = 24 then 1 else 0) + 1 == 2) = false
    by_cases e : l = 24 <;> simp [e]
  rw [hp2, Bool.and_false, hsub]
  rfl

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
  (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **THE FIELD rides AT ATTENTION's TWELVE DIGITS, AT THE CONSTANT.** -/
theorem k03_rides_dig_att : ∀ g < 12, ∀ A, (At.X Zp).A[g]? = some A → ∀ y tl,
    VerifiableInference.Desc.First.Look.digAt (At.X Zp) (2 * g + 1) = some (y, tl) →
    ∀ q, (h.toAtMg.row 𝔏)[k3K (2 * g + 1) true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g + 1) true = some b' →
    ∀ Lk, cF.links[2 * g + 1]? = some Lk →
    (∀ n r, (statesOfLink Lk 2).find? (fun x => x.1 == "join") = some (n, r) →
      r = VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm)
        (keysOfO A)) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g + 1) true) u →
      h.toAtMg.rch (k3K (2 * g + 1) true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g + 1) true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F, u.1.fork? = some F →
        ∀ g₀, (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm).heard u.1 = some g₀ →
        g₀.leaves.first + lvLen g₀ ≤ F.next ∧ g₀.leaves.first + lvLen g₀ ≤ F.ns ∧
        ∀ j, g₀.leaves.first ≤ j → j < g₀.leaves.first + lvLen g₀ → ¬ OnBytes.PscRun.Filled F j) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g + 1) true) u →
      h.toAtMg.rch (k3K (2 * g + 1) true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g + 1) true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "first"), (2, "keys"), (2, "second")],
        Fwd ((h.toAtMg.𝔇 h.𝔇).Rd (2 * g + 1)) p.1 p.2 u.1 v.1) →
      RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
        (k3K (2 * g + 1) true) q b' := by
  intro g hg A hA y tl hdig q hq b' hb' Lk hLk hfJ hWin hOwn
  have hl : 2 * g + 1 < 25 := by omega
  obtain ⟨hs, hx, hsh⟩ : ∃ hs, lookAt (At.X Zp) (2 * g + 1) true = some y ∧
      (VerifiableInference.Desc.First.Look.P.ofPlace
        (OnBytes.Params.settingOf (At.X Zp).P.frame) true y).shape = some hs := by
    unfold VerifiableInference.Desc.First.Look.digAt at hdig
    obtain ⟨x', hx', hd1⟩ := Option.bind_eq_some_iff.1 hdig
    obtain ⟨tl', -, hd2⟩ := Option.bind_eq_some_iff.1 hd1
    obtain ⟨s, hs', hd3⟩ := Option.map_eq_some_iff.1 hd2
    obtain ⟨rfl, -⟩ := Prod.mk.inj hd3
    exact ⟨s, hx', hs'⟩
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hsub : linksFull[2 * g + 1]? = some ModelPart.attention := by
    have h0 := List.all_eq_true.1 linksAttFull g (List.mem_range.2 hg)
    simpa using h0
  have hix : IM.k3Ix (2 * g + 1) false = 1 := by
    unfold IM.k3Ix
    simp [show 2 * g + 1 ≠ 24 by omega]
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  obtain ⟨L1, e1, hO⟩ := k03_objects_raw h.scope h.reads O (2 * g + 1) hl false
  obtain ⟨L2, e2, hG⟩ := k03_guests_raw h.scope h.reads O (2 * g + 1) hl false
  obtain ⟨L3, p, e3, -, hP⟩ := k03_planes_raw h.scope h.reads O (2 * g + 1) hl (readersOfO A)
    (by
      rw [hW]
      exact H2K5.Door.readersAt_att
        (_root_.Meaning.scope_plans h.scope h.reads h.pubOne).1 hA)
  obtain rfl : Lk = L1 := Option.some.inj (hLk.symm.trans e1)
  obtain rfl : Lk = L2 := Option.some.inj (hLk.symm.trans e2)
  obtain rfl : Lk = L3 := Option.some.inj (hLk.symm.trans e3)
  rw [hix] at hO hG hP
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
  exact ridesAtR_digits_att (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch
    (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g + 1) Lk) Lk K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape (IM.k3Place (2 * g + 1) true) b' hb'
    (Pc.planOk (2 * g + 1) hl true b' hb') rfl (k03_pieceAt_dig h.toAtMg (2 * g + 1)) rfl rfl hl
    hsub (k03_hlink h (2 * g + 1) Lk hLk) k03_atS2_calls
    (At.seats Zp) (k03_es h) (k03_hD h) (k03_hd h) q (K3Lot.k03_at_full (2 * g + 1) hl true) rfl
    (by
      show 7 ≤ (if (true : Bool) = true then 6 else 1) + (if 2 * g + 1 = 24 then 1 else 0) + 1
      simp)
    (Pc.back (2 * g + 1) hl true q hq) hx hsh (k03_index_low_dig h 𝔏 q₁ q₂ q₃ hl q hq)
    (fun _ _ _ _ => rfl) (k03_hHeadAll h q.base) A p.lm
    (fun n r e => (Prod.mk.inj (Option.some.inj (hO.symm.trans e))).2.symm)
    (fun n r e => (Prod.mk.inj (Option.some.inj (hG.symm.trans e))).2.symm)
    (fun n r e => (Prod.mk.inj (Option.some.inj (hP.symm.trans e))).2.symm)
    hfJ
    (fun _ u _ _ _ _ _ _ => hsil 1 "objects" u.1) (fun _ u _ _ _ _ _ _ => hsil 1 "guests" u.1)
    (fun _ u _ _ _ _ _ _ => hsil 1 "planes" u.1) (fun _ u _ _ _ _ _ _ => hsil 2 "join" u.1)
    (fun z u _ hu _ hm _ _ =>
      VerifiableInference.Desc.K1.here_att_of_stand
        (k03_stand_dig h hl hsub z u hu (Classical.not_not.1 hm)))
    hWin hOwn rfl

/-- **THE FIELD rides AT THE OUTPUT HEAD's DIGITS, AT THE CONSTANT.** -/
theorem k03_rides_dig_head : ∀ y tl,
    VerifiableInference.Desc.First.Look.digAt (At.X Zp) 24 = some (y, tl) →
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    ∀ Lk, cF.links[24]? = some Lk →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      (readerOf (statesOfLink Lk) 2 "objects" u.1).isSome = true) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      (readerOf (statesOfLink Lk) 2 "guests" u.1).isSome = true) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      (readerOf (statesOfLink Lk) 2 "planes" u.1).isSome = true) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F, u.1.fork? = some F →
        ∀ g₀, (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm).heard u.1 = some g₀ →
        g₀.leaves.first + lvLen g₀ ≤ F.next ∧ g₀.leaves.first + lvLen g₀ ≤ F.ns ∧
        ∀ j, g₀.leaves.first ≤ j → j < g₀.leaves.first + lvLen g₀ → ¬ OnBytes.PscRun.Filled F j) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      Fwd ((h.toAtMg.𝔇 h.𝔇).Rd 24) 3 "join" u.1 v.1) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits")],
        Fwd ((h.toAtMg.𝔇 h.𝔇).Rd 24) p.1 p.2 u.1 v.1) →
    (∀ kk,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) (k3K 24 true)
        (.forms 24 kk "weights") →
      ¬ insQ linksFull PS (k3K 24 true) (.forms 24 kk "weights") →
      ∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ w, (h.toAtMg.𝔇 h.𝔇).wt 24 (z, v.1) (strsOf FrD v.2) w →
        (h.toAtMg.𝔇 h.𝔇).wt 24 (z, u.1) (strsOf FrD u.2) w) →
      RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
        (k3K 24 true) q b' := by
  intro y tl hdig q hq b' hb' Lk hLk hrO hrG hrP hWin hJoin hOwn hWt
  have hU : (At.X Zp).H.tl.ix.U.getD 2 none = some 0 :=
    VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed.public_third h.pubOne
  have hl : 24 < 25 := by omega
  obtain ⟨hs, hx, hsh⟩ : ∃ hs, lookAt (At.X Zp) 24 true = some y ∧
      (VerifiableInference.Desc.First.Look.P.ofPlace
        (OnBytes.Params.settingOf (At.X Zp).P.frame) true y).shape = some hs := by
    unfold VerifiableInference.Desc.First.Look.digAt at hdig
    obtain ⟨x', hx', hd1⟩ := Option.bind_eq_some_iff.1 hdig
    obtain ⟨tl', -, hd2⟩ := Option.bind_eq_some_iff.1 hd1
    obtain ⟨s, hs', hd3⟩ := Option.map_eq_some_iff.1 hd2
    obtain ⟨rfl, -⟩ := Prod.mk.inj hd3
    exact ⟨s, hx', hs'⟩
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have hsub : linksFull[24]? = some ModelPart.head := by decide +kernel
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  have hrd : K3Lot.readersAt (At.X Zp) 24 = some (callerReaders (planesAt 0)) := by
    obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
    unfold K3Lot.readersAt VerifiableInference.Desc.K3.isHead
    rw [p4, ng, hU]
    rfl
  obtain ⟨L1, e1, hO⟩ := k03_objects_raw h.scope h.reads O 24 hl false
  obtain ⟨L2, e2, hG⟩ := k03_guests_raw h.scope h.reads O 24 hl false
  obtain ⟨L3, p, e3, -, hP⟩ := k03_planes_raw h.scope h.reads O 24 hl
    (callerReaders (planesAt 0)) (by rw [hW]; exact hrd)
  obtain rfl : Lk = L1 := Option.some.inj (hLk.symm.trans e1)
  obtain rfl : Lk = L2 := Option.some.inj (hLk.symm.trans e2)
  obtain rfl : Lk = L3 := Option.some.inj (hLk.symm.trans e3)
  exact ridesAtR_digits_head (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch
    (holesAt (At.X Zp) (headLink (At.X Zp)) 24 Lk) Lk K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb'
    (Pc.planOk 24 hl true b' hb') rfl (k03_pieceAt_dig h.toAtMg 24) rfl rfl hl
    hsub (k03_hlink h 24 Lk hLk) k03_atS2_calls
    (At.seats Zp) (k03_es h) (k03_hD h) (k03_hd h) q (K3Lot.k03_at_full 24 hl true) rfl
    (by decide)
    (Pc.back 24 hl true q hq) hx hsh (k03_index_low_dig h 𝔏 q₁ q₂ q₃ hl q hq)
    (fun _ _ _ _ => rfl) (k03_hHeadAll h q.base) 0 p.lm
    (fun n r e => (Prod.mk.inj (Option.some.inj (hO.symm.trans e))).2.symm)
    (fun n r e => (Prod.mk.inj (Option.some.inj (hG.symm.trans e))).2.symm)
    (fun n r e => (Prod.mk.inj (Option.some.inj (hP.symm.trans e))).2.symm)
    hrO hrG hrP
    (fun z u _ hu _ hm _ _ =>
      VerifiableInference.Desc.K1.here_head_of_stand
        (k03_stand_dig h hl hsub z u hu (Classical.not_not.1 hm)))
    hWin hJoin hOwn rfl hWt

end

end P5J

#print axioms P5J.linksAttFull
#print axioms P5J.linksAttFull_control
#print axioms P5J.k03_lk_at
#print axioms P5J.k03_stand_dig
#print axioms P5J.k03_rides_dig_att
#print axioms P5J.k03_rides_dig_head
