-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03RunAnswersHeadAt.lean: THE KIND "LOOKUP" (K3): IN FRONT OF THE LOOKUP ON THE OUTPUT
HEAD's DIGITS THE RUNS "objects" AND "guests" THEMSELVES ANSWER, AT THE CLOSED CONSTANT: two of
the seven premises on the states of `k03_rides_dig_head` (Johnson/P5J/K03RidesDigAt2.lean: hrO,
hrG), FROM THE HEAD, THE PROMISE IN FRONT AND "NO MARK", AT THE HEAD's OWN CHAIN's LINK 24 (hLk).
One closed test with code and five theorems: two by the kernel (one a negative test), the others
joinings.
  `formsObjOpenB`, `formsObjOpen_full`, `formsObjOpen_control`: the item "the forms of the run
    objects of the calls' lookup" of segment 24 is open at the border in front of that segment's
    digits; at the chain's start it is not.
  `k03_hrO_head`: the promise holds the public test tied to that open item; at the table's names
    it is `formsIn` at "objects"; where that test is true the link's reader answers; at the holes
    that the description lays the run's own reader answers then (another author's
    `objects_hr_of_formsIn`, Johnson/Top/H/Keep/RunAnswers.lean).
  `k03_hrG_head`: a ledger is open (`k03_stand_dig`; another author's `fork_of_stand`,
    Johnson/Desc/First/K8/ForkPromise.lean); "guests" without a guest answers wherever one is
    (`guests_hr`, RunAnswers.lean).
  `k03_rides_dig_head_five`: the field rides at the head's digits with the two laid in.
WHAT STAYS IN FRONT OF THAT FIELD, FIVE, EACH IN ITS AUTHOR's OWN TEXT: hrP ("planes" answers in
front) · hWin · hJoin · hOwn · hWt. UNTIL THEY HAVE PAYERS THE ROW BUYS NOTHING.
Limits: joinings. The head h and the free letters' three equations are premises. The full size
alone. No soundness is claimed.

-/
import Johnson.P5J.K03RidesDigAt2
import Johnson.Top.H.Keep.RunAnswers
import Johnson.Desc.First.K8.ForkPromise
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.Sound.MgAt.Runs

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
open VerifiableInference.Desc.First (Item ModelPart Pub start pubOfItems runsOf pubAll_formsIn)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.K9 (holesAt smallReader statesOfLink readerOf formsIn)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)
open VerifiableInference.Reads.Pass (Fwd)

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- The forms of the calls' lookup's run "objects" of segment 24 are open at border k. -/
def formsObjOpenB (k : ℕ) : Bool := (openQ linksFull PS k).contains (Item.forms 24 3 "objects")

set_option maxRecDepth 1000000 in
theorem formsObjOpen_full : formsObjOpenB (k3K 24 true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: at the chain's start it is not. -/
theorem formsObjOpen_control : formsObjOpenB 0 = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- **"objects" answers in front of the head's digits.** -/
theorem k03_hrO_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Lk : Link VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim)
    (hLk : cF.links[24]? = some Lk) (z : ProofFile.InstPub)
    (u : VerifiableInference.Desc.First.S × (FrD).E.Str)
    (hu : onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
      (k3K 24 true) u) (hm : u.1.failed = none) :
    (readerOf (statesOfLink Lk) 2 "objects" u.1).isSome = true := by
  have OP :=
    onParts_of_on _ _ _ _ (fun s : VerifiableInference.Desc.First.S => (z, s)) _ u hu hm
  have hopen : Item.forms 24 3 "objects" ∈ openQ linksFull PS (k3K 24 true) := by
    have h0 := formsObjOpen_full
    unfold formsObjOpenB at h0
    exact List.contains_iff_mem.1 h0
  have hq : Pub.formsIn 24 3 "objects" ∈ pubOfItems (openQ linksFull PS (k3K 24 true)) :=
    List.mem_flatMap.2 ⟨_, hopen, List.mem_singleton.2 rfl⟩
  have ht : (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsIn 24 3 "objects") (z, u.1) = true :=
    OP.pub _ (List.mem_append_right _ hq)
  rw [mgAll_pub, pubAll_formsIn] at ht
  have e : (h.toAtMg.𝔇 h.𝔇).pubD.runs 24 3 "objects" = [(2, "objects"), (2, "guests")] := by
    show runsAt linksFull 24 3 "objects" = _
    rw [runsAt_of linksFull 24 .head (by decide +kernel) 3 "objects"]
    decide
  rw [e] at ht
  have h1 := List.all_eq_true.1 ht (2, "objects") (List.mem_cons_self ..)
  have ea : (h.toAtMg.𝔇 h.𝔇).pubD.ah 2 "objects" = false :=
    (by decide : ("objects" == "K8.equations") = false)
  dsimp only at h1
  rw [ea] at h1
  have h2 : formsIn ((h.toAtMg.𝔇 h.𝔇).Rd 24) ((h.toAtMg.𝔇 h.𝔇).N.group 24) 2 "objects" u.1 =
      true := h1
  rw [k03_hlink h 24 Lk hLk] at h2
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L1, e1, hO⟩ := k03_objects_raw h.scope h.reads O 24 (by omega) false
  obtain rfl : Lk = L1 := Option.some.inj (hLk.symm.trans e1)
  exact objects_hr_of_formsIn (At.X Zp) (headLink (At.X Zp)) 24 Lk 2 _ K3Lot.ofForm
    k03_atS2_calls (fun n r e => (Prod.mk.inj (Option.some.inj (hO.symm.trans e))).2.symm) h2

/-- **"guests" answers in front of the head's digits.** -/
theorem k03_hrG_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Lk : Link VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim)
    (hLk : cF.links[24]? = some Lk) (z : ProofFile.InstPub)
    (u : VerifiableInference.Desc.First.S × (FrD).E.Str)
    (hu : onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
      (k3K 24 true) u) (hm : u.1.failed = none) :
    (readerOf (statesOfLink Lk) 2 "guests" u.1).isSome = true := by
  obtain ⟨F, hF⟩ := VerifiableInference.Desc.First.K8.fork_of_stand u.1 .head
    (k03_stand_dig h (by omega) (by decide +kernel) z u hu hm)
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L1, e1, hG⟩ := k03_guests_raw h.scope h.reads O 24 (by omega) false
  obtain rfl : Lk = L1 := Option.some.inj (hLk.symm.trans e1)
  exact guests_hr Lk 2 (fun _ _ => True) (fun _ => trivial)
    ⟨_, _, hG, fun _ _ _ hr _ => hr⟩ hF

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
  (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **THE FIELD rides AT THE OUTPUT HEAD's DIGITS, WITH "objects" AND "guests" LAID IN.** -/
theorem k03_rides_dig_head_five : ∀ y tl,
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
  intro y tl hdig q hq b' hb' Lk hLk hrP hWin hJoin hOwn hWt
  exact k03_rides_dig_head h 𝔏 q₁ q₂ q₃ y tl hdig q hq b' hb' Lk hLk
    (fun z u _ hu _ hm _ _ => k03_hrO_head h Lk hLk z u hu (Classical.not_not.1 hm))
    (fun z u _ hu _ hm _ _ => k03_hrG_head h Lk hLk z u hu (Classical.not_not.1 hm))
    hrP hWin hJoin hOwn hWt

end

end P5J

#print axioms P5J.formsObjOpen_full
#print axioms P5J.formsObjOpen_control
#print axioms P5J.k03_hrO_head
#print axioms P5J.k03_hrG_head
#print axioms P5J.k03_rides_dig_head_five
