-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/KeepsBetween.lean: THE FIRST CHAIN: WHAT THE LOOKUP ON A SEGMENT's CALLS HAS HEARD
STANDS IN FRONT OF THAT SEGMENT's BATCHING: AT STEP LEVEL: EACH SUB-PROTOCOL BETWEEN KEEPS IT AT ITS
OWN DECISION, AND SO DOES THE VERIFIER's FOLD OVER THEM. UNDER THE SCOPE, THE FILES READ, IM.Open
AND THE DESCRIPTION's TEST ON ITS PLAN. Lemmas; NONE OF THE LIBRARY's GOALS. No prover stands in
them. Nothing on completeness, soundness or hiding.
Why. `look_back_layers` (Johnson/P1K8R/LookAtBatch.lean), `look_back_att`, `look_back_head`
(LookAtBatchAll.lean) say it along "reached": from a state reached in front of the batching there is
SOME state reached behind the lookup that it keeps. The honest side's walk hands one fold from one
state: to tie the two the step-level form is wanted.

  `decides_at`   MergeLaw.alone_decides (Johnson/K11R/MaskSeat.lean); IM.flatIx_scope
      (Johnson/IMR/FlatScope.lean), IM.hear_at_flat (FlatIx.lean), as in that file's flat_at
  `keeps_digits_at` and five more, one a member   the ingredients are those of the three
      `look_back_…` proofs and of LinkJoin.back_k1_of, back_k8_of
      (Johnson/Desc/First/Link/Law/StretchParts.lean), OnBytes.Road.K4.InT.kept_reached
      (Johnson/Road/K4/InT/WinsReached.lean): THEIR LINES STAND HERE A SECOND TIME, CUT AT THE
      DECISION
  **`keeps_five`**, **`keeps_six`**   l < 24: numbers 14 l + 4 to 14 l + 8; the head's: 341 to 346
      (MergeLaw.seated_five, Johnson/K11R/LeavesAt346.lean, and the merge)
  **`rel_rides`**, `look_rides`   Keeps.foldBlocks_keeps (Johnson/Desc/FoldKeeps.lean)
Kin of `rel_rides`: the honest side's frame's authors' fold_keeps
(Johnson/Desc/ProofFile/Honest/Thread/MemberLaw.lean, a file of that frame, which this one does
not import and which the library may not hold): what every member's yes keeps is carried along a
fold: a predicate, at step level, along the whole fold; here a relation, at the decision, over a
window of a list. Not called: this file imports no file of that frame.
Limits. In scope alone. Nothing says that any fold returns or that any state is reached. "Keeps":
what is heard at the one state stands at the other; where nothing is heard it says nothing.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.LookAtBatchAll
import Johnson.Desc.FoldKeeps
import Johnson.Road.K4.KeptAtS
import Johnson.IMR.K4Seat
import Johnson.IMR.K8Seat
import Johnson.IMR.K11Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Decides)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE TOOL: the step-level form of LinkJoin.back_of
(Johnson/Desc/First/Link/Law/StretchBack.lean).** A sub-protocol laid alone at number i of segment l
stands at number 14 l + i + 2 of the flat list, and its decision keeps what the bare one's keeps.
The second half is MergeLaw.alone_decides (Johnson/K11R/MaskSeat.lean), called; the first
is that file's flat_at, which is at the head's segment, at any segment. -/
theorem decides_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l i : ℕ} (hl : l ≤ 24)
    {Lk : Link S Claim} {b b' : Block S Claim} {name : String} {a : Place}
    (e1 : c.links[l]? = some Lk) (e2 : Lk.hear[i]? = some b)
    (hA : IM.LaidAlone ProofFile.sameReply b b' name a) (hk : a.kind ≠ KindName.K7)
    {R : S → S → Prop} (hD : Decides R b') :
    ∃ b₀, c.blocksInOrder[14 * l + i + 2]? = some b₀ ∧ Decides R b₀ := by
  refine ⟨b, ?_, MergeLaw.alone_decides hk hA hD⟩
  rw [← IM.flatIx_scope hS hR O hl i]
  exact IM.hear_at_flat e1 e2

/-- The lookup on the digits, below the head's segment. -/
theorem keeps_digits_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) : ∃ b, c.blocksInOrder[14 * l + 8]? = some b ∧ Decides OnPublicFiles.KeepsLook b := by
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l (by omega) true
  obtain ⟨b'', e3', hk⟩ := OnPublicFiles.k03_const_ok hS hR O hOk l (by omega) true
  obtain rfl : b' = b'' := Option.some.inj (e3.symm.trans e3')
  have i3 : IM.k3Ix l true = 6 := by
    show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
    rw [if_pos rfl, if_neg (by omega)]
  rw [i3] at e2
  exact decides_at hS hR O (l := l) (i := 6) (by omega) e1 e2 e4 (fun q => nomatch q)
    (fun s rs gs t hd => OnPublicFiles.stated_keeps _ _ _ _ _ _ b' e3 hk l rfl
      (K3Lot.k03_place _ _ _ _ _ l true b' e3).1 s t rs gs hd)

/-- The sending of the digits. -/
theorem keeps_later_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 24) : ∃ b, c.blocksInOrder[14 * l + 7]? = some b ∧ Decides OnPublicFiles.KeepsLook b := by
  obtain ⟨Lk, b, Xl, pr, reads, digits, e1, e2, -, -, e4⟩ := IM.k1_digits_of hS hR O l (by omega)
  have i1 : IM.k1Ix l true = 5 := by
    show (if true = true then 5 else 3) + (if l = 24 then 1 else 0) = 5
    rw [if_pos rfl, if_neg (by omega)]
  rw [i1] at e2
  exact decides_at hS hR O (l := l) (i := 5) (by omega) e1 e2 e4 (fun q => nomatch q)
    (fun s rs gs t hd => MergeLaw.laterAt_keeps _ _ _ _ _ _ s rs gs t hd)

/-- The smallness test's own sub-protocol. -/
theorem keeps_small_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 24) : ∃ b, c.blocksInOrder[14 * l + 6]? = some b ∧ Decides OnPublicFiles.KeepsLook b := by
  have i8 : LinkJoin.k8Ix l = 4 := by
    show 4 + (if l = 24 then 1 else 0) = 4
    rw [if_neg (by omega)]
  obtain ⟨Lk, b, Xl, e1, e2, -, -, e4⟩ := IM.k8_alone O l (IM.subAt l)
    (IM.subs_scope hS hR O l (by omega)) (LinkJoin.k8Ix l) (LinkJoin.k8_kind_at l) (by
      rw [i8]
      omega)
  rw [i8] at e2
  exact decides_at hS hR O (l := l) (i := 4) (by omega) e1 e2 e4 (fun q => nomatch q)
    (MergeLaw.k8_keeps _)

/-- The sending of the reads, with the step that lays the tables. -/
theorem keeps_reads_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 24) : ∃ b, c.blocksInOrder[14 * l + 5]? = some b ∧ Decides OnPublicFiles.KeepsLook b := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, -, -, e4⟩ := IM.k1_reads_of hS hR O l (by omega)
  have i0 : IM.k1Ix l false = 3 := by
    show (if false = true then 5 else 3) + (if l = 24 then 1 else 0) = 3
    rw [if_neg (by decide), if_neg (by omega)]
  rw [i0] at e2
  exact decides_at hS hR O (l := l) (i := 3) (by omega) e1 e2 e4 (fun q => nomatch q)
    (MergeLaw.retype_decides (MergeLaw.k1Reads_keeps Z Bs.G₀ l Xl _ reads))

/-- An attention segment's own kind's sub-protocol. -/
theorem keeps_own_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {g : ℕ} (hg : g < 12) :
    ∃ b, c.blocksInOrder[14 * (2 * g + 1) + 4]? = some b ∧ Decides OnPublicFiles.KeepsLook b := by
  obtain ⟨Lk', b5, b5', a, f1, f2, f3, f4, -⟩ := IM.k5_of hS hR O g hg
  exact decides_at hS hR O (l := 2 * g + 1) (i := 2) (by omega) f1 f2 f4 (fun q => nomatch q)
    (fun s rs gs t hd => (Att.P.k5AtN_whole OnPublicFiles.KeepsLook (fun _ _ hx => hx)
      (fun s G => OnPublicFiles.keepsLook_of_eq (OnPublicFiles.look_putFork s G))
      (fun _ _ _ _ e => OnPublicFiles.keepsLook_of_eq (Att.P.lay_keeps_heard e)) f3).1 s rs gs t hd)

/-- A layers' segment's own kind's sub-protocol. -/
theorem keeps_own_lay (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {g : ℕ} (hg : g < 12) :
    ∃ b, c.blocksInOrder[14 * (2 * g) + 4]? = some b ∧ Decides OnPublicFiles.KeepsLook b := by
  obtain ⟨Lk, b₀, x, e1, e2, -, e4, -⟩ := IM.k4_of hS hR O g hg
  refine ⟨b₀, ?_, fun s rs gs t hd => ?_⟩
  · rw [show 14 * (2 * g) + 4 = 14 * (2 * g) + 2 + 2 by omega,
      ← IM.flatIx_scope hS hR O (by omega : 2 * g ≤ 24) 2]
    exact IM.hear_at_flat e1 e2
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hRest, -⟩ :=
      OnBytes.Road.K4.kept_atS ((IM.k4_yes e4 s t rs gs).1 hd).1
    exact OnPublicFiles.keepsLook_of_eq hRest.lookHeard

/-- **BELOW THE HEAD's SEGMENT: THE FIVE SUB-PROTOCOLS BETWEEN THE LOOKUP ON THE CALLS AND THE
BATCHING KEEP WHAT THAT LOOKUP HAS HEARD**, each at its own decision. The like of
MergeLaw.seated_five (Johnson/K11R/LeavesAt346.lean), which is at the head's segment. -/
theorem keeps_five (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) :
    ∀ i, i < 5 → ∃ b, c.blocksInOrder[14 * l + 4 + i]? = some b ∧ Decides OnPublicFiles.KeepsLook b := by
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact keeps_own_lay hS hR O (by omega)
    · exact keeps_own_att hS hR O (by omega)
  · exact keeps_reads_at hS hR O hl
  · exact keeps_small_at hS hR O hl
  · exact keeps_later_at hS hR O hl
  · exact keeps_digits_at hS hR O hOk hl

/-- **At the head's segment: the six.** MergeLaw.seated_five's five, and the merge. -/
theorem keeps_six (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∀ i, i < 6 → ∃ b, c.blocksInOrder[341 + i]? = some b ∧ Decides OnPublicFiles.KeepsLook b := by
  intro i hi
  by_cases h5 : i < 5
  · exact MergeLaw.seated_five hS hR O hOk i h5
  · obtain rfl : i = 5 := by omega
    obtain ⟨Lk, b, e1, e2, e4, -⟩ := IM.k11_of hS hR O
    exact decides_at hS hR O (l := 24) (i := 8) (by omega) e1 e2 e4 (fun q => nomatch q)
      (fun s rs gs t hd => OnPublicFiles.keepsLook_of_eq (MergeLaw.decide_leaves_look _ hd))

end

/-- **ALONG A FOLD.** flat: a list of sub-protocols; R: a relation on states that holds of every
state with itself and passes along; the m sub-protocols from number n on keep R, each at its own
decision. Then so does the verifier's fold over just these. -/
theorem rel_rides {R : S → S → Prop} (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (flat : List (Block S Claim)) (n m : ℕ)
    (hk : ∀ i, i < m → ∃ b, flat[n + i]? = some b ∧ Decides R b) {ft : ℕ}
    {s t : S} {r₁ r₂ : List Fmt.RoundView} {c₁ c₂ : List Desc.OpenedColumn}
    (hf : foldBlocks ft ((flat.take (n + m)).drop n) s r₁ c₁ = .ok (t, r₂, c₂)) : R s t := by
  refine Keeps.foldBlocks_keeps R hr ht ft _ (fun b hb => ?_) s r₁ c₁ _ hf
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hb
  rw [List.getElem?_drop, List.getElem?_take] at hj
  by_cases hlt : n + j < n + m
  · rw [if_pos hlt] at hj
    obtain ⟨b', hb', hd⟩ := hk j (by omega)
    obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hj)
    exact hd
  · rw [if_neg hlt] at hj
    exact nomatch hj

/-- The like at "keeps what the lookup on the calls has heard". -/
theorem look_rides (flat : List (Block S Claim)) (n m : ℕ)
    (hk : ∀ i, i < m → ∃ b, flat[n + i]? = some b ∧ Decides OnPublicFiles.KeepsLook b) {ft : ℕ}
    {s t : S} {r₁ r₂ : List Fmt.RoundView} {c₁ c₂ : List Desc.OpenedColumn}
    (hf : foldBlocks ft ((flat.take (n + m)).drop n) s r₁ c₁ = .ok (t, r₂, c₂)) :
    OnPublicFiles.KeepsLook s t :=
  rel_rides (fun _ _ hg => hg) (fun _ _ _ h k => h.trans k) flat n m hk hf

end P1K8

#print axioms P1K8.decides_at
#print axioms P1K8.keeps_digits_at
#print axioms P1K8.keeps_later_at
#print axioms P1K8.keeps_small_at
#print axioms P1K8.keeps_reads_at
#print axioms P1K8.keeps_own_att
#print axioms P1K8.keeps_own_lay
#print axioms P1K8.keeps_five
#print axioms P1K8.keeps_six
#print axioms P1K8.rel_rides
#print axioms P1K8.look_rides
