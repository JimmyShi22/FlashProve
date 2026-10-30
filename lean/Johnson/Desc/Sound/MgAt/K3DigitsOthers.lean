-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsOthers.lean: the lookup on the digits of a segment's approximate
range proof: THE FIELD othersPub OF THE KIND's LEDGER's DigOwedR
(Johnson/Desc/Sound/MgAt/K3Owed.lean: «the other kinds' public tests that are open or tied behind
hold behind»), IN ITS OWN TEXT, AT ITS OWN LETTERS, AT THE COMPOSED MEANING mgAll Dm Mg, ITEM BY
ITEM. Which items these are: a test on the table by the kernel (digits_sorted,
MgAt/K3DigitsSorted.lean). After the like file at the calls (MgAt/K3CallsOthers.lean). By calls
alone. NO SOUNDNESS IS CLAIMED.

Main name.
  othersPub_dig_mgAll: THE FIELD. (hForms has the field's own premises, «reached» and «no mark»
    among them.)
ITEM BY ITEM. unheard, indexIs, indexThere: the rule of footprints (sameBut_rides, K3Leaves.lean) ·
ledger, freeAbove: digLeft_ledgerB, digLeft_freeAboveB (K3KeeperRides.lean) · hasRow, "K5.okAt":
K3DigitsMadeMore.lean · "K5.plain": K3DigitsMadeTrees.lean.
WHAT IS LEFT, EACH A NAMED PREMISE, BOOKED.
  WHERE THE PIECE ACCEPTS: hForms: the tests formsIn l pc r of the written lists
    (five or six that stand in front too; one that is new: "objects" at the digits' own piece) at
    the state behind, under the field's own premises.
  TERMS: hM (the meaning beneath has no extra public test) · hlinks (the composed meaning's list of
    sorts is the written one) · hBase (the meaning beneath's public test reads no state).
  THE PLACE AND THE PIECE: hb, hOk, hback, hx.
NO FACT ALONG THE FOLD IS SPENT BY WHAT IS PAID HERE; hForms may spend «reached».
OBJECT. The composed public tests pubAll at the state behind an accept.
USER. digOwed_forms (MgAt/K3DigitsOwedForms.lean) · k03_othersPub_dig
(Johnson/P5J/K03DigOthersAt.lean). Meant: digOwed_mgAll's premise othersPub
(MgAt/K3DigitsOwed.lean).
LETTERS. Dm, Mg, Rch; codes, shape; l, sub, x, tl, q, b'.


Compiled with the whole library.


The ledger's two texts othersPub, othersP at the digits bear two premises behind the promise in
front: «reached» (Rch k ((z, u.1), u.2)) and «no mark» (u.1.failed = none).

Limits. The closed list mgMore of the build apart. A rule over letters.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsSorted
import Johnson.Desc.Sound.MgAt.K3At
import Johnson.Desc.Sound.MgAt.K3Tests
import Johnson.Desc.First.Look.K3DigitsMadeMore
import Johnson.Desc.First.Look.K3DigitsMadeTrees
import Johnson.Desc.First.Look.K3KeeperRides
import Johnson.Desc.First.Look.K3Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub Meaning shift pubFit pubSets pubStep pubRowM pubOfItems
  stepOpen openSets start pubAll_ledger pubAll_freeAbove)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **THE FIELD othersPub.** -/
theorem othersPub_dig_mgAll (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {})
    (hlinks : Dm.links = linksFull)
    (hBase : ∀ r (z : P) (s s' : Desc.First.S), Mg.pub r (z, s') = Mg.pub r (z, s)) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X l = some (x, tl))
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape l true = some b')
    (hOk : b'.planOk = true) (hback : q.back = [])
    (hForms : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        ∀ r ∈ keptDigits l sub ++ newDigits l sub, (∃ pc nm, r = .formsIn l pc nm) →
        (mgAll Dm Mg).pub r (z, v.1) = true) :
    ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
      ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)) ++
        pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[(k3K l true)]?.getD [])
          (Desc.First.rowOf linksFull (IM.k3Place l true))),
      k3Like r = false → (mgAll Dm Mg).pub r (z, v.1) = true := by
  intro B' hN z u τ v hout T DL hu hR hun r hr hlike
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l true b' hb
  obtain ⟨sub', hsub', -, hpcT⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  have hlook : lookAt X l true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  obtain ⟨-, -, -, cols, hd0⟩ := piece_hears_below
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT) B' rfl hback u τ v hout
  have hd := hN.1.2 _ _ _ _ hd0
  have eM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hM
  have hfront : ∀ p ∈ frontDig mgMore l, (mgAll Dm Mg).pub p (z, u.1) = true := by
    obtain ⟨-, hm | ⟨h1, -, -, -⟩⟩ := hu
    · exact absurd hun hm
    · simp only [Bool.and_eq_true] at h1
      have hp := h1.1.2
      unfold Desc.First.pubHeld at hp
      rw [List.all_eq_true, eM] at hp
      exact hp
  rw [eM] at hr
  obtain ⟨hsort, hkept⟩ := digits_sorted hl hsub
  have hIn : Desc.K3.k3OnIn
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) u.1 = true := by
    have hOpen := digits_lookIn_open (mgAll Dm Mg).more linksFull PS (k3K l true)
      (IM.k3Place l true) l sub' (hfit_mgAll Dm Mg hM) (K3Lot.k03_at_full l hl true) rfl hsub hpcT
      (.lookIn l (7 + shift sub')) (by simp)
    rw [eM] at hOpen
    have hp := hfront _ (List.mem_append_left _ hOpen)
    rw [hpcT.symm.trans hpc] at hp
    exact k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l true hlook z u.1 hp)
  obtain ⟨hs, hsh⟩ : ∃ hs,
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs := by
    cases e : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape with
    | none =>
      unfold Desc.K3.k3OnIn at hIn
      rw [e] at hIn
      cases hIn
    | some hs => exact ⟨hs, rfl⟩
  have hF : ∀ p ∈ keptDigits l sub' ++ newDigits l sub', (∃ pc nm, p = .formsIn l pc nm) →
      (mgAll Dm Mg).pub p (z, v.1) = true := hForms B' hN z u τ v hout T DL hu hR hun
  have hT : ∀ p ∈ keptDigits l sub', (mgAll Dm Mg).pub p (z, u.1) = true := fun p hp =>
    hfront p (hkept p hp)
  have three : ∀ p ∈ [Pub.unheard, Pub.indexIs, Pub.indexThere],
      (mgAll Dm Mg).pub p (z, u.1) = true → (mgAll Dm Mg).pub p (z, v.1) = true := by
    intro p hp ht
    rw [mgAll_pub] at ht ⊢
    exact sameBut_rides Dm.pubD Mg.pub _ (k3_three_ride _) z T (fun r _ => hBase r z u.1 v.1) p hp
      ht
  have led : (mgAll Dm Mg).pub (.ledger l) (z, u.1) = true →
      (mgAll Dm Mg).pub (.ledger l) (z, v.1) = true := by
    intro ht
    rw [mgAll_pub, pubAll_ledger] at ht ⊢
    exact digLeft_ledgerB DL ht
  have fre : (mgAll Dm Mg).pub (.ledger l) (z, u.1) = true →
      (mgAll Dm Mg).pub (.freeAbove l) (z, u.1) = true →
      (mgAll Dm Mg).pub (.freeAbove l) (z, v.1) = true := by
    intro hL ht
    rw [mgAll_pub, pubAll_ledger] at hL
    rw [mgAll_pub, pubAll_freeAbove] at ht ⊢
    cases hn : Dm.pubD.nsOf l with
    | none =>
      rw [hn] at ht
      cases ht
    | some n =>
      rw [hn] at ht
      exact digLeft_freeAboveB DL hL n ht
  rcases hsort r hr with h1 | h1 | h1
  · rw [hlike] at h1
    cases h1
  · have ht := hT r h1
    have h1m := h1
    have hLd : (mgAll Dm Mg).pub (.ledger l) (z, u.1) = true :=
      hT _ (by cases sub' <;> simp [keptDigits])
    cases sub' with
    | layers =>
      simp only [keptDigits, List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | h1
      · exact three _ (by simp) ht
      · exact led ht
      · exact fre hLd ht
      · exact three _ (by simp) ht
      · exact three _ (by simp) ht
      · rw [mgAll_pub] at ht ⊢
        exact digits_keeps_hasRow Dm.pubD Mg.pub K3Lot.ofForm (K3Lot.readersAt X) codes shape
          (IM.k3Place l true) b' hb hOk l rfl hpc z u.1 v.1 _ cols hd hlook hsh l ht
      · refine hF r (List.mem_append_left _ h1m) ?_
        rcases h1 with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
    | attention =>
      have hAtt : Dm.pubD.d5.isAtt l = true := by
        show (Dm.links[l]? == some ModelPart.attention) = true
        rw [hlinks, hsub]
        rfl
      simp only [keptDigits, List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h1
      · exact three _ (by simp) ht
      · exact led ht
      · exact fre hLd ht
      · rw [mgAll_pub] at ht ⊢
        exact digits_keeps_okAt Dm.pubD Mg.pub K3Lot.ofForm (K3Lot.readersAt X) codes shape
          (IM.k3Place l true) b' hb hOk l rfl hpc z u.1 v.1 _ cols hd hlook hsh l hAtt ht
      · rw [mgAll_pub] at ht ⊢
        exact digits_keeps_plain Dm.pubD Mg.pub K3Lot.ofForm (K3Lot.readersAt X) codes shape
          (IM.k3Place l true) b' hb hOk l rfl hpc z u.1 v.1 _ cols hd hlook hsh hIn l hAtt ht
      · exact three _ (by simp) ht
      · exact three _ (by simp) ht
      · refine hF r (List.mem_append_left _ h1m) ?_
        rcases h1 with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
    | head =>
      simp only [keptDigits, List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl | rfl | rfl | h1
      · exact led ht
      · exact fre hLd ht
      · exact three _ (by simp) ht
      · exact three _ (by simp) ht
      · refine hF r (List.mem_append_left _ h1m) ?_
        rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  · refine hF r (List.mem_append_right _ h1) ?_
    simp only [newDigits, List.mem_cons, List.not_mem_nil, or_false] at h1
    exact ⟨_, _, h1⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.othersPub_dig_mgAll
