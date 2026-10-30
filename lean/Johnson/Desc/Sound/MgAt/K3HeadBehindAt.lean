-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No state of the verifier is shown in Lean at which all premises hold
together.
Johnson/Desc/Sound/MgAt/K3HeadBehindAt.lean: the lookup argument on the calls at the output head's
segment: THE TWO PREMISES bPub AND bPubP OF `behindPartsR_mgAll`
(Johnson/Desc/Sound/MgAt/K3Calls.lean), IN THEIR OWN TEXT, AT l := 24: every public item that the
promise asks behind that place, beside the five that the rule there pays itself, holds at the state
behind an accept; and what each, but left 24, says beside its test with code holds there too. By
calls of the
lookups' files' lemmas. NO SOUNDNESS IS CLAIMED.

WHICH ITEMS: closed facts on the table of joints, by the kernel, at the composed meaning's closed
list of extra public tests (`mgMore`):
  `headKept` (five: asked in front too): tokenSmall, indexIs, indexThere, "frame.sentIs" 24,
    "ledger.treesAre" 24 · `headNew` (two: new behind): look 24, formsInT 24 3 "objects".
  `head_sorted`: each item asked behind is one of `paidCallsR 24 3` or one of these seven.
  `head_kept_front`: the five are asked in front. `head_tight`: all seven are asked behind.
  `head_said`: of each extra or table's public item open behind, but left 24, the table `saysNone`
    (Johnson/Desc/First/AllSaid.lean) says "no sentence is meant".
ITEM BY ITEM: indexIs, indexThere: the rule for what passes a place (`sameBut_rides`,
Johnson/Desc/First/Look/K3Leaves.lean) · tokenSmall, "frame.sentIs", "ledger.treesAre":
`tokenSmall_kept`, `sentIs_kept`, `treesAre_kept` (K3CallsKept.lean) · look 24: `look_head_made`
(K3CallsMade.lean).
Main names: `head_bPub_mgAll`, `head_bPubP_base`; and `head_parts_base`: the field parts of
`HeadRestR` (Johnson/Desc/Sound/MgAt/K3Mean.lean) in its own text, at the closed base.

WHAT IS LEFT, EACH A NAMED PREMISE.
  WHERE THE PIECE ACCEPTS, LEFT TO OTHER FILES: hObj: the test formsInT 24 3 "objects" at the state
    behind, under all that bPub's own text hands over (the promise in front, "reached", no mark,
    the accept, SameBut).
  TERMS: hM (the meaning beneath has no extra public test) · hBase (its public test reads no
    state) · hmH (the head's segment's number by the public parameters is 24).
  THE PLACE AND THE PIECE: hlook, hb, hOk, hback. AT `head_parts_base` SEVEN MORE: hns · next ·
    stand · fit · tells · hbase · hsmpT.
`head_bPubP_base` stands at the closed base alone and spends no premise.

Limits. The written full list and the closed list `mgMore` alone. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.Sound.MgAt.K3Calls
import Johnson.Desc.Sound.MgAt.K3Tests
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.First.Look.K3Base
import Johnson.Desc.First.Look.K3CallsKept
import Johnson.Desc.First.Look.K3CallsStatedYes
import Johnson.Desc.First.Look.K3Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub More Meaning shift pubFit pubSets pubStep pubRowM
  pubOfItems stepOpen openSets start pubAll_tokenSmall pubAll_more_sentIs pubAll_more_treesAre
  pubAll_look_head)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- The five that are asked on both sides of the place. -/
def headKept : List Pub :=
  [.tokenSmall, .indexIs, .indexThere, .more (some 24) "frame.sentIs",
    .more (some 24) "ledger.treesAre"]

/-- The two that are new behind it. -/
def headNew : List Pub := [.look 24, .formsInT 24 3 "objects"]

/-- What the promise asks behind the place: in the text of `behindPartsR_mgAll`'s premise bPub. -/
def headBehind (M : More) : List Pub :=
  pubStep ((pubSets M linksFull PS)[k3K 24 false]?.getD []) (pubRowM M linksFull
      (IM.k3Place 24 false)) ++
    pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k3K 24 false]?.getD [])
      (Desc.First.rowOf linksFull (IM.k3Place 24 false)))

/-- What it asks in front. -/
def headFront (M : More) : List Pub :=
  ((pubSets M linksFull PS)[k3K 24 false]?.getD []) ++
    pubOfItems ((openSets linksFull PS (start linksFull))[k3K 24 false]?.getD [])

set_option maxRecDepth 1000000 in
theorem head_sorted : ((headBehind mgMore).all fun p =>
    decide (p ∈ paidCallsR 24 3 ∨ p ∈ headKept ++ headNew)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem head_kept_front : (headKept.all fun p => decide (p ∈ headFront mgMore)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem head_tight :
    ((headKept ++ headNew).all fun p => decide (p ∈ headBehind mgMore)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem head_said : ((pubStep ((pubSets mgMore linksFull PS)[k3K 24 false]?.getD [])
    (pubRowM mgMore linksFull (IM.k3Place 24 false))).all fun p =>
      decide (p = .left 24) || (Desc.First.saysNone p).isSome) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem head_fresh : decide (Pub.linkFresh 24 ∈
    (pubSets mgMore linksFull PS)[k3K 24 false]?.getD []) = true := by decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT

/-- **bPub, at the head's calls.** -/
theorem head_bPub_mgAll (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {})
    (hBase : ∀ r (z : P) (s s' : Desc.First.S), Mg.pub r (z, s') = Mg.pub r (z, s))
    (hmH : headLink X = 24) {x : Desc.First.Look.Place} (hlook : lookAt X 24 false = some x)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape 24 false = some b')
    (hOk : b'.planOk = true) (hback : q.back = [])
    (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
    (hObj : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v, (strictAt B' q).ior.red.out u τ = some v →
      SameBut u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K 24 false) u →
      Rch (k3K 24 false) ((z, u.1), u.2) → u.1.failed = none →
      (mgAll Dm Mg).pub (.formsInT 24 3 "objects") (z, v.1) = true) :
    ∀ B', SeatOf b' B' → ∀ z : P, ∀ u v : Desc.First.S × Fr.E.Str,
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K 24 false) u →
      Rch (k3K 24 false) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k3K 24 false]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place 24 false)) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k3K 24 false]?.getD [])
            (Desc.First.rowOf linksFull (IM.k3Place 24 false))),
        p ∉ paidCallsR 24 (2 + shift ModelPart.head) → (mgAll Dm Mg).pub p (z, v.1) = true := by
  intro B' hN z u v hu hR hun ⟨τ, hout⟩ T p hp hpaid
  have eM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hM
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape 24 false b' hb
  have eP : placeAt X 24 false =
      some (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) := by
    unfold placeAt
    rw [hlook]
    rfl
  obtain ⟨laid, sent, rs, cols, -, hd⟩ := k3_calls_stated_yes K3Lot.ofForm (K3Lot.readersAt X) codes
    shape (IM.k3Place 24 false) b' B' hb hOk hN.1 (strictAt B' q) rfl rfl hpc eP hback u v τ hout
  have hfront : ∀ r ∈ headFront mgMore, (mgAll Dm Mg).pub r (z, u.1) = true := by
    obtain ⟨-, hm | ⟨h1, -, -, -⟩⟩ := hu
    · exact absurd hun hm
    · simp only [Bool.and_eq_true] at h1
      have hq := h1.1.2
      unfold Desc.First.pubHeld at hq
      rw [List.all_eq_true, eM] at hq
      exact hq
  have hIn : Desc.K3.k3OnIn
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) u.1 = true := by
    have hOpen := calls_asks_open (mgAll Dm Mg).more linksFull PS (k3K 24 false)
      (IM.k3Place 24 false) 24 ModelPart.head (hfit_mgAll Dm Mg hM)
      (K3Lot.k03_at_full 24 (by decide) false) rfl (by decide) rfl
      (.lookIn 24 (2 + shift ModelPart.head)) (by simp)
    rw [eM] at hOpen
    have h0 := hfront _ (List.mem_append_left _ hOpen)
    have h3 : 2 + shift ModelPart.head = Desc.K3.pieceAt X 24 false := hpc
    rw [h3] at h0
    exact k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) 24 false hlook z u.1 h0)
  obtain ⟨hs, hsh⟩ : ∃ hs,
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).shape = some hs := by
    cases e : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).shape with
    | none =>
      unfold Desc.K3.k3OnIn at hIn
      rw [e] at hIn
      cases hIn
    | some hs => exact ⟨hs, rfl⟩
  have hK : ∀ r ∈ headKept, (mgAll Dm Mg).pub r (z, u.1) = true := fun r hr =>
    hfront r (of_decide_eq_true (List.all_eq_true.1 head_kept_front r hr))
  rw [eM] at hp
  have hseven : p ∈ headKept ++ headNew :=
    (of_decide_eq_true (List.all_eq_true.1 head_sorted p hp)).resolve_left hpaid
  simp only [headKept, headNew, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hseven
  rcases hseven with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h0 := hK .tokenSmall (by simp [headKept])
    rw [mgAll_pub, pubAll_tokenSmall] at h0 ⊢
    exact tokenSmall_kept (hd := hd) (h0 := h0)
  · have h0 := hK .indexIs (by simp [headKept])
    rw [mgAll_pub] at h0 ⊢
    exact sameBut_rides Dm.pubD Mg.pub _ (k3_three_ride _) z T (fun r _ => hBase r z u.1 v.1) _
      (by simp) h0
  · have h0 := hK .indexThere (by simp [headKept])
    rw [mgAll_pub] at h0 ⊢
    exact sameBut_rides Dm.pubD Mg.pub _ (k3_three_ride _) z T (fun r _ => hBase r z u.1 v.1) _
      (by simp) h0
  · have h0 := hK (.more (some 24) "frame.sentIs") (by simp [headKept])
    rw [mgAll_pub, pubAll_more_sentIs] at h0 ⊢
    exact sentIs_kept (hd := hd) (h0 := h0)
  · have h0 := hK (.more (some 24) "ledger.treesAre") (by simp [headKept])
    rw [mgAll_pub, pubAll_more_treesAre] at h0 ⊢
    exact treesAre_kept (hs := hsh) (hd := hd) (hIn := hIn) (h0 := h0)
  · have e24 : ((24 : ℕ) == Dm.pubD.mH) = true := by
      show ((24 : ℕ) == headLink X) = true
      rw [hmH]
      rfl
    rw [mgAll_pub, pubAll_look_head _ _ 24 e24]
    exact look_head_made (hs := hsh) (hd := hd) (hIn := hIn) (hS := Dm.pubD.hShape)
      (iU3 := Dm.pubD.iU3)
  · exact hObj B' hN z u τ v hout T hu hR hun

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT

/-- **bPubP, at the head's calls, at the closed base.** -/
theorem head_bPubP_base (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (B' : Desc.Block Desc.First.S ProofFile.Cl) (z : P) :
    ∀ u v : Desc.First.S × Fr.E.Str,
      onQ Dm.N (mgAll Dm mgBase) linksFull PS (fun s => (z, s)) (k3K 24 false) u →
      Rch (k3K 24 false) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm mgBase).more linksFull PS)[k3K 24 false]?.getD [])
          (pubRowM (mgAll Dm mgBase).more linksFull (IM.k3Place 24 false)),
        p ≠ .left 24 → (mgAll Dm mgBase).pubP p (z, v.1) := by
  intro u v _ _ _ _ _ p hp hne
  rw [mgAll_more_base] at hp
  have h := List.all_eq_true.1 head_said p hp
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (of_decide_eq_true h) hne
  · exact mgAll_pubP_said Dm p (z, v.1) h

/-- **So: the promise behind the head's calls, in the text of `HeadRestR`'s field parts**
(Johnson/Desc/Sound/MgAt/K3Mean.lean), at the closed base: by `behindPartsR_mgAll`. What of that
theorem's premises is closed, or follows from the place and the piece, is paid here; seven stay. -/
theorem head_parts_base (codes : Codes) (shape : Params.ReqShape) (hmH : headLink X = 24)
    {x : Desc.First.Look.Place} (hlook : lookAt X 24 false = some x)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape 24 false = some b')
    (hOk : b'.planOk = true) (hback : q.back = [])
    (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
    (hObj : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v, (strictAt B' q).ior.red.out u τ = some v →
      SameBut u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm mgBase) linksFull PS (fun s => (z, s)) (k3K 24 false) u →
      Rch (k3K 24 false) ((z, u.1), u.2) → u.1.failed = none →
      (mgAll Dm mgBase).pub (.formsInT 24 3 "objects") (z, v.1) = true)
    {a' : Desc.Place} {told : List (List Desc.Oracle)}
    (hns : (Dm.built[24]?).map (·.ns) =
      some (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).ns)
    (next : PS[k3K 24 false + 1]? = some a')
    (stand : Desc.First.sameStand linksFull (IM.k3Place 24 false) a' = true)
    (fit : Desc.First.bookFit Dm.N PS told = true) (tells : told[k3K 24 false]? = some [])
    (hbase : ∀ t ∈ Desc.First.sampledIn Dm.N
      ((openSets linksFull PS (start linksFull))[k3K 24 false]?.getD []), t.1 < q.base)
    (hsmpT : ∀ (z : P) (s s' : Desc.First.S), s'.st = s.st → Dm.smp (z, s') = Dm.smp (z, s)) :
    ∀ B', SeatOf b' B' → ∀ z : P,
      BehindPartsR (Fr := Fr) x (Params.settingOf X.P.frame) Dm.N (mgAll Dm mgBase) linksFull PS z
        (k3K 24 false) 24 3 (Dm.sent.arrayOf.getD 24 #[]) (IM.k3Place 24 false) a' told
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
        (fun u => Rch (k3K 24 false) ((z, u.1), u.2)) := by
  intro B' hN z
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape 24 false b' hb
  have eP : placeAt X 24 false =
      some (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) := by
    unfold placeAt
    rw [hlook]
    rfl
  have hSB : ∀ u τ v, (strictAt B' q).ior.red.out u τ = some v → SameBut u.1 v.1 := by
    intro u τ v hout
    obtain ⟨laid, sent, rs, cols, -, hd⟩ := k3_calls_stated_yes K3Lot.ofForm (K3Lot.readersAt X)
      codes shape (IM.k3Place 24 false) b' B' hb hOk hN.1 (strictAt B' q) rfl rfl hpc eP hback u v
      τ hout
    exact k3_calls_sameBut _ _ _ _ _ _ _ _ _ _ hd
  have hfresh : Pub.linkFresh 24 ∈
      (pubSets (mgAll Dm mgBase).more linksFull PS)[k3K 24 false]?.getD [] := by
    rw [mgAll_more_base]
    exact of_decide_eq_true head_fresh
  exact behindPartsR_mgAll Dm mgBase B' z (sub := ModelPart.head) (fun _ _ _ _ _ _ => rfl) hns hlook
    hpc.symm (K3Lot.k03_at_full 24 (by decide) false) next rfl (by decide) rfl stand fit tells
    (hfit_mgAll Dm mgBase rfl) hfresh hbase hSB hsmpT
    (head_bPub_mgAll Dm mgBase codes shape rfl (fun _ _ _ _ => rfl) hmH hlook q b' hb hOk hback Rch
      hObj B' hN z)
    (head_bPubP_base Dm q Rch B' z)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.head_sorted
#print axioms VerifiableInference.OnPublicFiles.head_kept_front
#print axioms VerifiableInference.OnPublicFiles.head_tight
#print axioms VerifiableInference.OnPublicFiles.head_said
#print axioms VerifiableInference.OnPublicFiles.head_bPub_mgAll
#print axioms VerifiableInference.OnPublicFiles.head_bPubP_base
#print axioms VerifiableInference.OnPublicFiles.head_fresh
#print axioms VerifiableInference.OnPublicFiles.head_parts_base
