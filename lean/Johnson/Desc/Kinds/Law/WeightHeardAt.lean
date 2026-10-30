-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WeightHeardAt.lean: WHO GIVES THE ONE PREMISE OF weightAt_kept
(Johnson/Desc/Kinds/Law/WeightAtSame.lean): "the head's seat's reader heard answers at the earlier
state": behind an accept of the output head's own sub-protocol, and at the borders in front of the
four sub-protocols that follow it in the head's segment (places 342 to 345 of the full chain), at
the composed meaning mgAll D Mg (Johnson/Desc/Sound/MgAll.lean).

THE ANSWER. Behind the accept: the accept itself (heard_behind). At the four borders: THE TABLE'S
PROMISE ITSELF: the claim on the head's own three runs is open there (formsT 24 4 "own" at 342,
forms 24 4 "own" from 343 on: by the kernel's evaluation), and its tied public test says that the
reader of the run (3, "norm") answers; that reader is the run itself, called at the state, or at the
state with the tables laid; the run reads its letters through heard. No fact on reached states is
asked.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  heard_withTables: laying the tables leaves what heard answers.
  heard_of_reader: where the segment's reader answers at "norm", heard answers.
  answers_of_formsInT, answers_of_formsIn: the public tests say that the reader answers.
  ownT_open_342, own_open_343, own_open_344, own_open_345: the claim is open at the four borders.
  heard_at_T, heard_at_F: heard answers wherever the promise holds at a border at which the claim is
      open, at a state without a mark.
  heard_behind: heard answers behind an accept of the piece at the head's own sub-protocol.

Every letter under "there is": H, R: each pinned by its reader's equation.
What it does not say. That the promise can be met. hreaders, hown (equations on the meaning's
parameters) and K (K6States: on the IOP as written in Lean) are premises. THE FULL CHAIN ALONE.
Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.WeightAtSame
import Johnson.Desc.Kinds.Law.K6RidersAtMgAll
import Johnson.Desc.Kinds.Law.K6Silent
import Johnson.Desc.Kinds.Law.RunsStill

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Item Meaning)
open VerifiableInference.Desc.K9 (RunOf readerOf readersOfLink statesOfLink formsInT formsIn)
open VerifiableInference.Desc.Sound (Piece Frame MsgT onQ openQ linksFull MgData mgAll
  onParts_of_on)

/-! ## 1 From the reader's answer to heard -/

/-- Laying the tables leaves what heard answers. -/
theorem heard_withTables (h : Model.Head.Shape) (iU3 : ℕ) (P8 : K8.ReadsQuiet.PH) (s e : S)
    (he : withTables P8 s = some e) : (seatAt h iU3).heard e = (seatAt h iU3).heard s := by
  unfold withTables at he
  cases hh : s.here with
  | head a =>
    rw [hh] at he
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.1 he
    show (a.squaresP.bind fun q => a.x.bind fun x =>
        allOf a.F x (some (Head.keptOf q x.wpl.sL))) =
      (match s.here with
        | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
          allOf o.F x (some (Head.keptOf q x.wpl.sL))
        | _ => none)
    rw [hh]
  | _ => rw [hh] at he; exact nomatch he

/-- **Where the segment's reader answers at "norm", heard answers.** -/
theorem heard_of_reader {h : Model.Head.Shape} {iU3 l piece b : ℕ} {p : Par} {Lk : Link S Claim}
    (K : K6States h iU3 p l piece (statesOfLink Lk) b) (P8 : K8.ReadsQuiet.PH)
    (small : S → Option K9.Read) (s : S) (R : K9.Read)
    (hR : (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk).forms b "norm" s = some R) :
    ∃ H, (seatAt h iU3).heard s = some H := by
  have key : ∀ t R', readerOf (statesOfLink Lk) b "norm" t = some R' →
      ∃ H, (seatAt h iU3).heard t = some H := by
    intro t R' h'
    obtain ⟨v, _, hl, _⟩ := reader_own K "norm" (Or.inl rfl) t R' h'
    obtain ⟨H, _, _, hH, _⟩ := lettersAt_ok h iU3 p hl
    exact ⟨H, hH⟩
  have h' : (match readerOf (statesOfLink Lk) b "norm" s with
      | some R => some R
      | Option.none => k6Silent P8 (statesOfLink Lk) b "norm" s) = some R := hR
  cases e : readerOf (statesOfLink Lk) b "norm" s with
  | some R' => exact key s R' e
  | none =>
    rw [e] at h'
    obtain ⟨t, ht, hR'⟩ := Option.bind_eq_some_iff.1 (show (withTables P8 s).bind
      (readerOf (statesOfLink Lk) b "norm") = some R from h')
    obtain ⟨H, hH⟩ := key t R hR'
    exact ⟨H, (heard_withTables h iU3 P8 s t ht).symm.trans hH⟩

theorem answers_of_formsInT (Rd : K9.Readers) (own : List (ℕ × ℕ)) (pc : ℕ) (run : String) (s : S)
    (h : formsInT Rd own pc run s = true) : ∃ R, Rd.forms pc run s = some R := by
  unfold formsInT at h
  split at h
  · rename_i a R _ hR
    exact ⟨R, hR⟩
  · exact absurd h Bool.false_ne_true

theorem answers_of_formsIn (Rd : K9.Readers) (own : List (ℕ × ℕ)) (pc : ℕ) (run : String) (s : S)
    (h : formsIn Rd own pc run s = true) : ∃ R, Rd.forms pc run s = some R := by
  unfold formsIn at h
  split at h
  · rename_i a R _ hR
    exact ⟨R, hR⟩
  · exact absurd h Bool.false_ne_true

/-! ## 2 At the table -/

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

set_option maxRecDepth 1000000 in
theorem ownT_open_342 : Item.formsT 24 4 "own" ∈ openQ linksFull PS 342 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem own_open_343 : Item.forms 24 4 "own" ∈ openQ linksFull PS 343 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem own_open_344 : Item.forms 24 4 "own" ∈ openQ linksFull PS 344 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem own_open_345 : Item.forms 24 4 "own" ∈ openQ linksFull PS 345 := by decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) {Fr : Frame}

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- **In front of the segment's second sending.** -/
theorem heard_at_T {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    {l6 piece6 : ℕ}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (K : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l6 piece6 (statesOfLink Lk) 3)
    (k : ℕ) (hopen : Item.formsT 24 4 "own" ∈ openQ linksFull PS k) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) k a) (hm : a.1.2.failed = none) :
    ∃ H, (seatAt Wp.hS (readsOf Wp)).heard a.1.2 = some H := by
  have hpub : (MGA).pub (.formsInT 24 4 "own") a.1 = true :=
    (onParts_of_on D.N MGA linksFull PS (fun a => a) k a ha hm).pub _
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hopen, List.mem_singleton.2 rfl⟩))
  have h1 : formsInT (D.Rd 24) (D.N.sent 24 0) 3 "norm" a.1.2 = true :=
    List.all_eq_true.1 hpub (3, "norm") (by rw [hown]; simp)
  rw [hreaders] at h1
  obtain ⟨R, hR⟩ := answers_of_formsInT _ _ _ _ _ h1
  exact heard_of_reader K P8 small a.1.2 R hR

/-- **Behind it.** -/
theorem heard_at_F {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    {l6 piece6 : ℕ}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (K : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l6 piece6 (statesOfLink Lk) 3)
    (k : ℕ) (hopen : Item.forms 24 4 "own" ∈ openQ linksFull PS k) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) k a) (hm : a.1.2.failed = none) :
    ∃ H, (seatAt Wp.hS (readsOf Wp)).heard a.1.2 = some H := by
  have hpub : (MGA).pub (.formsIn 24 4 "own") a.1 = true :=
    (onParts_of_on D.N MGA linksFull PS (fun a => a) k a ha hm).pub _
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hopen, List.mem_singleton.2 rfl⟩))
  have h0 : (if D.ah 3 "norm" = true then
      K9.formsInA (D.Rd 24) (D.N.sent 24) (D.N.group 24) 3 "norm" a.1.2
      else formsIn (D.Rd 24) (D.N.group 24) 3 "norm" a.1.2) = true :=
    List.all_eq_true.1 hpub (3, "norm") (by rw [hown]; simp)
  have h1 : formsIn (D.Rd 24) (D.N.group 24) 3 "norm" a.1.2 = true := h0
  rw [hreaders] at h1
  obtain ⟨R, hR⟩ := answers_of_formsIn _ _ _ _ _ h1
  exact heard_of_reader K P8 small a.1.2 R hR

/-- **Behind an accept of the head's own sub-protocol.** -/
theorem heard_behind
    {q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
    {l : ℕ} {bef : List (ℕ × ℕ)} {B bS : Block S Claim} (Hs : Seated Wp .two Fr q l bef B bS)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP .two) q.ds))
    (hb : q.ior.red.out a τ = some b)
    (hW : WellLaid ((seatAt Wp.hS (readsOf Wp)).ledger a.1.2)) :
    ∃ H, (seatAt Wp.hS (readsOf Wp)).heard b.1.2 = some H := by
  obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated Hs a b τ hb
  obtain ⟨hcan, hd'⟩ := canonical_of_below b6 a.1.2 b.1.2 rs gs hd
  obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp h6
  have hr : readsOf Wp = iU3 := by
    unfold readsOf
    rw [hu]
    rfl
  subst hbb
  have hd2 : (blockAt Wp.hS (readsOf Wp) (workOf Wp) l).decide a.1.2 rs gs = .ok b.1.2 := by
    rw [hr]
    exact hd'
  obtain ⟨_, H, _, _, _, _, _, hH, _⟩ := Came.mergeClaim_behind Wp l hd2 hW hcan
  exact ⟨H, hH⟩

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heard_of_reader
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.ownT_open_342
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.own_open_343
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.own_open_344
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.own_open_345
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heard_at_T
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heard_at_F
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heard_behind
