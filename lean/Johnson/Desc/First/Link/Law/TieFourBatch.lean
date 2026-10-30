-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TieFourBatch.lean: THE DEBT t4 OF THE TIES OF A LINK's FIRST PIECE (the
batching's) AT THE TABLE (`TieRestR`, LinkTiedR.lean), AT THE COMPOSED MEANING (`mgAll 𝔇 Mg₀`) AND
AT THE LAW's LETTERS AS TieThreeFour.lean AND WorthTiedR.lean HAVE THEM: the kind's own relation in
front of the piece (`relFW`: the listed runs' forms are worth 0 at the clamped reader, and the two
sentences on the lookup on the digits) gives what the row closes (`formsOf sub m`: six or seven
items "forms" and the two items "worth"), with what it reads (the pins). Theorems.

What is said.
  `formsOf_cases`: an item that the batching's row closes is an item "forms" whose run is not
    "weights", or one of the two items "worth" at the piece 7 + shift sub.
  `forms_at`: one item "forms": each of its runs is listed; the law's sentence at `rdC` is the
    composed meaning's at `seatTab` (formsQ_clamp, under its InsideAt); at a run
    that the composed meaning reads "ahead" the two forms are one where nothing is ahead
    (formsQA_iff, Johnson/Desc/Sound/FormsAhead.lean): the premise hno.
  `worth_at`: the two items "worth": the composed meaning's letter at the digits' piece IS the
    law's two sentences, by unfolding (worth_at_digits), at the letters
    fork := forkR · heard := heardD · D := 𝔇.sent · rad | seat | arr := 𝔇.l3's.
  `t4_batch`: **t4 AT THE BATCHING's PIECE**, ending in the field's own type at R := relFW.

Limits. PREMISES: what the table's row at the place closes and reads (closed facts on the written
list) · the digits' piece's number and place (closed facts on the public values) · every run of a
closed item is listed (a closed fact) · the piece's extractor is idle (the law's own hextb) ·
`InsideAt` at the part of each state in front, and hno ("no array of the open link is still to be
sent"), both asked only inside the condition `onTR`: SHOWN AT NO STATE HERE · `PinAsks` for the
pins' ride backward. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.TieThreeFour
import Johnson.Desc.First.Link.Law.WorthTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (atS Where segAt?)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers pinsOf formsOf shift)
open VerifiableInference.Desc.First.Look (digAt)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

/-- What the batching's row closes, by sorts. -/
theorem formsOf_cases (sub : ModelPart) (m : ℕ) (i : Item) (hi : i ∈ formsOf sub m) :
    (∃ kk r, i = .forms m kk r ∧ r ≠ "weights") ∨ i = .worth m (7 + shift sub) "planes" ∨
      i = .worth m (7 + shift sub) "keys" := by
  unfold formsOf at hi
  dsimp only at hi
  rcases List.mem_append.1 hi with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, _, rfl, by decide⟩
    · exact Or.inl ⟨_, _, rfl, by decide⟩
    · exact Or.inl ⟨_, _, rfl, by decide⟩
    · exact Or.inl ⟨_, _, rfl, by decide⟩
    · exact Or.inl ⟨_, _, rfl, by decide⟩
    · exact Or.inl ⟨_, _, rfl, by decide⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · split at h
    · obtain rfl := List.mem_singleton.1 h
      exact Or.inl ⟨_, _, rfl, by decide⟩
    · exact nomatch h

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "Mg" => mgAll 𝔇 Mg₀
local notation "rdW" => rdC (Cells := CellsQ rows cols) (Tok := Tok) 𝔇.cs 𝔇.arr 𝔇.ms
local notation "own" => 𝔇.N.group m
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- **One item "forms".** -/
theorem forms_at (items : List (ℕ × String)) (kk : ℕ) (r : String) (hr : r ≠ "weights")
    (hruns : ∀ p ∈ 𝔇.runs m kk r, p ∈ items) (s : S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT)
    (hin : ∀ x, segAt? s = some x → InsideAt 𝔇.cs 𝔇.ms own x)
    (hno : ∀ x, segAt? s = some x → ∀ b, K9.aheadIn (𝔇.N.sent m) own x b = none)
    (h : ∀ e ∈ items, formsQ (𝔇.Rd m) own e.1 e.2 s (rdW w)) :
    (mgAll 𝔇 Mg₀).forms m kk r (z, s) y w := by
  rw [mgAll_forms]
  refine ⟨fun p hp => ?_, fun e => absurd e hr⟩
  have h2 : formsQ (𝔇.Rd m) own p.1 p.2 s (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) :=
    (formsQ_clamp 𝔇.cs 𝔇.arr 𝔇.ms own (𝔇.Rd m) p.1 p.2 s w hin).1 (h p (hruns p hp))
  by_cases ha : 𝔇.ah p.1 p.2 = true
  · rw [if_pos ha]
    exact (formsQA_iff (𝔇.N.sent m) own (𝔇.Rd m) p.1 p.2 s _ hno).2 h2
  · rw [if_neg ha]
    exact h2

/-- **The two items "worth".** -/
theorem worth_at (pc : ℕ) (hpc : pc = Desc.K3.pieceAt X m true) (x : First.Look.Place)
    (tlD : HTailF2) (hdig : digAt X m = some (x, tlD)) (s : S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT)
    (h : WorthTwo forkR heardD x tlD 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link true j.1) 𝔇.l3.arr
      s w) :
    (mgAll 𝔇 Mg₀).worth m pc "planes" (z, s) y w ∧ (mgAll 𝔇 Mg₀).worth m pc "keys" (z, s) y w := by
  subst hpc
  rw [mgAll_worth]
  unfold fillK3Both
  constructor
  · rw [worth_at_digits X 𝔇.sent 𝔇.l3 _ m hdig]
    unfold worthDig
    rw [if_pos rfl]
    exact h.1
  · rw [worth_at_digits X 𝔇.sent 𝔇.l3 _ m hdig]
    unfold worthDig
    rw [if_neg (by decide), if_pos rfl]
    exact h.2

/-- **t4 AT THE BATCHING's PIECE.** -/
theorem t4_batch {C : CK} (sub : ModelPart) (items : List (ℕ × String)) (x : First.Look.Place)
    (tlD : HTailF2) (hins : (rowQ links pl k).ins = formsOf sub m)
    (hctx : (rowQ links pl k).ctx = pinsOf m) (hpc : 7 + shift sub = Desc.K3.pieceAt X m true)
    (hdig : digAt X m = some (x, tlD))
    (hruns : ∀ kk r, Item.forms m kk r ∈ formsOf sub m → ∀ p ∈ 𝔇.runs m kk r, p ∈ items)
    (hin : ∀ a, onK k a → ∀ x, segAt? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x)
    (hno : ∀ a, onK k a → ∀ x, segAt? a.1 = some x →
      ∀ b, K9.aheadIn (𝔇.N.sent m) own x b = none)
    (pb : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (hext : ∀ a τ w, pb.ext a τ w = w)
    (hpin : ∀ a τ b, onK k a → pb.ior.red.out a τ = some b →
      PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pb.base a.1 b.1) :
    ∀ a τ b w, onK k a → pb.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      relFW (𝔇.Rd m) own rdW items forkR heardD x tlD 𝔇.sent 𝔇.l3.rad
        (fun j => 𝔇.l3.seat x.link true j.1) 𝔇.l3.arr a (pb.ext a τ w) →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (insQ links pl k) a (pb.ext a τ w) := by
  intro a τ b w ha hout _ h hR
  rw [hext] at hR ⊢
  refine relAt_ins 𝔇.N Mg links pl _ k a w ha.1.2 (fun i hi => ?_) fun i hi => ?_
  · rw [hins] at hi
    have hW := worth_at 𝔇 Mg₀ z m (7 + shift sub) hpc x tlD hdig a.1 (strsOf F a.2) w hR.2
    rcases formsOf_cases sub m i hi with ⟨kk, r, rfl, hr⟩ | rfl | rfl
    · exact forms_at 𝔇 Mg₀ z m items kk r hr (hruns kk r hi) a.1 (strsOf F a.2) w (hin a ha)
        (hno a ha) hR.1
    · exact hW.1
    · exact hW.2
  · rw [hctx] at hi
    exact (ctxPins_iff 𝔇.N Mg z m a w).1
      (hc_at 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.N Mg (mgAll_pin 𝔇 Mg₀) z m pb (onK k) hpin a τ b w
        ha hout (ctx_of_outs 𝔇 Mg₀ links pl z k m hctx b w h)) i hi

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.formsOf_cases
#print axioms VerifiableInference.Desc.LinkJoin.forms_at
#print axioms VerifiableInference.Desc.LinkJoin.worth_at
#print axioms VerifiableInference.Desc.LinkJoin.t4_batch
