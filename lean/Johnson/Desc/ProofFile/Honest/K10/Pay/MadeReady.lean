-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeReady.lean: the closing of a segment (K10): the test `ownReady` in front of the
job's rows (Honest/K2/AtPlan.lean) is the code switch's public test `publicOk` at the place behind the segment, and the test
`ownHeard` on what was heard.

  `forIn_all`          a loop that returns has gone on at each member, where a step either goes on or refuses
  `laid_of_ownLaid`    where `ownLaid` returns, every own message of these segments has an address and its arrays are laid
  `ownReady_of_laid`   `ownReady` returns where each own message has an address, its arrays are laid and its data is ready
  `addrs_of_place`     a place of the code switch has the addresses that the closing's job reads
  `ownReady_of_place`  `ownReady` at the closing's segments, from `publicOk` at a place at these segments and `ownHeard`

Limits. `publicOk` and `ownHeard` are premises here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeParts
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeShape
import Johnson.Desc.ProofFile.Honest.K2.Law.LaidLight
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open ProofFile.Honest.K2 (SegmentPub SwitchPlace arraysLaid ownLaid ownReady ownHeard publicOk switchPlaces)
open ProofFile.Honest.K2.Law (forIn_yields bind_yields placesAt switchPlaces_is)

/-- A loop that returns has gone on at each member, where a step either goes on or refuses. -/
theorem forIn_all {α : Type} (l : List α) (f : α → PUnit → Except String (ForInStep PUnit))
    (hy : ∀ x st, f x PUnit.unit = .ok st → st = .yield PUnit.unit)
    (h : forIn l PUnit.unit f = (.ok PUnit.unit : Except String PUnit)) :
    ∀ x ∈ l, f x PUnit.unit = .ok (.yield PUnit.unit) := by
  induction l with
  | nil =>
    intro x hx
    cases hx
  | cons a t ih =>
    rw [List.forIn_cons] at h
    cases e : f a PUnit.unit with
    | error s =>
      rw [e] at h
      cases h
    | ok st =>
      obtain rfl := hy a st e
      rw [e] at h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact e
      · exact ih h x hx

/-- **Where `ownLaid` returns, every own message of these segments has an address and its arrays are laid.** -/
theorem laid_of_ownLaid {D : RowData} {lay : OnBytes.Params.ReqLayout} {p : SwitchPlace} {segs : List SegmentPub}
    (h : ownLaid D lay p segs = .ok ()) :
    ∀ x ∈ segs.zipIdx, ∀ s ∈ (x.1.ownShapes (x.2 == 0)).zipIdx, ∃ a, p.addrs x.2 s.2 = some a ∧
      arraysLaid D lay x.1.sizes.codes s.1 x.2 s.2 a = true := by
  unfold ownLaid at h
  obtain ⟨⟨⟩, h1, -⟩ := bind_ok h
  intro x hx s hs
  have O := forIn_all _ _ (fun y st e => by
    obtain ⟨⟨⟩, -, e2⟩ := bind_ok e
    exact (Except.ok.inj e2).symm) h1 x hx
  obtain ⟨⟨⟩, i2, -⟩ := bind_ok O
  have I := forIn_all _ _ (fun y st e => by
    split at e
    · cases e
    · split at e
      · cases e
      · exact (Except.ok.inj e).symm) i2 s hs
  cases ha : p.addrs x.2 s.2 with
  | none =>
    simp only [ha] at I
    cases I
  | some a =>
    refine ⟨a, rfl, ?_⟩
    simp only [ha] at I
    by_contra c
    have c' : (!arraysLaid D lay x.1.sizes.codes s.1 x.2 s.2 a) = true := by simpa using c
    rw [if_pos c'] at I
    cases I

/-- **`ownReady` returns where each own message has an address, its arrays are laid and its data is ready.** -/
theorem ownReady_of_laid {D : RowData} {lay : OnBytes.Params.ReqLayout} {addrs : Nat → Nat → Option MsgAddr}
    {segs : List SegmentPub} {heard : List Fmt.Drawn}
    (h : ∀ x ∈ segs.zipIdx, ∀ s ∈ (x.1.ownShapes (x.2 == 0)).zipIdx, ∃ a, addrs x.2 s.2 = some a ∧
      arraysLaid D lay x.1.sizes.codes s.1 x.2 s.2 a = true ∧ D.readyAt heard a = true) :
    ownReady D lay (askPlace addrs) segs heard = .ok () := by
  unfold ownReady
  refine bind_yields (forIn_yields _ _ fun x hx => ?_)
    (bind_yields (forIn_yields _ _ fun n hn => ?_) rfl)
  · refine bind_yields (forIn_yields _ _ fun s hs => ?_) rfl
    obtain ⟨a, ha, h1, h2⟩ := h x hx s hs
    show (match addrs x.2 s.2 with
      | none => _
      | some a => _) = _
    rw [ha]
    simp [h1, h2]
    rfl
  · simp [askPlace] at hn

/-- A place of the code switch has the addresses that the closing's job reads. -/
theorem addrs_of_place {Z : ProofFile.Pub} {G : ProofFile.Ground} {p : SwitchPlace} (hp : p ∈ switchPlaces Z G) :
    p.addrs = addrsAt Z G := by
  rw [switchPlaces_is] at hp
  unfold addrsAt
  unfold placesAt at hp
  cases e1 : P1K2.prepOf Z G with
  | none =>
    rw [e1] at hp
    cases hp
  | some P =>
    cases e2 : ProofFile.spotsOf Z.cuts with
    | none =>
      rw [e1, e2] at hp
      cases hp
    | some sps =>
      rw [e1, e2] at hp
      obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hp
      rfl

/-- **`ownReady` at the closing's segments, from the code switch's public test at a place with these segments, and
`ownHeard`.** -/
theorem ownReady_of_place {Xi : Type} {Z : ProofFile.Pub} {G : ProofFile.Ground} {p : SwitchPlace} {rows : RowDataOf Xi} {x : Xi}
    {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub} {heard : List Fmt.Drawn}
    (hp : p ∈ switchPlaces Z G) (hPub : publicOk rows lay p segs x = true)
    (hOwn : ownHeard (rows x) (askPlace (addrsAt Z G)) segs heard = true) :
    ownReady (rows x) lay (askPlace (addrsAt Z G)) segs heard = .ok () := by
  have hl : ownLaid (rows x) lay p segs = .ok () := by
    unfold publicOk at hPub
    cases e : ownLaid (rows x) lay p segs with
    | error s =>
      rw [e] at hPub
      cases hPub
    | ok u =>
      cases u
      rfl
  refine ownReady_of_laid fun y hy s hs => ?_
  obtain ⟨a, ha, h1⟩ := laid_of_ownLaid hl y hy s hs
  rw [addrs_of_place hp] at ha
  refine ⟨a, ha, h1, ?_⟩
  have c := List.all_eq_true.1 (List.all_eq_true.1 hOwn y hy) s hs
  have c' : (((addrsAt Z G) y.2 s.2).map ((rows x).readyAt heard)).getD true = true := c
  rw [ha] at c'
  exact c'

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.forIn_all
#print axioms ProofFile.Honest.K10.laid_of_ownLaid
#print axioms ProofFile.Honest.K10.ownReady_of_laid
#print axioms ProofFile.Honest.K10.addrs_of_place
#print axioms ProofFile.Honest.K10.ownReady_of_place
