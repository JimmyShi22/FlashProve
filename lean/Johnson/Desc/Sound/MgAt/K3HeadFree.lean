-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3HeadFree.lean: in front of the output head's lookup on the calls, inside
the promise at the composed meaning (mgAll), at a state of the verifier without a mark: the ledger
is there, has its sizes, and is free above its next slot (FreeAt at the calls' seat). Statements and
proofs.

How. Two public items are open at that border (MgAt.k3_open_calls, by the kernel), and the promise
asks their tests:
  lookIn 24 3     at mgAll: lookInC: at some place of the lookup, k3OnIn: so the ledger is there,
                  with its sizes (sizedB)
  freeAbove 24    at mgAll: at the planned number of slots, the table's own freeAboveB
                  (Johnson/Desc/First/FillKeeper.lean), whose first half is the lookups' freeAboveB
and the lookups' freeAboveB_iff makes "free above" of that test at a ledger with its sizes.

  fork_of_onIn      k3OnIn p s = true → ∃ G, s.fork? = some G ∧ sizedB G = true
  free_of_keeper    First.freeAboveB n s = true → the lookups' freeAboveB s = true
  any_some          a test that some value of an option passes: there is the value
  headMg_pub        the promise at the border gives the test of every public item open there
  headMg_freeIn     FreeAt (K3.seatCalls claim).fork a.1

The premise hx (the head's place is there) is the statement's as it was asked; THE PROOF DOES NOT
SPEND IT: lookInC has its own place. The border is written MgAt.borderOf 24 false (= 340);
k3K 24 false (Johnson/Desc/First/Look/K3Base.lean) has the same text; that file is not imported
here.
Can the premises be met? As at headMg_tokIn (K3HeadIn.lean). Where the plan has no number of slots
for segment 24 the item freeAbove's test rejects, and the promise itself cannot be met there.
Limits. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAt.K3Open
import Johnson.Desc.Sound.OnParts
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Look.K3HeadFill
import Johnson.Desc.First.Look.K3CallsKeeps
import Johnson.Desc.First.Look.K3KeepsFree
import Johnson.Desc.First.Look.K3DigitsTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound.MgAt
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open VerifiableInference.OnPublicFiles (headLink sort_head FreeAt freeAboveB_iff sized_of_sizedB)
open VerifiableInference.Desc.First (Meaning Pub flatPlacesOf)
open VerifiableInference.Desc.First.Look (lookInC)

/-- In front of a lookup the ledger is there, with its sizes. -/
theorem fork_of_onIn {p : First.Look.P} {s : First.S} (h : Desc.K3.k3OnIn p s = true) :
    ∃ G, s.fork? = some G ∧ Desc.K3.sizedB G = true := by
  unfold Desc.K3.k3OnIn at h
  cases hp : p.shape with
  | none =>
    rw [hp] at h
    cases h
  | some sh =>
    rw [hp] at h
    simp only [Bool.and_eq_true] at h
    cases hf : s.fork? with
    | none =>
      rw [hf] at h
      exact absurd h.2 (by simp)
    | some G =>
      rw [hf] at h
      simp only [Option.any_some, Bool.and_eq_true] at h
      exact ⟨G, rfl, h.2.1.2⟩

/-- The table's own test on the ledger gives the lookups'. -/
theorem free_of_keeper {n : ℕ} {s : First.S} (h : First.freeAboveB n s = true) :
    VerifiableInference.OnPublicFiles.freeAboveB s = true := by
  unfold First.freeAboveB at h
  unfold VerifiableInference.OnPublicFiles.freeAboveB
  cases hf : s.fork? with
  | none =>
    rw [hf] at h
    cases h
  | some G =>
    rw [hf] at h
    exact (Eq.mp (Bool.and_eq_true _ _) h).1

/-- A test that some value of an option passes: there is the value. -/
theorem any_some {α : Type} {o : Option α} {f : α → Bool} (h : o.any f = true) :
    ∃ x, f x = true := by
  cases o with
  | none => cases h
  | some x => exact ⟨x, h⟩

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- The promise at the border gives the test of every public item that is open there. -/
theorem headMg_pub {Fr : Frame} (hM : Mg.more = {}) (z : P) (a : First.S × Fr.E.Str) (k : ℕ)
    (ha : onQ 𝔇.N (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) k a)
    (hu : a.1.failed = none) (q : Pub) (hq : q ∈ openAt k) :
    First.pubAll 𝔇.pubD Mg.pub q (z, a.1) = true := by
  have hmem : q ∈ pubQ (mgAll 𝔇 Mg).more linksFull (flatPlacesOf linksFull true) k := by
    rw [mgAll_more_closed 𝔇 Mg hM]
    exact hq
  have hp := (onParts_of_on 𝔇.N (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true)
    (fun s => (z, s)) k a ha hu).pub q (List.mem_append_left _ hmem)
  rw [mgAll_pub] at hp
  exact hp

/-- **The ledger is there, has its sizes, and is free above its next slot.** -/
theorem headMg_freeIn {Fr : Frame} {Cl : Type} (claim : Aff → Cl) {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (hl24 : headLink X = 24) (hM : Mg.more = {})
    (z : P) (a : First.S × Fr.E.Str)
    (ha : onQ 𝔇.N (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s))
      (borderOf 24 false) a)
    (hu : a.1.failed = none) : FreeAt (Desc.K3.seatCalls claim).fork a.1 := by
  letI := VerifiableInference.OnPublicFiles.k3SizesAt X
  letI := VerifiableInference.OnPublicFiles.k3PolicyAt X
  obtain ⟨o1, o2, -⟩ := k3_open_calls (l := 24) (by decide)
  -- the ledger, with its sizes
  have h1 := headMg_pub 𝔇 Mg hM z a _ ha hu _ o1
  have hs : First.Look.k3SortAt 𝔇.pubD.d3.X 24 3 = some false := by
    have e := sort_head X
    rw [hl24] at e
    exact e
  have h1' : First.pubAll 𝔇.pubD Mg.pub (.lookIn 24 3) (z, a.1) = true := h1
  rw [First.pubAll_lookIn 𝔇.pubD Mg.pub 24 3 false hs] at h1'
  unfold lookInC at h1'
  obtain ⟨p, hp⟩ := any_some h1'
  obtain ⟨G, hG, hsz⟩ := fork_of_onIn (Eq.mp (Bool.and_eq_true _ _) hp).1
  -- free above
  have h2 := headMg_pub 𝔇 Mg hM z a _ ha hu _ o2
  rw [First.pubAll_freeAbove] at h2
  obtain ⟨n, hn⟩ := any_some h2
  have hf : VerifiableInference.OnPublicFiles.freeAboveB a.1 = true := free_of_keeper hn
  have hS := sized_of_sizedB hsz
  exact ⟨G, hG, hS, (freeAboveB_iff hG hS).1 hf⟩

end VerifiableInference.Desc.Sound.MgAt

#print axioms VerifiableInference.Desc.Sound.MgAt.fork_of_onIn
#print axioms VerifiableInference.Desc.Sound.MgAt.free_of_keeper
#print axioms VerifiableInference.Desc.Sound.MgAt.any_some
#print axioms VerifiableInference.Desc.Sound.MgAt.headMg_pub
#print axioms VerifiableInference.Desc.Sound.MgAt.headMg_freeIn
