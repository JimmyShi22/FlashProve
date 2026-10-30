-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/HRdAtBase.lean: k01_fifty_atBase's BINDER
hRd, TO THE LETTER, FROM Fwd RUN BY RUN AT THE CHAIN's OWN LINKS. A statement
with its proof.

Why. At the composed meaning the readers and the map of names are not letters:
MgData.Rd is K9.readersAt 𝔇.lk X (headLink X) and MgData.runs is runsAt 𝔇.links, by the make
(Johnson/Desc/Sound/MgAll.lean). So hRd speaks of K9.readersOfLink at the link 𝔇.lk l, at the
written list of runs (Johnson/Desc/K1/Law/ReadersByRun.lean: runsL). Where the chain has no link of the number,
the reader answers nowhere and nothing is owed.

OBJECT · USER. Johnson/Desc/K1/Law/K01FiftyAtBase.lean's binder hRd (G₀ := Bs.G₀).
PAID INSIDE. The map of names (hDlk, a binder that the top has) · the door's list (runsFit_mw1, by
the kernel) · a segment without a link · **the approximate range proof's run at all 25 digits'
places** (pairStays_small · fwd_digits).
THE PREMISE THAT STAYS. hF: behind the accept and the promise in front, at each run p of
runsL l false (4 at a segment of the sort "layers", 7 at "attention", 7 at the output head), at
both later places of segment l: Fwd (readersOfLink (holesAt XV (headLink XV) l lk) lk) p.1 p.2.
What is not claimed. hF of any run. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.ReadersByRun
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (Readers LinkHoles readersOfLink holesAt readersAt readersAt_some
  readersAt_none)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

/-- A run on the digits' list is on the reads' list, or it is the approximate range proof's. -/
theorem runsL_true (l : ℕ) (p : ℕ × String) (h : p ∈ runsL l true) :
    p ∈ runsL l false ∨ p.2 = "K8.equations" := by
  unfold runsL at h ⊢
  cases e : linksFull[l]? with
  | none =>
    rw [e] at h
    cases h
  | some sub =>
    rw [e] at h
    cases sub <;>
      · simp only [Option.map_some, Option.getD_some, runsOfSort, if_true, List.mem_append,
          List.mem_singleton] at h
        rcases h with h | h
        · left
          simpa [runsOfSort] using h
        · right
          rw [h]

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}

/-- **hRd, to the letter.** -/
theorem hRd_atBase (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (Z : ProofFile.Pub)
    (G₀ : ProofFile.Ground) (hDlk : Dm.links = linksFull)
    (hF : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, G₀.built[l]? = some X → ∀ lk, Dm.lk l = some lk →
      ∀ x x' y, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true)
        (noL l d) x y →
      ∀ p ∈ runsL l false,
        Fwd (readersOfLink (holesAt XV (headLink XV) l lk) lk) p.1 p.2 x.2 x'.2) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → (Pub.formsIn m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨ Pub.formsInT m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) → ReadersStay (dK Dm.pubD Dm.sent) m j r x.2 x'.2 := by
  intro l hl d X arrs hX
  refine hRd_of_runs Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) Dm.pubD
    (show runsAt Dm.links = runsAt linksFull by rw [hDlk]) (blkL Z G₀ l d X arrs) l d (runsL l d)
    (runsFit_mw1 Dm dk mgBase rfl l hl d) ?_
  intro x x' y hy hIn p hp
  show Fwd (readersAt Dm.lk XV (headLink XV) l) p.1 p.2 x.2 x'.2
  cases e : Dm.lk l with
  | none =>
    rw [readersAt_none _ _ _ _ e]
    intro R hR
    cases hR
  | some lk =>
    rw [readersAt_some _ _ _ _ lk e]
    cases d with
    | false => exact hF l hl false X arrs hX lk e x x' y hy hIn p hp
    | true =>
      rcases runsL_true l p hp with h | h
      · exact hF l hl true X arrs hX lk e x x' y hy hIn p h
      · obtain ⟨b, n⟩ := p
        obtain rfl : n = "K8.equations" := h
        exact fwd_digits Z G₀ l X arrs _ _ lk rfl (b, "K8.equations")
          (pairStays_small XV (headLink XV) l lk b) x x' hy

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.runsL_true
#print axioms VerifiableInference.Desc.K1.hRd_atBase
