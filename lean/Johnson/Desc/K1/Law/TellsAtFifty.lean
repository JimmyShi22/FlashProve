-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TellsAtFifty.lean: THE ROW N6
OF K01_law: IN SCOPE, WHAT THE DESCRIPTION's OWN BLOCK AT EACH OF KIND K1's FIFTY LATER PLACES TELLS
OF THE TREES THAT IT SENDS IS THE PLACE's LAYOUT (K1.Declares, Johnson/Desc/K1/Law/Declares.lean).
Statements with their proofs.
OBJECT. The first chain's flat list c.blocksInOrder of the proof file's written description, at the numbers
14 l + k1Ix l d + 2; Sound.toldBy c.blocksInOrder (Johnson/Desc/Sound/BaseOfBookFit.lean): for each block the
oracles beneath the roots that it sends.
USER. The field "tells" of PlanK1 (Johnson/Desc/K1/Law/CallsC.lean), at told := toldBy
c.blocksInOrder: parL Z G₀ l false | true are the two places' numbers below, by unfolding.
LETTERS. As in Johnson/Desc/K1/Law/K01LawTied.lean (hS, hR, O: in scope; the description is open).
  oracles_blockAt, oracles_readsQuietAt, oracles_k1Quiet: the quiet block behind the reads tells
                   nothing (where none could be made the refuser tells nothing either).
  can_of_planOk    the kind's test on the plan holds "the trees can be laid".
  told_of          what a block tells whose field "oracles" is K1's own text's, with nothing behind.
  tells_digits, tells_reads: **the two sorts of place.**
PREMISE THAT STAYS. hok: every block of the flat list passes its own test on the plan (a clause of
blocksOk, Johnson/Desc/Block.lean): it is spent for "the trees can be laid".
What is not claimed. That the description's tests say yes. Nothing on soundness.
oracles_blockAt, oracles_readsQuietAt and oracles_k1Quiet stand in
Johnson/Desc/K1/Law/QuietTellsNothing.lean, which is imported.

-/
import Johnson.Desc.K1.Law.K01LawTied
import Johnson.Desc.K1.Law.QuietTellsNothing
import Johnson.Desc.K1.Law.Declares
import Johnson.Desc.Sound.BaseOfBookFit
import Johnson.Desc.K1.Law.BookAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Oracle)
open VerifiableInference.Desc.Sound (toldBy)
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)
open ProofFile (Cl)
open IM (Open LaidAlone k1Reads k1Quiet k1Ix k1PlaceL)

/-! ## What a sending's block tells -/

/-- The kind's test on the plan holds "the trees can be laid". -/
theorem can_of_planOk (P : Par) (h : planOkOwn P = true) :
    layTrees P.codes P.sent = some (layOf P) := by
  unfold planOkOwn at h
  have h1 := (Bool.and_eq_true_iff.1 h).1
  unfold planOk at h1
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.1.2
  rw [Own.treesCan_eq] at h2
  obtain ⟨lay, hl⟩ := Option.isSome_iff_exists.1 h2
  unfold layOf
  rw [hl]
  rfl

/-- What a block tells whose field "oracles" is K1's own text's. -/
theorem told_of (P : Par) (h : planOkOwn P = true) (os : List (List Oracle))
    (e : os = oracles P) :
    ∃ decl, os.flatMap id = decl ∧ Declares decl (layOf P) P.sent.size (tenantOf P) := by
  obtain ⟨decl, e1, hD⟩ := oracles_declares P (layOf P) (can_of_planOk P h)
  exact ⟨decl, by rw [e, e1]; simp, hD⟩

theorem toldBy_at {T C : Type} (bs : List (Block T C)) (k : ℕ) (b : Block T C)
    (h : bs[k]? = some b) : (toldBy bs)[k]? = some (b.oracles.flatMap id) := by
  unfold toldBy
  rw [List.getElem?_map, h]
  rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **A digits' place.** -/
theorem tells_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true) (l : ℕ) (hl : l < 25) :
    ∃ decl, (toldBy c.blocksInOrder)[14 * l + k1Ix l true + 2]? = some decl ∧
      Declares decl (layOf (parLater Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2))
        (parLater Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2).sent.size
        (tenantOf (parLater Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2)) := by
  obtain ⟨b, digits, h5, h⟩ := k01_flat_digits hS hR O l hl
  have hp := hok b (List.mem_of_getElem? h5)
  rw [IM.alone_planOk h] at hp
  have hp1 : (planOkOwn (parLater Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2) &&
      digits.isSome) = true := (IM.retype_planOk _ hp).1
  obtain ⟨decl, e, hD⟩ := told_of _ (Bool.and_eq_true_iff.1 hp1).1 b.oracles
    (by rw [IM.alone_oracles h]; rfl)
  exact ⟨decl, by rw [toldBy_at _ _ b h5, e], hD⟩

/-- **A reads' place.** -/
theorem tells_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true) (l : ℕ) (hl : l < 25) :
    ∃ decl, (toldBy c.blocksInOrder)[14 * l + k1Ix l false + 2]? = some decl ∧
      Declares decl (layOf (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1))
        (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1).sent.size
        (tenantOf (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1)) := by
  obtain ⟨b, Xl, reads, h5, _, h⟩ := k01_flat_reads hS hR O l hl
  have hp := hok b (List.mem_of_getElem? h5)
  rw [IM.alone_planOk h] at hp
  have hp1 : ((planOkOwn (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1) &&
      reads.isSome) && (k1Quiet Bs.G₀ l Xl).planOk) = true := (IM.retype_planOk _ hp).1
  have hp2 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hp1).1).1
  obtain ⟨decl, e, hD⟩ := told_of _ hp2 b.oracles (by
    rw [IM.alone_oracles h]
    show oracles (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1) ++
      (k1Quiet Bs.G₀ l Xl).oracles = _
    rw [oracles_k1Quiet, List.append_nil])
  exact ⟨decl, by rw [toldBy_at _ _ b h5, e], hD⟩

end

end VerifiableInference.Desc.K1
