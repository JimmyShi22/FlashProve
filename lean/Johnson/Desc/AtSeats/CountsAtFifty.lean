-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/CountsAtFifty.lean: the row "TS.54", its fifty: IN THE GOALS' SCOPE, AT THE
NUMBERS CLOSED OVER THE FIRST CHAIN's OWN SUB-PROTOCOLS (N.atBlocks s links c.blocksInOrder, at any N s
links), THE TWO COUNTS AT EACH OF THE KIND K1's FIFTY LATER PLACES GO ON BY THE PLACE's LAYOUT's
TREES AND BY THE MESSAGES THAT IT SENDS: the binders trees and msgs of hear_K1
(Johnson/Desc/AtSeats/HearAtFifty.lean). IN LIGHT LETTERS: no50 l d and par50 Z G l d, typed
here, in the place of K1.noL and K1.parL (LaterOne.lean; one value each: by unfolding; by cases
on d).
A joining of what lies. A law file; no running text imports it.
  at_fifty: in scope: at the number no50 l d of the flat list stands a sub-protocol that declares
      what K1's text declares at the place par50 Z G₀ l d, and that place passes its own test on its
      parameters. By Johnson/IMR/'s k1_reads_of, k1_digits_of, hear_at_flat,
      flatIx_scope (the same three calls as k01_flat_reads, k01_flat_digits:
      K01LawTied.lean, which stands above heavy imports), alone_oracles, alone_planOk,
      retype_planOk and oracles_k1Quiet
  trees_fifty, msgs_fifty: the two binders

PREMISES THAT STAY. hok: every sub-protocol of the flat list passes its own test on its parameters
(FileDescription.planOk gives it). hps, hn: the flat list's places are the written list, which has no place
twice: hn is paid by Lean's kernel in Johnson/Desc/AtSeats/CountsAtFour.lean, hps in scope by
blockPlaces_full (Johnson/LPFK9R/SubsFull.lean), called in Johnson/Desc/AtSeats/CountsInScope.lean.

What is not claimed. That the composed meaning's N (P5J.At.N, Johnson/P5J/LettersAt.lean) is the
numbers so closed. Nothing on the verifier's state. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.CountsAtSend
import Johnson.Desc.K1.Law.QuietTellsNothing
import Johnson.Desc.Sound.AtDriver
import Johnson.IMR.K1Scope
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HashBuild
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart Numbers blockPlaces flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K1 (Par layOf oracles planOkOwn parLater gpOf laterAt)
open IM (k1Ix)
open ProofFile (Cl)

/-- The number, in the first chain's flat list, of segment l's later sending: d = false: the
commitment before the approximate range proof; d = true: the digits'. (K1.noL.) -/
abbrev no50 (l : ℕ) (d : Bool) : ℕ := 14 * l + k1Ix l d + 2

/-- That sending's place. (K1.parL, by cases on d.) -/
def par50 (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) : Par :=
  parLater G.first (gpOf Z) l (k1Ix l d + 1) (cond d 2 1)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **What stands at the fifty numbers.** -/
theorem at_fifty (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true) (l : ℕ) (hl : l < 25) (d : Bool) :
    ∃ b : Block S Cl, c.blocksInOrder[no50 l d]? = some b ∧
      b.oracles.flatten = (oracles (par50 Z Bs.G₀ l d)).flatten ∧
      planOkOwn (par50 Z Bs.G₀ l d) = true := by
  cases d with
  | true =>
    obtain ⟨Lk, b, Xl, pr, reads, digits, e1, e2, -, -, h⟩ := IM.k1_digits_of hS hR O l hl
    have h5 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) (k1Ix l true)] at h5
    have hp := hok b (List.mem_of_getElem? h5)
    rw [IM.alone_planOk h] at hp
    have hp1 : (planOkOwn (parLater Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2) &&
        digits.isSome) = true := (IM.retype_planOk _ hp).1
    exact ⟨b, h5, by rw [IM.alone_oracles h]; rfl, (Bool.and_eq_true_iff.1 hp1).1⟩
  | false =>
    obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, -, -, h⟩ := IM.k1_reads_of hS hR O l hl
    have h5 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) (k1Ix l false)] at h5
    have hp := hok b (List.mem_of_getElem? h5)
    rw [IM.alone_planOk h] at hp
    have hp0 := (IM.retype_planOk _ hp).1
    have hp1 : ((planOkOwn (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1) &&
        reads.isSome) && (IM.k1Quiet Bs.G₀ l Xl).planOk) = true := hp0
    refine ⟨b, h5, ?_, (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hp1).1).1⟩
    rw [IM.alone_oracles h]
    show ((laterAt Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1 reads : Block S Unit).oracles ++
      (IM.k1Quiet Bs.G₀ l Xl).oracles).flatten = _
    rw [K1.oracles_k1Quiet, List.append_nil]
    rfl

variable (N : Numbers) (s : OnBytes.Params.ReqShape) (links : List ModelPart)

/-- **The binder "trees" of hear_K1.** -/
theorem trees_fifty (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    (hps : blockPlaces c.blocksInOrder = flatPlacesOf linksFull true)
    (hn : (flatPlacesOf linksFull true).Nodup) :
    ∀ l < 25, ∀ d : Bool,
      (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[no50 l d + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[no50 l d]? +
          (layOf (par50 Z Bs.G₀ l d)).shapes.size := by
  intro l hl d
  obtain ⟨b, hb, ho, hB⟩ := at_fifty hS hR O hok l hl d
  exact (K1.counts_at_send N s links c.blocksInOrder _ hps hn (no50 l d) b hb _ ho hB).1

/-- **The binder "msgs" of hear_K1.** -/
theorem msgs_fifty (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    (hps : blockPlaces c.blocksInOrder = flatPlacesOf linksFull true)
    (hn : (flatPlacesOf linksFull true).Nodup) :
    ∀ l < 25, ∀ d : Bool,
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[no50 l d + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[no50 l d]? +
          (par50 Z Bs.G₀ l d).sent.size := by
  intro l hl d
  obtain ⟨b, hb, ho, hB⟩ := at_fifty hS hR O hok l hl d
  exact (K1.counts_at_send N s links c.blocksInOrder _ hps hn (no50 l d) b hb _ ho hB).2

end

end HashBuild

#print axioms HashBuild.at_fifty
#print axioms HashBuild.trees_fifty
#print axioms HashBuild.msgs_fifty
