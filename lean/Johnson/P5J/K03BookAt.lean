-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03BookAt.lean: THE LOOKUPS' LEDGER's DEBTS «book · tells», AND TWO OF THE THREE PREMISES OF k03_base_at, AT THE CLOSED CONSTANT.
FIRST OF ALL: bookFit AT THE CONSTANT IS TRUE BY THE MAKE AND SAYS NOTHING OF cF (see k03_book_at).
  k03_book_at: bookFit (At.N Zp cF) PS (At.told cF) = true, AT EVERY Zp AND cF: NO PREMISE. IT IS TRUE BY THE MAKE: At.N is «… .withTold At.ps (At.told cF)»: the two numbers by place that the test reads ARE laid off that very telling (bookFit_withTold, Johnson/Desc/Sound/BaseOfBookFit.lean; the places have no twin: flatPlaces_nodup, Johnson/Desc/ProofFile/Law/KindPlaces.lean). SO THE TEST SAYS NOTHING OF cF HERE: what it is spent for (the pieces' bases are the numbers' treesAt) is carried by the telling being the chain's own.
  k3_tells_nothing: a block that the kind's own constant K3.theStated returns tells no tree: its oracles, flattened, are the empty list. (Other files have the like for the count of told messages; no sentence on the oracles lay.)
  k03_tells_at: under the head: ∀ l < 25, ∀ d, (At.told cF)[k3K l d]? = some []: the ledger's tells | hn at all fifty.
  k03_blocks_at: k03_base_at's hb, under the head.
  k03_bookHeld_at: k03_base_at's hf: NO PREMISE (as k03_book_at; the held blocks tell what the blocks tell).
NOT HERE: k03_base_at's THIRD, hg : fenceFit (At.N Zp cF) linksFull PS = true: a theorem for it lies (P5T.fence_in_scope) UNDER the entry tests' first pin and the written cut, in Johnson/P5T/FenceTie.lean: here it stays a named test. (Where this and lean/THEOREM.md differ, the page holds.) (A limit on that test: it bounds the sampled tenants' trees from above; that they are exactly the told ones comes from seatsFitP.)

Limits. It pays two debts of each of the fifty and two premises of one lemma. The head is a premise; a member of it is proved at the second hash function OnBytes.secondHashFunction, at two written sets of public files VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap, in the side library (AtFullSide/Top/: headMember_zFull, headMember_zGap); at other files or hashes none is shown. At OnBytes.secondHashFunction (the opening's lemmas stand there).
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03PiecesAt
import Johnson.Desc.Sound.BaseOfBookFit
import Johnson.Desc.Sound.PieceSeated
import Johnson.Desc.ProofFile.Law.KindPlaces
import Johnson.IMR.K3Seat
import Johnson.IMR.MsgsSeat
import Johnson.IMR.FlatScope
import Johnson.IMR.PlanOkFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Block Place)
open VerifiableInference.Desc.Sound (linksFull held)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **book, at the constant: by the make.** -/
theorem k03_book_at (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) :
    VerifiableInference.Desc.First.bookFit (At.N Zp cF)
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true) (At.told cF) = true :=
  VerifiableInference.Desc.Sound.bookFit_withTold _ _ (At.told cF) (ProofFile.Law.flatPlaces_nodup linksFull true)

/-- The kind's own block, before it is joined or stated, tells no tree. -/
theorem k3Own_tells {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place)
    {b : Block VerifiableInference.Desc.First.S Cl}
    (h : VerifiableInference.Desc.K3.theOwn claim runs X codes shape a = some b) :
    b.oracles.flatten = [] := by
  unfold VerifiableInference.Desc.K3.theOwn at h
  split at h
  · cases h
  obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨digits, -, h⟩ := List.exists_of_findSome?_eq_some h
  split at h
  · cases h
  obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sent, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨laid, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨key, -, h⟩ := Option.map_eq_some_iff.1 h
  dsimp only at h
  split at h
  · subst h
    exact List.flatten_eq_nil_iff.2 fun _ k => Meaning.Carry.map_nil_mem k
  · subst h
    exact List.flatten_eq_nil_iff.2 fun _ k => Meaning.Carry.map_nil_mem k

/-- **A lookup argument's block tells no tree.** -/
theorem k3_tells_nothing (claim : Aff → ProofFile.Cl)
    (readers : Nat → Option (VerifiableInference.Desc.K3.Readers VerifiableInference.Desc.First.S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    {b : Block VerifiableInference.Desc.First.S ProofFile.Cl}
    (h : VerifiableInference.Desc.K3.theStated claim readers X codes shape a = some b) :
    b.oracles.flatten = [] := by
  unfold VerifiableInference.Desc.K3.theStated at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  have e : b.oracles = w.oracles := by
    split at h
    · cases h
      rfl
    · split at h
      · cases h
        rfl
      · split at h
        · cases h
          rfl
        · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
          rfl
  rw [e]
  unfold VerifiableInference.Desc.K3.theWhole at hw
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hw
  have k := k3Own_tells claim true X codes shape a ho
  split
  · show (o.oracles ++ _).flatten = []
    rw [List.flatten_append, k]
    rfl
  · exact k

/-- **tells, at all fifty, under the head.** -/
theorem k03_tells_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ l, l < 25 → ∀ d : Bool, (At.told cF)[k3K l d]? = some [] := by
  intro l hl d
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of h.scope h.reads O l hl d
  have q := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by omega : l ≤ 24) (IM.k3Ix l d)] at q
  have t : b.oracles.flatten = [] := by
    rw [IM.alone_oracles e4]
    exact k3_tells_nothing _ _ _ _ _ _ e3
  rw [At.told_is, List.getElem?_map, q]
  exact congrArg some t

/-- **k03_base_at's hb, under the head.** -/
theorem k03_blocks_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    VerifiableInference.Desc.blocksOk ((F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map
      (held (P := (F0T OnBytes.secondHashFunction Zp Np cF).XiPub))) = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  rw [VerifiableInference.Desc.Sound.blocksOk_held]
  exact IM.blocksOk_of_planOk O h.laid.planOk

/-- **k03_base_at's hf: by the make.** -/
theorem k03_bookHeld_at (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) :
    VerifiableInference.Desc.First.bookFit (At.N Zp cF)
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true)
      (VerifiableInference.Desc.First.toldOf ((F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map
        (held (P := (F0T OnBytes.secondHashFunction Zp Np cF).XiPub)))) = true := by
  rw [← told_two, VerifiableInference.Desc.Sound.toldOf_held]
  exact k03_book_at Zp cF

end P5J

#print axioms P5J.k03_book_at
#print axioms P5J.k3Own_tells
#print axioms P5J.k3_tells_nothing
#print axioms P5J.k03_tells_at
#print axioms P5J.k03_blocks_at
#print axioms P5J.k03_bookHeld_at
