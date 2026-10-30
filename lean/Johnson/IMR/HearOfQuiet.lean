--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/HearOfQuiet.lean: IN THE GOALS' SCOPE, AT THE OLDER HASH: WHERE ONE OF
OUR 101 NUMBERS STANDS: if the sub-protocol b at number k of the first chain is of the kind K3, K4,
K5, K6, K8 or K11, then k is 14 l + i + 2, in front of link l's batching, and b is a lot's own
sub-protocol b', seated alone at the place (1, l, i + 1, its kind). One theorem, proved.



  hear_of_quiet   the case split flat_cases, once, with its one living case
    handed out: the same split stands inside three_at and rows_at.

OBJECT: c.blocksInOrder[k]. USER: Johnson/IMR/K8Owed.lean. LETTERS: none beside the scope's.

What is not claimed. Anything on a state of the verifier. No soundness.
-/
import Johnson.IMR.RideAt

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S kindsBeforeBatching closeKinds backKinds)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **WHERE ONE OF OUR 101 NUMBERS STANDS.** -/
theorem hear_of_quiet (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hq : quietMaker b.place.kind = true) :
    ∃ (l i : ℕ) (k0 : KindName) (b' : Block S Cl) (name : String), l < 25 ∧
      (kindsBeforeBatching (subAt l) (l == 0))[i]? = some k0 ∧
      (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) ∧
      b'.place = { chain := 1, link := some l, piece := i + 1, kind := k0 } ∧
      LaidAlone ProofFile.sameReply b b' name
        { chain := 1, link := some l, piece := i + 1, kind := k0 } ∧
      k = 14 * l + i + 2 := by
  have hkind : kindW k = some b.place.kind := by
    unfold kindW
    rw [place_at hS hR O hb]
    rfl
  cases flat_cases hS hR O k b hb with
  | front b hr hd =>
    rw [kinds_ends.1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | laid l hl b hr hd =>
    rw [(kinds_at hl).1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | first l hl k0 b b' hk lot hp hj =>
    rw [joined_spot hj] at hq
    have hq' : quietMaker k0 = true := hq
    exfalso
    by_cases h24 : l < 24
    · have e := (first_kind l h24).symm.trans hk
      by_cases h0 : l = 0
      · rw [if_pos h0] at e
        rw [← Option.some.inj e] at hq'
        exact absurd hq' (by decide)
      · rw [if_neg h0] at e
        rw [← Option.some.inj e] at hq'
        exact absurd hq' (by decide)
    · obtain rfl : l = 24 := by omega
      obtain rfl : KindName.K7 = k0 := Option.some.inj hk
      exact absurd hq' (by decide)
  | hear l hl i hi k0 b b' name hk lot hp hla =>
    exact ⟨l, i, k0, b', name, hl, hk, lot, hp, hla, rfl⟩
  | batch l hl Lk p e1 hp hal =>
    rw [(kinds_at hl).2.1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | behind l hl Lk b e1 hr hd =>
    rw [(kinds_at hl).2.2.1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | close l hl p Q q k0 b x hp hQ hk ex hla =>
    rw [alone_place hla] at hq
    have hm := List.mem_of_getElem? hk
    have hq' : quietMaker k0 = true := hq
    exfalso
    clear hq hla hk hkind hb ex
    revert hm hq'
    cases k0 <;> decide
  | cleared l hl fs f b hfs hf hr hd =>
    rw [(kinds_at hl).2.2.2.2.2.2] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | back q k0 b b' name hk lot hp hla =>
    have hq' : quietMaker k0 = true := by
      have e : b.place = { chain := 1, link := none, piece := q + 1, kind := k0 } :=
        alone_place hla
      have hq2 : quietMaker b.place.kind = true := hq
      rw [e] at hq2
      exact hq2
    have hm := List.mem_of_getElem? hk
    exfalso
    clear hq hla hk hkind hb hp lot
    revert hm hq'
    cases k0 <;> decide
  | last lot hla =>
    rw [kinds_ends.2.2] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)

end IM

#print axioms IM.hear_of_quiet
