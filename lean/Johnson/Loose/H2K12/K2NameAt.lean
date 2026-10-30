-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.IMR.K2Seat
import Johnson.IMR.SameSpot
import Johnson.IMR.BackSeat
import Johnson.IMR.BackPlace
import Johnson.IMR.PureChain
/-
Johnson/Loose/H2K12/K2NameAt.lean: Code switching (the kind K2) on the
proof file's first chain: AT EACH OF THE 25 WRITTEN ADDRESSES OF THE KIND, THE SUB-PROTOCOL THAT STANDS THERE IN THE FIRST CHAIN's FLAT LIST BEARS
THE NAME OF THE PLAN's PLACE AT THAT ADDRESS. At an opening of the IOP as written in Lean, in the goals' scope, under "no two places of the kind
have one address". Statements and proofs: calls of other files' lemmas; nothing is evaluated.
What for. Where the verifier's entry test on the division into sub-protocols accepts, the flat list's names are written ones:
with this file so are the names of the plan's places of the kind, and by a name's head goes a place's dress
(`IM.spot_head`, Johnson/IMR/K2Seat.lean).
  `mem_pure`: a place of the plan's list that is of the kind K2 is a member of the kind's list of places.
  `name_at_hear`: the step at a place in front of a segment's batching: `IM.hear_first_spot` (Johnson/IMR/SameSpot.lean) names the
    first place, but the last, of the plan's list at the address (a member of a list without its last is a member of the
    list); it is the given one, since no two have one address.
  `k2_name_at`: at ⟨1, some l, 1, K2⟩ for 1 ≤ l < 24 (`IM.k2_link_of`), at ⟨1, some 24, 2, K2⟩ (`IM.k2_head_of`) and at
    ⟨1, none, 1, K2⟩ (`IM.chain_back`, `IM.back_at_flat`).
What it is not. "No two places of the kind have one address" is a premise here. It says nothing on what the sub-protocol does.
NO EXAMPLE BY A THEOREM HERE of an opening in scope. No soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)

/-- A place of the plan's list that is of the kind K2 is a member of the kind's list of places. -/
theorem mem_pure {Z : ProofFile.Pub} {sps : List ProofFile.Spot} (hs : ProofFile.spotsOf Z.cuts = some sps) {sp : ProofFile.Spot}
    (h : sp ∈ sps) (hk : sp.place.kind = KindName.K2) : sp ∈ P1K2.purePlaces Z := by
  unfold P1K2.purePlaces
  rw [hs]
  exact List.mem_filter.2 ⟨h, by simp [hk]⟩

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The step at a place in front of a segment's batching.** -/
theorem name_at_hear (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hA : ((P1K2.purePlaces Z).map (·.place)).Nodup) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ) (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K2)
    {Lk : Link S ProofFile.Cl} {b : Block S ProofFile.Cl} (e1 : c.links[l]? = some Lk) (e2 : Lk.hear[i]? = some b)
    (hpl : b.place = { chain := 1, link := some l, piece := i + 1, kind := .K2 }) {sp : ProofFile.Spot}
    (hsp : sp ∈ P1K2.purePlaces Z)
    (ha : sp.place = { chain := 1, link := some l, piece := i + 1, kind := .K2 }) :
    ∃ b ∈ c.blocksInOrder, b.place = sp.place ∧ b.name = sp.name := by
  obtain ⟨Lk', b', sp', e1', e2', hf, hn⟩ := IM.hear_first_spot O l sub hl i .K2 hk (by decide)
  obtain rfl : Lk' = Lk := Option.some.inj (e1'.symm.trans e1)
  obtain rfl : b' = b := Option.some.inj (e2'.symm.trans e2)
  have hm : sp' ∈ Bs.spots := List.dropLast_subset _ (List.mem_of_find?_eq_some hf)
  have hp' : sp'.place = { chain := 1, link := some l, piece := i + 1, kind := .K2 } := by
    simpa using List.find?_some hf
  have hm' : sp' ∈ P1K2.purePlaces Z := mem_pure (IM.base_made O.made).1 hm (by rw [hp'])
  obtain rfl : sp' = sp := List.inj_on_of_nodup_map hA hm' hsp (hp'.trans ha.symm)
  exact ⟨b', IM.hear_mem_flat e1 e2, hpl.trans ha.symm, hn⟩

end

/-- **At each of the 25 written addresses of the kind, the flat list's sub-protocol bears the plan's place's name.** -/
theorem k2_name_at {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hA : ((P1K2.purePlaces Z).map (·.place)).Nodup) {sp : ProofFile.Spot} (hsp : sp ∈ P1K2.purePlaces Z)
    (ha : (∃ l, 1 ≤ l ∧ l < 24 ∧ sp.place = ⟨1, some l, 1, .K2⟩) ∨ sp.place = ⟨1, some 24, 2, .K2⟩ ∨
      sp.place = ⟨1, none, 1, .K2⟩) :
    ∃ b ∈ c.blocksInOrder, b.place = sp.place ∧ b.name = sp.name := by
  rcases ha with ⟨l, h1, h24, ha⟩ | ha | ha
  · obtain ⟨Lk, b, x, e1, e2, -, hla, -⟩ := IM.k2_link_of hS hR O l h1 h24
    have hpl : b.place = { chain := 1, link := some l, piece := 0 + 1, kind := .K2 } := by
      rcases hla with h | ⟨fb, -, h⟩
      · exact IM.alone_place h
      · exact congrArg (fun z : Block S ProofFile.Cl => z.place) h
    have hl0 : (l == 0) = false := by simpa using (by omega : l ≠ 0)
    by_cases he : l % 2 = 0
    · have h := IM.subs_at hS hR O.pub O.blank (g := l / 2) (by omega)
      rw [show 2 * (l / 2) = l by omega] at h
      exact name_at_hear O hA l .layers h 0 (by rw [hl0]; rfl) e1 e2 hpl hsp ha
    · have h := IM.subs_att hS hR O.pub O.blank (g := l / 2) (by omega)
      rw [show 2 * (l / 2) + 1 = l by omega] at h
      exact name_at_hear O hA l .attention h 0 (by rw [hl0]; rfl) e1 e2 hpl hsp ha
  · obtain ⟨Lk, b, x, e1, e2, -, hla, -⟩ := IM.k2_head_of hS hR O
    exact name_at_hear O hA 24 .head (IM.subs_head hS hR O.pub O.blank) 1
      (by unfold kindsBeforeBatching; rfl) e1 e2 (IM.alone_place hla) hsp ha
  · obtain ⟨-, -, -, hall⟩ := IM.base_made O.made
    obtain ⟨b, e1, sp', hm, L, -, b', -, es, -, hla⟩ :=
      IM.chain_back hall (IM.makers_K9 Z Bs.G₀) O.places O.chain 0 .K2 (fun sv => by cases sv <;> rfl)
        (by decide)
    have hm' : sp' ∈ P1K2.purePlaces Z := mem_pure (IM.base_made O.made).1 hm (by rw [es])
    obtain rfl : sp' = sp := List.inj_on_of_nodup_map hA hm' hsp (es.trans ha.symm)
    refine ⟨_, List.mem_of_getElem? (IM.back_at_flat e1), ?_, ?_⟩
    · show b.place = sp'.place
      rw [IM.alone_place hla, es]
    · show b.name = sp'.name
      exact IM.alone_name hla

end H2K12

#print axioms H2K12.mem_pure
#print axioms H2K12.name_at_hear
#print axioms H2K12.k2_name_at
