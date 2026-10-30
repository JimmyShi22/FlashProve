-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/SharesParts.lean: what has to be proved of one part's stops, and
`ChainHeld` from the parts' conditions. `ChainHeld` (Honest/Law/SharesChain.lean) is stated gate by
gate over `chainGates`: which gate belongs to which part, and at which stretch of the chain's data
it is, has to be read from three definitions. This file has `StopDebt`, one part's own condition;
which gate of a list and of a chain belongs to which part (`rowGates_mem`, `chainGates_mem`); and
`chainHeld_of`: the parts' conditions give `ChainHeld`. So the lemmas on the sets of `honestBatchProverOfFile`
(`bad_held`, `hid_held`, Honest/Law/SharesStops.lean; `hid_held_on`, Honest/Law/SharesOn.lean) can
be applied to what is proved part by part.

What this is. A definition, meant as a hypothesis; two lemmas on lists; and a conditional lemma
about a definition of this folder. None of the library's goals. Probabilities are over the
verifier's messages, drawn uniformly (`Iop.prRho`), at a fixed private input and instance.

  `StopDebt`, `stopDebt_none`, `rowGates_mem`, `chainGates_mem`, `chainHeld_of`

Trivially met. A number of 1 or more.

Limits.
  * It is not proved that any part of the protocol satisfies `StopDebt`.
  * The number is a parameter here; `bad_held` and `hid_held` take the stated shares' values.
  * The kit C of verifier's messages is a parameter.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.SharesChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc (Block)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl V W Y : Type}

/-- **What has to be proved for the stops of one part**, by whoever writes the part. `sp`: which
results of `Part.stopAt` count: for a first stop `(·.isSome)`, at v := none; for a second stop
`(· == some Why.hid)`, at v := what the part sees of an input with its trace. `dsp`: the data of the
part's own rounds. `q`: its number; in the lemmas on the sets of `honestBatchProverOfFile` it is the stated share's
value. The bound is asked at every list `fr` of challenges heard before the part's own, of any
length. A stop that reads such challenges may meet that with the number 1 alone. Should such a stop
come, the definition would take a parameter P on `fr` (as in `MarkDebt`, Honest/Law/CoverJoin.lean).
-/
def StopDebt (C : CK) (sp : Option Why → Bool) (v : Option V) (p : Part V W Y) (dsp : List RDT)
    (q : ℝ≥0∞) : Prop :=
  ∀ fr, Iop.prRho {ρ : Iop.Rho (uLT C dsp) | sp (p.stopAt v fr (drawnT C dsp ρ)) = true} ≤ q

/-- **For a part that is never stopped nothing has to be proved**: its condition holds at any
number. -/
theorem stopDebt_none (C : CK) (sp : Option Why → Bool) (v : Option V) (p : Part V W Y)
    (dsp : List RDT) (q : ℝ≥0∞) (hsp : sp none = false) (h : ∀ loc ds, p.stopAt v loc ds = none) :
    StopDebt C sp v p dsp q := fun fr =>
  le_trans (Iop.prRho_empty _ fun ρ hρ => by
    have h' : sp (p.stopAt v fr (drawnT C dsp ρ)) = true := hρ
    rw [h, hsp] at h'
    cases h') (zero_le _)

section
variable (sp : Option Why → Bool) (v : Option V) (val : Part V W Y → ℝ≥0∞)

/-- **Which gate of a list belongs to which part.** `A`: the parts before p. -/
theorem rowGates_mem : ∀ (ps : List (Part V W Y)) (ds : List RDT), ∀ g ∈ rowGates sp v val ps ds,
    ∃ A p B, ps = A ++ p :: B ∧
      g = ⟨(ds.drop (A.map (·.moves.length)).sum).take p.moves.length,
        fun fr own => sp (p.stopAt v fr own), val p⟩
  | [], _, g, hg => by cases hg
  | p :: ps, ds, g, hg => by
    rcases List.mem_cons.1 hg with rfl | hg'
    · exact ⟨[], p, ps, rfl, rfl⟩
    · obtain ⟨A, q, B, e, rfl⟩ := rowGates_mem ps (ds.drop p.moves.length) g hg'
      refine ⟨p :: A, q, B, by rw [e]; rfl, ?_⟩
      rw [List.drop_drop, List.map_cons, List.sum_cons]

variable (hs : List (Placed V W Y))

/-- **Which gates of a chain belong to which sub-protocol.** `A`: the sub-protocols before b. -/
theorem chainGates_mem : ∀ (bs : List (Block S Cl)) (ds : List RDT),
    ∀ g ∈ chainGates sp v val hs bs ds, ∃ A b B, bs = A ++ b :: B ∧
      g ∈ memberGates sp v val hs b
        ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length)
  | [], _, g, hg => by cases hg
  | b :: bs, ds, g, hg => by
    rcases List.mem_append.1 hg with h | h
    · exact ⟨[], b, bs, rfl, h⟩
    · obtain ⟨A, c, B, e, hm⟩ := chainGates_mem bs (ds.drop b.rounds.length) g h
      refine ⟨b :: A, c, B, by rw [e]; rfl, ?_⟩
      rw [List.drop_drop] at hm
      rw [List.flatMap_cons, List.length_append]
      exact hm

/-- **`ChainHeld` from the parts' conditions.** The hypothesis: at each sub-protocol b of the chain
at whose place there is a prover's side g, and at each part p of g, `StopDebt` holds at p's own
stretch of the chain's data and at val p. -/
theorem chainHeld_of (C : CK) (bs : List (Block S Cl)) (ds : List RDT)
    (h : ∀ (A : List (Block S Cl)) (b : Block S Cl) (B : List (Block S Cl)), bs = A ++ b :: B →
      ∀ g, (hs.find? fun g => g.place == b.place) = some g →
      ∀ (A' : List (Part V W Y)) (p : Part V W Y) (B' : List (Part V W Y)),
      g.parts = A' ++ p :: B' →
      StopDebt C sp v p
        ((((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length).drop
          (A'.map (·.moves.length)).sum).take p.moves.length) (val p)) :
    ChainHeld sp v val hs C bs ds := by
  intro g hg fr
  obtain ⟨A, b, B, e, hm⟩ := chainGates_mem sp v val hs bs ds g hg
  unfold memberGates at hm
  cases hf : hs.find? fun g => g.place == b.place with
  | none =>
    rw [hf] at hm
    obtain rfl := List.mem_singleton.1 hm
    exact le_trans (Iop.prRho_empty _ fun ρ hρ => by
      have h' : false = true := hρ
      cases h') (zero_le _)
  | some x =>
    rw [hf] at hm
    obtain ⟨A', p, B', e', rfl⟩ := rowGates_mem sp v val x.parts _ g hm
    exact h A b B e x hf A' p B' e' fr

end

end ProofFile.Honest

#print axioms ProofFile.Honest.stopDebt_none
#print axioms ProofFile.Honest.rowGates_mem
#print axioms ProofFile.Honest.chainGates_mem
#print axioms ProofFile.Honest.chainHeld_of
