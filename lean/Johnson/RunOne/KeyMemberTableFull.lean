-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyMemberTableFull.lean: THEOREMS. **The member with the stored table in the third place, at the full size's written numbers**: the decoder with a record at the sizes frS and the sample map frZ (OnBytes/Slice/FullRecLink.lean), beside the two messages at csKey · shIdx · shMul · 6130 · 3131959.
OBJECT: dec₃ | cond₃ of KeyMemberTable.lean at DF := decRec frS.P.T frS.P.v 2852142980 29 1 (DF_eq: it is frS.toDecR frZ 402653181, by definition). USER: none yet. LETTERS: in member_full₃ | member_exists₃ none (the plainest: the public part is the record; the strings are the two words and the stored table).
  df_a | df_k | df_e | df_J | df_3 | df_l | df_share   the premises on numbers, by evaluation in the kernel; df_share at K = 128; df_share_not: the control: false at K = 192
  share_table     **at every stored table, fixed before the seed: the seeds at which the record does not single one table out are at most 2^-128 of all seeds**. A count of typed seeds: no proof of work enters; no claim on a round's error. For soundness; the member does not need it
  dcd_full        at the stored table of M with its true record the decoder returns M's message parts, and there is no collision, at every seed
  member_full₃    **for all m₀ r₀ m₁ r₁ (the second's two main rows over the base field) and every table M of full messages over the base field and EVERY THREE SEEDS there is a point, with the true record and the honest strings, at which cond₃ holds and dec₃ returns (m₀, m₁, the message parts of M)**
  member_exists₃  the closed sentence
What is not claimed. That the keys which M holds lie in their range tables. The layout of the matrix in the table. That these numbers are a key file's (said elsewhere). Nothing on soundness or on hiding.

-/
import Johnson.RunOne.KeyMemberTable
import Johnson.RunOne.KeyMemberFull
import OnBytes.Slice.FullRecLink

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob Blocks
open VerifiableInference.Desc VerifiableInference.Desc.K1
open Johnson.Top.H (csKey shIdx shMul)

/-- The decoder's data at the full size. -/
def DF : DecR := decRec frS.P.T frS.P.v 2852142980 29 1

/-- It is the data of the sizes frS at the sample map frZ and the cut before the three pad entries. -/
theorem DF_eq : frS.toDecR frZ 402653181 = DF := rfl

theorem df_a : DF.T.a ≤ 32 := by decide +kernel
theorem df_k : DF.T.r + DF.T.l ≤ 2 ^ DF.T.a := by decide +kernel
theorem df_e : DF.eM < 2 ^ DF.T.a - (DF.T.r + DF.T.l) + 1 := by decide +kernel
theorem df_J : InJohnson (2 ^ frS.P.T.a) (2 ^ frS.P.T.a - (frS.P.T.r + frS.P.T.l) + 1) 2852142980 := by decide +kernel
theorem df_3 : 3 * 1 ≤ frS.P.T.l := by decide +kernel
theorem df_l : frS.P.T.l - 3 * 1 ≤ 2 ^ 29 := by decide +kernel

theorem df_share : (listMax (2 ^ frS.P.T.a) (2 ^ frS.P.T.a - (frS.P.T.r + frS.P.T.l) + 1) 2852142980).choose 2 * clashSeeds (Fmt.Fld.two.p ^ 3) 29 ^ 1 * 2 ^ 128 ≤
    allSeeds (Fmt.Fld.two.p ^ 3) 29 ^ 1 := by
  rw [Nat.choose_two_right]
  decide +kernel

theorem df_share_not : ¬ (listMax (2 ^ frS.P.T.a) (2 ^ frS.P.T.a - (frS.P.T.r + frS.P.T.l) + 1) 2852142980).choose 2 * clashSeeds (Fmt.Fld.two.p ^ 3) 29 ^ 1 * 2 ^ 192 ≤
    allSeeds (Fmt.Fld.two.p ^ 3) 29 ^ 1 := by
  rw [Nat.choose_two_right]
  decide +kernel

/-- For soundness, at a table that an adversary picks; the member does not need it. -/
theorem share_table (f : Fin (2 ^ frS.P.T.a) → Run.PQ.SgX) :
    cnt ((decRec frS.P.T frS.P.v 2852142980 29 1).coll f) * 2 ^ 128 ≤ Fintype.card (recZ frS.P.T.l 29 1).D :=
  coll_share frS.P.T frS.P.v 2852142980 29 1 128 df_a df_k df_e df_J df_3 df_l df_share f

attribute [local irreducible] DF

theorem dcd_full (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (ρ : DF.Z.D) :
    DF.dcd (stored DF M) (recOfM DF M ρ) = some (DF.ix.view (upM DF M)) ∧ ¬ DF.coll (stored DF M) ρ :=
  ⟨dcd_stored DF df_a df_k df_e M ρ, not_coll_stored DF df_a df_k df_e M ρ⟩

theorem member_full₃ (m₀ : (portCode csKey shIdx).J → GE) (r₀ : (portCode csKey shIdx).Q → GE) (m₁ : (portCode csKey shMul).J → GE) (r₁ : (portCode csKey shMul).Q → GE)
    (h₁ : Sendable csKey shMul m₁ r₁) (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF)
    (ρ₀ : (Fin (bitsZ csKey shIdx) → GE) × GEˣ) (ρ₁ : (Fin (bitsZ csKey shMul) → GE) × GEˣ) (ρ : DF.Z.D) :
    ∃ a : (DF.Rec × Statement) × ((portOmZ csKey shIdx 6130).Str × (portOmZ csKey shMul 3131959).Str × (DF.toDec.Pos → Run.PQ.SgX)),
      a.1.1 = recOfM DF M ρ ∧ a.2 = (sent csKey shIdx 6130 m₀ r₀, sent csKey shMul 3131959 m₁ r₁, stored DF M) ∧
      cond₃ csKey shIdx shMul 6130 3131959 0 1 id (fun y => y.1) (fun y => y.2.1) (fun q y => ¬ DF.coll y.2.2 (id q : DF.Rec).1) a ∧
        dec₃ csKey shIdx shMul 6130 3131959 0 1 id (fun y => y.1) (fun y => y.2.1) (fun q y => DF.dcd y.2.2 (id q)) a = some (m₀, m₁, DF.ix.view (upM DF M)) :=
  member_three_has DF df_a df_k df_e tieIdx tieMul meetsIdx meetsMul (sendIdx m₀ r₀) h₁ M ρ₀ ρ₁ ρ

/-- **The closed sentence.** -/
theorem member_exists₃ :
    ∃ (a : (DF.Rec × Statement) × ((portOmZ csKey shIdx 6130).Str × (portOmZ csKey shMul 3131959).Str × (DF.toDec.Pos → Run.PQ.SgX)))
      (u : Two csKey shIdx shMul (DF.ix.Row × DF.toDec.En → GE)),
      cond₃ csKey shIdx shMul 6130 3131959 0 1 id (fun y => y.1) (fun y => y.2.1) (fun q y => ¬ DF.coll y.2.2 (id q : DF.Rec).1) a ∧
        dec₃ csKey shIdx shMul 6130 3131959 0 1 id (fun y => y.1) (fun y => y.2.1) (fun q y => DF.dcd y.2.2 (id q)) a = some u := by
  obtain ⟨a, -, -, h⟩ := member_full₃ 0 0 0 0 (fun _ => ⟨fun _ => ⟨0, map_zero _⟩, fun _ => ⟨0, map_zero _⟩⟩) (fun _ _ => 0) (fun _ => 0, 1) (fun _ => 0, 1) (Classical.arbitrary _)
  exact ⟨a, _, h⟩

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.DF_eq
#print axioms Johnson.RunOne.KeyLetters.df_share
#print axioms Johnson.RunOne.KeyLetters.df_share_not
#print axioms Johnson.RunOne.KeyLetters.share_table
#print axioms Johnson.RunOne.KeyLetters.dcd_full
#print axioms Johnson.RunOne.KeyLetters.member_full₃
#print axioms Johnson.RunOne.KeyLetters.member_exists₃
