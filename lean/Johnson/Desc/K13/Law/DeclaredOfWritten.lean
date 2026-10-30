-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/DeclaredOfWritten.lean: at a block whose declared rounds are kind K13's
(battRounds P), the stretch of the file's data is dZ :: d0 :: ds with Declared P dZ d0 ds
(Johnson/Desc/K13/Law/Tries.lean) and the kinds of the three names (KindsM3). Statements with their
proofs. Kin: k9_cut (Johnson/Desc/First/Batch/Law/CutAt.lean), the like at a block of one round.
  declared_of_tags     from the entries and kinds of the declared rounds.
  declared_of_written  at the data of three written lists (Johnson/Desc/Sound/StretchTags.lean).
No number of any plan is named.
What is not claimed. That a description's block has these declared rounds. Nothing on soundness.

-/
import Johnson.Desc.Sound.StretchTags

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Maker OnBytes.Flat
open OnBytes.Params (Rounds)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open _root_.Desc.K14.Law (roundsIn)

theorem plain_of_tag {d : RDT} {n : String} {en : Fmt.Entry} (h : tagR d = (en, Fmt.kindOf n))
    (hn : Fmt.kindOf n ≠ some .sealed ∧ Fmt.kindOf n ≠ some .seeds) :
    d.entry = en ∧ PlainKind d := by
  have h1 : d.entry = en := congrArg Prod.fst h
  have h2 : some d.kind = Fmt.kindOf n := congrArg Prod.snd h
  exact ⟨h1, fun e => hn.1 (by rw [← h2, e]), fun e => hn.2 (by rw [← h2, e])⟩

theorem plainSigma :
    Fmt.kindOf "BAT-sigma" ≠ some .sealed ∧ Fmt.kindOf "BAT-sigma" ≠ some .seeds := by
  decide
theorem plainEps :
    Fmt.kindOf "PSC epsilon" ≠ some .sealed ∧ Fmt.kindOf "PSC epsilon" ≠ some .seeds := by
  decide
theorem plainRound :
    Fmt.kindOf "PSC round" ≠ some .sealed ∧ Fmt.kindOf "PSC round" ≠ some .seeds := by
  decide

/-- The three names' kinds. -/
theorem kindSigma : Fmt.kindOf "BAT-sigma" = some .elems := by decide
theorem kindEps : Fmt.kindOf "PSC epsilon" = some .join := by decide
theorem kindRound : Fmt.kindOf "PSC round" = some .elems := by decide

/-- The stretch's rounds have the kinds of their names. -/
def KindsM3 (dZ d0 : RDT) (ds : List RDT) : Prop :=
  dZ.kind = .elems ∧ d0.kind = .join ∧ ∀ d ∈ ds, d.kind = .elems

theorem kind_of_tag {d : RDT} {n : String} {en : Fmt.Entry} {k : Fmt.Kind}
    (h : tagR d = (en, Fmt.kindOf n)) (hn : Fmt.kindOf n = some k) : d.kind = k :=
  Option.some.inj ((congrArg Prod.snd h).trans hn)

/-- **From the tags of K13's declared rounds.** -/
theorem declared_of_tags (P : Where) (L : List RDT) (h : L.map tagR = (battRounds P).map tagD) :
    ∃ dZ d0 ds, L = dZ :: d0 :: ds ∧ Declared P dZ d0 ds ∧ KindsM3 dZ d0 ds := by
  unfold battRounds at h
  match L, h with
  | [], h => simp at h
  | [_], h => simp at h
  | dZ :: d0 :: ds, h =>
    simp only [List.map_cons, List.cons.injEq, List.map_replicate] at h
    obtain ⟨hZ, h0, hs⟩ := h
    have hv : ∀ d ∈ ds, tagR d = tagD { entry := roundEntry P } := fun d hd => by
      have hm : tagR d ∈ ds.map tagR := List.mem_map.2 ⟨d, hd, rfl⟩
      rw [hs] at hm
      exact List.eq_of_mem_replicate hm
    refine ⟨dZ, d0, ds, rfl, ⟨?_, plain_of_tag (n := "BAT-sigma") hZ plainSigma,
      plain_of_tag (n := "PSC epsilon") h0 plainEps,
      fun d hd => plain_of_tag (n := "PSC round") (hv d hd) plainRound⟩, ?_⟩
    · have := congrArg List.length hs
      simpa using this.symm
    · exact ⟨kind_of_tag (n := "BAT-sigma") hZ kindSigma,
        kind_of_tag (n := "PSC epsilon") h0 kindEps,
        fun d hd => kind_of_tag (n := "PSC round") (hv d hd) kindRound⟩

/-- **The stretch at a block with K13's declared rounds.** -/
theorem declared_of_written {T Cl : Type} (a : ℕ) (R₁ R₂ R₃ : Rounds)
    {e : List (List ByteArray × ByteArray)} (bs : List (Block T Cl))
    (hW : WrittenAs e (bs.flatMap (·.rounds)) R₁) (k : ℕ) (x : Block T Cl) (hx : bs[k]? = some x)
    (hroom : roundsIn (bs.take k) + x.rounds.length < roundsIn bs) (P : Where)
    (hr : x.rounds = battRounds P) :
    ∃ dZ d0 ds, ((dataOf a R₁ R₂ R₃).ds₁.drop (roundsIn (bs.take k))).take x.rounds.length =
      dZ :: d0 :: ds ∧ Declared P dZ d0 ds ∧ KindsM3 dZ d0 ds :=
  declared_of_tags P _ (by rw [stretch_tags a R₁ R₂ R₃ bs hW k x hx hroom, hr])

end VerifiableInference.Desc.K13.Law
