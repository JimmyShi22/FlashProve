-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OwedFillM4.lean: A STATEMENT THAT IS OWED, WRITTEN AS A DEFINITION OF A Prop:
no proof stands here.
IN PLAIN WORDS. WHAT THE TIE AT W's COMMITMENT ASKS OF THE TABLE's LETTERS (`FillM4`,
Johnson/Desc/K13/Law/AtTableW.lean), OUT OF KIND K13's PREMISES ON THE LETTER Mg (`MgK13`,
MgK13.lean) AND TESTS ON THE PLAN: the like, at W's commitment, of `fillM3_at` there.
THE ROAD THAT IS MEANT. `fillM4_of` (FillFromSentences.lean) at hS := the structure's `ours` (the
code table is the place's: cs := P'.codes) · hO := `OwedOthers4` (OwedOthers4.lean: a premise here)
at the structure's `sig`, `masks`, `seats`, `ours.indexThere` and the plan's `below` · the riders:
`rider4_book` (the structure's `book` counts from 0: so hft at ft := 0), `rider4_seats`,
`rider4_shapes` (RidersK12.lean) at the plan's hp, hs, hx; `rider4_frontOk`; `rider4_pileMasks`
(PileMasks.lean); at "K13.weightsOk": the second half of `OwedKeeps wB`.
Who spends it: `w_tied_seat`'s hF (AtTableW.lean), for the first chain's number 356.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.MgK13
import Johnson.Desc.K13.Law.OwedOthers4
import Johnson.Desc.K13.Law.PlanTestsM4
import Johnson.Desc.K13.Law.FillM3Paid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem Frame)

/-- **OWED.** `FillM4` out of the structure, the tests on the plan and what is owed beside. -/
def OwedFillM4 : Prop :=
  ∀ {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {F : Frame} (_y₀ : F.E.Str) (P : Where) (P' : K1.Par)
    (N : Numbers) (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (sh : Params.ReqShape)
    (ly : Params.ReqLayout) (rest : Pp × S → Bool) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE) (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf P'.codes s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (M : List OracleShape) (L : K12.Door.Laid) (wB : S → Bool) (Q : List Pub) (p : Option Place),
    MgK13 P N Mg P'.codes sh ly rest arr mat G smp ms decT M L →
    PlanK13 Pp N P'.codes ms M L → PlanM4 0 L M N p P' →
    (atM4 (Cl := Cl) P (K1.sendAtS P')).planOk = true →
    (∀ x, Mg.pub weightsItem x = wB x.2) → (∀ x, Mg.pubP weightsItem x) →
    (∀ q ∈ Q, q ∈ knownK13 ∨ q = .frontOk ∨ q = weightsItem) →
    (∀ q ∈ knownK13, q ∈ Q) → Pub.frontOk ∈ Q →
    OwedOthers4 → OwedKeeps wB → SmpOld N p ms smp → DecBlind decT →
    (∀ x x', StepM4 Cl P P' x x' → rest x = true → rest x' = true) →
    FillM4 Cl P P' N Mg Q p

end VerifiableInference.Desc.K13.Law
