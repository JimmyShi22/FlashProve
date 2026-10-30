-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Goal/Skeleton/Kinds/K6Bridge.lean: the kind K6 (the sub-protocol at the output head; one
place, 341): its files' own named condition, under the head `P5J.AtMgA`, gives the kind's field in
the form in which a kind's law is counted, `P5J.AtMgA.Kind h 𝔏 .K6` (Johnson/P5J/RowsAtAll.lean).
`K6Cond` has no free letter H0: nor has this
file. The condition stands at the one fence of
Johnson/Goal/Skeleton/Kinds/Unmarked.lean, `h.rchU`: "reached, at a typed instance's public part,
and no mark". `K6Cond` is written with its full name: inside the definition of
`P5J.AtMgA.K6Cond` Lean takes the bare name for the definition that is being made.

  `AtMgA.K6Cond h 𝔏`: there are letters piece6, Lk, Lp, Mm with `K6Cond`
    (Johnson/Desc/Kinds/Law/K06AtConst.lean), to the letter, at the seated frame, at the first
    chain's own pieces `h.row 𝔏`, AND AT THE FENCE `h.rchU` in the place of its letter Rch.
  `k06_kind_all`: `h.K6Cond 𝔏` → `h.Kind 𝔏 .K6`. Two calls: K6's files' rule at letters,
    `k06_at_const`, which is general in Rch and ends at `mgAtAll h`, and `AtMgA.kind_of_unmarked`.
    That its lists of sorts and places, its numbers and its extractor are the form's: by
    definition; Lean checks it in that line.
  `k06_kind_bare`: the same end from K6's files' condition at bare `RchAt`: `k06_kind`, then
    `AtMgA.kind_of_reached`.

Why at `h.rchU`. K6's files' last step (`k06_kind`) lays Rch := `RchAt`: there `K6Cond`'s fields
along "reached" (fold, reqIs, three of `K6StateMg`'s and one of `K6LeftMg`'s) are asked at every
reached state, whatever its public part. Rch stands in these fields as a premise alone: at `h.rchU`
they ask less. (Each of the six has "no mark" beside Rch already: here the narrower fence changes
nothing but the spelling; it is taken so that all kinds' conditions stand at one fence.)

Limits. IT PAYS NOTHING. No member of the condition is known: it follows from the head and the three
equations (`k6Cond_of_head`, Johnson/Desc/Kinds/Law/K06CountedHead.lean), but that there is a head
is proved at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap` (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side
library AtFullSide/Top/); at other files: evaluated, not proved. It can hold only at an 𝔏 whose
first row is the description's own flat list (read from K6's files, not shown here): the three
equations on the lists' heads stand in the statement for one shape with the other kinds' and are not
spent. At `OnBytes.secondHashFunction` alone, though K6's files' rule is general in that function.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.Kinds.Unmarked
import Johnson.Desc.Kinds.Law.K06Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

/- The names in scope are those of Johnson/Desc/Kinds/Law/K06Kind.lean. -/
namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}

/-- **The output head's kind's named condition, at the closed constant and the one fence.** -/
def _root_.P5J.AtMgA.K6Cond (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop :=
  ∃ (piece6 : ℕ) (Lk : Link S Claim) (Lp : K12.Door.Laid) (Mm : List OracleShape),
    _root_.VerifiableInference.Desc.Kinds.Head.Law.AtTable.K6Cond h
      (Sound.frameAt (D.at OnBytes.Slice.frS.P.T.a)
        (Sound.allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      piece6 Lk h.rchU Lp Mm (h.toAtMg.row 𝔏)

/-- **The field.** -/
theorem _root_.P5J.k06_kind_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (_q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (_q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (_q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (C : h.K6Cond 𝔏) : h.Kind 𝔏 KindName.K6 := by
  obtain ⟨piece6, Lk, Lp, Mm, C⟩ := C
  exact h.kind_of_unmarked 𝔏 KindName.K6
    (k06_at_const h _ piece6 Lk _ Lp Mm _ 𝔏.c₀ P5J.At.tokOf C)

/-- The same end from K6's files' condition at bare "reached". -/
theorem _root_.P5J.k06_kind_bare (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (piece6 : ℕ) (Lk : Link S Claim) (Lp : K12.Door.Laid)
    (Mm : List OracleShape)
    (C : _root_.VerifiableInference.Desc.Kinds.Head.Law.AtTable.K6Cond h _ piece6 Lk
      (Johnson.Desc.First.Walk.Tied.RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) Lp Mm
      (h.toAtMg.row 𝔏)) : h.Kind 𝔏 KindName.K6 :=
  h.kind_of_reached 𝔏 KindName.K6 (k06_kind h 𝔏 piece6 Lk Lp Mm C)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms P5J.k06_kind_all
#print axioms P5J.k06_kind_bare
