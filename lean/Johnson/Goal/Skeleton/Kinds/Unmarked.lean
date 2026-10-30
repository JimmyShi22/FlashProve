-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Goal/Skeleton/Kinds/Unmarked.lean: ONE FENCE FOR EVERY KIND's CONDITION: "reached, at a
typed instance's public part, AND THE STATE BEARS NO MARK". A kind's share of the first chain's
chain of promises at that narrower fence IS the kind's field in the form in which a kind's law is
counted, `P5J.AtMgA.Kind h 𝔏 K` (Johnson/P5J/RowsAtAll.lean). Kind-free. The two
proofs open `AtMgA.Kind` by name and call the more general `KindTiedR.monoOn`: Lean does not open
`h.rchU` and `h.Kind` by itself.


Why. A kind's condition that asks a fact of EVERY reached state may have no payer at a state that
bears a mark of failure: by reading, not shown here, a marked state is inside every promise of
the table, and the facts along the fold are asked of unmarked states alone. One field without a
payer empties the whole list of conditions. But each of the five ties of `TiedAtR`
(Johnson/Desc/Sound/ChainOfPromisesR.lean) has "no mark" in hand beside "reached": so a kind's
condition may ask its facts of unmarked states alone and lose nothing.

  `AtMgA.rchU h k a`: `h.rch k a` and `¬ a.1.2.failed ≠ none` (the ties' own spelling of "no mark").
    `AtMgA.rchU_rch`, `AtMgA.rchU_unmarked`: its two halves.
  **`AtMgA.kind_of_unmarked`**: `KindTiedR` at the form's own letters and at `h.rchU` gives
    `h.Kind 𝔏 K`. One call: `KindTiedR.monoOn` (Johnson/Desc/Kinds/Law/TiedRMonoOn.lean).
  `AtMgA.kind_iff_unmarked`: and back (`KindTiedR.mono`, Johnson/Desc/Sound/TiedRMono.lean): THE TWO
    ARE ONE PROPOSITION UP TO "IF AND ONLY IF": the narrower fence neither adds to the field nor
    takes from it.

What it asks of a piece: NOTHING NEW. "A mark stays" and "decodes rides" are the sixth and the
seventh part of `TiedAtR` itself; they do not read the fence and are handed on as they are. The
hand-on of "reached" (`HandsOn`) is no part of `KindTiedR`: the tower pays it kind-free, at `h.rch`,
as before.

Limits. BOOK-KEEPING. IT PAYS NO LAW. No member of any condition is known: of the conditions that
stand at this fence, K6's and K8's follow from the head (`k6Cond_of_head`,
Johnson/Desc/Kinds/Law/K06CountedHead.lean; `k08_cond_head`, Johnson/P1K8R/KindFromHead.lean), but
that there is a head is proved at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap` (at secondHashFunction, with `fixedConfigurationDigest` in the
digest's place; side library AtFullSide/Top/); at other files: evaluated, not proved.
No soundness is claimed.

-/
import Johnson.P5J.RowsAtAll
import Johnson.Desc.Kinds.Law.TiedRMonoOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Sound

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The one fence: reached, at a typed instance's public part, and no mark.** -/
def AtMgA.rchU (h : AtMgA o Z D r Zp Np cF x) (k : ℕ)
    (a : (ProofFile.InstPub × VerifiableInference.Desc.First.S) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) : Prop :=
  h.toAtMg.rch k a ∧ ¬ a.1.2.failed ≠ none

theorem AtMgA.rchU_rch (h : AtMgA o Z D r Zp Np cF x) {k : ℕ}
    {a : (ProofFile.InstPub × VerifiableInference.Desc.First.S) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str}
    (u : h.rchU k a) : h.toAtMg.rch k a := u.1

theorem AtMgA.rchU_unmarked (h : AtMgA o Z D r Zp Np cF x) {k : ℕ}
    {a : (ProofFile.InstPub × VerifiableInference.Desc.First.S) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str}
    (u : h.rchU k a) : a.1.2.failed = none := not_not.1 u.2

/-- **A KIND's SHARE AT THE NARROWER FENCE IS THE COUNTED FIELD.** -/
theorem AtMgA.kind_of_unmarked (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (K : KindName)
    (k : KindTiedR (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      (At.N Zp cF) (mgAtAll h) fullLinks At.ps h.rchU (h.toAtMg.ex 𝔏) (h.toAtMg.row 𝔏) K) :
    h.Kind 𝔏 K := by
  unfold AtMgA.Kind
  exact KindTiedR.monoOn (fun _ _ _ h' hm => ⟨h', hm⟩) k

/-- **And back: the two are one.** -/
theorem AtMgA.kind_iff_unmarked (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (K : KindName) :
    h.Kind 𝔏 K ↔
      KindTiedR (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
        (At.N Zp cF) (mgAtAll h) fullLinks At.ps h.rchU (h.toAtMg.ex 𝔏) (h.toAtMg.row 𝔏) K := by
  constructor
  · intro k
    unfold AtMgA.Kind at k
    exact KindTiedR.mono (fun _ _ u => u.1) k
  · exact h.kind_of_unmarked 𝔏 K

end P5J

#print axioms P5J.AtMgA.rchU_unmarked
#print axioms P5J.AtMgA.kind_of_unmarked
#print axioms P5J.AtMgA.kind_iff_unmarked
