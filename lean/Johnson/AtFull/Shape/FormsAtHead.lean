-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/FormsAtHead.lean: THE ROWS' MAKES BEHIND K1's DIGITS' COMMITMENT, AT ITS SEAT
IN THE PROOF FILE's OWN FIRST CHAIN, AT ALL 25 LINKS; AND WHAT ROUNDS THAT FIT K1's TWO DECLARED
ROUNDS GIVE. Under the head P5J.AtMgA. Nothing is evaluated.

  1 `answers_len`, **`k1_fit`**: roundsFit (K1.rounds P) rs = true ⊢ rs = [r₁, r₂], r₁ draws just
    seeds × (coordinates + 1) elements, and r₂ holds just P.answers answers. So two of the three
    premises that K1's laws on shapes take of the rounds are paid by the frame's own test on the
    rounds' form. The third (isZeroE: no seed's factor is spelt by three words 0) falls to it too:
    by factors_of_fit (Johnson/Prover/Send/Form.lean), which is not called here.
  2 **`digits_forms_at`**: at the member number 14 l + IM.k1Ix l true + 2 of cF.blocksInOrder: its declared
    rounds are K1.rounds of the plan's numbers; at rounds that fit, shown without the sealed
    digest, behind a yes: formsOf t.st = sendForms ‹the plan's numbers› ‹the number of messages in
    front, off the shape› (formsOf s.st).

Limits. The digits' members alone. That the head has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files, in a side library. At the format's second hash
function. No state is shown at which a step returns. Nothing on soundness, completeness or hiding.

-/
import Johnson.AtFull.Shape.DigitsAtHead
import Johnson.Desc.First.Shape.ChainF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 Rounds that fit K1's two declared rounds -/

/-- Items that are all answers. -/
theorem answers_len : ∀ (l : List Fmt.ItemValue) (n : Nat),
    l.map VerifiableInference.Desc.itemOf = List.replicate n .answer →
    (l.filterMap fun | .answer x => some (E.ofTriple x) | _ => none).length = n
  | [], n, h => by
    cases n with
    | zero => rfl
    | succ n => cases h
  | g :: l, n, h => by
    cases n with
    | zero => cases h
    | succ n =>
      rw [List.map_cons, List.replicate_succ] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      cases g with
      | answer x =>
        rw [List.filterMap_cons]
        show (_ :: _).length = _
        rw [List.length_cons, answers_len l n h2]
      | f _ => cases h1
      | e _ => cases h1
      | word _ => cases h1
      | root _ => cases h1

/-- Rounds that fit the kind's declared rounds are two; the first draws just as many elements as the
seeds take; the second holds just the answers. -/
theorem k1_fit {P : VerifiableInference.Desc.K1.Par} {rs : List Fmt.RoundView}
    (h : roundsFit (VerifiableInference.Desc.K1.rounds P) rs = true) :
    ∃ r₁ r₂, rs = [r₁, r₂] ∧ r₁.drawn.elems.length = P.seeds * (P.coordinates + 1) ∧
      (VerifiableInference.Desc.K1.answersIn r₂).length = P.answers := by
  unfold VerifiableInference.Desc.K1.rounds at h
  match rs, h with
  | [r₁, r₂], h =>
    simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨r₁, r₂, rfl, h.1.1.1.1.1.1.2, ?_⟩
    have hv := h.2.1.1.1.1.1.1.1
    refine answers_len r₂.vals P.answers ?_
    rw [hv]
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, VerifiableInference.Desc.K1.answerEntry]
  | [], h => cases h
  | [_], h => simp [roundsFit] at h
  | _ :: _ :: _ :: _, h => simp [roundsFit] at h

/-- A round without the sealed digest draws what it drew. -/
theorem noDigest_elems (r : Fmt.RoundView) : (noDigest r).drawn.elems = r.drawn.elems := rfl

/-! ## 2 The digits' commitment at its seat: the rows' makes -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The rows' makes behind the digits' commitment, at all 25 links**: at rounds that fit the
member's declared rounds. -/
theorem digits_forms_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Bs : ProofFile.PureBase) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      cF.blocksInOrder[14 * l + IM.k1Ix l true + 2]? = some b ∧
      b.rounds = VerifiableInference.Desc.K1.rounds (VerifiableInference.Desc.K1.parLater
        Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) l (IM.k1Ix l true + 1) 2) ∧
      ∀ s rs gs t, roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok t →
        formsOf t.st = sendForms (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) l (IM.k1Ix l true + 1) 2)
          (chainSh s).core.st.oracles.length (formsOf s.st) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, Xl, pr, reads, digits, eL, eb, hX, hn, la⟩ :=
    IM.k1_digits_of h.scope h.reads O l hl
  have hy := IM.yes_alone la (by intro k; cases k)
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : l ≤ 24) (IM.k1Ix l true)] at q
  have hr : b.rounds = VerifiableInference.Desc.K1.rounds (VerifiableInference.Desc.K1.parLater
      Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) l (IM.k1Ix l true + 1) 2) :=
    IM.alone_rounds la
  refine ⟨Bs, b, O.made, q, hr, fun s rs gs t hf hd => ?_⟩
  rw [hr] at hf
  obtain ⟨r₁, r₂, rfl, -, -⟩ := k1_fit hf
  have hd' := ((hy s t _ gs).1 hd).1
  exact commit_forms hd'

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.answers_len
#print axioms Johnson.AtFull.Shape.k1_fit
#print axioms Johnson.AtFull.Shape.digits_forms_at
#print axioms Johnson.AtFull.Shape.noDigest_elems
