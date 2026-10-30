-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawTeeth.lean: THE SMALLNESS TEST, ITS FIRST HALF: A LAW AT THE CARRIED
RECORD, WITH A WEAKENED TEXT THAT HAS IT NOT.

A law of Johnson/Desc/First/K8/LawAtS.lean says what a yes of the kind's block means at the first
chain's carried record: the place's numbers are the typed block's (`yes_atS`, from tests (d), (e),
(f)). A law that every text had would say nothing. Here the law is stated of ANY family of blocks
at that record, proved of the kind's own text, and refuted of the kind's text with just these tests
left out.
  `ConditionAt b p c`: wherever the block b p says yes on the round of the written verifier message
    c, at a record in which the smallness test's record tl lies, `Fits p` holds at the library's
    sizes of tl. `hear_conditionAt`: the kind's text has it, at all p and c.
  `noDEF`: the kind's text without tests (d), (e), (f). `noDEF_conditionAt`: it has it at no c, at
    the toy place: it says yes at a record with no matrix.
Definitions, statements and proofs.
Limits. The weakened text is typed here by hand, beside the kind's text, and stands in no
description. The record at which it says yes is a toy, made by hand: no run reaches it. That the
law fails at one weakened text does not show that each single test is needed: (d), (e) and (f) are
left out together.

-/
import Johnson.Desc.First.K8.LawAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model OnBytes.Tie.Pv.Tail Cb.Pv.Tail OnBytes.Slice

/-- A block with the kind's round reads no column: as a step it is its decision. -/
theorem step_at_round {S Cl : Type} (b : Block S Cl) (p : Par) (hb : b.rounds = [round p])
    (ft : Nat) (st : S) (r : Fmt.RoundView) (cols : List Col) (hfit : roundsFit [round p] [r] = true) :
    b.step ft st [r] cols = (b.decide st [noDigest r] []).map fun s' => (s', 0) := by
  have hg : groupsOf ft [round p] ([r].map (·.drawn)) = [] := by
    simp [groupsOf, round]
  unfold Block.step
  rw [hb, hfit, hg]
  simp only [need, List.flatMap_nil, List.length_nil, List.take_zero, List.map_nil, List.map_cons,
      regroup]
  cases b.decide st [noDigest r] [] <;> rfl

/-! ## The place's numbers are the typed block's -/

/-- The first half of the row `K08ConditionHearing`, of any family of blocks. -/
def ConditionAt {Cl : Type} (b : Par → Block S Cl) (p : Par) (c : (wRound (rd p)).Chal) : Prop :=
  ∀ (tl : HTailF2) (ft : Nat) (st st' : S) (n : Nat) (cols : List Col) (r : Fmt.RoundView),
    st.tl? = some tl → r.vals = [] → r.drawn.elems = [] → r.drawn.poss = [] →
    r.drawn.trits = kitTrits c → (b p).step ft st [r] cols = .ok (st', n) →
    Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl).size

/-- The kind's own text has it. -/
theorem hear_conditionAt {Cl : Type} (p : Par) (c : (wRound (rd p)).Chal) :
    ConditionAt (approximateRangeProofDrawKind (Cl := Cl) atS) p c := fun tl ft st st' n cols r hst h1 h2 h3 h4 h =>
  (yes_atS (Cl := Cl) p tl c ft st st' n cols r hst h1 h2 h3 h4 h).choose

/-- The kind's text without tests (d), (e), (f). -/
def noDEF (p : Par) : Block S Unit :=
  { approximateRangeProofDrawKind atS p with
    decide := fun s rs _ =>
      match rs with
      | [r] =>
        if !atS.closed s then .error "a"
        else if !atS.nothingOwed s then .error "b"
        else if atS.drawn s then .error "c"
        else if atS.tabs s != tabs p then .error "t"
        else atS.lay s r.drawn.trits.toArray (firstColumns p)
      | _ => .error "rounds" }

/-- A carried record inside a layers' link: the smallness test's record tl, an empty ledger. -/
def toyIn (tl : HTailF2) : S :=
  { S.blank with here := .lay { L := { check := S.blank.check }, F := {}, tl := tl } }

/-- A record of the smallness test with no matrix, its list of tables closed. -/
def toyNone : HTailF2 := { funClosed := true }

/-- **Without (d), (e), (f) the law fails**, at every written verifier message of the toy place. -/
theorem noDEF_conditionAt (c : (wRound (rd toyPar)).Chal) : ¬ ConditionAt noDEF toyPar c :=
  fun h => by
  have hs : ∃ st', (noDEF toyPar).step 0 (toyIn toyNone) [toyRoundAt c] [] = .ok (st', 0) := by
    rw [step_at_round (noDEF toyPar) toyPar rfl 0 _ _ _ (fit_of toyFits c (toyRoundAt c) rfl rfl
      rfl rfl)]
    exact ⟨_, rfl⟩
  obtain ⟨st', hs⟩ := hs
  have e : (0 : Nat) = 1 := (h toyNone 0 _ st' 0 [] (toyRoundAt c) rfl rfl rfl rfl rfl hs).nm
  exact absurd e (by decide)

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.hear_conditionAt
#print axioms VerifiableInference.Desc.First.K8.noDEF_conditionAt
