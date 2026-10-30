-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/ExactKept.lean: the kind "lookup" (K3): the field `exact`
of `Good` (Honest/Side.lean) at each member of a side whose row is a lookup's seated row that passes
its tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean), each part beside the simulator of the row
that passes nothing on (`lookSims`, Honest/K3/Row.lean). Two theorems; no definition.

Never to be retold as "the row that passes its tables on is simulated". One sentence, the field
`exact`, is carried to this row's members from parts of which it is had. No new simulator, no new
measure, no coin opened.

Terms. Honest/K3/GLOSSARY.md. `ExactMember`: Honest/Small/Field.lean. `Keeps`, `partKeep`:
Honest/K3/RowKeep.lean. `RowStated`: Honest/K3/Law/Good/K3ExactStated.lean.

What is shown.
  `member_keep`: a member of such a side is its stage's: the stage's part, seated, beside the
    stage's simulator.
  `k3_exact_kept`: **the field `exact` at every member of such a side, at every entry sentence and
    every budget of positions.**

Hypotheses that remain, in `k3_exact_kept`.
  `hrow`: the side's row is the seated row beside `lookSims`. Nobody shows that a side of a filling
    has this row.
  `hK`: each stage's job has the shape of the stage's call, and there is a job just where there is a
    call (`Keeps.Shaped`, Honest/K3/Law/Keep/RowKeepFits.lean). `fastKeeps_shaped`
    (Honest/K3/Law/Keep/SeatKeepFits.lean) shows it at the filling's letters.
  `hgs`, `hsg`: get reads what set has laid; laying what get reads turns nothing.
  `hSt`: the declared rounds state what the stages' calls state (`RowStated`).
No `Keeps.Lawful`, no `KeepJob.FaithfulOn`, no `Keeps.StoreOk` and no `Keeps.SteadyFrom` is asked:
the statement stands at jobs right or wrong.

The store holds no coin: by the type of `Keeps.store`, which lays it, and by the type of
`Move.hand`, which passes it on. The frame's authors' own line (Honest/Frame.lean, at `Move.hand`):
"It is given no coin and nothing that was sent: so by type `own` is computed from
the input and the challenges alone". The store is passed on from part to part through that value.

How the proof goes. By cases on the member's stage, in the four arms of `partKeep`: a job, not at
`Stage.bits`: `exact_keepPart_lift`; a job at `Stage.bits`, whose last move drops the store:
`exact_keepPart_lastHand_lift`; `Stage.alpha`, which lays the store, and every other stage without a
job: `exact_quietLay_lift` (all three in Honest/AlikeFields/ExactCarry.lean). It is not carried from
the members of `lookRow` (Honest/K3/Row.lean). By a reading of the definitions, not by Lean: a job
of this row reads the store that an earlier part has passed on, so the two rows need not say the
same from every two states with one input and one list of challenges heard. No such two states are
exhibited.

Limits. Never without `hrow`: "`exact` at the filling" is not had. Of `Good`'s other fields (`fits`,
`plays`, `acc`, `fresh`) nothing is carried. It does not say that this row sends what `lookRow`
sends: that is `rowSame_keep` (Honest/K3/Law/Keep/RowKeepLaw.lean), under hypotheses of its own.
Nothing on what is sent. The parts from which the sentence is carried are of no row that a prover
runs. What `exact` itself leaves free stands in the Limits of Honest/Side.lean. One side: nothing on
a chain, a run or a prover as a whole. No instance of the hypotheses together is exhibited in this
file. What may be said of the sentence and of its term is not this
file's to say.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.AlikeFields.ExactCarry
import Johnson.Desc.ProofFile.Honest.K3.RowQuietIs
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.RowKeepFits
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3ExactStated
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3Members

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.AlikeFields (exact_keepPart_lift exact_keepPart_lastHand_lift exact_quietLay_lift)

variable {S Cl V W X' Pb : Type}

/-- **A member of the side is its stage's.** Conditional on hrow. -/
theorem member_keep {σ' : Side S Cl V W X' Pb} (Kp : Keeps) (wit : W → Ask) (get : X' → RowOwn)
    (set : X' → RowOwn → X') (a : At)
    (hrow : σ'.row = (proverSideOfLookupInChainKeepingTablesAtOneOwner Kp wit get set a).parts.zip (lookSims a))
    (u : Member V W X' Pb) (hu : u ∈ σ'.members) :
    ∃ st, (stages a.face)[u.number]? = some st ∧
      u.part = (partKeep (V := Unit) Kp a st u.number).lift (fun _ => ()) wit get set ∧
      u.sim = simOf a st u.number := by
  unfold Side.members at hu
  rw [hrow] at hu
  obtain ⟨i, x, hx, rfl⟩ := membersOf_spec _ 0 _ u hu
  unfold proverSideOfLookupInChainKeepingTablesAtOneOwner lookRowKeep lookSims at hx
  simp only [List.getElem?_zip_eq_some, List.getElem?_map, Option.map_eq_some_iff,
    List.getElem?_zipIdx, Nat.zero_add] at hx
  obtain ⟨⟨p, ⟨y, ⟨st, hst, rfl⟩, rfl⟩, h1⟩, ⟨y', ⟨st', hst', rfl⟩, h2⟩⟩ := hx
  obtain rfl : st = st' := Option.some.inj (hst.symm.trans hst')
  exact ⟨st, by simpa using hst, by simpa using h1.symm, by simpa using h2.symm⟩

/-- Never to be retold as "the row that passes its tables on is simulated". Never without hrow: it
does not say that any side of a filling has this row. Nothing on `fresh`, `plays`, `acc`.
Conditional: hgs, hsg, hK, hrow, hSt. **The field `exact` at every member of the side**, each beside
the simulator of the row that passes nothing on. -/
theorem k3_exact_kept (φ : Face V W Pb) {σ' : Side S Cl V W X' Pb} (Kp : Keeps) (wit : W → Ask)
    (get : X' → RowOwn) (set : X' → RowOwn → X') (a : At) (hgs : ∀ x y, get (set x y) = y)
    (hsg : ∀ x, set x (get x) = x) (hK : Kp.Shaped a.face)
    (hrow : σ'.row = (proverSideOfLookupInChainKeepingTablesAtOneOwner Kp wit get set a).parts.zip (lookSims a))
    (hSt : RowStated a.face σ') (chain firstTree : Nat)
    (On' : (u : Member V W X' Pb) → CsAll u.part.carries → Mid W X' → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    ∀ u' ∈ σ'.members, ExactMember φ σ' chain firstTree On' bud u' := by
  intro u' hu'
  obtain ⟨st, hst, hp, hs⟩ := member_keep Kp wit get set a hrow u' hu'
  have hKs := hK st
  cases hc : st.call a.face with
  | some k =>
    rw [hc] at hKs
    obtain ⟨Jk, hJ, rfl⟩ := Option.map_eq_some_iff.1 hKs
    obtain ⟨h1, h2, h3⟩ := hSt.sums u' hu' st _ hst hc
    obtain ⟨j, rs, p, sm⟩ := u'
    have hp' : p = (partKeep (V := Unit) Kp a st j).lift (fun _ => ()) wit get set := hp
    have hs' : sm = simOf a st j := hs
    have es : simOf (Pb := Pb) a st j = sumSim ⟨a.place, j⟩ Jk.base.shape := by
      unfold simOf
      simp only [hc]
    subst hp'
    rw [hs', es]
    by_cases hb : st = .bits
    · subst hb
      rw [partKeep_bits Kp a j Jk hJ]
      exact exact_keepPart_lastHand_lift φ σ' chain firstTree On' bud (fun _ => ()) wit get set hgs
        hsg _ _ Jk h1 rs h2 h3 j _ _
    · rw [partKeep_some Kp a st j Jk hJ hb]
      exact exact_keepPart_lift φ σ' chain firstTree On' bud (fun _ => ()) wit get set hgs hsg _ _
        Jk h1 rs h2 h3 j _
  | none =>
    rw [hc] at hKs
    have hJ : Kp.job st = none := Option.map_eq_none_iff.1 hKs
    have h1 := hSt.quiets u' hu' st hst hc
    obtain ⟨j, rs, p, sm⟩ := u'
    have hp' : p = (partKeep (V := Unit) Kp a st j).lift (fun _ => ()) wit get set := hp
    have hs' : sm = simOf a st j := hs
    have es : simOf (Pb := Pb) a st j = ProofFile.Honest.quietSim ⟨a.place, j⟩ 1 := by
      unfold simOf
      simp only [hc]
      rfl
    subst hp'
    rw [hs', es]
    by_cases hα : st = .alpha
    · subst hα
      rw [partKeep_alpha Kp a j hJ]
      exact exact_quietLay_lift φ σ' chain firstTree On' bud j rs _ (fun _ => ()) wit get set _ h1
    · rw [partKeep_none Kp a st j hJ hα]
      exact exact_quietLay_lift φ σ' chain firstTree On' bud j rs _ (fun _ => ()) wit get set
        (fun t => t.own) h1

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.member_keep
#print axioms ProofFile.Honest.K3.Law.k3_exact_kept
