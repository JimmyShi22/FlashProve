-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormFront6Cut.lean: THE FORM's HALF: front6_all (FormFront6More.lean) FROM ONE
roundsFit, at the six front blocks' declared rounds in a row, AND ONE LIST OF COLUMNS, which are, in
key, position and width, what these rounds read; more columns may lie behind.

Why. Whoever joins the chain holds one roundsFit at all declared rounds and one list of wanted
columns (groupsOf, Johnson/Desc/Block.lean); front6_all asks roundsFit block by block, and the
columns in a letter of its own (linkWant).

Main names.
  six_rounds      the six's declared rounds in a row.
  fit6_cut        one roundsFit is front6's four, at five rounds.
  want6           what the six's rounds read is what "LINK" is owed.
  front6_join     THE STATEMENT.

How. roundsFit_append, roundsFit_length (Johnson/Top/H0/StepLaws/StepLaws.lean); blocksV_eq
(Johnson/Desc/K15/SendOwnLaw.lean).

Limits. front6_all's other premises stay: the plan's four, the keys' four.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFront6More
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc
open Desc.K15 (St Par15 P15)

/-- The six front blocks' declared rounds in a row. -/
theorem six_rounds (P : P15) (he : Desc.K15.entries P = some (Desc.K15.fiveOf P)) :
    (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap (·.rounds) =
      (Desc.K15.bPoint P (Desc.K15.fiveOf P)).rounds ++ K1.rounds (Desc.K15.parK1 P) ++
        (Desc.K15.bLink P (Desc.K15.fiveOf P)).rounds ++
        (Desc.K15.bPhi P (Desc.K15.fiveOf P)).rounds := by
  rw [Desc.K15.blocksV_eq P _ he]
  rfl

/-- **One roundsFit is front6's four, at five rounds.** -/
theorem fit6_cut (P : P15) (rs : List Fmt.RoundView)
    (he : Desc.K15.entries P = some (Desc.K15.fiveOf P))
    (h : roundsFit ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap (·.rounds)) rs =
      true) :
    ∃ r0 r1 r2 r3 r4, rs = [r0, r1, r2, r3, r4] ∧
      roundsFit (Desc.K15.bPoint P (Desc.K15.fiveOf P)).rounds [r0] = true ∧
      roundsFit (K1.rounds (Desc.K15.parK1 P)) [r1, r2] = true ∧
      roundsFit (Desc.K15.bLink P (Desc.K15.fiveOf P)).rounds [r3] = true ∧
      roundsFit (Desc.K15.bPhi P (Desc.K15.fiveOf P)).rounds [r4] = true := by
  rw [six_rounds P he] at h
  have hl : rs.length = 5 := roundsFit_length _ _ h
  obtain ⟨r0, r1, r2, r3, r4, rfl⟩ : ∃ r0 r1 r2 r3 r4, rs = [r0, r1, r2, r3, r4] := by
    rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, t⟩⟩⟩⟩⟩⟩
    all_goals first
      | exact ⟨_, _, _, _, _, rfl⟩
      | (simp at hl)
  obtain ⟨h123, h4⟩ := (roundsFit_append _ _ _).1 h
  obtain ⟨h12, h3⟩ := (roundsFit_append _ _ _).1 h123
  obtain ⟨h1, h2⟩ := (roundsFit_append _ _ _).1 h12
  exact ⟨r0, r1, r2, r3, r4, rfl, h1, h2, h3, h4⟩

/-- **What the six's declared rounds read, in a row, is what "LINK" is owed.** -/
theorem want6 (P : P15) (r0 r1 r2 r3 r4 : Fmt.RoundView)
    (he : Desc.K15.entries P = some (Desc.K15.fiveOf P)) :
    (groupsOf 0 ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap (·.rounds))
      ([r0, r1, r2, r3, r4].map (·.drawn))).flatMap id = linkWant P.S r3 := by
  rw [six_rounds P he]
  show (groupsOf 0 [{ entry := _ }, { entry := _ }, { entry := _ },
    { entry := _, stored := Desc.K15.readsAtLink P.S }, { entry := _ }]
    [r0.drawn, r1.drawn, r2.drawn, r3.drawn, r4.drawn]).flatMap id = _
  simp only [groupsOf, List.map_nil, List.nil_append, List.append_nil]
  unfold linkWant partWant
  simp [List.flatMap_map]

/-- **front6 IN THE LETTERS OF THE CHAIN's JOIN.** -/
theorem front6_join (P : P15) (x : TableKey × TableKey) (rs : List Fmt.RoundView) (c more : List OpenedColumn)
    (he : Desc.K15.entries P = some (Desc.K15.fiveOf P)) (hl : P.codes.lengthsOk = true)
    (hok : linkOk P.codes P.S P.set.samples = true)
    (hp : K1.planOkOwn (Desc.K15.parK1 P) = true) (k0 : Own.keyFits x.1 P.S.table = true)
    (k1 : Own.keyFits x.2 P.S.table = true) (z0 : x.1.seeds.all (!isZeroE ·.beta) = true)
    (z1 : x.2.seeds.all (!isZeroE ·.beta) = true)
    (hf : roundsFit ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap (·.rounds)) rs =
      true)
    (hc : c.map (fun y => (y.1, y.2.1, y.2.2.length)) =
      (groupsOf 0 ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap (·.rounds))
        (rs.map (·.drawn))).flatMap id) :
    ∃ d' G', foldBlocks 0 (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P)
        (Desc.K15.first P.codes x) rs (c ++ more) = .ok (d', [], more) ∧
      LinkSeats P.par d' G' ∧ Means.InOrder d'.st ∧
      G'.rows.size =
        2 * P.S.table.answers + (P.S.columnsFirst + P.S.columnsFurther) + 1 := by
  obtain ⟨r0, r1, r2, r3, r4, rfl, f0, f12, f3, f4⟩ := fit6_cut P rs he hf
  rw [want6 P r0 r1 r2 r3 r4 he] at hc
  have hlen : c.length = (linkWant P.S r3).length := by rw [← hc, List.length_map]
  obtain ⟨d', G', e, H, hI, hn⟩ := front6_all P x r0 r1 r2 r3 r4 (c ++ more) he hl hok hp k0 k1 z0
    z1 f0 f12 f3 (by rw [← hlen, List.take_left' rfl]; exact hc) f4
  rw [← hlen, List.drop_left' rfl] at e
  exact ⟨d', G', e, H, hI, hn⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.six_rounds
#print axioms Johnson.Prover.Link.fit6_cut
#print axioms Johnson.Prover.Link.want6
#print axioms Johnson.Prover.Link.front6_join
