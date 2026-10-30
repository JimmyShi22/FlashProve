-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormWalks.lean: THE FORM's HALF: **THE LINK's SIX FRONT BLOCKS IN THE LETTERS OF
THE CHAIN's JOIN**: the blocks' decisions in a row (Walks, Johnson/Prover/Link/ChainDefs.lean), at
the blocks as Chain.blocksInOrder lays them; with it the fold's equation, and what stands behind the six.

Main names.
  flat_split      the chain's flat list: the six, then the test's block and the chain's end.
  bare_same       a list of blocks, and the same as Chain.blocksInOrder lays them: rounds and decisions are
  one.
  front6_walks    GENERAL IN THE PARAMETERS AND THE LOOK-UP: from one roundsFit and one «served» at
    the six's declared rounds.
  decls_split     the chain's declared rounds begin with the six's, which are five.
  front6_of_decls the same from the chain's one roundsFit and one «served», at the first five
  rounds.
  front6_walks_full   at the typed parameters frP and the written keys.

How. front6_join (FormFront6Cut.lean); colsFor_served (ChainYes.lean); walks_of_fold, walks_congr
(ChainBack.lean); roundsFit_append, groupsOf_app (Johnson/Top/H0/StepLaws/StepLaws.lean); plan_full,
keys_full (AtD.lean).

Limits. roundsFit and «served» are premises. It ends in front of the proximity test. Nothing on
soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFront6Cut
import Johnson.Prover.Link.AtD
import Johnson.Prover.Link.ChainBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Flat
open VerifiableInference.Desc
open VerifiableInference.Desc.Plain.One (colsFor)
open Desc.K15 (St Par15 P15 frP linkDeclaredRounds)

/-- The chain's flat list: the six front blocks, then the test's block and the chain's end. -/
theorem flat_split (P : P15) : (Desc.K15.linkProtocolChain P).blocksInOrder =
    (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).map
        (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ++
      [{ Desc.K15.testBlock P with
          planOk := (Desc.K15.testBlock P).planOk && (Desc.K15.testBlock P).hasNoClaimsAndNothingAfter },
        { (Desc.K15.linkProtocolChain P).last with
          planOk := (Desc.K15.linkProtocolChain P).last.planOk && (Desc.K15.linkProtocolChain P).last.hasNoClaimsAndNothingAfter }] := by
  unfold Chain.blocksInOrder
  show _ :: ([].map _ ++ [].flatMap _ ++ (Desc.K15.blocksOrV P ++ [Desc.K15.testBlock P]).map _ ++
    [_]) = _
  simp
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A list of blocks, and the same as Chain.blocksInOrder lays them: rounds and decisions are one. -/
theorem bare_same {S Cl : Type} : ∀ l : List (Block S Cl),
    List.Forall₂ (fun b b' => b.rounds = b'.rounds ∧ b.decide = b'.decide) l
      (l.map fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter })
  | [] => .nil
  | _ :: l => .cons ⟨rfl, rfl⟩ (bare_same l)

/-- **front6_walks**, general in the parameters and in the look-up. -/
theorem front6_walks (P : P15) (x : TableKey × TableKey) (L : Nat → Nat → Option (List UInt64))
    (rs : List Fmt.RoundView) (more : List OpenedColumn) (he : Desc.K15.entries P = some (Desc.K15.fiveOf P))
    (hl : P.codes.lengthsOk = true) (hok : linkOk P.codes P.S P.set.samples = true)
    (hp : K1.planOkOwn (Desc.K15.parK1 P) = true) (k0 : Own.keyFits x.1 P.S.table = true)
    (k1 : Own.keyFits x.2 P.S.table = true) (z0 : x.1.seeds.all (!isZeroE ·.beta) = true)
    (z1 : x.2.seeds.all (!isZeroE ·.beta) = true)
    (hf : roundsFit ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap (·.rounds)) rs =
      true)
    (hs : Served L ((groupsOf 0 ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap
      (·.rounds)) (rs.map (·.drawn))).flatMap id)) :
    ∃ d' G' c,
      colsFor L ((groupsOf 0 ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap (·.rounds))
        (rs.map (·.drawn))).flatMap id) = some c ∧
      foldBlocks 0 (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P) (Desc.K15.first P.codes x) rs
        (c ++ more) = .ok (d', [], more) ∧
      Walks 0 L ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).map
        (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter })) (Desc.K15.first P.codes x) rs d' ∧
      LinkSeats P.par d' G' ∧ Means.InOrder d'.st ∧
      G'.rows.size =
        2 * P.S.table.answers + (P.S.columnsFirst + P.S.columnsFurther) + 1 := by
  obtain ⟨c, c1, c2⟩ := colsFor_served L _ hs
  obtain ⟨d', G', e, H, hI, hn⟩ := front6_join P x rs c more he hl hok hp k0 k1 z0 z1 hf c2
  exact ⟨d', G', c, c1, e,
    walks_congr 0 L _ _ _ _ _ (bare_same _) (walks_of_fold 0 L _ _ d' rs c more more c1 e), H, hI,
    hn⟩

/-- The chain's declared rounds begin with the six's, which are five. -/
theorem decls_split (P : P15) (he : Desc.K15.entries P = some (Desc.K15.fiveOf P)) :
    ∃ tail, linkDeclaredRounds P =
        (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap (·.rounds) ++ tail ∧
      ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap (·.rounds)).length = 5 := by
  refine ⟨(Desc.K15.testBlock P).rounds ++ ((Desc.K15.linkProtocolChain P).last.rounds ++ []), ?_, ?_⟩
  · unfold linkDeclaredRounds
    rw [flat_split, List.flatMap_append, List.flatMap_map]
    rfl
  · rw [six_rounds P he]
    rfl

/-- **The same from the chain's one roundsFit and one «served»**, at the first five rounds. -/
theorem front6_of_decls (P : P15) (x : TableKey × TableKey)
    (L : Nat → Nat → Option (List UInt64)) (rs : List Fmt.RoundView) (more : List OpenedColumn)
    (he : Desc.K15.entries P = some (Desc.K15.fiveOf P)) (hl : P.codes.lengthsOk = true)
    (hok : linkOk P.codes P.S P.set.samples = true)
    (hp : K1.planOkOwn (Desc.K15.parK1 P) = true) (k0 : Own.keyFits x.1 P.S.table = true)
    (k1 : Own.keyFits x.2 P.S.table = true) (z0 : x.1.seeds.all (!isZeroE ·.beta) = true)
    (z1 : x.2.seeds.all (!isZeroE ·.beta) = true) (hf : roundsFit (linkDeclaredRounds P) rs = true)
    (hs : Served L ((groupsOf 0 (linkDeclaredRounds P) (rs.map (·.drawn))).flatMap id)) :
    ∃ d' G' c,
      colsFor L ((groupsOf 0 ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).flatMap (·.rounds))
        ((rs.take 5).map (·.drawn))).flatMap id) = some c ∧
      foldBlocks 0 (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P) (Desc.K15.first P.codes x)
        (rs.take 5) (c ++ more) = .ok (d', [], more) ∧
      Walks 0 L ((Desc.K15.frontBlock P :: Desc.K15.blocksOrV P).map
        (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter })) (Desc.K15.first P.codes x)
        (rs.take 5) d' ∧
      LinkSeats P.par d' G' ∧ Means.InOrder d'.st ∧
      G'.rows.size =
        2 * P.S.table.answers + (P.S.columnsFirst + P.S.columnsFurther) + 1 := by
  obtain ⟨tail, e1, e2⟩ := decls_split P he
  rw [e1] at hf hs
  obtain ⟨f1, _⟩ := (roundsFit_append _ _ _).1 hf
  rw [groupsOf_app, ← List.map_take, List.flatMap_append] at hs
  rw [e2] at f1 hs
  exact front6_walks P x L (rs.take 5) more he hl hok hp k0 k1 z0 z1 f1 fun y hy =>
    hs y (List.mem_append_left _ hy)

/-- **AT THE COPY's FILE's OWN PLAN AND KEYS**: nothing is left but the chain's one roundsFit and
one «served». -/
theorem front6_walks_full (rr : RecFull × RecFull) (L : Nat → Nat → Option (List UInt64))
    (rs : List Fmt.RoundView) (more : List OpenedColumn) (hf : roundsFit (linkDeclaredRounds frP) rs = true)
    (hs : Served L ((groupsOf 0 (linkDeclaredRounds frP) (rs.map (·.drawn))).flatMap id)) :
    ∃ d' G' c,
      colsFor L ((groupsOf 0 ((Desc.K15.frontBlock frP :: Desc.K15.blocksOrV frP).flatMap
        (·.rounds)) ((rs.take 5).map (·.drawn))).flatMap id) = some c ∧
      foldBlocks 0 (Desc.K15.frontBlock frP :: Desc.K15.blocksOrV frP)
        (Desc.K15.first frP.codes (keyOf (fun β : NZ => β.val) rr.1,
          { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }))
        (rs.take 5) (c ++ more) = .ok (d', [], more) ∧
      Walks 0 L ((Desc.K15.frontBlock frP :: Desc.K15.blocksOrV frP).map
        (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }))
        (Desc.K15.first frP.codes (keyOf (fun β : NZ => β.val) rr.1,
          { keyOf (fun β : NZ => β.val) rr.2 with item := 1 })) (rs.take 5) d' ∧
      LinkSeats frP.par d' G' ∧ Means.InOrder d'.st ∧
      G'.rows.size =
        2 * frP.S.table.answers + (frP.S.columnsFirst + frP.S.columnsFurther) + 1 := by
  obtain ⟨p1, p2, p3, p4⟩ := plan_full
  obtain ⟨k0, k1, z0, z1⟩ := keys_full rr
  exact front6_of_decls frP _ L rs more p1 p2 p3 p4 k0 k1 z0 z1 hf hs

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.flat_split
#print axioms Johnson.Prover.Link.bare_same
#print axioms Johnson.Prover.Link.front6_walks
#print axioms Johnson.Prover.Link.decls_split
#print axioms Johnson.Prover.Link.front6_of_decls
#print axioms Johnson.Prover.Link.front6_walks_full
