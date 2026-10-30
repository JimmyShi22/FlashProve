-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/ShapesOfIds.lean: `ShapesAre` (LayoutOfShapes.lean, beside this file)
AND "THE NUMBERING PARTS THE MEMBERS", WITH THE NUMBERING AS A TERM, FROM FOUR SENTENCES IN A WALK's
OWN TERMS: the group's members are a list of numbers ids; no number stands twice; the flags are the
joiners' flags; the messages' shapes at ids are the joiners' shapes. Definitions, statements and
proofs.

Why. `k10_public_full` (PublicFull.lean) asks `ShapesAre T G lo kb no` and that no parts the
members, general in a numbering no. A walk along the chain ends in what the makers append: a list of
message numbers, a list of flags, the new messages' shapes. The written request's shape says who
joins (`joinersAt`, ReqKept.lean).
  `noOf lo ids`: THE NUMBERING: the member at the place n among the members bears ids' n-th number.
  `pos_at`: the member at the place n stands at the place n. `map_noOf`: the members' numbers are
    ids, where ids has as many numbers as lo has members. `noOf_inj`: if no number stands twice in
    ids, the numbering parts the members.
  `shapesAre_of_ids`: general in lo and kb: G.members.toList = ids; as many numbers as members;
    G.kept.toList = the members' flags; at each place n the message number ids[n] has the n-th
    member's written shape: `ShapesAre T G lo kb (noOf lo ids)`.
  `joiners_full`, `joiners_small`: at each of the 25 (5) links: the written list's members' flags
    `kbAt` and shapes ARE the joiners' flags and shapes, in order: by the kernel.
  `shapesAre_full {l} (hl : l < 25)`, `shapesAre_small`: G.members.toList = ids; ids.Nodup;
    G.kept.toList = the joiners' flags; the shapes at ids are the joiners' shapes: `ShapesAre` at
    the l-th written list, the flags `kbAt shapeFull l` and `noOf`, AND the numbering parts the
    members: the two premises of `k10_public_full`.
Limits. The four sentences are shown of no verifier's state here: they are what the walk by place in
other files is to end in, with the two makers' laws. `joinersAt` is typed after the program's two
rules and tied to the program by no lemma. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.CubeOfShapes
import Johnson.Desc.First.Close.Law.ReqKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.G
open VerifiableInference.Desc.ReqLit

/-- **The numbering off a list of numbers.** -/
def noOf (lo : List (OracleShape × ℕ)) (ids : List ℕ) (i : Fin lo.length) : ℕ :=
  ids.getD (posOf lo i) 0

/-- The member at the place n stands at the place n. -/
theorem pos_at (lo : List (OracleShape × ℕ)) {n : ℕ} (h : n < (membersOf lo).length) :
    posOf lo (membersOf lo)[n] = n := by
  have hm : (membersOf lo)[n] ∈ membersOf lo := List.getElem_mem h
  have e := (List.getElem?_eq_some_iff.1 (pos_get lo _ hm)).2
  exact (List.Nodup.getElem_inj_iff (members_nodup lo)).1 e

theorem map_noOf (lo : List (OracleShape × ℕ)) (ids : List ℕ)
    (hlen : ids.length = (membersOf lo).length) : (membersOf lo).map (noOf lo ids) = ids := by
  refine List.ext_getElem (by rw [List.length_map, hlen]) fun n h1 h2 => ?_
  rw [List.getElem_map]
  unfold noOf
  rw [pos_at lo (by rwa [List.length_map] at h1), List.getD_eq_getElem _ _ h2]

theorem noOf_inj (lo : List (OracleShape × ℕ)) (ids : List ℕ)
    (hlen : ids.length = (membersOf lo).length) (hn : ids.Nodup) :
    ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, noOf lo ids i = noOf lo ids j → i = j := by
  intro i hi j hj e
  have pi : posOf lo i < ids.length := hlen ▸ pos_lt lo i hi
  have pj : posOf lo j < ids.length := hlen ▸ pos_lt lo j hj
  unfold noOf at e
  rw [List.getD_eq_getElem _ _ pi, List.getD_eq_getElem _ _ pj] at e
  have ep := (List.Nodup.getElem_inj_iff hn).1 e
  have gi := pos_get lo i hi
  rw [ep, pos_get lo j hj] at gi
  exact (Option.some.inj gi).symm

section
variable {T : Statement} {G : Group}

/-- **ShapesAre from a list of numbers**, general in the written list and the flags. -/
theorem shapesAre_of_ids {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool} {ids : List ℕ}
    (hm : G.members.toList = ids) (hlen : ids.length = (membersOf lo).length)
    (hk : G.kept.toList = (membersOf lo).map kb)
    (hs : ∀ n (h : n < (membersOf lo).length),
      (T.oracles[ids.getD n 0]?).map (fun x : OnBytes.Oracle => x.shape) =
        some (lo.get (membersOf lo)[n]).1) : ShapesAre T G lo kb (noOf lo ids) where
  members := by rw [hm, map_noOf lo ids hlen]
  kept := hk
  shape := fun i hi => by
    have h := hs (posOf lo i) (pos_lt lo i hi)
    rw [(List.getElem?_eq_some_iff.1 (pos_get lo i hi)).2] at h
    exact h

end

/-- The test at a link: the written list's members' flags and shapes are the joiners'. -/
def joinersFit (s : ReqShape) (lo : List (OracleShape × ℕ)) (l : ℕ) : Bool :=
  decide ((membersOf lo).map (kbAt s l lo) = (joinersAt s l).map (·.2)) &&
    decide ((membersOf lo).map (fun i => (lo.get i).1) = (joinersAt s l).map (·.1))

set_option maxRecDepth 1000000 in
theorem joiners_full :
    ((List.range 25).all fun l => joinersFit shapeFull (linksFullLit.getD l []) l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem joiners_small :
    ((List.range 5).all fun l => joinersFit shapeSmall (linksSmallLit.getD l []) l) = true := by
  decide +kernel

section
variable {T : Statement} {G : Group}

/-- From the test's yes. -/
theorem shapesAre_of_joiners {s : ReqShape} {lo : List (OracleShape × ℕ)} {l : ℕ}
    (hj : joinersFit s lo l = true) {ids : List ℕ} (hm : G.members.toList = ids)
    (hn : ids.Nodup) (hk : G.kept.toList = (joinersAt s l).map (·.2))
    (hs : ids.map (fun o => (T.oracles[o]?).map fun x : OnBytes.Oracle => x.shape) =
      (joinersAt s l).map fun x => some x.1) :
    ShapesAre T G lo (kbAt s l lo) (noOf lo ids) ∧
      ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, noOf lo ids i = noOf lo ids j → i = j := by
  unfold joinersFit at hj
  obtain ⟨j1, j2⟩ := Bool.and_eq_true _ _ ▸ hj
  have j1' := of_decide_eq_true j1
  have j2' := of_decide_eq_true j2
  have hlen : ids.length = (membersOf lo).length := by
    have a := congrArg List.length hs
    have b := congrArg List.length j2'
    simp only [List.length_map] at a b
    omega
  refine ⟨shapesAre_of_ids hm hlen (hk.trans j1'.symm) fun n h => ?_, noOf_inj lo ids hlen hn⟩
  have hn' : n < ids.length := hlen ▸ h
  have a : (ids.map fun o => (T.oracles[o]?).map fun x : OnBytes.Oracle => x.shape)[n]? =
      ((joinersAt s l).map fun x => some x.1)[n]? := by rw [hs]
  have b : ((membersOf lo).map fun i => (lo.get i).1)[n]? = ((joinersAt s l).map (·.1))[n]? := by
    rw [j2']
  rw [List.getElem?_map, List.getElem?_eq_getElem hn', List.getElem?_map] at a
  rw [List.getElem?_map, List.getElem?_eq_getElem h, List.getElem?_map] at b
  rw [List.getD_eq_getElem _ _ hn']
  cases hx : (joinersAt s l)[n]? with
  | none => rw [hx] at a; cases a
  | some x =>
    rw [hx] at a b
    have a' : (T.oracles[ids[n]]?).map (fun x : OnBytes.Oracle => x.shape) = some x.1 :=
      Option.some.inj a
    have b' : (lo.get (membersOf lo)[n]).1 = x.1 := Option.some.inj b
    rw [a', b']

/-- **AT THE FULL SIZE's 25 LINKS: the two premises of k10_public_full.** -/
theorem shapesAre_full {l : ℕ} (hl : l < 25) {ids : List ℕ} (hm : G.members.toList = ids)
    (hn : ids.Nodup) (hk : G.kept.toList = (joinersAt shapeFull l).map (·.2))
    (hs : ids.map (fun o => (T.oracles[o]?).map fun x : OnBytes.Oracle => x.shape) =
      (joinersAt shapeFull l).map fun x => some x.1) :
    ShapesAre T G (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l []))
        (noOf (linksFullLit.getD l []) ids) ∧
      ∀ i ∈ membersOf (linksFullLit.getD l []), ∀ j ∈ membersOf (linksFullLit.getD l []),
        noOf (linksFullLit.getD l []) ids i = noOf (linksFullLit.getD l []) ids j → i = j :=
  shapesAre_of_joiners (List.all_eq_true.1 joiners_full l (List.mem_range.2 hl)) hm hn hk hs

/-- The like at the small size's 5 links. -/
theorem shapesAre_small {l : ℕ} (hl : l < 5) {ids : List ℕ} (hm : G.members.toList = ids)
    (hn : ids.Nodup) (hk : G.kept.toList = (joinersAt shapeSmall l).map (·.2))
    (hs : ids.map (fun o => (T.oracles[o]?).map fun x : OnBytes.Oracle => x.shape) =
      (joinersAt shapeSmall l).map fun x => some x.1) :
    ShapesAre T G (linksSmallLit.getD l []) (kbAt shapeSmall l (linksSmallLit.getD l []))
        (noOf (linksSmallLit.getD l []) ids) ∧
      ∀ i ∈ membersOf (linksSmallLit.getD l []), ∀ j ∈ membersOf (linksSmallLit.getD l []),
        noOf (linksSmallLit.getD l []) ids i = noOf (linksSmallLit.getD l []) ids j → i = j :=
  shapesAre_of_joiners (List.all_eq_true.1 joiners_small l (List.mem_range.2 hl)) hm hn hk hs

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.shapesAre_of_ids
#print axioms VerifiableInference.Desc.First.Close.joiners_full
#print axioms VerifiableInference.Desc.First.Close.joiners_small
#print axioms VerifiableInference.Desc.First.Close.shapesAre_full
#print axioms VerifiableInference.Desc.First.Close.shapesAre_small
