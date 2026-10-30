-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CutKey.lean: THE KEY FILE's FIRST CHAIN CUT IN PIECES: callsFrom's routine at
«key 0» (`key0R`, Johnson/AtFull/Rows/Tail.lean) is its pieces one behind the other, down to one
product tree of a lookup a piece. After the pattern of Johnson/AtFull/Rows/Cut.lean, which cuts
«proof 0». Definitions and theorems. A law file; no running text imports it.

Why. A closed test on a slice of «key 0»'s noted calls (`sliceD`, Slice.lean) runs the whole routine
once for its calls before it walks its slice. A piece is run alone.

Definitions.
  `partsOf x`: `nLookup`'s own «parts» (Johnson/G/Calls.lean).
  `lookHead x`, `lookEnd x`: SECOND TEXTS of `nLookup`'s lines in front of and behind its loop on
    the product trees.
  `lookPieces x`: the head, one piece a product tree, the end.
  `rangesHead`, `rangesEnd`: SECOND TEXTS of `nRanges`' lines in front of and behind its loop on the
    lookups. `rangesPieces`.
  `key0Head`, `key0End`: SECOND TEXTS of `key0R`'s lines in front of and behind `nRanges`.
    `key0Pieces`.
Statements.
  `forIn_seqN`: a loop over a list whose body is a routine without a value is `seqN` of the list's
    routines.
  `seqN_flatMap`: `seqN` over lists laid end to end.
  `nLookup_seq`, `nRanges_seq`, `key0R_seq`: each routine is `seqN` of its pieces.
  `fr_key0Pieces`, `faith_key0Pieces`: each piece reads no round, and is faithful.

Limits. None of the second texts is running text; each is tied to the routine that it repeats by one
of the three equations, which Lean checks. They will have to be turned with `nLookup`, `nRanges` and
`key0R`; the three equations would then fail. No closed fact is here. Nothing on soundness or on
hiding.
-/
import Johnson.AtFull.Rows.Slice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- A loop whose body is a routine without a value. -/
theorem forIn_seqN {γ : Type} (f : γ → N Unit) : ∀ l : List γ,
    (forIn l PUnit.unit fun a _ => do f a; pure (ForInStep.yield PUnit.unit)) = seqN (l.map f)
  | [] => by
    rw [List.forIn_nil]
    rfl
  | a :: l => by
    rw [List.forIn_cons]
    simp only [bind_assoc, pure_bind, List.map_cons, seqN]
    rw [forIn_seqN f l]

theorem seqN_flatMap {γ : Type} (f : γ → List (N Unit)) : ∀ l : List γ,
    seqN (l.flatMap f) = seqN (l.map fun a => seqN (f a))
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, seqN_append, seqN_flatMap f l]
    rfl

/-- nLookup's own «parts». -/
def partsOf (x : LookupSize) : List Nat := if x.parts.isEmpty then [x.v] else x.parts

/-- nLookup's lines in front of its loop on the product trees. -/
def lookHead (x : LookupSize) : N Unit := do
  let s ← (theSetting : Planning Setting)
  let slots := 2 ^ min x.mu 6
  let w := if x.live != 0 then x.live else slots
  let parts := if x.parts.isEmpty then [x.v] else x.parts
  let keys := sumT (parts.map (2 ^ ·))
  (needs (decide (1 ≤ x.mu) && decide (x.mu ≤ 6) && decide (2 ≤ w) && decide (w ≤ slots)) :
    Planning Unit)
  (needs (decide (keys < 2 ^ w) && decide (2 ^ x.d * (2 ^ w - 1) < s.p)) : Planning Unit)
  if x.shifted then note (.shift (2 ^ x.d))
  note (.lkp keys)
  note (.psc { degreeY := 3, values := 3 })
  for _ in List.range (w - 2) do note (.psc { degreeY := 3, values := 2 })
  for _ in List.range (parts.length - 1) do note (.psc {})
  note (.join x.mu)

/-- nLookup's lines behind that loop. -/
def lookEnd (x : LookupSize) : N Unit := do
  note (.productTree x.d x.mu)
  note (.psc { degree := List.replicate x.d 3 ++ List.replicate x.mu 2, withY := false })
  note (.zero (x.mu + x.d))
  note (.psc { degree := List.replicate (x.mu + x.d) 3, degreeY := 2, values := 1 })

/-- The pieces of a lookup: one product tree a piece. -/
def lookPieces (x : LookupSize) : List (N Unit) :=
  lookHead x :: (partsOf x).map (fun v => note (.productTree v 0)) ++ [lookEnd x]

/-- **A lookup is its pieces, one behind the other.** -/
theorem nLookup_seq (x : LookupSize) : nLookup x = seqN (lookPieces x) := by
  unfold lookPieces
  rw [List.cons_append]
  unfold seqN
  rw [seqN_append, seqN_one, ← forIn_seqN]
  unfold nLookup lookHead lookEnd partsOf
  simp only [bind_assoc, ite_bindN, pure_bind]
  try rfl

open OnBytes.Plan in
/-- nRanges' lines in front of its loop on the lookups. -/
def rangesHead (codes : Codes) (z : OnBytes.Plan.RangesSized) : N Unit := do
  let roots ← (must (treesOf codes (Wf.messageOf z.x)) : Planning Nat)
  note (.send [⟨cubeBitsOf codes z.x.message.shape, [z.test.first]⟩] roots true)

open OnBytes.Plan in
/-- nRanges' lines behind that loop. -/
def rangesEnd (codes : Codes) (z : OnBytes.Plan.RangesSized) : N Unit := do
  (needs (sizedFits codes z.x.stages z.test.stages) : Planning Unit)
  nIopp z.test.stages (Wf.rowsBatched z.x z.matrix) (if z.x.choice.masksRide then 0 else 1)
    z.x.choice.masksRide
  if 1 < z.pending then note (.batt z.pending z.matrix.kCol)

open OnBytes.Plan in
/-- The pieces of the proof of the ranges. -/
def rangesPieces (codes : Codes) (z : OnBytes.Plan.RangesSized) : List (N Unit) :=
  rangesHead codes z :: (lookupSizes z.x z.matrix).flatMap lookPieces ++ [rangesEnd codes z]

/-- **The proof of the ranges is its pieces, one behind the other.** -/
theorem nRanges_seq (codes : Codes) (z : OnBytes.Plan.RangesSized) :
    nRanges codes z = seqN (rangesPieces codes z) := by
  unfold rangesPieces
  rw [List.cons_append]
  unfold seqN
  rw [seqN_append, seqN_one, seqN_flatMap]
  simp only [← nLookup_seq]
  rw [← forIn_seqN]
  unfold nRanges rangesHead rangesEnd
  simp only [bind_assoc]
  try rfl

/-- key0R's lines in front of the proof of the ranges. -/
def key0Head (c : Configured) : N Unit := do
  note (.record c.sized.key.once.table)
  note (.send [⟨cubeBitsOf c.sized.key.codes c.sized.key.once.input.shape,
    [c.sized.key.once.own.first]⟩] 1 true)

/-- key0R's lines behind it. -/
def key0End (c : Configured) : N Unit := do
  nLinFirst c.sized.key.codes c.sized.key.once
  note .seal

/-- The pieces of «key 0». -/
def key0Pieces (c : Configured) : List (N Unit) :=
  key0Head c :: rangesPieces c.sized.key.codes c.sized.key.ranges ++ [key0End c]

/-- **«key 0» is its pieces, one behind the other.** -/
theorem key0R_seq (c : Configured) : key0R c = seqN (key0Pieces c) := by
  unfold key0Pieces
  rw [List.cons_append]
  unfold seqN
  rw [seqN_append, seqN_one, ← nRanges_seq]
  unfold key0R key0Head key0End
  simp only [bind_assoc]

theorem fr_lookPieces (x : LookupSize) : ∀ y ∈ lookPieces x, Fr y := by
  intro y hy
  unfold lookPieces at hy
  rcases List.mem_append.1 hy with hy | hy
  · rcases List.mem_cons.1 hy with rfl | hy
    · unfold lookHead
      frn
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy
      exact fr_note _
  · rcases List.mem_singleton.1 hy with rfl
    unfold lookEnd
    frn

theorem faith_lookPieces (x : LookupSize) : ∀ y ∈ lookPieces x, Faith y := by
  intro y hy
  unfold lookPieces at hy
  rcases List.mem_append.1 hy with hy | hy
  · rcases List.mem_cons.1 hy with rfl | hy
    · unfold lookHead
      fth
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy
      exact faith_note _
  · rcases List.mem_singleton.1 hy with rfl
    unfold lookEnd
    fth

theorem fr_rangesPieces (codes : Codes) (z : OnBytes.Plan.RangesSized) :
    ∀ y ∈ rangesPieces codes z, Fr y := by
  intro y hy
  unfold rangesPieces at hy
  rcases List.mem_append.1 hy with hy | hy
  · rcases List.mem_cons.1 hy with rfl | hy
    · unfold rangesHead
      frn
    · obtain ⟨p, -, hp⟩ := List.mem_flatMap.1 hy
      exact fr_lookPieces p y hp
  · rcases List.mem_singleton.1 hy with rfl
    unfold rangesEnd
    frn

theorem faith_rangesPieces (codes : Codes) (z : OnBytes.Plan.RangesSized) :
    ∀ y ∈ rangesPieces codes z, Faith y := by
  intro y hy
  unfold rangesPieces at hy
  rcases List.mem_append.1 hy with hy | hy
  · rcases List.mem_cons.1 hy with rfl | hy
    · unfold rangesHead
      fth
    · obtain ⟨p, -, hp⟩ := List.mem_flatMap.1 hy
      exact faith_lookPieces p y hp
  · rcases List.mem_singleton.1 hy with rfl
    unfold rangesEnd
    fth

/-- **Each piece of «key 0» reads no round.** -/
theorem fr_key0Pieces (c : Configured) : ∀ y ∈ key0Pieces c, Fr y := by
  intro y hy
  unfold key0Pieces at hy
  rcases List.mem_append.1 hy with hy | hy
  · rcases List.mem_cons.1 hy with rfl | hy
    · unfold key0Head
      frn
    · exact fr_rangesPieces _ _ y hy
  · rcases List.mem_singleton.1 hy with rfl
    have := fr_nLinFirst c.sized.key.codes c.sized.key.once
    unfold key0End
    frn

/-- **Each piece of «key 0» is faithful.** -/
theorem faith_key0Pieces (c : Configured) : ∀ y ∈ key0Pieces c, Faith y := by
  intro y hy
  unfold key0Pieces at hy
  rcases List.mem_append.1 hy with hy | hy
  · rcases List.mem_cons.1 hy with rfl | hy
    · unfold key0Head
      fth
    · exact faith_rangesPieces _ _ y hy
  · rcases List.mem_singleton.1 hy with rfl
    have := faith_nLinFirst c.sized.key.codes c.sized.key.once
    unfold key0End
    fth

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.forIn_seqN
#print axioms VerifiableInference.Desc.LinkJoin.seqN_flatMap
#print axioms VerifiableInference.Desc.LinkJoin.nLookup_seq
#print axioms VerifiableInference.Desc.LinkJoin.nRanges_seq
#print axioms VerifiableInference.Desc.LinkJoin.key0R_seq
#print axioms VerifiableInference.Desc.LinkJoin.fr_lookPieces
#print axioms VerifiableInference.Desc.LinkJoin.faith_lookPieces
#print axioms VerifiableInference.Desc.LinkJoin.fr_rangesPieces
#print axioms VerifiableInference.Desc.LinkJoin.faith_rangesPieces
#print axioms VerifiableInference.Desc.LinkJoin.fr_key0Pieces
#print axioms VerifiableInference.Desc.LinkJoin.faith_key0Pieces
