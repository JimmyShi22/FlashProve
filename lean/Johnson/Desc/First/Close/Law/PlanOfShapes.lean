-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/PlanOfShapes.lean (kind K10): THE TERM FOR pS (`pSseed`,
Johnson/Desc/First/Link/Law/DrawnSeed.lean) AT A PUBLIC STATEMENT AND A PUBLIC LAYOUT IS THE SAME
TERM AT ANY STATE WHOSE GROUP HOLDS THE WRITTEN LIST's MEMBERS: the field plan of
`ShapesOwes` (TiedOfShapes.lean). Definitions, statements and proofs.

Why. K10's law has pS in front of all statements: it cannot read the state. `pSseed cs lo R N T₀ L₀
no` reads a statement T₀ and a layout L₀; `RowsTied` wants it at the begun statement and its layout.
It reads them through five functions alone (`mainWeight`, `mainBack`, `keptWeight`, `maskWeight`,
`maskBack`), and these read: of the layout: the members, the flags, the first rows of the two kinds,
k and h; of the statement: the bits of a message's rows, which hang on its shape alone
(`has_of_shape`, LayoutOfShapes.lean).
  `SameLay L L'`: the six fields agree. `find_congr`, `mainWeight_congr`, `mainBack_congr`,
    `keptWeight_congr`, `maskWeight_congr`, `maskBack_congr`: the five functions hang on these and
    on the rows' bits. `pSseed_congr`: so does `pSseed`.
  `stPub lo no`: A PUBLIC STATEMENT: one at which every member's number bears the written shape, if
    there is one (picked by choice: WITHOUT CODE); `stPub_shape`. `layPub lo kb no`: A PUBLIC LAYOUT
    (an Option): that of the statement made of the list (`stOf`), with the members' numbers no and
    the flags kb; `layPub_some`: it is there where `LayoutAgrees lo kb`.
  `sameLay_of_shapes`: a statement's layout at a group with `ShapesAre T G lo kb no` has `layPub`'s
    six fields. `bits_of_shapes`: the rows' bits at a member's number are `stPub`'s.
  `plan_of_shapes`: SO at R := `groupLayK ..`, L₀ what `layPub` returns: `pSseed .. (stPub lo no) L₀
    no as D = pSseed .. T L no as D` wherever T.groups[g]? = some G, T.layout g = some L and
    `ShapesAre T G lo kb no`: THE FIELD plan, at T₀ := `stPub lo no`.
Limits. `ShapesAre` at a state is a premise. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.DrawnSeed
import Johnson.Desc.First.Close.Law.CubeOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb
open OnBytes.LayLaw (laySizes layout_eq)
open VerifiableInference.Desc.LinkJoin (pSseed)

/-- Two layouts agree in what the five functions read. -/
structure SameLay (L L' : GroupLayout) : Prop where
  members : L.members = L'.members
  kept : L.kept = L'.kept
  mainFirst : L.mainFirst = L'.mainFirst
  maskFirst : L.maskFirst = L'.maskFirst
  k : L.k = L'.k
  h : L.h = L'.h

section
variable {S S' : Statement} {L L' : GroupLayout} (Y : SameLay L L') (o : ℕ)

include Y in
theorem find_congr : L.find o = L'.find o := by
  unfold GroupLayout.find
  rw [Y.members]

include Y in
theorem mainWeight_congr (hb : S.rowBits o .main = S'.rowBits o .main) (J : ℕ) :
    mainWeight (K := GE) S L o J = mainWeight (K := GE) S' L' o J := by
  unfold mainWeight
  rw [find_congr Y o, Y.kept, Y.mainFirst, Y.k, hb]

include Y in
theorem mainBack_congr (hb : S.rowBits o .main = S'.rowBits o .main) (J : ℕ) :
    mainBack S L o J = mainBack S' L' o J := by
  unfold mainBack
  rw [Y.k, hb]

include Y in
theorem keptWeight_congr : keptWeight (K := GE) L o = keptWeight (K := GE) L' o := by
  unfold keptWeight
  rw [find_congr Y o, Y.kept]

include Y in
theorem maskWeight_congr (hb : S.rowBits o .mask = S'.rowBits o .mask) (J : ℕ) :
    maskWeight (K := GE) S L o J = maskWeight (K := GE) S' L' o J := by
  unfold maskWeight
  rw [find_congr Y o, Y.maskFirst, Y.h, hb]

include Y in
theorem maskBack_congr (hb : S.rowBits o .mask = S'.rowBits o .mask) (J : ℕ) :
    maskBack S L o J = maskBack S' L' o J := by
  unfold maskBack
  rw [Y.h, hb]

end

/-- **The term for pS hangs on the six fields and on the members' rows' bits.** -/
theorem pSseed_congr (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ)) (R : RowsK (sigOf cs lo))
    (N : SlotNames R) {T T' : Statement} {L L' : GroupLayout} (no : Fin lo.length → ℕ)
    (Y : SameLay L L')
    (hb : ∀ (a : R.G.A) (part : Part), T.rowBits (no a.1) part = T'.rowBits (no a.1) part)
    (as : Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S) (D : ((sigOf cs lo).om as.1.1).Z.D) :
    pSseed cs lo R N T L no as D = pSseed cs lo R N T' L' no as D := by
  have e1 := mainWeight_congr Y (no as.1.1) (hb as.1 .main)
  have e2 := mainBack_congr Y (no as.1.1) (hb as.1 .main)
  have e3 := keptWeight_congr Y
  have e4 := maskWeight_congr Y (no as.1.1) (hb as.1 .mask)
  have e5 := maskBack_congr Y (no as.1.1) (hb as.1 .mask)
  unfold pSseed
  simp only [e1, e2, e3, e4, e5]

open Classical in
/-- A public statement: every member's number bears the written shape, if a statement does so. -/
noncomputable def stPub (lo : List (OracleShape × ℕ)) (no : Fin lo.length → ℕ) : Statement :=
  if h : ∃ T : Statement, ∀ i ∈ membersOf lo,
      (T.oracles[no i]?).map (fun x : OnBytes.Oracle => x.shape) = some (lo.get i).1 then
    h.choose
  else stOf lo fun _ => false

theorem stPub_shape {lo : List (OracleShape × ℕ)} {no : Fin lo.length → ℕ}
    (h : ∃ T : Statement, ∀ i ∈ membersOf lo,
      (T.oracles[no i]?).map (fun x : OnBytes.Oracle => x.shape) = some (lo.get i).1) :
    ∀ i ∈ membersOf lo,
      ((stPub lo no).oracles[no i]?).map (fun x : OnBytes.Oracle => x.shape) =
        some (lo.get i).1 := by
  unfold stPub
  rw [dif_pos h]
  exact h.choose_spec

/-- A public layout: that of the statement made of the list, under the numbers no. -/
def layPub (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) (no : Fin lo.length → ℕ) :
    Option GroupLayout :=
  ((stOf lo kb).layout 0).map fun L =>
    { L with members := ((membersOf lo).map no).toArray, kept := ((membersOf lo).map kb).toArray }

section
variable {T : Statement} {G : Group} {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool}
  {no : Fin lo.length → ℕ}

/-- The rows' bits at a member's number are the public statement's. -/
theorem bits_of_shapes (H : ShapesAre T G lo kb no) (i : Fin lo.length) (hi : i ∈ membersOf lo)
    (part : Part) : (stPub lo no).rowBits (no i) part = T.rowBits (no i) part := by
  rw [(has_of_shape (stPub_shape ⟨T, H.shape⟩ i hi) part).2, (has_of_shape (H.shape i hi) part).2]

/-- **A layout at a group that holds the list's members has the public layout's six fields.** -/
theorem sameLay_of_shapes {g : ℕ} {L : GroupLayout} (hG : T.groups[g]? = some G)
    (hL : T.layout g = some L) (H : ShapesAre T G lo kb no) :
    ∃ L₀, layPub lo kb no = some L₀ ∧ SameLay L₀ L := by
  have e1 := layout_eq T g G hG
  rw [hL] at e1
  obtain rfl := Option.some.inj e1
  unfold layPub
  rw [layout_eq (stOf lo kb) 0 (groupOf lo kb) (stOf_group lo kb)]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((membersOf lo).map no).toArray = G.members
    rw [← H.members]
  · show ((membersOf lo).map kb).toArray = G.kept
    rw [← H.kept]
  all_goals simp only [H.sizes]

/-- **THE FIELD plan**: the term for pS at the public statement and the public layout is the term
at any statement whose group holds the list's members, and its layout. -/
theorem plan_of_shapes (cs : OnBytes.Codes) (s : Sg) (e : ℕ)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    (N : SlotNames (groupLayK cs lo s e kb hM hZ)) {g : ℕ} {L L₀ : GroupLayout}
    (h0 : layPub lo kb no = some L₀) (hG : T.groups[g]? = some G) (hL : T.layout g = some L)
    (H : ShapesAre T G lo kb no)
    (as : Σ a : (groupLayK cs lo s e kb hM hZ).G.A, ((sigOf cs lo).om a.1).Z.S)
    (D : ((sigOf cs lo).om as.1.1).Z.D) :
    pSseed cs lo (groupLayK cs lo s e kb hM hZ) N (stPub lo no) L₀ no as D =
      pSseed cs lo (groupLayK cs lo s e kb hM hZ) N T L no as D := by
  obtain ⟨L₁, h1, Y⟩ := sameLay_of_shapes hG hL H
  obtain rfl : L₁ = L₀ := Option.some.inj (h1.symm.trans h0)
  exact pSseed_congr cs lo _ N no Y
    (fun a part => bits_of_shapes H a.1 (mem_members.2 a.2) part) as D

/-- The public layout is there wherever the program lays the statement made of the list. -/
theorem layPub_some (hA : LayoutAgrees lo kb) : ∃ L₀, layPub lo kb no = some L₀ := by
  unfold LayoutAgrees at hA
  unfold layPub
  cases h : (stOf lo kb).layout 0 with
  | none => rw [h] at hA; exact hA.elim
  | some L => exact ⟨_, rfl⟩

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.pSseed_congr
#print axioms VerifiableInference.Desc.First.Close.stPub_shape
#print axioms VerifiableInference.Desc.First.Close.bits_of_shapes
#print axioms VerifiableInference.Desc.First.Close.sameLay_of_shapes
#print axioms VerifiableInference.Desc.First.Close.plan_of_shapes
#print axioms VerifiableInference.Desc.First.Close.layPub_some
#print axioms VerifiableInference.Desc.First.Close.find_congr
#print axioms VerifiableInference.Desc.First.Close.mainWeight_congr
#print axioms VerifiableInference.Desc.First.Close.mainBack_congr
#print axioms VerifiableInference.Desc.First.Close.keptWeight_congr
#print axioms VerifiableInference.Desc.First.Close.maskWeight_congr
#print axioms VerifiableInference.Desc.First.Close.maskBack_congr
