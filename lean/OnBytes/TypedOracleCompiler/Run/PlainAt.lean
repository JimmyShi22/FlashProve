-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlainAt.lean: plain parts of the protocol in three stretches, by the typed round:
how a stretch's round's message and a seam's plain part stand in the one type of plain parts of the
whole shape, with partial codes and ways in and out.

A chain query of the sibling (a second form of the library's soundness road, under
OnBytes/TypedOracleCompiler/) holds a plain part of the type `PlainPart s A`, a sum over all rounds of the shape s. The
shape of `Stretches` (OnBytes/TypedOracleCompiler/Slice/Plain3.lean) is a seam, the first stretch's rounds, two
seams, the second stretch's, a seam, the third's. The sibling's code of a round's message, `PQ.rcL`
(OnBytes/TypedOracleCompiler/Run/PageQChain.lean), is over the plain parts of one list of written rounds alone. A
page for the whole shape needs the like over `PlainPart G.sh`, and for each seam a way to put its plain
part in and to read it out.
 - `rcApp C t rt ds i`: the code of (roots, plain part) at round i of `PQ.uL C ds ++ t`: within ds
   the round's own message (`PQ.pRound`), behind ds what `rt` gives at the rounds of t; `rcApp_ge`:
   its strings have at least 64 bits if rt's have;
 - `appIn`, `appOut`, with both laws: a plain part of t as one of `PQ.uL C ds ++ t`, and back;
 - `rc₃`, `rc₂`, `rcG G i`: the code at the typed round i of G.sh: a stretch's round's message;
   NOTHING at the four seams; `rcG_ge`;
 - `in0` .. `in3`, `out0` .. `out3`, with both laws each: a seam's plain part as a plain part of
   G.sh, and back;
 - `n₁`, `n₂`: the stretches' lengths; `at1`, `at2`, `at3`: the typed rounds of the seams s1, s2,
   s3.

Main definitions: `rcApp`, `appIn`, `appOut`, `rcG`, `in0`, `in1`, `in2`, `in3`, `out0`, `out1`,
`out2`, `out3`.
Main theorems: `rcApp_ge`, `rcG_ge`, `appOut_appIn`, `appIn_appOut`, and the two laws of each seam.

Not claimed. Codes and maps alone: no page, no string of the format. That `rcG G i` writes the
message of the round that a chain asks at the typed round i is by its definition's recursion and is
stated in no theorem here. Nothing ties G to a key file. Nothing on soundness.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageQChain
import OnBytes.TypedOracleCompiler.Slice.Plain3

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PlainAt
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- The plain parts of a shape all of whose rounds are local. -/
abbrev PBa (s : Shape) : Type := PlainPart s (RoundSplits.allLocal s)

/-! ## Written rounds before a shape -/

section
variable (C : PQ.CK) (t : Shape)

/-- The code of (roots, plain part) at round i of written rounds ds before a shape t: within ds the
round's own message; behind ds what rt gives, counted from t's first round. -/
def rcApp (rt : ℕ → PCode (List (Dig 256) × PBa t)) :
    (ds : List PQ.RD) → ℕ → PCode (List (Dig 256) × PBa (PQ.uL C ds ++ t))
  | [], i => rt i
  | d :: _, 0 => inL (inR (PQ.pRound d.entry.work d.items))
  | _ :: ds, i + 1 => inR (rcApp rt ds i)

/-- Its strings have at least 64 bits, if rt's have. -/
theorem rcApp_ge (rt : ℕ → PCode (List (Dig 256) × PBa t))
    (h : ∀ i y s, (rt i).put y = some s → 64 ≤ s.length) :
    ∀ (ds : List PQ.RD) (i : ℕ) (y : List (Dig 256) × PBa (PQ.uL C ds ++ t)) (s : List Bool),
      (rcApp C t rt ds i).put y = some s → 64 ≤ s.length
  | [], i, y, s, hs => h i y s hs
  | d :: _, 0, y, s, hs => by
      obtain ⟨y1, h1⟩ := inL_put _ y s hs
      obtain ⟨y2, h2⟩ := inR_put _ y1 s h1
      rw [PQ.pRound_len d.entry.work d.items y2 s h2]
      omega
  | _ :: ds, i + 1, y, s, hs => by
      obtain ⟨y1, h1⟩ := inR_put _ y s hs
      exact rcApp_ge rt h ds i y1 s h1

/-- A plain part of t as a plain part of written rounds before t. -/
def appIn : (ds : List PQ.RD) → PBa t → PBa (PQ.uL C ds ++ t)
  | [], z => z
  | _ :: ds, z => .inr (appIn ds z)

/-- And back: nothing at a plain part of one of the written rounds. -/
def appOut : (ds : List PQ.RD) → PBa (PQ.uL C ds ++ t) → Option (PBa t)
  | [], z => some z
  | _ :: _, .inl _ => none
  | _ :: ds, .inr z => appOut ds z

/-- The way back undoes the way in. -/
theorem appOut_appIn : ∀ (ds : List PQ.RD) (z : PBa t), appOut C t ds (appIn C t ds z) = some z
  | [], _ => rfl
  | _ :: ds, z => appOut_appIn ds z

/-- The way in undoes the way back. -/
theorem appIn_appOut : ∀ (ds : List PQ.RD) (y : PBa (PQ.uL C ds ++ t)) (z : PBa t),
    appOut C t ds y = some z → appIn C t ds z = y
  | [], y, z, h => (Option.some.inj h).symm
  | _ :: _, .inl _, _, h => by cases h
  | _ :: ds, .inr y, z, h => congrArg Sum.inr (appIn_appOut ds y z h)

end

/-! ## The three stretches -/

variable (G : Stretches)

/-- The first stretch's number of rounds. -/
def n₁ : ℕ := G.ds₁.length

/-- The second stretch's number of rounds. -/
def n₂ : ℕ := G.ds₂.length

/-- The typed round of the seam s1. -/
def at1 : ℕ := n₁ G + 1

/-- The typed round of the seam s2. -/
def at2 : ℕ := n₁ G + 2

/-- The typed round of the seam s3. -/
def at3 : ℕ := n₁ G + n₂ G + 3

/-- The code at the rounds from the seam s3 on: nothing at the seam; then the third stretch's. -/
def rc₃ : ℕ → PCode (List (Dig 256) × PBa G.sh₃)
  | 0 => PCode.empty _
  | i + 1 => inR (PQ.rcL G.C G.ds₃ i)

/-- The code at the rounds from the seam s1 on: nothing at the two seams; the second stretch's;
then `rc₃`. -/
def rc₂ : ℕ → PCode (List (Dig 256) × PBa G.sh₂)
  | 0 => PCode.empty _
  | 1 => PCode.empty _
  | i + 2 => inR (inR (rcApp G.C G.sh₃ (rc₃ G) G.ds₂ i))

/-- The code of (roots, plain part) at the typed round i of the whole shape: a stretch's round's
own message; nothing at the four seams. -/
def rcG : ℕ → PCode (List (Dig 256) × PBa G.sh)
  | 0 => PCode.empty _
  | i + 1 => inR (rcApp G.C G.sh₂ (rc₂ G) G.ds₁ i)

/-- `rc₃`'s strings have at least 64 bits. -/
theorem rc₃_ge : ∀ (i : ℕ) (y : List (Dig 256) × PBa G.sh₃) (s : List Bool),
    (rc₃ G i).put y = some s → 64 ≤ s.length
  | 0, _, _, h => by cases h
  | i + 1, y, s, h => by
      obtain ⟨y1, h1⟩ := inR_put _ y s h
      exact PQ.rcL_ge G.C G.ds₃ i y1 s h1

/-- `rc₂`'s strings have at least 64 bits. -/
theorem rc₂_ge : ∀ (i : ℕ) (y : List (Dig 256) × PBa G.sh₂) (s : List Bool),
    (rc₂ G i).put y = some s → 64 ≤ s.length
  | 0, _, _, h => by cases h
  | 1, _, _, h => by cases h
  | i + 2, y, s, h => by
      obtain ⟨y1, h1⟩ := inR_put _ y s h
      obtain ⟨y2, h2⟩ := inR_put _ y1 s h1
      exact rcApp_ge G.C G.sh₃ (rc₃ G) (rc₃_ge G) G.ds₂ i y2 s h2

/-- `rcG`'s strings have at least 64 bits: what the data of a chain's code ask. -/
theorem rcG_ge : ∀ (i : ℕ) (y : List (Dig 256) × PBa G.sh) (s : List Bool),
    (rcG G i).put y = some s → 64 ≤ s.length
  | 0, _, _, h => by cases h
  | i + 1, y, s, h => by
      obtain ⟨y1, h1⟩ := inR_put _ y s h
      exact rcApp_ge G.C G.sh₂ (rc₂ G) (rc₂_ge G) G.ds₁ i y1 s h1

/-! ## The seams' plain parts -/

/-- The seam s0's plain part as a plain part of the whole shape. -/
def in0 (z : G.s0.r.Plain) : PBa G.sh := .inl (.inr z)

/-- And back. -/
def out0 : PBa G.sh → Option G.s0.r.Plain
  | .inl (.inr z) => some z
  | _ => none

/-- The seam s1's plain part as a plain part of the whole shape. -/
def in1 (z : G.s1.r.Plain) : PBa G.sh := .inr (appIn G.C G.sh₂ G.ds₁ (.inl (.inr z)))

/-- And back. -/
def out1 : PBa G.sh → Option G.s1.r.Plain
  | .inr y =>
      match appOut G.C G.sh₂ G.ds₁ y with
      | some (.inl (.inr z)) => some z
      | _ => none
  | _ => none

/-- The seam s2's plain part as a plain part of the whole shape. -/
def in2 (z : G.s2.r.Plain) : PBa G.sh := .inr (appIn G.C G.sh₂ G.ds₁ (.inr (.inl (.inr z))))

/-- And back. -/
def out2 : PBa G.sh → Option G.s2.r.Plain
  | .inr y =>
      match appOut G.C G.sh₂ G.ds₁ y with
      | some (.inr (.inl (.inr z))) => some z
      | _ => none
  | _ => none

/-- The seam s3's plain part as a plain part of the whole shape. -/
def in3 (z : G.s3.r.Plain) : PBa G.sh :=
  .inr (appIn G.C G.sh₂ G.ds₁ (.inr (.inr (appIn G.C G.sh₃ G.ds₂ (.inl (.inr z))))))

/-- And back. -/
def out3 : PBa G.sh → Option G.s3.r.Plain
  | .inr y =>
      match appOut G.C G.sh₂ G.ds₁ y with
      | some (.inr (.inr y2)) =>
          match appOut G.C G.sh₃ G.ds₂ y2 with
          | some (.inl (.inr z)) => some z
          | _ => none
      | _ => none
  | _ => none

/-- The way back undoes the way in, at s0. -/
theorem out0_in0 (z : G.s0.r.Plain) : out0 G (in0 G z) = some z := rfl

/-- The way in undoes the way back, at s0. -/
theorem in0_out0 (y : PBa G.sh) (z : G.s0.r.Plain) (h : out0 G y = some z) : in0 G z = y := by
  rcases y with (y | y) | y
  · cases h
  · exact congrArg (fun w => Sum.inl (Sum.inr w)) (Option.some.inj h).symm
  · cases h

/-- The way back undoes the way in, at s1. -/
theorem out1_in1 (z : G.s1.r.Plain) : out1 G (in1 G z) = some z := by
  show (match appOut G.C G.sh₂ G.ds₁ (appIn G.C G.sh₂ G.ds₁ (.inl (.inr z))) with
    | some (.inl (.inr z)) => some z
    | _ => none) = some z
  rw [appOut_appIn]

/-- The way in undoes the way back, at s1. -/
theorem in1_out1 (y : PBa G.sh) (z : G.s1.r.Plain) (h : out1 G y = some z) : in1 G z = y := by
  rcases y with y | y
  · cases h
  · have h' : (match appOut G.C G.sh₂ G.ds₁ y with
      | some (.inl (.inr z)) => some z
      | _ => none) = some z := h
    cases ha : appOut G.C G.sh₂ G.ds₁ y with
    | none => rw [ha] at h'; cases h'
    | some w =>
      rw [ha] at h'
      rcases w with (w | w) | w
      · cases h'
      · obtain rfl := Option.some.inj h'
        exact congrArg Sum.inr (appIn_appOut G.C G.sh₂ G.ds₁ y _ ha)
      · cases h'

/-- The way back undoes the way in, at s2. -/
theorem out2_in2 (z : G.s2.r.Plain) : out2 G (in2 G z) = some z := by
  show (match appOut G.C G.sh₂ G.ds₁ (appIn G.C G.sh₂ G.ds₁ (.inr (.inl (.inr z)))) with
    | some (.inr (.inl (.inr z))) => some z
    | _ => none) = some z
  rw [appOut_appIn]

/-- The way in undoes the way back, at s2. -/
theorem in2_out2 (y : PBa G.sh) (z : G.s2.r.Plain) (h : out2 G y = some z) : in2 G z = y := by
  rcases y with y | y
  · cases h
  · have h' : (match appOut G.C G.sh₂ G.ds₁ y with
      | some (.inr (.inl (.inr z))) => some z
      | _ => none) = some z := h
    cases ha : appOut G.C G.sh₂ G.ds₁ y with
    | none => rw [ha] at h'; cases h'
    | some w =>
      rw [ha] at h'
      rcases w with w | (w | w) | w
      · cases h'
      · cases h'
      · obtain rfl := Option.some.inj h'
        exact congrArg Sum.inr (appIn_appOut G.C G.sh₂ G.ds₁ y _ ha)
      · cases h'

/-- The way back undoes the way in, at s3. -/
theorem out3_in3 (z : G.s3.r.Plain) : out3 G (in3 G z) = some z := by
  show (match appOut G.C G.sh₂ G.ds₁ (appIn G.C G.sh₂ G.ds₁
      (.inr (.inr (appIn G.C G.sh₃ G.ds₂ (.inl (.inr z)))))) with
    | some (.inr (.inr y2)) =>
        match appOut G.C G.sh₃ G.ds₂ y2 with
        | some (.inl (.inr z)) => some z
        | _ => none
    | _ => none) = some z
  rw [appOut_appIn]
  show (match appOut G.C G.sh₃ G.ds₂ (appIn G.C G.sh₃ G.ds₂ (.inl (.inr z))) with
    | some (.inl (.inr z)) => some z
    | _ => none) = some z
  rw [appOut_appIn]

/-- The way in undoes the way back, at s3. -/
theorem in3_out3 (y : PBa G.sh) (z : G.s3.r.Plain) (h : out3 G y = some z) : in3 G z = y := by
  rcases y with y | y
  · cases h
  · have h' : (match appOut G.C G.sh₂ G.ds₁ y with
      | some (.inr (.inr y2)) =>
          match appOut G.C G.sh₃ G.ds₂ y2 with
          | some (.inl (.inr z)) => some z
          | _ => none
      | _ => none) = some z := h
    cases ha : appOut G.C G.sh₂ G.ds₁ y with
    | none => rw [ha] at h'; cases h'
    | some w =>
      rw [ha] at h'
      rcases w with w | w | w
      · cases h'
      · cases h'
      · have h2 : (match appOut G.C G.sh₃ G.ds₂ w with
          | some (.inl (.inr z)) => some z
          | _ => none) = some z := h'
        cases hb : appOut G.C G.sh₃ G.ds₂ w with
        | none => rw [hb] at h2; cases h2
        | some v =>
          rw [hb] at h2
          rcases v with (v | v) | v
          · cases h2
          · obtain rfl := Option.some.inj h2
            have e2 := appIn_appOut G.C G.sh₃ G.ds₂ w _ hb
            have e1 := appIn_appOut G.C G.sh₂ G.ds₁ y _ ha
            exact congrArg Sum.inr
              ((congrArg (fun u => appIn G.C G.sh₂ G.ds₁ (.inr (.inr u))) e2).trans e1)
          · cases h2

end TypedOracleCompiler.Run.PlainAt
