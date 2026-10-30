-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/PartD.lean: what a plain part of a file's rounds is, read back along the data: a
running twin of `partOf` (OnBytes/Maker/Page/Fill.lean), and the equation of the two.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

`partOf` cuts the plain part by `splitPB`, which matches on the shape: so at every call the three
chains' shapes are built as data and walked. Here the walk goes down the plain part and the lists
`D.ds₁`, `D.ds₂`, `D.ds₃` together, with a counter: no shape is built, nothing is mapped on the way
back, every call in the walk is a tail call. What lies behind a stretch stands behind functions of
Unit, so that it is in types alone.

Main names.
  `saidAt`: what one written round's plain part says, at the place k of its stretch.
  `peelLo`, `peelSh`: down a stretch of local | shared rounds with more rounds behind it: what the
    plain part says, or the plain part of the rounds behind.
  `lastLo`: down the last stretch.
  `part3D`, `partJD`, `partOfD`: from the seam on; from the joining round on; the twin, with
    `partOf`'s own type.
  `peelLo_eq`, `peelSh_eq`, `lastLo_eq`: each walk is `splitPB`, then `saidLo` | `saidSh`.
  `partOfD_eq`: `partOfD = partOf`, at every argument. No premise.
Limits. A call walks the rounds before the one that it reads: over a chain of n rounds, each read
once, some n * n / 2 steps in all. Who builds the plain part pays for its own walk: that is not
treated here. Nothing here lays the twin into `fillJ`: a caller takes it and carries it back by
`partOfD_eq`.
Nothing is run here. Nothing on any hash. Nothing on soundness.

-/
import OnBytes.Maker.Page.Fill

set_option autoImplicit false

namespace Johnson.RunOne

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open OnBytes OnBytes.Maker OnBytes.Maker.Page

/-- What one written round's plain part says, at the place k of its stretch. -/
def saidAt (C : CK) (d : RDT) (k : ℕ) (pl : (roundT C d).Plain) : Said :=
  ⟨k, (saidOf C d pl).msg, (saidOf C d pl).nonce⟩

/-- Down a stretch of local rounds with the rounds `uf ()` behind it. k: the rounds passed. -/
def peelLo (C : CK) (uf : Unit → Shape) (Bf : (x : Unit) → RoundSplits (uf x)) :
    (ds : List RDT) → ℕ →
    PlainPart (uLT C ds ++ uf ()) (RoundSplits.app (RoundSplits.allLocal (uLT C ds)) (Bf ())) →
    Option Said ⊕ PlainPart (uf ()) (Bf ())
  | [], _, z => .inr z
  | d :: ds, k, z =>
    match (z : (Unit ⊕ (roundT C d).Plain) ⊕
        PlainPart (uLT C ds ++ uf ()) (RoundSplits.app (RoundSplits.allLocal (uLT C ds)) (Bf ()))) with
    | .inl (.inr pl) => .inl (some (saidAt C d k pl))
    | .inl (.inl _) => .inl none
    | .inr w => peelLo C uf Bf ds (k + 1) w

/-- Down a stretch of shared rounds with the rounds `uf ()` behind it. -/
def peelSh (C : CK) (uf : Unit → Shape) (Bf : (x : Unit) → RoundSplits (uf x)) :
    (ds : List RDT) → ℕ →
    PlainPart (uLT C ds ++ uf ()) (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (Bf ())) →
    Option Said ⊕ PlainPart (uf ()) (Bf ())
  | [], _, z => .inr z
  | d :: ds, k, z =>
    match (z : ((roundT C d).Plain ⊕ Unit) ⊕
        PlainPart (uLT C ds ++ uf ()) (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (Bf ()))) with
    | .inl (.inl pl) => .inl (some (saidAt C d k pl))
    | .inl (.inr _) => .inl none
    | .inr w => peelSh C uf Bf ds (k + 1) w

/-- Down the last stretch, of local rounds. -/
def lastLo (C : CK) : (ds : List RDT) → ℕ → PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds)) → Option Said
  | [], _, _ => none
  | d :: ds, k, z =>
    match (z : (Unit ⊕ (roundT C d).Plain) ⊕ PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds))) with
    | .inl (.inr pl) => some (saidAt C d k pl)
    | .inl (.inl _) => none
    | .inr w => lastLo C ds (k + 1) w

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- From the seam on. -/
def part3D (z₃ : PlainPart (chainsOf C D tF tJ t3).sh₃ (chainsOf C D tF tJ t3).ann₃) : PartJ TF TJ T3 :=
  match (z₃ : (Unit ⊕ T3) ⊕ PlainPart (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃))) with
  | .inl (.inr p) => .seam p
  | .inl (.inl _) => .nothing
  | .inr w₃ => PartJ.ofSaid (D.ds₁.length + D.ds₂.length + 2) (lastLo C D.ds₃ 0 w₃)

/-- From the joining round on. -/
def partJD (zJ : PlainPart (chainsOf C D tF tJ t3).shJ (chainsOf C D tF tJ t3).annJ) : PartJ TF TJ T3 :=
  match (zJ : (TJ ⊕ Unit) ⊕ PlainPart (uLT C D.ds₂ ++ (chainsOf C D tF tJ t3).sh₃)
      (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂)) (chainsOf C D tF tJ t3).ann₃)) with
  | .inl (.inl p) => .join p
  | .inl (.inr _) => .nothing
  | .inr w₂ =>
    Sum.elim (PartJ.ofSaid (D.ds₁.length + 1)) (part3D C D tF tJ t3)
      (peelSh C (fun _ => (chainsOf C D tF tJ t3).sh₃) (fun _ => (chainsOf C D tF tJ t3).ann₃)
        D.ds₂ 0 w₂)

/-- **What a plain part of a file's rounds is, read back along the data.** -/
def partOfD (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) : PartJ TF TJ T3 :=
  match (z : (Unit ⊕ TF) ⊕ PlainPart (uLT C D.ds₁ ++ (chainsOf C D tF tJ t3).shJ)
      (RoundSplits.app (RoundSplits.allLocal (uLT C D.ds₁)) (chainsOf C D tF tJ t3).annJ)) with
  | .inl (.inr p) => .front p
  | .inl (.inl _) => .nothing
  | .inr w =>
    Sum.elim (PartJ.ofSaid 0) (partJD C D tF tJ t3)
      (peelLo C (fun _ => (chainsOf C D tF tJ t3).shJ) (fun _ => (chainsOf C D tF tJ t3).annJ)
        D.ds₁ 0 w)

end

/-! ## The equation -/

/-- A said with its place moved on by k. -/
def addK (k : ℕ) (s : Said) : Said := ⟨k + s.k, s.msg, s.nonce⟩

/-- One place on, then k places: k + 1 places. -/
theorem addK_next (k : ℕ) (s : Said) : addK k s.next = addK (k + 1) s := by
  show (⟨k + (s.k + 1), s.msg, s.nonce⟩ : Said) = ⟨k + 1 + s.k, s.msg, s.nonce⟩
  rw [Nat.add_right_comm k 1 s.k, Nat.add_assoc]

/-- No place on: the same. -/
theorem addK_zero (s : Said) : addK 0 s = s := by
  show (⟨0 + s.k, s.msg, s.nonce⟩ : Said) = s
  rw [Nat.zero_add]

/-- `addK_next`, where there may be nothing said. -/
theorem map_addK_next (k : ℕ) (o : Option Said) :
    (o.map Said.next).map (addK k) = o.map (addK (k + 1)) := by
  cases o with
  | none => rfl
  | some s => exact congrArg some (addK_next k s)

/-- `addK_zero`, where there may be nothing said. -/
theorem map_addK_zero (o : Option Said) : o.map (addK 0) = o := by
  cases o with
  | none => rfl
  | some s => exact congrArg some (addK_zero s)

/-- The last stretch: the walk with a counter says what `saidLo` says, moved on by k. -/
theorem lastLo_eq (C : CK) : ∀ (ds : List RDT) (k : ℕ)
    (z : PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds))),
    lastLo C ds k z = (saidLo C ds z).map (addK k)
  | [], _, _ => rfl
  | d :: ds, k, z =>
    match (z : (Unit ⊕ (roundT C d).Plain) ⊕ PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds))) with
    | .inl (.inr _) => rfl
    | .inl (.inl _) => rfl
    | .inr w => by
      show lastLo C ds (k + 1) w = ((saidLo C ds w).map Said.next).map (addK k)
      rw [lastLo_eq C ds (k + 1) w, map_addK_next]

/-- A stretch of local rounds with rounds behind it: the walk is `splitPB`, then `saidLo`. -/
theorem peelLo_eq (C : CK) (uf : Unit → Shape) (Bf : (x : Unit) → RoundSplits (uf x)) :
    ∀ (ds : List RDT) (k : ℕ)
    (z : PlainPart (uLT C ds ++ uf ()) (RoundSplits.app (RoundSplits.allLocal (uLT C ds)) (Bf ()))),
    peelLo C uf Bf ds k z =
      (splitPB (s := uLT C ds) (u := uf ()) (A := RoundSplits.allLocal (uLT C ds)) (B := Bf ()) z).map
        (fun w => (saidLo C ds w).map (addK k)) id
  | [], _, _ => rfl
  | d :: ds, k, z =>
    match (z : (Unit ⊕ (roundT C d).Plain) ⊕
        PlainPart (uLT C ds ++ uf ()) (RoundSplits.app (RoundSplits.allLocal (uLT C ds)) (Bf ()))) with
    | .inl (.inr _) => rfl
    | .inl (.inl _) => rfl
    | .inr w => by
      show peelLo C uf Bf ds (k + 1) w =
        ((splitPB (s := uLT C ds) (u := uf ()) (A := RoundSplits.allLocal (uLT C ds)) (B := Bf ()) w).map
          Sum.inr id).map (fun w => (saidLo C (d :: ds) w).map (addK k)) id
      rw [peelLo_eq C uf Bf ds (k + 1) w]
      cases splitPB (s := uLT C ds) (u := uf ()) (A := RoundSplits.allLocal (uLT C ds)) (B := Bf ()) w with
      | inl w' => exact congrArg Sum.inl (map_addK_next k (saidLo C ds w')).symm
      | inr _ => rfl

/-- The same at a stretch of shared rounds. -/
theorem peelSh_eq (C : CK) (uf : Unit → Shape) (Bf : (x : Unit) → RoundSplits (uf x)) :
    ∀ (ds : List RDT) (k : ℕ)
    (z : PlainPart (uLT C ds ++ uf ()) (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (Bf ()))),
    peelSh C uf Bf ds k z =
      (splitPB (s := uLT C ds) (u := uf ()) (A := RoundSplits.const (RAnn.ofShared .sh) (uLT C ds))
        (B := Bf ()) z).map (fun w => (saidSh C ds w).map (addK k)) id
  | [], _, _ => rfl
  | d :: ds, k, z =>
    match (z : ((roundT C d).Plain ⊕ Unit) ⊕
        PlainPart (uLT C ds ++ uf ()) (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (Bf ()))) with
    | .inl (.inl _) => rfl
    | .inl (.inr _) => rfl
    | .inr w => by
      show peelSh C uf Bf ds (k + 1) w =
        ((splitPB (s := uLT C ds) (u := uf ()) (A := RoundSplits.const (RAnn.ofShared .sh) (uLT C ds))
          (B := Bf ()) w).map Sum.inr id).map (fun w => (saidSh C (d :: ds) w).map (addK k)) id
      rw [peelSh_eq C uf Bf ds (k + 1) w]
      cases splitPB (s := uLT C ds) (u := uf ()) (A := RoundSplits.const (RAnn.ofShared .sh) (uLT C ds))
          (B := Bf ()) w with
      | inl w' => exact congrArg Sum.inl (map_addK_next k (saidSh C ds w')).symm
      | inr _ => rfl

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- `partOf`'s inner match on the first chain's rounds, under a name. -/
def fst1S (z₁ : PlainPart (chainsOf C D tF tJ t3).c₁ (chainsOf C D tF tJ t3).A₁) : PartJ TF TJ T3 :=
  match (z₁ : (Unit ⊕ TF) ⊕ PlainPart (uLT C D.ds₁) (RoundSplits.allLocal (uLT C D.ds₁))) with
  | .inl (.inr p) => .front p
  | .inl (.inl _) => .nothing
  | .inr w => PartJ.ofSaid 0 (saidLo C D.ds₁ w)

/-- Its inner match on the second chain's rounds. -/
def mid2S (z₂ : PlainPart (chainsOf C D tF tJ t3).c₂ (chainsOf C D tF tJ t3).A₂) : PartJ TF TJ T3 :=
  match (z₂ : (TJ ⊕ Unit) ⊕ PlainPart (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂))) with
  | .inl (.inl p) => .join p
  | .inl (.inr _) => .nothing
  | .inr w => PartJ.ofSaid (D.ds₁.length + 1) (saidSh C D.ds₂ w)

/-- Its inner match on the third chain's rounds. -/
def tail3S (z₃ : PlainPart (chainsOf C D tF tJ t3).c₃ (chainsOf C D tF tJ t3).A₃) : PartJ TF TJ T3 :=
  match (z₃ : (Unit ⊕ T3) ⊕ PlainPart (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃))) with
  | .inl (.inr p) => .seam p
  | .inl (.inl _) => .nothing
  | .inr w => PartJ.ofSaid (D.ds₁.length + D.ds₂.length + 2) (saidLo C D.ds₃ w)

/-- `partOf`, with its two cuts laid open. -/
theorem partOf_elim (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) :
    partOf C D tF tJ t3 z =
      Sum.elim (fst1S C D tF tJ t3)
        (fun z' => Sum.elim (mid2S C D tF tJ t3) (tail3S C D tF tJ t3)
          (splitPB (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
            (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) z'))
        (splitPB (s := (chainsOf C D tF tJ t3).c₁)
          (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃)
          (A := (chainsOf C D tF tJ t3).A₁)
          (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃) z) := by
  unfold partOf
  cases splitPB (s := (chainsOf C D tF tJ t3).c₁)
      (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃)
      (A := (chainsOf C D tF tJ t3).A₁)
      (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃) z with
  | inl z₁ => rfl
  | inr z' =>
    show (match splitPB (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
        (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) z' with
      | .inl z₂ => mid2S C D tF tJ t3 z₂
      | .inr z₃ => tail3S C D tF tJ t3 z₃) =
      Sum.elim (mid2S C D tF tJ t3) (tail3S C D tF tJ t3)
        (splitPB (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
          (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) z')
    cases splitPB (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
        (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) z' with
    | inl _ => rfl
    | inr _ => rfl

/-- From the seam on, the twin is `partOf`'s last match. -/
theorem part3D_eq (z₃ : PlainPart (chainsOf C D tF tJ t3).sh₃ (chainsOf C D tF tJ t3).ann₃) :
    part3D C D tF tJ t3 z₃ = tail3S C D tF tJ t3 z₃ :=
  match (z₃ : (Unit ⊕ T3) ⊕ PlainPart (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃))) with
  | .inl (.inr _) => rfl
  | .inl (.inl _) => rfl
  | .inr w => by
    show PartJ.ofSaid _ (lastLo C D.ds₃ 0 w) = PartJ.ofSaid _ (saidLo C D.ds₃ w)
    rw [lastLo_eq, map_addK_zero]

/-- From the joining round on. -/
theorem partJD_eq (zJ : PlainPart (chainsOf C D tF tJ t3).shJ (chainsOf C D tF tJ t3).annJ) :
    partJD C D tF tJ t3 zJ =
      Sum.elim (mid2S C D tF tJ t3) (tail3S C D tF tJ t3)
        (splitPB (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
          (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) zJ) :=
  match (zJ : (TJ ⊕ Unit) ⊕ PlainPart (uLT C D.ds₂ ++ (chainsOf C D tF tJ t3).sh₃)
      (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂)) (chainsOf C D tF tJ t3).ann₃)) with
  | .inl (.inl _) => rfl
  | .inl (.inr _) => rfl
  | .inr w₂ => by
    show Sum.elim (PartJ.ofSaid (D.ds₁.length + 1)) (part3D C D tF tJ t3)
        (peelSh C (fun _ => (chainsOf C D tF tJ t3).sh₃) (fun _ => (chainsOf C D tF tJ t3).ann₃)
          D.ds₂ 0 w₂) =
      Sum.elim (mid2S C D tF tJ t3) (tail3S C D tF tJ t3)
        ((splitPB (s := uLT C D.ds₂) (u := (chainsOf C D tF tJ t3).sh₃)
          (A := RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂))
          (B := (chainsOf C D tF tJ t3).ann₃) w₂).map Sum.inr id)
    rw [peelSh_eq]
    cases splitPB (s := uLT C D.ds₂) (u := (chainsOf C D tF tJ t3).sh₃)
        (A := RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂))
        (B := (chainsOf C D tF tJ t3).ann₃) w₂ with
    | inl w' =>
      show PartJ.ofSaid _ ((saidSh C D.ds₂ w').map (addK 0)) = PartJ.ofSaid _ (saidSh C D.ds₂ w')
      rw [map_addK_zero]
    | inr z₃ => exact part3D_eq C D tF tJ t3 z₃

/-- **The twin is `partOf`**, at every plain part. No premise. -/
theorem partOfD_eq (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) :
    partOfD C D tF tJ t3 z = partOf C D tF tJ t3 z :=
  match (z : (Unit ⊕ TF) ⊕ PlainPart (uLT C D.ds₁ ++ (chainsOf C D tF tJ t3).shJ)
      (RoundSplits.app (RoundSplits.allLocal (uLT C D.ds₁)) (chainsOf C D tF tJ t3).annJ)) with
  | .inl (.inr _) => rfl
  | .inl (.inl _) => rfl
  | .inr w => by
    rw [partOf_elim]
    show Sum.elim (PartJ.ofSaid 0) (partJD C D tF tJ t3)
        (peelLo C (fun _ => (chainsOf C D tF tJ t3).shJ) (fun _ => (chainsOf C D tF tJ t3).annJ)
          D.ds₁ 0 w) =
      Sum.elim (fst1S C D tF tJ t3)
        (fun z' => Sum.elim (mid2S C D tF tJ t3) (tail3S C D tF tJ t3)
          (splitPB (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
            (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) z'))
        ((splitPB (s := uLT C D.ds₁) (u := (chainsOf C D tF tJ t3).shJ)
          (A := RoundSplits.allLocal (uLT C D.ds₁)) (B := (chainsOf C D tF tJ t3).annJ) w).map
          Sum.inr id)
    rw [peelLo_eq]
    cases splitPB (s := uLT C D.ds₁) (u := (chainsOf C D tF tJ t3).shJ)
        (A := RoundSplits.allLocal (uLT C D.ds₁)) (B := (chainsOf C D tF tJ t3).annJ) w with
    | inl w' =>
      show PartJ.ofSaid 0 ((saidLo C D.ds₁ w').map (addK 0)) = PartJ.ofSaid 0 (saidLo C D.ds₁ w')
      rw [map_addK_zero]
    | inr zJ => exact partJD_eq C D tF tJ t3 zJ

end

#print axioms Johnson.RunOne.addK_next
#print axioms Johnson.RunOne.addK_zero
#print axioms Johnson.RunOne.map_addK_next
#print axioms Johnson.RunOne.map_addK_zero
#print axioms Johnson.RunOne.lastLo_eq
#print axioms Johnson.RunOne.peelLo_eq
#print axioms Johnson.RunOne.peelSh_eq
#print axioms Johnson.RunOne.partOf_elim
#print axioms Johnson.RunOne.part3D_eq
#print axioms Johnson.RunOne.partJD_eq
#print axioms Johnson.RunOne.partOfD_eq

end Johnson.RunOne
