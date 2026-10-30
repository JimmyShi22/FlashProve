-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Fill.lean: the data of a file's page (OnBytes/Maker/Page/Frame.lean, `FileJ`) at
the rounds of a whole file (OnBytes/Maker/Whole.lean, `chainsOf`). Definitions alone.

A typed chain query holds the plain part of one component of one round, as a point of the plain
parts of the interface's protocol. The format hashes a message's bytes. Here the way back is laid:
from a plain part of the file's own rounds to what it says (`splitPB`, `saidLo`, `saidSh`,
`partOf`), and, through a read-back `rd` from the interface's plain parts to the file's, to the data
(`fillJ`).

  `splitPB`: a plain part of the rounds of `s ++ u` is one of `s` or one of `u`.
  `Said`: what the plain part of a written round says: the round's place in its stretch, the
    message's bytes as a function of the roots, the nonce.
  `saidLo`, `saidSh`: at a stretch of local rounds, and of shared rounds.
  `PartJ`, `partOf`: what a plain part of a file's rounds is: the front round's, the joining round's
    or the seam's message, or a written round's, with its typed round.
  `rdAt`, `kindAt`, `workAt`: a written round's data, its kind's number and its bits of work, by the
    typed round.
  `SilentJ`: the labels, the digests, and how the three statements' bytes and the two later run
    values are read off the three silent rounds' messages.
  `fillJ`: the data.

What is not claimed. That `rd` reads back what the verifier's embedding writes: no law is stated
here. Where `rd` says nothing, or the plain part is not of the round that the query names, or is the
half of a round's pair that sends nothing: the message and the three statements are empty, the two
run values are the empty string, the nonce is 0. `kindAt` and `workAt` are 0 where no written round
stands. A message takes its roots in their order: a root that is missing writes nothing, roots
beyond the round's items are dropped (`bytesL`). No test is laid here:
OnBytes/Maker/Page/FitAt.lean.


-/
import OnBytes.Maker.Page.Frame
import OnBytes.Maker.Whole
import OnBytes.TypedOracleCompiler.Run.PlanQSpell

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run _root_.Run.PQ _root_.Compile.Joined

/-- A plain part of the rounds of s ++ u is one of s or one of u. -/
def splitPB : {s u : Shape} → {A : RoundSplits s} → {B : RoundSplits u} → PlainPart (s ++ u) (RoundSplits.app A B) →
    PlainPart s A ⊕ PlainPart u B
  | [], _, _, _, z => .inr z
  | _ :: _, _, (_, _), _, .inl z => .inl (.inl z)
  | _ :: _, _, (_, _), _, .inr z => (splitPB z).map .inr id

/-- What the plain part of a written round says. -/
structure Said where
  /-- the round's place in its stretch, from 0 -/
  k : ℕ
  /-- the message's bytes, from the roots -/
  msg : List ByteArray → ByteArray
  nonce : ℕ

def Said.next (s : Said) : Said := ⟨s.k + 1, s.msg, s.nonce⟩

/-- What one written round's plain part says. -/
def saidOf (C : CK) (d : RDT) (pl : (roundT C d).Plain) : Said :=
  ⟨0, fun rts => TypedOracleCompiler.Run.PQ.bytesL rts d.items (GPlain.old (b := d.entry.work) pl),
    GPlain.nonce (b := d.entry.work) pl⟩

/-- At a stretch of local rounds. -/
def saidLo (C : CK) : (ds : List RDT) → PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds)) → Option Said
  | [], _ => none
  | d :: ds, z =>
    match (z : (Unit ⊕ (roundT C d).Plain) ⊕ PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds))) with
    | .inl (.inr pl) => some (saidOf C d pl)
    | .inl (.inl _) => none
    | .inr w => (saidLo C ds w).map Said.next

/-- At a stretch of shared rounds. -/
def saidSh (C : CK) : (ds : List RDT) →
    PlainPart (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) → Option Said
  | [], _ => none
  | d :: ds, z =>
    match (z : ((roundT C d).Plain ⊕ Unit) ⊕
        PlainPart (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds))) with
    | .inl (.inl pl) => some (saidOf C d pl)
    | .inl (.inr _) => none
    | .inr w => (saidSh C ds w).map Said.next

/-- What a plain part of a file's rounds is. -/
inductive PartJ (TF TJ T3 : Type)
  | front (p : TF)
  | join (p : TJ)
  | seam (p : T3)
  /-- a written round's: the typed round, the message's bytes from the roots, the nonce -/
  | row (i : ℕ) (msg : List ByteArray → ByteArray) (nonce : ℕ)
  | nothing

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- A written round's part, from what it says and the typed round before its stretch. -/
def PartJ.ofSaid (a : ℕ) : Option Said → PartJ TF TJ T3
  | some s => .row (a + 1 + s.k) s.msg s.nonce
  | none => .nothing

/-- **What a plain part of a file's rounds is.** -/
def partOf (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) : PartJ TF TJ T3 :=
  match splitPB (s := (chainsOf C D tF tJ t3).c₁)
      (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃)
      (A := (chainsOf C D tF tJ t3).A₁)
      (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃) z with
  | .inl z₁ =>
    match (z₁ : (Unit ⊕ TF) ⊕ PlainPart (uLT C D.ds₁) (RoundSplits.allLocal (uLT C D.ds₁))) with
    | .inl (.inr p) => .front p
    | .inl (.inl _) => .nothing
    | .inr w => PartJ.ofSaid 0 (saidLo C D.ds₁ w)
  | .inr z' =>
    match splitPB (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
        (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) z' with
    | .inl z₂ =>
      match (z₂ : (TJ ⊕ Unit) ⊕
          PlainPart (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂))) with
      | .inl (.inl p) => .join p
      | .inl (.inr _) => .nothing
      | .inr w => PartJ.ofSaid (D.ds₁.length + 1) (saidSh C D.ds₂ w)
    | .inr z₃ =>
      match (z₃ : (Unit ⊕ T3) ⊕ PlainPart (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃))) with
      | .inl (.inr p) => .seam p
      | .inl (.inl _) => .nothing
      | .inr w => PartJ.ofSaid (D.ds₁.length + D.ds₂.length + 2) (saidLo C D.ds₃ w)

end

/-- A written round's data, by the typed round. -/
def rdAt (D : WholeD) (i : ℕ) : Option RDT :=
  if i = 0 then none
  else if i ≤ D.ds₁.length then D.ds₁[i - 1]?
  else if i = D.ds₁.length + 1 then none
  else if i ≤ D.ds₁.length + 1 + D.ds₂.length then D.ds₂[i - (D.ds₁.length + 2)]?
  else if i = D.ds₁.length + D.ds₂.length + 2 then none
  else D.ds₃[i - (D.ds₁.length + D.ds₂.length + 3)]?

/-- The kind's number, by the typed round; 0 where no written round stands. -/
def kindAt (D : WholeD) (i : ℕ) : ℕ := ((rdAt D i).map (·.kind.num)).getD 0

/-- The bits of work, by the typed round. -/
def workAt (D : WholeD) (i : ℕ) : ℕ := ((rdAt D i).map (·.entry.work)).getD 0

/-- **The labels, the digests, and how the statements' bytes and the later run values are read off
the three silent rounds' messages.** -/
structure SilentJ (X TF TJ T3 : Type) where
  lab₁ : ℕ
  lab₂ : ℕ
  lab₃ : ℕ
  pd₁ : ByteArray
  pd₂ : ByteArray
  pd₃ : ByteArray
  /-- from the outer roots, the instance and the front round's message -/
  stm₁ : List (Dig 256) → Option X → TF → ByteArray
  /-- from the outer roots, the request root and the joining round's message -/
  stm₂ : List (Dig 256) → Bits → TJ → ByteArray
  run₂ : TJ → Bits
  /-- from the second chain's seal, the first chain's seal and the seam's message -/
  stm₃ : Bits → Bits → T3 → ByteArray
  run₃ : T3 → Bits

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF)
  (tJ : TJ) (t3 : T3)
  (rd : PBt L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))

/-- What a plain part of the interface's protocol is, through the read-back. -/
def partAt (z : PBt L t) : PartJ TF TJ T3 :=
  match rd z with
  | some w => partOf C D tF tJ t3 w
  | none => .nothing

/-- **The data of a file's page, at the rounds of a whole file.** -/
def fillJ (S : SilentJ X TF TJ T3) : FileJ L t where
  lab₁ := S.lab₁
  lab₂ := S.lab₂
  lab₃ := S.lab₃
  pd₁ := S.pd₁
  pd₂ := S.pd₂
  pd₃ := S.pd₃
  n₁ := D.ds₁.length
  n₂ := D.ds₂.length
  n₃ := D.ds₃.length
  kind := kindAt D
  work := workAt D
  msg := fun i rts z =>
    match partAt C D tF tJ t3 rd z with
    | .row i' m _ => if i' = i then m rts else ByteArray.empty
    | _ => ByteArray.empty
  nonce := fun i z =>
    match partAt C D tF tJ t3 rd z with
    | .row i' _ n => if i' = i then n else 0
    | _ => 0
  stm₁ := fun cms x z =>
    match partAt C D tF tJ t3 rd z with
    | .front p => S.stm₁ cms x p
    | _ => ByteArray.empty
  stm₂ := fun cms r z =>
    match partAt C D tF tJ t3 rd z with
    | .join p => S.stm₂ cms r p
    | _ => ByteArray.empty
  run₂ := fun z =>
    match partAt C D tF tJ t3 rd z with
    | .join p => S.run₂ p
    | _ => []
  stm₃ := fun ρ0 c z =>
    match partAt C D tF tJ t3 rd z with
    | .seam p => S.stm₃ ρ0 c p
    | _ => ByteArray.empty
  run₃ := fun z =>
    match partAt C D tF tJ t3 rd z with
    | .seam p => S.run₃ p
    | _ => []

end

end OnBytes.Maker.Page
