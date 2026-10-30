-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsTwoSpellings.lean: one family of three checks (parameters) over the value of a
public reading (a computation that queries the hash function), the two inputs that are made of it,
and: under named hypotheses, bounds on the checks of the first input give bounds on those of the
second.

What this file states. `ArmFam` holds the object, a type D, the public reading `Pub`, which returns
a value d of D, `part : D → Dig 256`, the three checks at d, and what else an input holds.
`ArmFam.asking F enc` is the input of Johnson/Top/OnFilesArms.lean: each check is "run `Pub`, then
the member at its value". `ArmFam.told F enc c₀` is the input of Johnson/Top/OnFilesArmsC.lean with
C := 256 bits: each check is "run `Pub`; no, unless `part d` is the key's c; then the member at d";
its committer runs F's, then `Pub`, and puts `part d` into the key. Both inputs have one object, one
pair of annotations, one builder. `told_liftK_det`, `told_liftE_det`, `told_liftP_det`: at every
hash function g, at the key whose c is `part (Pub.det g)`, each lifted check of `F.told` has the
value of that of `F.asking`. `told_liftK_le`, `told_liftE_le`, `told_liftP_le`: at every key and
every g it accepts no more often. `coreCD_of_coreD`: `CoreArmsD b` at `F.asking` gives `CoreArmsCD`
at `F.told`, at the remaining data `ArmFam.besideCD b`, with the same three errors; by
`ZKCP.Gen.ArmBoundD.widerKey` (Johnson/Top/ArmsWiderKey.lean). Motive (no Lean here says it): the
verifier's public digests are answers of the hash function at public strings.

Under which hypotheses. `CoreArmsD b` is a hypothesis. Two further premises: `Pub` draws no coin; no
member draws a coin. The three statements that end in `_le` take the first of these two.

What it does not show. All fields of `ArmFam` are parameters: no family is given here. The
implication goes one way. The reading b.rd of the bounds is a parameter of its own: nothing here
says that it is `Pub`; what is intended is b.rd := fun _ => `Pub`. That the committer of `F.told` is
honest in any sense is not said: completeness is not spoken of. The two codes of a key are
parameters, linked by nothing. Soundness alone.


-/
import Johnson.Top.ArmsWiderKey
import Johnson.Top.OnFilesArmsCD

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open Prob (pr)
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- One family of checks over the value of a public reading. -/
structure ArmFam where
  I : Type
  X : Type
  L : HolographicProtocol I X
  aT : RoundSplits L.offline.shape
  aL : RoundSplits L.link.shape
  /-- what the public reading gives -/
  D : Type
  /-- the public reading -/
  Pub : Rom.OComp (rom 256) D
  /-- the part of its value that stands in a key -/
  part : D → Dig 256
  /-- the key file's check at d -/
  vK : D → Dig 256 → L.Rec → OneProtocolProof 256 (batTC L aT) → Rom.OComp (rom 256) Bool
  /-- the entry file's check at d -/
  vE : D → Dig 256 → Dig 256 → L.Rec → L.Rec → OneProtocolProof 256 (batLC L aL) → Rom.OComp (rom 256) Bool
  /-- the proof file's check at d -/
  vP : D → Dig 256 → X → L.Rec → ℕ → OneProtocolProof 256 L.onlineBatch → Rom.OComp (rom 256) Bool
  build : List Token × List Token → List Token → Option X
  nextToken : I → List Token → Option Token
  ISK : Type
  commit : I → Rom.OComp (rom 256) (KeyRoot 256 L × ISK)
  prove : ISK → (l : List (X × Unit)) → Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 L aT aL) l)
  bound : ℕ
  π₀ : KeyRoot 256 L × OfflineLinkOnlineProof 256 L aT aL

variable (F : ArmFam)

/-- The input whose checks query: run the reading, then the member at its value. -/
def ArmFam.asking (enc : KeyRoot 256 F.L → Option ZKCP.Str) : InputArms where
  I := F.I
  X := F.X
  L := F.L
  aT := F.aT
  aL := F.aL
  armK := fun cm rc p => F.Pub.bind fun d => F.vK d cm rc p
  armE := fun cm cm' rc rc' p => F.Pub.bind fun d => F.vE d cm cm' rc rc' p
  armP := fun cm x rc n p => F.Pub.bind fun d => F.vP d cm x rc n p
  enc := enc
  build := F.build
  nextToken := F.nextToken
  ISK := F.ISK
  commit := F.commit
  prove := F.prove
  bound := F.bound
  π₀ := F.π₀

/-- The input whose key is told a part: run the reading; no, unless the part of its value that
stands in a key is the key's c; then the member at the whole value. -/
def ArmFam.told (enc : Dig 256 × KeyRoot 256 F.L → Option ZKCP.Str) (c₀ : Dig 256) :
    InputArmsC where
  I := F.I
  X := F.X
  L := F.L
  aT := F.aT
  aL := F.aL
  C := Dig 256
  armK := fun c cm rc p => F.Pub.bind fun d =>
    if F.part d = c then F.vK d cm rc p else .pure false
  armE := fun c cm cm' rc rc' p => F.Pub.bind fun d =>
    if F.part d = c then F.vE d cm cm' rc rc' p else .pure false
  armP := fun c cm x rc n p => F.Pub.bind fun d =>
    if F.part d = c then F.vP d cm x rc n p else .pure false
  enc := enc
  build := F.build
  nextToken := F.nextToken
  ISK := F.ISK
  commit := fun i => (F.commit i).bind fun o => F.Pub.bind fun d => .pure ((F.part d, o.1), o.2)
  prove := F.prove
  bound := F.bound
  π₀ := ((c₀, F.π₀.1), F.π₀.2)

variable {F} (encA : KeyRoot 256 F.L → Option ZKCP.Str)
  (encT : Dig 256 × KeyRoot 256 F.L → Option ZKCP.Str) (c₀ : Dig 256)

/-- Behind one reading without coins: "no, unless the part is c; then A d" accepts no more often
than "A d". -/
theorem pr_told_le (hn : F.Pub.NoCoin) (A : F.D → Rom.OComp (rom 256) Bool) (c : Dig 256)
    (f : Fam (rom 256)) :
    pr ((F.Pub.bind fun d => if F.part d = c then A d else .pure false).runEager f)
        {b | b = true} ≤ pr ((F.Pub.bind A).runEager f) {b | b = true} :=
  ZKCP.Gen.toldPart_le hn F.part (fun d (_ : Unit) (_ : Unit) (_ : Unit) => A d) f (c, ()) () ()

/-- At c := the part of the reading's value the two have one value. -/
theorem det_told (A : F.D → Rom.OComp (rom 256) Bool) (g : Fam (rom 256)) :
    (F.Pub.bind fun d => if F.part d = F.part (F.Pub.det g) then A d else .pure false).det g =
      (F.Pub.bind A).det g :=
  ZKCP.Gen.toldPart_det F.Pub F.part (fun d (_ : Unit) (_ : Unit) (_ : Unit) => A d) g () () ()

theorem told_liftK_le (hn : F.Pub.NoCoin) (f : Fam (rom 256))
    (ck : Dig 256 × KeyRoot 256 F.L) (x : F.X) (π : OfflineLinkOnlineProof 256 F.L F.aT F.aL) :
    pr ((liftKC (F.told encT c₀) ck x π).runEager f) {b | b = true} ≤
      pr ((liftK (F.asking encA) ck.2 x π).runEager f) {b | b = true} := by
  unfold liftKC liftK
  cases π.piT with
  | none => exact le_refl _
  | some p => exact pr_told_le hn _ _ f

theorem told_liftE_le (hn : F.Pub.NoCoin) (f : Fam (rom 256))
    (ck : Dig 256 × KeyRoot 256 F.L) (x : F.X) (π : OfflineLinkOnlineProof 256 F.L F.aT F.aL) :
    pr ((liftEC (F.told encT c₀) ck x π).runEager f) {b | b = true} ≤
      pr ((liftE (F.asking encA) ck.2 x π).runEager f) {b | b = true} := by
  unfold liftEC liftE
  cases π.link.2.2 with
  | none => exact le_refl _
  | some p => exact pr_told_le hn _ _ f

theorem told_liftP_le (hn : F.Pub.NoCoin) (f : Fam (rom 256))
    (ck : Dig 256 × KeyRoot 256 F.L) (x : F.X) (π : OfflineLinkOnlineProof 256 F.L F.aT F.aL) :
    pr ((liftPC (F.told encT c₀) ck x π).runEager f) {b | b = true} ≤
      pr ((liftP (F.asking encA) ck.2 x π).runEager f) {b | b = true} := by
  unfold liftPC liftP
  cases π.piB with
  | none => exact le_refl _
  | some p => exact pr_told_le hn _ _ f

/-- At every hash function, at the key whose c is the part of the reading's value there, the told
input's lifted check for the key file has the asking input's value. -/
theorem told_liftK_det (g : Fam (rom 256)) (k : KeyRoot 256 F.L) (x : F.X)
    (π : OfflineLinkOnlineProof 256 F.L F.aT F.aL) :
    (liftKC (F.told encT c₀) (F.part (F.Pub.det g), k) x π).det g =
      (liftK (F.asking encA) k x π).det g := by
  unfold liftKC liftK
  cases π.piT with
  | none => rfl
  | some p => exact det_told _ g

/-- The same for the entry file. -/
theorem told_liftE_det (g : Fam (rom 256)) (k : KeyRoot 256 F.L) (x : F.X)
    (π : OfflineLinkOnlineProof 256 F.L F.aT F.aL) :
    (liftEC (F.told encT c₀) (F.part (F.Pub.det g), k) x π).det g =
      (liftE (F.asking encA) k x π).det g := by
  unfold liftEC liftE
  cases π.link.2.2 with
  | none => rfl
  | some p => exact det_told _ g

/-- The same for the proof file. -/
theorem told_liftP_det (g : Fam (rom 256)) (k : KeyRoot 256 F.L) (x : F.X)
    (π : OfflineLinkOnlineProof 256 F.L F.aT F.aL) :
    (liftPC (F.told encT c₀) (F.part (F.Pub.det g), k) x π).det g =
      (liftP (F.asking encA) k x π).det g := by
  unfold liftPC liftP
  cases π.piB with
  | none => rfl
  | some p => exact det_told _ g

/-- What the theorems need beside the told input, made of what they need beside the asking input. -/
def ArmFam.besideCD (b : BesideArmsD (F.asking encA)) : BesideArmsCD (F.told encT c₀) where
  D := b.D
  rd := fun ck => b.rd ck.2
  q₀ := b.q₀
  wordOf := b.wordOf
  Wn := b.Wn
  Rno := b.Rno
  εK := b.εK
  εE := b.εE
  εP := b.εP
  x₀ := b.x₀

/-- No member of the family draws a coin. -/
def ArmFam.NoCoin (F : ArmFam) : Prop :=
  (∀ d cm rc p, (F.vK d cm rc p).NoCoin) ∧ (∀ d cm cm' rc rc' p, (F.vE d cm cm' rc rc' p).NoCoin) ∧
    ∀ d cm x rc n p, (F.vP d cm x rc n p).NoCoin

/-- **The five named hypotheses cross from the asking input to the told input**, with the same three
errors. -/
theorem coreCD_of_coreD (hn : F.Pub.NoCoin) (hv : F.NoCoin) {b : BesideArmsD (F.asking encA)}
    (h : CoreArmsD b) : CoreArmsCD (ArmFam.besideCD encA encT c₀ b) where
  keyArm := ZKCP.Gen.ArmBoundD.widerKey (fun k => (h.reading k).1) (told_liftK_le encA encT c₀ hn)
    h.keyArm
  entryArm := ZKCP.Gen.ArmBoundD.widerKey (fun k => (h.reading k).1) (told_liftE_le encA encT c₀ hn)
    h.entryArm
  proofArm := ZKCP.Gen.ArmBoundD.widerKey (fun k => (h.reading k).1) (told_liftP_le encA encT c₀ hn)
    h.proofArm
  reading := fun k => h.reading k.2
  noCoin := by
    obtain ⟨a1, a2, a3⟩ := hv
    refine ⟨fun c cm rc p => hn.bind fun d => ?_, fun c cm cm' rc rc' p => hn.bind fun d => ?_,
      fun c cm x rc n p => hn.bind fun d => ?_⟩
    · by_cases e : F.part d = c
      · rw [if_pos e]
        exact a1 _ _ _ _
      · rw [if_neg e]
        trivial
    · by_cases e : F.part d = c
      · rw [if_pos e]
        exact a2 _ _ _ _ _ _
      · rw [if_neg e]
        trivial
    · by_cases e : F.part d = c
      · rw [if_pos e]
        exact a3 _ _ _ _ _ _
      · rw [if_neg e]
        trivial

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.told_liftE_det
#print axioms VerifiableInference.OnPublicFiles.told_liftE_le
#print axioms VerifiableInference.OnPublicFiles.coreCD_of_coreD
