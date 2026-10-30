-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/ArmsToldTests.lean: at the input `F.told`, whose typed key holds a part of the value
of a public reading (a computation that queries the hash function), each of the three checks tests
that part by its own text; so, under named hypotheses, bounds on the three checks of the other
input, `F.asking`, give soundness of `F.told`'s system for an extractor that reads the commitment
and the committer's log alone.

What this file states. Johnson/Top/ArmsTwoSpellings.lean has a family F of checks over the value d
of a public reading `F.Pub`, and two inputs made of it: `F.asking`, whose checks are "run `F.Pub`,
then the member at d", and `F.told`, whose checks are "run `F.Pub`; no, unless `F.part d` is the
key's c; then the member at d". Johnson/TypedOracleCompiler/Top/ArmsPlainOfD.lean passes from the checks' bounds
with the reading b'.rd run in the experiment (`CoreArmsCD`) to the bounds in the plain shape
(`CoreArmsC`) under two named hypotheses: `WordReadsPart`: the word under a root depends on the
reading's value through its part in the key alone; `ArmsTestC`: each check says yes only where the
part of the reading's value is the key's c. `ArmsTestC` is shown of no check there. Here:
`armsTestC_told`: `ArmsTestC` at `F.told encT c₀`, for all remaining data b' and every part whose
value at what b'.rd gives is `F.part` of what `F.Pub` gives, at every key and f (hrd). At b'.rd :=
fun _ => `F.Pub` and part := `F.part`, hrd holds by definition. `coreC_of_coreD_told`: `CoreArmsD b`
at `F.asking encA`, hrd and `WordReadsPart` give `CoreArmsC` at `F.told encT c₀`, at the same three
errors. `sound_told`, `sound_told_own`: `SoundForWith` of `systemArmsC (F.told encT c₀)` for the
extractor `extTold`: find in the committer's log the query that was answered by the commitment; read
the key back off its string; decode, at that key's record, the word under its root, read at its c
off the log. It asks the hash function nothing. At the system's own claim this is the second premise
of `front_sound_text` (Johnson/Top/FrontParts.lean).

Under which hypotheses. `CoreArmsD b` (at `F.asking encA`), `WordReadsPart`, hrd, "no two keys have
one code", the meaning and the bound on the errors are hypotheses of the theorems: Lean's list of
axioms does not show them. So are hn and hv: `F.Pub` and the family's members toss no coin. In
`sound_told_own` hrd is no premise.

What it does not show. F, encA, encT, c₀, b, part and wordC are parameters: no family, code, reading
or word is given here. All hold vacuously at checks that never say yes, or at errors of 1 or more:
they claim nothing there. A code that gives no key a string meets "no two keys have one code"
vacuously, and then the system's verifier refuses all. A word that does not read d meets
`WordReadsPart` vacuously. `ArmsTestC` is proved from the text of the checks of `F.told`: nothing
here says that another verifier's parts are these checks. One direction. All limits of the heads of
the three files named apply. Soundness alone. For proofs only; no program imports this file.


-/
import Johnson.Top.ArmsTwoSpellings
import Johnson.TypedOracleCompiler.Top.ArmsPlainOfD
import Johnson.TypedOracleCompiler.Top.OnFilesArmsCPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {F : ArmFam}

/-- Where "run the reading; no, unless the part of its value is c; then A d" says yes at f, the part
of the reading's value at f is c. -/
theorem part_of_told_yes (A : F.D → Rom.OComp (rom 256) Bool) (c : Dig 256) (f : Fam (rom 256))
    (h : (F.Pub.bind fun d => if F.part d = c then A d else .pure false).det f = true) :
    F.part (F.Pub.det f) = c := by
  rw [Rom.OComp.det_bind] at h
  by_contra e
  rw [if_neg e] at h
  exact Bool.noConfusion (show false = true from h)

variable (encA : KeyRoot 256 F.L → Option ZKCP.Str)
  (encT : Dig 256 × KeyRoot 256 F.L → Option ZKCP.Str) (c₀ : Dig 256)

/-- **`ArmsTestC` at `F.told`.** hrd: at every key and f, the part of what the bounds' reading gives
is the family's part of what the family's reading gives. -/
theorem armsTestC_told (b' : BesideArmsCD (F.told encT c₀)) (part : b'.D → Dig 256)
    (hrd : ∀ k (f : Fam (rom 256)), part ((b'.rd k).det f) = F.part (F.Pub.det f)) :
    ArmsTestC b' part where
  key := fun f k x π => by
    rw [hrd]
    unfold liftKC
    cases π.piT with
    | none => exact fun h => Bool.noConfusion (show false = true from h)
    | some p => exact part_of_told_yes _ _ f
  entry := fun f k x π => by
    rw [hrd]
    unfold liftEC
    cases π.link.2.2 with
    | none => exact fun h => Bool.noConfusion (show false = true from h)
    | some p => exact part_of_told_yes _ _ f
  proof := fun f k x π => by
    rw [hrd]
    unfold liftPC
    cases π.piB with
    | none => exact fun h => Bool.noConfusion (show false = true from h)
    | some p => exact part_of_told_yes _ _ f

variable {encA}

/-- **From the three checks' bounds at `F.asking` to the bounds in the plain shape at `F.told`**, at
the same three errors. hW: the word depends on d through its part alone. -/
theorem coreC_of_coreD_told (hn : F.Pub.NoCoin) (hv : F.NoCoin) {b : BesideArmsD (F.asking encA)}
    (h : CoreArmsD b) (part : b.D → Dig 256)
    (hrd : ∀ k (f : Fam (rom 256)), part ((b.rd k).det f) = F.part (F.Pub.det f))
    (wordC : Dig 256 → Rom.Trace (rom 256) → Dig 256 → Fin F.L.wordLength → F.L.Symbol)
    (hW : ∀ d tr cm, b.wordOf d tr cm = wordC (part d) tr cm) :
    CoreArmsC (besidePlain (ArmFam.besideCD encA encT c₀ b) wordC) :=
  coreArmsC_of_CD (coreCD_of_coreD encA encT c₀ hn hv h)
    (show WordReadsPart (ArmFam.besideCD encA encT c₀ b) part wordC from hW)
    (armsTestC_told encT c₀ (ArmFam.besideCD encA encT c₀ b) part fun k f => hrd k.2 f)

/-- The extractor: find in the committer's log the query that was answered by the commitment; read
the key back off its string; decode, at that key's record, the word under its root, read at its c
off the log. -/
def extTold (b : BesideArmsD (F.asking encA))
    (wordC : Dig 256 → Rom.Trace (rom 256) → Dig 256 → Fin F.L.wordLength → F.L.Symbol) :
    Commitment → QueryLog → Option F.I :=
  ((extCodeC (besidePlain (ArmFam.besideCD encA encT c₀ b) wordC)).buildInstance :
    ZKCP.Extractor 256 F.I (List Token × List Token) Unit (ZKCP.Digest 256)
      (List Token × ((Dig 256 × KeyRoot 256 F.L) × OfflineLinkOnlineProof 256 F.L F.aT F.aL))).Ei

/-- **Soundness of the told input's system for an extractor that reads the commitment and the
committer's log alone**, from the three checks' bounds at the asking input. -/
theorem sound_told (hn : F.Pub.NoCoin) (hv : F.NoCoin) {b : BesideArmsD (F.asking encA)}
    (h : CoreArmsD b) (part : b.D → Dig 256)
    (hrd : ∀ k (f : Fam (rom 256)), part ((b.rd k).det f) = F.part (F.Pub.det f))
    (wordC : Dig 256 → Rom.Trace (rom 256) → Dig 256 → Fin F.L.wordLength → F.L.Symbol)
    (hW : ∀ d tr cm, b.wordOf d tr cm = wordC (part d) tr cm)
    (hcode : ZKCP.CodeIsOneToOne encT) (claim : F.I → List Token → List Token → Prop)
    (hs : HoleArmsD.soundFor b claim) (ε : ℕ → ℝ≥0∞)
    (hε : ∀ tC tP, b.εK tC tP + (b.εE tC tP + b.εP tC tP) + epsCode (tC + tP) ≤ ε (tC + tP)) :
    SoundForWith (systemArmsC (F.told encT c₀)) (extTold encT c₀ b wordC) claim ε :=
  verify_sound_arms_C_plain (r := F.told encT c₀) claim ε
    (coreC_of_coreD_told encT c₀ hn hv h part hrd wordC hW) hcode hs hε

variable (encA)

/-- What the theorems need beside the asking input, with the family's own reading for the bounds'
reading. -/
def ArmFam.besideOwn (q₀ : ℕ)
    (wordOf : F.D → Rom.Trace (rom 256) → Dig 256 → Fin F.L.wordLength → F.L.Symbol) (Wn : Type)
    (Rno : F.I → F.X → Wn → Prop) (εK εE εP : ℕ → ℕ → ℝ≥0∞) (x₀ : F.X) :
    BesideArmsD (F.asking encA) where
  D := F.D
  rd := fun _ => F.Pub
  q₀ := q₀
  wordOf := wordOf
  Wn := Wn
  Rno := Rno
  εK := εK
  εE := εE
  εP := εP
  x₀ := x₀

/-- `sound_told` where the bounds' reading is the family's own: hrd holds by definition. -/
theorem sound_told_own (hn : F.Pub.NoCoin) (hv : F.NoCoin) {q₀ : ℕ}
    {wordOf : F.D → Rom.Trace (rom 256) → Dig 256 → Fin F.L.wordLength → F.L.Symbol} {Wn : Type}
    {Rno : F.I → F.X → Wn → Prop} {εK εE εP : ℕ → ℕ → ℝ≥0∞} {x₀ : F.X}
    (h : CoreArmsD (ArmFam.besideOwn encA q₀ wordOf Wn Rno εK εE εP x₀))
    (wordC : Dig 256 → Rom.Trace (rom 256) → Dig 256 → Fin F.L.wordLength → F.L.Symbol)
    (hW : ∀ d tr cm, wordOf d tr cm = wordC (F.part d) tr cm)
    (hcode : ZKCP.CodeIsOneToOne encT) (claim : F.I → List Token → List Token → Prop)
    (hs : HoleArmsD.soundFor (ArmFam.besideOwn encA q₀ wordOf Wn Rno εK εE εP x₀) claim)
    (ε : ℕ → ℝ≥0∞)
    (hε : ∀ tC tP, εK tC tP + (εE tC tP + εP tC tP) + epsCode (tC + tP) ≤ ε (tC + tP)) :
    SoundForWith (systemArmsC (F.told encT c₀))
      (extTold encT c₀ (ArmFam.besideOwn encA q₀ wordOf Wn Rno εK εE εP x₀) wordC) claim ε :=
  sound_told encT c₀ hn hv h F.part (fun _ _ => rfl) wordC hW hcode claim hs ε hε

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.part_of_told_yes
#print axioms VerifiableInference.OnPublicFiles.armsTestC_told
#print axioms VerifiableInference.OnPublicFiles.coreC_of_coreD_told
#print axioms VerifiableInference.OnPublicFiles.sound_told
#print axioms VerifiableInference.OnPublicFiles.sound_told_own
