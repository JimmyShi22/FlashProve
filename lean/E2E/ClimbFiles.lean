-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbFiles.lean: the three soundness conditions of the compiled verifier, which count proof of
work, say the same as three clauses at the object without proof of work.

The conditions. `CompilerSoundnessConditionStatements.keySound`, `entrySound`, `proofSound` (Johnson/Top/InnerCompiledVerifier.lean) say of
the three protocols of an object (key file; entry file, that is the copy's file with its link proof;
proof file): there is a list of counts with which the protocol is round-by-round sound (the proof
file: in the library's form for batches, with a witness map under ∃), and every count is at most εs
as a fraction of its round's verifier messages. In the object that the verifier is compiled from, a
round's proof of work stands in the round: b further bits of the verifier message, all of which must
be 0. So εs is a bound with proof of work counted.

What is shown. Let F and F₀ be three files' protocols over one configuration, joined by a
`FilesPair`: E2E/ClimbPairBatch.lean's pair at each of the three (F has further verifier messages,
all rejected, and further parts of prover messages, all ignored), and numbers of bits g with the law
that a round of F has 2^b times the verifier messages of F₀'s. Then each condition at F holds IF AND
ONLY IF the clause at F₀ holds: the same language or relation, THE SAME COUNTS, and the bound
εs * 2^b for a round with b bits (`Err.BelowG`, Iop/Grind.lean). `filesPair`: the files made by the
makers (`filesOf`, Johnson/EntryRec/AtFiles.lean) are such a pair with the files at data without
proof of work.

On "there is a list". The three conditions bind their lists by ∃, and so do the three clauses: the
list is the same list, copied, and it stays unnamed. Of it one knows the bound εs * 2^b round by
round and nothing more. Where a proof names its list, the forms with explicit lists name the list on
the other side: `climb_sound_at`, `descend_sound_at`, `FilesPair.soundAtR_iff`.

Main names:
  `climb_sound_at`, `descend_sound_at`, `sound_exists_iff`: one protocol with its marks.
  `FilesPair F₀ F`.
  `KeySound0`, `EntrySound0`, `ProofSound0`: the three clauses without proof of work, as statements.
  `keySound_iff`, `entrySound_iff`, `proofSound_iff`: the three conditions, both ways.
  `FilesPair.soundAtR_iff`: the five clauses of `HolographicProtocol.SoundAtR` with explicit lists, both ways.
  `below_at_most`: if no round has more than w bits, every round is below εs * 2^w.
  `EntrySoundAt`, `EntrySound0.at_most`: so for the entry file, whose rounds are all local.
  `belowG_zero_iff`; `keySound0_zero`, `entrySound0_zero`, `proofSound0_zero`: at bits 0.
  `filesPair`: the makers' files.

What does not come along. Acceptance and soundness alone. A `FilesPair` ties prover messages,
verifier messages and the three decisions; it ties nothing on queries (`reads`, `extReads`,
`blinded`, the oracles' positions and answers, the cut into oracle and plain part). Completeness is
not among the three conditions. At an object with proof of work in its rounds the honest prover of
the interactive protocol is rejected whenever a bit is 1, so acceptance outside an abort set
(`Honest.Acc`) can hold only with an abort set that holds all such randomness, which is not small
(no theorem here says so); at the object without proof of work completeness is open, and nothing
here bears on it. Nothing on zero knowledge. Both objects' honest provers are free letters, of which
no clause asks anything. The three protocols are taken apart: nothing on a whole run.

Tests against emptiness. At bits 0 the three clauses are equivalent to the three conditions, list by
list (`keySound0_zero`, `entrySound0_zero`, `proofSound0_zero`): the clauses' form loses nothing. If
the bound allows some round a count as large as that round of F₀ (εs * 2^b at least 1; at least n
in a shared round), then with such a count the clause holds of every protocol, and so does the
condition at F (at most that many verifier messages of F's round have bits 0): both sides have
content only where εs * 2^b < 1 in every round. Whether either side can be met is not this file's
matter: F is a letter here. E2E/ClimbAtD.lean applies `entrySound_iff` where the condition is a
theorem, and states the other two equivalences at the full size; no statement applies these two
where their conditions are proved (in scope, where `protocolDataWellFormed` says yes: `keySound_at_holds`,
Johnson/Goal/Conditions/KeyOpenHolds.lean; `proofSound_of_verify`,
Johnson/Goal/Skeleton/SoundOfVerifyGoals.lean).

On "knowledge". The proof file's condition and clause have the library's form with a witness map and
a relation `Rno` that it calls relaxed. At the configuration of the full size (`relationsAndEncodingOfClaims`,
OnBytes/Flat/FilesAt.lean) the witness type has one element and `Rno` is the same term as the
configuration's `Ryes`: there both are soundness, not knowledge soundness. How strict that one
relation is hangs on the claims: at the IOP as written in Lean they are made of the integer model's
relaxed relation.

"Without proof of work" is a reading of this folder's writers: the same rounds' data with the number
of proof-of-work bits set to 0, under the same decision functions. Whether that protocol may stand
for "the IOP without proof of work" is an open question, which no theorem here settles.

This file's definitions may be read as stating a goal, that is, something that is to be proved. They
count as none.




-/
import E2E.ClimbWhole
import E2E.ClimbLink
import Johnson.Flat.InnerInputOfThreeProtocols
import Johnson.EntryRec.AtFiles

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob Hiop
open OnBytes.Flat (Files)
open VerifiableInference.OnPublicFiles (InnerCompilerInputFieldsOverThreeProtocols SoundnessAnalysisFieldsOverThreeProtocols innerInputOfThreeProtocols soundnessAnalysisDataOfThreeProtocols)
open scoped ENNReal

/-! ## 1. One protocol with its marks -/

/-- Multiplying the counts of the shared rounds by n, then copying the list, is copying it and then
multiplying. -/
theorem BPair.timesShared (n : ℕ) {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t} (q : BPair A A')
    (ε : Err t) :
    q.toPair.toEmb.err (Err.timesShared n A' ε) = Err.timesShared n A (q.toPair.toEmb.err ε) := by
  rw [← q.toEmb_eq]
  exact BEmb.timesShared n q.toBEmb ε

section
variable {X : Type} {E : ExtSpec} {Q₀ Q : BatchInteractiveOracleProof X E}

/-- From the protocol with the bits, an explicit list: sound at ε with the bound c, a shared round's
count taken n times, gives sound at the copied list with the bound c * 2^b. -/
theorem climb_sound_at (S : BatchPair Q₀ Q) (g : GBits Q₀.loc.shape)
    (hg : S.pair.toPair.toEmb.Bits g) (n : ℕ) (c : ℝ≥0∞) (L : X → E.Str → Prop)
    (ε : Err Q.loc.shape) (hb : Err.Below (Err.timesShared n Q.ann ε) c)
    (hs : Q.loc.Sound L ε) :
    Err.BelowG g (Err.timesShared n Q₀.ann (S.pair.toPair.toEmb.err ε)) c ∧
      Q₀.loc.Sound L (S.pair.toPair.toEmb.err ε) :=
  ⟨(congrArg (fun z => Err.BelowG g z c) (BPair.timesShared n S.pair ε)).mp
      ((below_iff_belowG S.pair.toPair.toEmb g (Err.timesShared n Q.ann ε) c hg).1 hb),
    S.loc.toEmb.sound hs⟩

/-- To the protocol with the bits, an explicit list. -/
theorem descend_sound_at (S : BatchPair Q₀ Q) (g : GBits Q₀.loc.shape)
    (hg : S.pair.toPair.toEmb.Bits g) (n : ℕ) (c : ℝ≥0∞) (L : X → E.Str → Prop)
    (ε₀ : Err Q₀.loc.shape) (hb : Err.BelowG g (Err.timesShared n Q₀.ann ε₀) c)
    (hs : Q₀.loc.Sound L ε₀) :
    Err.Below (Err.timesShared n Q.ann (S.pair.toPair.down ε₀)) c ∧
      Q.loc.Sound L (S.pair.toPair.down ε₀) :=
  ⟨(below_iff_belowG S.pair.toPair.toEmb g (Err.timesShared n Q.ann (S.pair.toPair.down ε₀)) c
      hg).2 ((congrArg (fun z => Err.BelowG g z c)
        ((BPair.timesShared n S.pair (S.pair.toPair.down ε₀)).trans
          (congrArg (Err.timesShared n Q₀.ann) (S.pair.toPair.err_down ε₀)))).mpr hb),
    S.loc.sound_down hs⟩

/-- **"There is a list", both ways.** -/
theorem sound_exists_iff (S : BatchPair Q₀ Q) (g : GBits Q₀.loc.shape)
    (hg : S.pair.toPair.toEmb.Bits g) (n : ℕ) (c : ℝ≥0∞) (L : X → E.Str → Prop) :
    (∃ ε, Err.Below (Err.timesShared n Q.ann ε) c ∧ Q.loc.Sound L ε) ↔
      ∃ ε₀, Err.BelowG g (Err.timesShared n Q₀.ann ε₀) c ∧ Q₀.loc.Sound L ε₀ :=
  ⟨fun h => h.elim fun ε hε =>
      ⟨S.pair.toPair.toEmb.err ε, climb_sound_at S g hg n c L ε hε.1 hε.2⟩,
    fun h => h.elim fun ε₀ hε =>
      ⟨S.pair.toPair.down ε₀, descend_sound_at S g hg n c L ε₀ hε.1 hε.2⟩⟩

end

/-! ## 2. Three files -/

variable {C : ConfigurationWithOutOfDomainSample}

/-- Three files' protocols F₀ and F over the same configuration, each of the three in a pair with
bits that fits its marks (E2E/ClimbPairBatch.lean); the numbers of bits g, with the law that a round
of F has 2^b times the verifier messages of F₀'s; the same number of requests in a batch, the same
early and late parts of an instance. -/
structure FilesPair (F₀ F : Files C) where
  key : BatchPair (X := C.Rec) (E := C.E0) ⟨F₀.key, F₀.annT⟩ ⟨F.key, F.annT⟩
  entry :
    BatchPair (X := C.Rec × C.Rec) (E := twoExternalStrings C.n C.Sg) ⟨F₀.entry, F₀.annL⟩ ⟨F.entry, F.annL⟩
  proof : BatchPair F₀.batch F.batch
  gT : GBits F₀.key.shape
  gL : GBits F₀.entry.shape
  gB : GBits F₀.proof.shape
  bitsT : key.pair.toPair.toEmb.Bits gT
  bitsL : entry.pair.toPair.toEmb.Bits gL
  bitsB : proof.pair.toPair.toEmb.Bits gB
  hN : F₀.N = F.N
  hearly : F₀.early = F.early
  hlate : F₀.late = F.late

/-- Key file, without proof of work: round-by-round sound for "the table has a collision at the OOD
seed, or decodes with the OOD sample to an index"; a round with b in g has error at most c * 2^b, a
shared round's count taken n times. -/
def KeySound0 (F₀ : Files C) (g : GBits F₀.key.shape) (n : ℕ) (c : ℝ≥0∞) : Prop :=
  ∃ ε, Err.BelowG g (Err.timesShared n F₀.annT ε) c ∧
    F₀.key.Sound (fun rec y => C.coll y rec.1 ∨ C.D y rec ≠ none) ε

/-- Entry file, without proof of work: the same for "the first table does not decode to an index, or
the further table has a collision, or both decode to the same index". -/
def EntrySound0 (F₀ : Files C) (g : GBits F₀.entry.shape) (n : ℕ) (c : ℝ≥0∞) : Prop :=
  ∃ ε, Err.BelowG g (Err.timesShared n F₀.annL ε) c ∧
    F₀.entry.Sound
      (fun rr y => C.D y.1 rr.1 = none ∨ C.coll y.2 rr.2.1 ∨ C.D y.2 rr.2 = C.D y.1 rr.1) ε

/-- Proof file, without proof of work: the library's form for batches with a witness map (`SndBKT`),
for its relation `Rno` at the decoded index. Whether that is more than soundness hangs on the
configuration: at that of the full size it is not (this file's head, On "knowledge"). -/
def ProofSound0 (F₀ : Files C) (g : GBits F₀.proof.shape) (c : ℝ≥0∞) : Prop :=
  ∃ (wit : C.X × C.Rec → C.E0.Str → Tr F₀.proof.shape → C.Cells) (ε : Err F₀.proof.shape),
    Err.BelowG g ε c ∧ ∀ rec : C.Rec,
      (F₀.batch.comap fun x : C.X => (x, rec)).SndBKT F₀.N F₀.early F₀.late
        (fun x y w => C.D y rec = none ∨ ∃ i, C.D y rec = some i ∧ C.Rno i x w)
        (fun x y τ => wit (x, rec) y τ) ε

section
variable {F₀ F : Files C} (S : FilesPair F₀ F) (P : F.Provers) (T : InnerCompilerInputFieldsOverThreeProtocols F P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols F P)

/-- **The key file's condition, both ways.** -/
theorem keySound_iff :
    VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols F P T U) ↔
      KeySound0 F₀ S.gT (2 ^ T.W.depthReqT) U.εs :=
  sound_exists_iff S.key S.gT S.bitsT (2 ^ T.W.depthReqT) U.εs
    (fun rec y => C.coll y rec.1 ∨ C.D y rec ≠ none)

/-- **The entry file's condition, both ways.** -/
theorem entrySound_iff :
    VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataOfThreeProtocols F P T U) ↔
      EntrySound0 F₀ S.gL (2 ^ T.W.depthReqL) U.εs :=
  sound_exists_iff S.entry S.gL S.bitsL (2 ^ T.W.depthReqL) U.εs
    (fun rr y => C.D y.1 rr.1 = none ∨ C.coll y.2 rr.2.1 ∨ C.D y.2 rr.2 = C.D y.1 rr.1)

/-- The proof file's condition gives the clause without proof of work. The witness map is given the
transcript with the fixed nonce and bits 0. -/
theorem proofSound_climb
    (h : VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols F P T U)) :
    ProofSound0 F₀ S.gB U.εs := by
  obtain ⟨wit, ε, hb, hs⟩ := h
  unfold ProofSound0
  refine ⟨fun a y τ => wit a y (S.proof.pair.toPair.toEmb.tr τ), S.proof.pair.toPair.toEmb.err ε,
    (below_iff_belowG S.proof.pair.toPair.toEmb S.gB ε U.εs S.bitsB).1 hb, fun rec => ?_⟩
  have h1 := (S.proof.comap fun x : C.X => (x, rec)).sndBKT_up (hs rec)
  rw [S.hN, S.hearly, S.hlate]
  exact h1

/-- The clause without proof of work gives the proof file's condition. The witness map is given the
stripped transcript. -/
theorem proofSound_descend (h : ProofSound0 F₀ S.gB U.εs) :
    VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols F P T U) := by
  obtain ⟨wit, ε, hb, hs⟩ := h
  unfold VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.proofSound
  refine ⟨fun a y τ => wit a y (S.proof.pair.toPair.strip τ), S.proof.pair.toPair.down ε,
    (below_iff_belowG S.proof.pair.toPair.toEmb S.gB (S.proof.pair.toPair.down ε) U.εs
      S.bitsB).2 ((congrArg (fun z => Err.BelowG S.gB z U.εs)
        (S.proof.pair.toPair.err_down ε)).mpr hb), fun rec => ?_⟩
  have h0 := hs rec
  rw [S.hN, S.hearly, S.hlate] at h0
  exact (S.proof.comap fun x : C.X => (x, rec)).sndBKT_down h0

/-- **The proof file's condition, both ways.** -/
theorem proofSound_iff :
    VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols F P T U) ↔
      ProofSound0 F₀ S.gB U.εs :=
  ⟨proofSound_climb S P T U, proofSound_descend S P T U⟩

end

/-- With 0 bits in every round the bound with the bits counted is the bound itself. -/
theorem belowG_zero_iff : ∀ {s : Iop.Shape} (ε : Err s) (c : ℝ≥0∞),
    Err.BelowG (GBits.zero s) ε c ↔ Err.Below ε c
  | [], _, _ => Iff.rfl
  | r :: s, (n, ε), c => by
      show ((n : ℝ≥0∞) ≤ c * ((2 : ℝ≥0∞) ^ 0 * (Fintype.card r.Chal : ℝ≥0∞)) ∧
          Err.BelowG (GBits.zero s) ε c) ↔
        ((n : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞) ∧ Err.Below ε c)
      rw [pow_zero, one_mul, belowG_zero_iff ε c]

section
variable (F : Files C) (P : F.Provers) (T : InnerCompilerInputFieldsOverThreeProtocols F P) (U : SoundnessAnalysisFieldsOverThreeProtocols F P)

/-- At bits 0 the key file's clause is equivalent to the key file's condition, list by list. -/
theorem keySound0_zero :
    KeySound0 F (GBits.zero F.key.shape) (2 ^ T.W.depthReqT) U.εs ↔
      VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols F P T U) :=
  exists_congr fun _ => and_congr_left' (belowG_zero_iff _ U.εs)

/-- At bits 0 the entry file's clause is equivalent to the entry file's condition, list by list. -/
theorem entrySound0_zero :
    EntrySound0 F (GBits.zero F.entry.shape) (2 ^ T.W.depthReqL) U.εs ↔
      VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataOfThreeProtocols F P T U) :=
  exists_congr fun _ => and_congr_left' (belowG_zero_iff _ U.εs)

/-- At bits 0 the proof file's clause is equivalent to the proof file's condition, list by list. -/
theorem proofSound0_zero :
    ProofSound0 F (GBits.zero F.proof.shape) U.εs ↔
      VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols F P T U) :=
  exists_congr fun _ => exists_congr fun ε => and_congr_left' (belowG_zero_iff ε U.εs)

end

/-- Where all rounds are local, no count is multiplied. -/
theorem timesShared_local (N : ℕ) :
    ∀ (s : Iop.Shape) (ε : Err s), Err.timesShared N (RoundSplits.allLocal s) ε = ε
  | [], () => rfl
  | _ :: s, (e, ε) => congrArg (Prod.mk e) (timesShared_local N s ε)

/-- Entry file: round-by-round sound for the entry file's language, every round's error at most
c. -/
def EntrySoundAt (F₀ : Files C) (c : ℝ≥0∞) : Prop :=
  ∃ ε, Err.Below ε c ∧
    F₀.entry.Sound
      (fun rr y => C.D y.1 rr.1 = none ∨ C.coll y.2 rr.2.1 ∨ C.D y.2 rr.2 = C.D y.1 rr.1) ε

/-- Where the entry file's rounds are all local and none has more than w bits, the clause without
proof of work gives one bound for all rounds: c * 2^w. -/
theorem EntrySound0.at_most {F₀ : Files C} {g : GBits F₀.entry.shape} {n : ℕ} {c : ℝ≥0∞}
    (h : EntrySound0 F₀ g n c) (hA : F₀.annL = RoundSplits.allLocal F₀.entry.shape) (w : ℕ)
    (hw : g.AllLe w) : EntrySoundAt F₀ (c * 2 ^ w) := by
  obtain ⟨ε, hb, hs⟩ := h
  rw [hA, timesShared_local] at hb
  exact ⟨ε, below_of_allLe g ε c w hw hb, hs⟩

/-- **The five clauses with explicit lists, both ways**: the object without proof of work has them
with the witness map wit, the count eR of OOD seeds and the three lists, if and only if the object
with proof of work has them with wit at the stripped transcript, eR and the same three lists. -/
theorem FilesPair.soundAtR_iff {F₀ F : Files C} (S : FilesPair F₀ F) (P₀ : F₀.Provers)
    (P : F.Provers) {Wn : Type} (Rno : C.I → C.X → Wn → Prop)
    (wit : C.X × C.Rec → C.E0.Str → Tr F₀.proof.shape → Wn) (eR : ℕ) (εT : Err F₀.key.shape)
    (εL : Err F₀.entry.shape) (εB : Err F₀.proof.shape) :
    (F₀.withProvers P₀).SoundAtR Rno wit eR εT εL εB ↔
      (F.withProvers P).SoundAtR Rno (fun a y τ => wit a y (S.proof.pair.toPair.strip τ)) eR
        (S.key.pair.toPair.down εT) (S.entry.pair.toPair.down εL)
        (S.proof.pair.toPair.down εB) := by
  constructor
  · intro h
    refine ⟨h.noneColl, h.rcd, S.key.loc.sound_down h.sndT, S.entry.loc.sound_down h.sndL,
      fun rec => ?_⟩
    have h0 : (F₀.batch.comap fun x : C.X => (x, rec)).SndBKT F₀.N F₀.early F₀.late
        ((F₀.withProvers P₀).relB Rno rec) (fun x y τ => wit (x, rec) y τ) εB := h.sndB rec
    rw [S.hN, S.hearly, S.hlate] at h0
    exact (S.proof.comap fun x : C.X => (x, rec)).sndBKT_down h0
  · intro h
    refine ⟨h.noneColl, h.rcd, (S.key.loc.sound_iff _ εT).2 h.sndT,
      (S.entry.loc.sound_iff _ εL).2 h.sndL, fun rec => ?_⟩
    show (F₀.batch.comap fun x : C.X => (x, rec)).SndBKT F₀.N F₀.early F₀.late
      ((F₀.withProvers P₀).relB Rno rec) (fun x y τ => wit (x, rec) y τ) εB
    rw [S.hN, S.hearly, S.hlate]
    exact ((S.proof.comap fun x : C.X => (x, rec)).sndBKT_iff F.N F.early F.late
      ((F₀.withProvers P₀).relB Rno rec) (fun x y τ => wit (x, rec) y τ) εB).2 (h.sndB rec)

/-- If no round has more than w bits, a list that is below c with the bits counted is below c * 2^w
in every round. -/
theorem below_at_most {s : Iop.Shape} (g : GBits s) (ε : Err s) (c : ℝ≥0∞) (w : ℕ)
    (hw : g.AllLe w) (h : Err.BelowG g ε c) : Err.Below ε (c * 2 ^ w) :=
  below_of_allLe g ε c w hw h

/-! ## 3. The makers' files -/

section
open OnBytes.Maker OnBytes.RunA
open _root_.Run (ckP)
open _root_.Run.PQ (View)

variable {a : ℕ} (Kc : ConfLetters a) (f : _root_.Fmt.Fld) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → View → View → View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (runP : Kc.conf.X × Kc.conf.Rec → View → View → View → Bool)
  (eL₀ eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)

theorem wholeBatchPair_bits (Ck : _root_.Run.PQ.CK) (K : KitFree Ck) {Xi TF TJ T3 : Type}
    (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool) (D : WholeD)
    (tF : TF) (tJ : TJ) (t3 : T3) :
    (wholeBatchPair Ck K silent run D tF tJ t3).pair.toPair.toEmb.Bits (bitsW Ck D tF tJ t3) :=
  (congrArg (fun p : Pair (chainsOf Ck (noWork D) tF tJ t3).sh (chainsOf Ck D tF tJ t3).sh =>
      p.toEmb.Bits (bitsW Ck D tF tJ t3))
    (wholeBatchPair_toPair Ck K silent run D tF tJ t3)).mpr (pairW_bits Ck K D tF tJ t3)

/-- **The makers' files are the makers' files at data without proof of work, with the bits added**,
at verifier messages as hash blocks. The entry file's protocol is a letter on both sides, with its
pair and its numbers of bits. -/
def filesPair
    (SL : BatchPair (X := Kc.conf.Rec × Kc.conf.Rec) (E := twoExternalStrings (2 ^ a) _root_.Run.PQ.SgX)
      ⟨eL₀.QL, eL₀.aL⟩ ⟨eL.QL, eL.aL⟩)
    (gL : GBits eL₀.QL.shape) (hL : SL.pair.toPair.toEmb.Bits gL) :
    FilesPair
      (filesOf Kc f (noWork DK) (noWork DP) tFk tJk t3k tFp tJp t3p silK runK silP runP eL₀ N
        early late)
      (filesOf Kc f DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early late) where
  key := wholeBatchPair (ckP f) (kitFree_ckP f) silK runK (DK.at a) tFk tJk t3k
  entry := SL
  proof := wholeBatchPair (ckP f) (kitFree_ckP f) silP runP (DP.at a) tFp tJp t3p
  gT := bitsW (ckP f) (DK.at a) tFk tJk t3k
  gL := gL
  gB := bitsW (ckP f) (DP.at a) tFp tJp t3p
  bitsT := wholeBatchPair_bits (ckP f) (kitFree_ckP f) silK runK (DK.at a) tFk tJk t3k
  bitsL := hL
  bitsB := wholeBatchPair_bits (ckP f) (kitFree_ckP f) silP runP (DP.at a) tFp tJp t3p
  hN := rfl
  hearly := rfl
  hlate := rfl

end

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.sound_exists_iff
#print axioms AtPublicFiles.Climb.keySound_iff
#print axioms AtPublicFiles.Climb.entrySound_iff
#print axioms AtPublicFiles.Climb.proofSound_iff
#print axioms AtPublicFiles.Climb.keySound0_zero
#print axioms AtPublicFiles.Climb.entrySound0_zero
#print axioms AtPublicFiles.Climb.proofSound0_zero
#print axioms AtPublicFiles.Climb.FilesPair.soundAtR_iff
#print axioms AtPublicFiles.Climb.filesPair
