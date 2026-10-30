-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Top.lean: the compiled verifier of a file is sound, as an implication from a
written list of hypotheses.

A second form of the compiler's verifier side, beside the library's own. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

A file of the prover (a key, a proof) is verified along three hash chains, which are joined: the
first chain ends in a seal, whose value stands at a leaf (a slot) of a tree; the root of that tree
starts the second chain, which many slots share; the second chain ends in a seal; both seals start
the third chain. A chain may open trees whose roots another chain has sent. In the compiler's types
this is ONE batch protocol over the rounds `G : Chains` (Compile/Joined/Types.lean): local rounds, a
joining round, shared rounds, local rounds. Its verifier `F.verify` walks the three chains one after
the other (OnBytes/TypedOracleCompiler/Joined/Verifier.lean), over wire records with lists of trees.

What is here.
  `Links G A`      the typed descriptions of the three chains over the rounds G, as reductions
                   (`Reduction`, Iop/Compose.lean) from the file's statement to the trivial
                   statement, each with its relations, its extractor and its errors.
  `Links.Knows`    the soundness clause (`Know`, Ior/Know.lean) of each chain, and that each hands
                   on only statements of which the next chain's clause speaks: five fields.
  `Links.Lg`       the language of which the top speaks: the statement "what the first query holds
                   of the instance; the external strings" has a witness in the description's
                   relation R₀, if it is one of which the first chain's clause speaks.
  `Links.worst`    the error a query, computed from the description's errors and the number of
                   slots.
  `FileLaws`, `FileHoles`, `FileHolesLate`   THE LISTS: one named field for each thing that is not
                   proved here: of the file itself; with the description where the first query
                   binds the whole instance; with the description where a later round of the
                   first chain binds the rest of it.
  `sound_verifyFile`   THE TOP: `FileHoles` gives `SoundAt` (OnBytes/TypedOracleCompiler/Joined/Bound.lean) of
                   `F.verify`: there is an event on traces that is rare for every algorithm with t
                   queries (at most t εs + 2 (t + 1)² / 2^lam, εs := `Links.worst`), is never
                   undone, and outside which every string accepted under outer roots with `UnderTwo`
                   has its statement in `Links.Lg`, at the external strings `extStr` that the trace
                   determines under these roots (OnBytes/TypedOracleCompiler/Joined/ExtractReads.lean).
  `lane_verifyFile`    the same with the event in the open (`SoundLane`, BoundFiles.lean), for a
                   verifier that calls several files' verifiers.
  `sound_verifyFile_late`, `lane_verifyFile_late`   the two at `FileHolesLate`: the language speaks
                   of the whole instance.
  `lane_verifyFile_noInst`   the lane of a file that lays no instance into its queries, whatever
                   `L.late` is.
  `detBound_verifyFile`   PROVED: `F.verify` tosses no coin; a bound on its queries.
  `row_sound`      PROVED from `knows` and `decides`: the joined protocol, as an ordinary protocol,
                   is sound round by round with the three chains' errors in a row.
  `row_sndBKT`, `row_sndBKT_late`   PROVED from the same: the joined batch protocol is sound round
                   by round with a witness. These three are the forms in which a verifier with
                   records takes the protocols of its files.

How the top is proved: `F.verify` is `verifyOneProtocol` at the joined protocol (`FileW.verify_eq`); a yes of
`verifyOneProtocol` gives a yes of the verifier on whole paths (`runsIn_verifyB_of_strict`); the three
chains' clauses give round-by-round soundness of the joined protocol (`sndBL_of_three_worst`,
or `sndBL_of_three_late`, CompileK/Joined/ExtractKnow.lean); from there `laneFor_of_snd`
(BoundFiles.lean), at the reading `extStr` (`extReads_extStr`).

Limits. This is the statement for ONE file. The verifier of a key, an entry and a proof with their
records calls a file's verifier once for each; that joining is another file's matter
(OnBytes/TypedOracleCompiler/Joined/BoundFiles.lean has the event for several files under different tags). Nothing
in the lists is shown here, nor that their fields can be met together. The theorem is as strong as
the description: `Links.Lg` is said with the description's own on₀ and R₀, and a description whose
clause speaks of no statement gives a language that holds of everything. All rounds of the second
chain pay the number of slots in the error. Where no later query takes in more of the instance
(`L.late = none`), what `early` drops of an instance stands in no query, and these statements do not
bind it: `Links.Lg early` speaks of `early x` alone (what `early` drops is reached only by a further
step, from the verifier's yes at x and the transcript: it is asked of whoever uses `row_sndBKT`, and
is not shown here), and `early` is a letter that the read-back's laws do not pin (a constant map
meets them, and the language then says nothing of x): whoever uses the theorem must show it. The
values of the second and third chains' runs, the answers of the record and the number of the stored
copy ride in plain parts of the proof string as the prover's free data: `SoundAt` speaks of every
proof string, so of every such value; whatever the decision needs of them (that two copies agree;
that a number is the instance's) is the description's to test. The seeds of a table's record stand
in no query of the three chains: here they are part of the instance, and whoever calls this verifier
fixes them. The laws of a wire record (`wire`) ask that K uniform blocks give an exactly uniform
verifier message in every round. `UnderTwo` is a condition on the list of outer roots with which the
verifier is called; the verifier does not test it. So is okX in `lane_verifyFile_noInst`: whoever
calls the verifier builds the list from the instance by a one-to-one code; at an okX that holds
nowhere the lane says nothing. `F.verify` is a function fit for a theorem's statement; that it can
be evaluated at the size of a real file is not claimed. Completeness, and what a proof string shows
of the prover's inputs, are not spoken of.
Beside the lists the tops take two things more: a read-back R (`ReadBack F.written early`,
OnBytes/TypedOracleCompiler/Joined/Bound.lean; in `lane_verifyFile_noInst` a `ReadBackC`, BoundC.lean: data with
laws) and hl, which says which case of `L.late` it is (there: hx and hu). The probability in
`SoundAt` is over the family of typed oracles, lazily drawn: nothing here carries it to one hash
function.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.ExtractReads
import OnBytes.TypedOracleCompiler.Joined.BoundFiles
import OnBytes.TypedOracleCompiler.Joined.BoundNoInst
import OnBytes.TypedOracleCompiler.Joined.Verifier
import OnBytes.TypedOracleCompiler.Joined.WireOf
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestSound
import OnBytes.TypedOracleCompiler.Compile.Batch.GlueTools
import CompileK.Joined.ExtractKnow

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains worst3)
open _root_.CompileK.Joined (AllKind allKind_const sndBL_of_three_worst sndBL_of_three_late
  KnowLate sndBKT_of_three sndBKT_of_three_late)
open scoped ENNReal

/-! ## The three chains' typed descriptions -/

/-- The typed descriptions of the three chains of a file over the rounds G, with statements in A:
three reductions in a row, each over its chain's rounds with the chain's first round, the last to
the trivial statement; for each the statements of which soundness speaks, the relation before it,
its extractor and its errors. -/
structure Links (G : Chains) (A : Type) where
  /-- the statements that the first chain hands to the second -/
  A₁ : Type
  /-- the statements that the second chain hands to the third -/
  A₂ : Type
  /-- the witnesses of the file's statements -/
  W₀ : Type
  /-- the witnesses of the statements in A₁ -/
  W₁ : Type
  /-- the witnesses of the statements in A₂ -/
  W₂ : Type
  /-- the first chain: it rejects, or hands on a statement -/
  out₁ : A → Tr G.c₁ → Option A₁
  /-- the second chain -/
  out₂ : A₁ → Tr G.c₂ → Option A₂
  /-- the third chain: it rejects or accepts -/
  out₃ : A₂ → Tr G.c₃ → Option Unit
  /-- the statements of which the first chain's soundness speaks -/
  on₀ : A → Prop
  /-- those of the second -/
  on₁ : A₁ → Prop
  /-- those of the third -/
  on₂ : A₂ → Prop
  /-- the relation of the file's statements -/
  R₀ : A → W₀ → Prop
  /-- the relation between the first chain and the second -/
  R₁ : A₁ → W₁ → Prop
  /-- the relation between the second chain and the third -/
  R₂ : A₂ → W₂ → Prop
  /-- the first chain's extractor -/
  e₁ : A → Tr G.c₁ → W₁ → W₀
  /-- the second chain's -/
  e₂ : A₁ → Tr G.c₂ → W₂ → W₁
  /-- the third chain's -/
  e₃ : A₂ → Tr G.c₃ → Unit → W₂
  /-- the first chain's errors, round by round -/
  ε₁ : Err G.c₁
  /-- the second chain's -/
  ε₂ : Err G.c₂
  /-- the third chain's -/
  ε₃ : Err G.c₃
  /-- a value for the extractor where the first verifier rejects -/
  d₀ : W₀
  /-- a value for the extractor where the second verifier rejects -/
  d₁ : W₁

namespace Links
variable {G : Chains} {A : Type} (C : Links G A)

/-- the first chain as a reduction -/
@[reducible] def K₁ : Reduction A C.A₁ := ⟨G.c₁, C.out₁⟩
/-- the second chain -/
@[reducible] def K₂ : Reduction C.A₁ C.A₂ := ⟨G.c₂, C.out₂⟩
/-- the third chain -/
@[reducible] def K₃ : Reduction C.A₂ Unit := ⟨G.c₃, C.out₃⟩

/-- the three chains in a row: a reduction over the rounds of the whole file -/
@[reducible] def all : Reduction A Unit := C.K₁.seq (C.K₂.seq C.K₃)

/-- the errors of the three chains in a row -/
def err : Err C.all.shape := Err.app C.ε₁ (Err.app C.ε₂ C.ε₃)

/-- the same, with those of the second chain counted once for each of N slots -/
def errN (N : ℕ) : Err C.all.shape := Err.app C.ε₁ (Err.app (Err.times N C.ε₂) C.ε₃)

/-- the extractor of the three chains in a row: the later chain's first -/
def ext : A → Tr C.all.shape → Unit → C.W₀ :=
  Reduction.extSeq C.K₁ (C.K₂.seq C.K₃) C.e₁ (Reduction.extSeq C.K₂ C.K₃ C.e₂ C.e₃ C.d₁) C.d₀

/-- **Owed of the description**: the soundness clause of each chain, and that each chain hands on
only statements of which the next chain's clause speaks. -/
structure Knows : Prop where
  /-- the first chain's soundness clause -/
  know₁ : C.K₁.Know C.on₀ C.R₀ C.R₁ C.e₁ C.ε₁
  /-- the second chain's -/
  know₂ : C.K₂.Know C.on₁ C.R₁ C.R₂ C.e₂ C.ε₂
  /-- the third chain's: it ends in the trivial statement -/
  know₃ : C.K₃.Know C.on₂ C.R₂ (fun _ _ => True) C.e₃ C.ε₃
  /-- what the first chain hands on is a statement of which the second's clause speaks -/
  hands₁ : ∀ a τ b, C.on₀ a → C.K₁.out a τ = some b → C.on₁ b
  /-- what the second chain hands on is a statement of which the third's clause speaks -/
  hands₂ : ∀ a τ b, C.on₁ a → C.K₂.out a τ = some b → C.on₂ b

/-- The three chains in a row have the soundness clause, with the errors in a row. -/
theorem Knows.all {C : Links G A} (h : C.Knows) :
    C.all.Know C.on₀ C.R₀ (fun _ _ => True) C.ext C.err :=
  Reduction.Know.seq h.know₁ (Reduction.Know.seq h.know₂ h.know₃ h.hands₂ C.d₁) h.hands₁ C.d₀

end Links

/-- The language of a file, by its description: the statement "what the first query holds of the
instance x; the external strings y" has a witness in R₀, if it is a statement of which the first
chain's clause speaks. -/
def Links.Lg {G : Chains} {Y S : Type} (C : Links G (Y × S)) (early : Y → Y) (x : Y) (y : S) :
    Prop :=
  C.on₀ (early x, y) → ∃ w, C.R₀ (early x, y) w

/-- The error a query, computed from the description: the greatest error of a round, as a
probability; those of the second chain count once for each of the N slots. -/
noncomputable def Links.worst {G : Chains} {A : Type} (C : Links G A) (N : ℕ) : ℝ≥0∞ :=
  worst3 N C.ε₁ C.ε₂ C.ε₃

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## What is owed of the file itself -/

/-- **What is owed of a file F itself** (`FileW`, OnBytes/TypedOracleCompiler/Joined/Wire.lean), whatever its
description. prjE: how a symbol of an external string is read back from a leaf. -/
structure FileLaws {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec} (F : FileW W G Y E)
    (prjE : Body L → Option E.Sym) : Prop where
  /-- THE FILE'S DECISION depends on the oracles only where it reads -/
  isLocal : F.D.proto.IsLocal
  /-- THE ROUNDS: the joining round is shared, and its annotation is coherent -/
  laws : G.Laws
  /-- THE WIRE: the laws of the wire record, with lists of trees. Among them: in every round K
  uniform blocks give an exactly uniform verifier message. So the theorem is meant at rounds whose
  verifier message IS the blocks of the hash, with the way from blocks to field elements inside the
  description (the library's pass through samplers); at other rounds this law is false. -/
  wire : F.wq.OKG
  /-- THE WRITING: a symbol of an external string that was written into a leaf is read back -/
  prjE_emb : ∀ a, prjE (F.embE a) = some a

section File
variable {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec} {F : FileW W G Y E}
  {prjE : Body L → Option E.Sym} {early : Y → Y} {Lg : Y → E.Str → Prop} {εs : ℝ≥0∞}

/-- From round-by-round soundness of the joined protocol: the file has a lane of the analysis
(`SoundLane`, OnBytes/TypedOracleCompiler/Joined/BoundFiles.lean) under its tag: outside the two hash events and the
lane's state event a yes of `F.verify` means "in the language". -/
theorem FileLaws.lane (B : FileLaws F prjE) (sMT sFS : ℕ) (R : ReadBack F.written early)
    (hsnd : ∃ ε : Err G.sh,
      Err.Below ε εs ∧ F.D.batch.SndBL (2 ^ W.dReq F.t) early L.late Lg ε) :
    SoundLane W F.t (F.verify sMT sFS) (UnderTwo F.wq.ext) Lg (extStr F.wq.ext prjE) εs := by
  obtain ⟨ε, hb, hs⟩ := hsnd
  obtain ⟨ℓ, hℓ⟩ := laneFor_of_snd F.written R (N := 2 ^ W.dReq F.t) (Lg := Lg) (ε := ε) hs hb
    B.wire B.isLocal (F.coherent B.laws) (UnderTwo F.wq.ext) (extStr F.wq.ext prjE)
    fun tr cms x π hu hM => extReads_extStr _ B.wire.ext B.prjE_emb hM hu
  refine ⟨ℓ, _, rfl, hℓ.of_yes fun tr cms x π' hr => ?_⟩
  rw [F.verify_eq] at hr
  obtain ⟨P1, P2, hl⟩ := runsIn_verifyB_of_strict B.wire hr
  exact ⟨_, hl⟩

/-- The verifier of a file tosses no coin and asks at most as many queries as the compiled verifier
at the joined protocol. No hypothesis. -/
theorem detBound_verifyFile (F : FileW W G Y E) (sMT sFS : ℕ) (cms : List (Dig lam)) (x : Y)
    (π : F.Prf) : DetBound (F.verify sMT sFS cms x π) (tVQB F.wq (W.dReq F.t)) := by
  rw [F.verify_eq]
  exact detBound_verifyBS sMT sFS F.t F.D.batch F.wq F.embS F.embP F.xin F.embE (W.dReq F.t) cms x π

/-- The same with the event under "there is". -/
theorem FileLaws.sound (B : FileLaws F prjE) (sMT sFS : ℕ) (R : ReadBack F.written early)
    (hsnd : ∃ ε : Err G.sh,
      Err.Below ε εs ∧ F.D.batch.SndBL (2 ^ W.dReq F.t) early L.late Lg ε) :
    SoundAt W (F.verify sMT sFS) (UnderTwo F.wq.ext) Lg (extStr F.wq.ext prjE) εs :=
  (B.lane sMT sFS R hsnd).soundAt

end File

/-! ## The list and the top: the whole instance is bound by the first query -/

/-- **All that is owed for a file** F over the rounds G, where no later query takes in more of the
instance. C: the three chains' typed descriptions, on statements "an instance and the external
strings"; early: what of an instance the first query holds. Beside the list the top takes a
read-back of what else F writes (`ReadBack`, OnBytes/TypedOracleCompiler/Joined/Bound.lean): three maps, each with a
law that is owed like the fields here: a symbol, a plain part, and what the queries hold of an
instance are read back as they were written. The number of slots is that of the leaves of the
request tree at the file's tag: 2 ^ W.dReq F.t. -/
structure FileHoles {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec} (F : FileW W G Y E)
    (C : Links G (Y × E.Str)) (prjE : Body L → Option E.Sym) (early : Y → Y) : Prop
    extends FileLaws F prjE where
  /-- THE DESCRIPTION: each chain's soundness clause -/
  knows : C.Knows
  /-- THE DESCRIPTION AND THE FILE'S DECISION: where the file's verifier accepts, none of the three
  chains in a row rejects, on what the first query holds of the instance -/
  decides : ∀ x y (τ : Tr G.sh), F.D.accept x y τ = true → (C.all.out (early x, y) τ).isSome = true

section Early
variable {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec} {F : FileW W G Y E}
  {C : Links G (Y × E.Str)} {prjE : Body L → Option E.Sym} {early : Y → Y}

/-- The three chains' clauses give round-by-round soundness of the joined protocol, in the form in
which no later query takes in more of the instance. -/
theorem FileHoles.joins (H : FileHoles F C prjE early) (N : ℕ) :
    ∃ ε : Err G.sh, Err.Below ε (C.worst N) ∧ F.D.batch.SndBL N early none (C.Lg early) ε :=
  sndBL_of_three_worst F.D.batch N early (C.Lg early) C.K₁ C.K₂ C.K₃ G.A₁ G.A₂ G.A₃
    (allKind_const (fun _ => rfl) G.c₁) ⟨H.laws.kindJ, allKind_const (fun _ => rfl) G.s₂⟩
    (allKind_const (fun _ => rfl) G.c₃) C.d₀ C.d₁ H.knows.know₁ H.knows.know₂ H.knows.know₃
    H.knows.hands₁ H.knows.hands₂ rfl HEq.rfl H.decides fun _ _ h => h

/-- **The verifier of a file, which walks its three chains, is sound, given the list**, in the case
hl: no later query takes in more of the instance. -/
theorem sound_verifyFile (F : FileW W G Y E) (sMT sFS : ℕ) (R : ReadBack F.written early)
    (H : FileHoles F C prjE early) (hl : L.late = none) :
    SoundAt W (F.verify sMT sFS) (UnderTwo F.wq.ext) (C.Lg early) (extStr F.wq.ext prjE)
      (C.worst (2 ^ W.dReq F.t)) :=
  H.toFileLaws.sound sMT sFS R (hl ▸ H.joins (2 ^ W.dReq F.t))

/-- **The same with the event in the open.** In this form several files, and further queries of a
verifier that calls them, share one event, and the hash events are paid once. -/
theorem lane_verifyFile (F : FileW W G Y E) (sMT sFS : ℕ) (R : ReadBack F.written early)
    (H : FileHoles F C prjE early) (hl : L.late = none) :
    SoundLane W F.t (F.verify sMT sFS) (UnderTwo F.wq.ext) (C.Lg early) (extStr F.wq.ext prjE)
      (C.worst (2 ^ W.dReq F.t)) :=
  H.toFileLaws.lane sMT sFS R (hl ▸ H.joins (2 ^ W.dReq F.t))

/-- **A file that lays no instance into its queries** (hx): its instance is read back from the list
of outer roots with which the verifier is called, at the calls with okX (`ReadBackC`,
OnBytes/TypedOracleCompiler/Joined/BoundC.lean); hu: at these calls the list is as `UnderTwo` asks. Given the list
`FileHoles` at early := id, the file has a lane (`SoundLaneC`, OnBytes/TypedOracleCompiler/Joined/BoundNoInst.lean),
WHATEVER `L.late` IS: so such a file can stand in one world with a file whose later query takes in
more of its instance. -/
theorem lane_verifyFile_noInst (F : FileW W G Y E) (sMT sFS : ℕ)
    {okX : List (Dig lam) → Y → Prop} (R : ReadBackC F.written id okX)
    (H : FileHoles F C prjE id) (hx : ∀ x, F.xin x = none)
    (hu : ∀ cms x, okX cms x → UnderTwo F.wq.ext cms) :
    SoundLaneC W F.t (F.verify sMT sFS) okX (C.Lg id) (extStr F.wq.ext prjE)
      (C.worst (2 ^ W.dReq F.t)) := by
  obtain ⟨ε, hb, hs⟩ := H.joins (2 ^ W.dReq F.t)
  obtain ⟨ℓ, N, hN, hℓ⟩ := soundLaneC_noInst_of_snd F.written R hx H.wire H.isLocal
    (F.coherent H.laws) (extStr F.wq.ext prjE)
    (fun tr cms x π hC hM => extReads_extStr _ H.wire.ext H.prjE_emb hM (hu cms x hC)) hs hb
  refine ⟨ℓ, N, hN, hℓ.of_yes fun tr cms x π' hr => ?_⟩
  rw [F.verify_eq] at hr
  obtain ⟨P1, P2, hl⟩ := runsIn_verifyB_of_strict H.wire hr
  exact ⟨_, hl⟩

/-- **The joined protocol as an ordinary protocol is sound round by round**, with the three chains'
errors in a row, for the language of the description: the form in which a verifier that pays for
the shared rounds itself takes a file's protocol (`InteractiveOracleProof.Sound`, Iop/InteractiveOracleProof.lean). Of the list it
uses `knows` and `decides`, at early := id. -/
theorem row_sound (D : _root_.Compile.Joined.Desc G Y E) (hk : C.Knows)
    (hd : ∀ x y (τ : Tr G.sh), D.accept x y τ = true → (C.all.out (x, y) τ).isSome = true) :
    D.proto.Sound (C.Lg id) C.err := fun x y hL =>
  Doomed.mono _ _
    (fun τ hτ => by
      cases ha : D.accept x y τ with
      | false => exact ha
      | true =>
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hd x y τ ha)
        exact absurd ⟨(), trivial⟩ (hτ u hu))
    (hk.all.toSound (x, y) fun h => hL fun ho => h.elim (fun hn => absurd ho hn) id)

/-- **The joined protocol is sound round by round, with a witness** (`BatchInteractiveOracleProof.SndBKT`,
Ior/KnowWide.lean), where no later query takes in more of the instance: the witness map is the three
extractors in a row, the errors are `Links.errN`. -/
theorem row_sndBKT (D : _root_.Compile.Joined.Desc G Y E) (hG : G.Laws) (hk : C.Knows)
    (hd : ∀ x y (τ : Tr G.sh),
      D.accept x y τ = true → (C.all.out (early x, y) τ).isSome = true) (N : ℕ) :
    D.batch.SndBKT N early none (fun x y w => C.on₀ (early x, y) → C.R₀ (early x, y) w)
      (fun x y τ => C.ext (early x, y) τ ()) (C.errN N) :=
  sndBKT_of_three D.batch N early C.K₁ C.K₂ C.K₃ G.A₁ G.A₂ G.A₃
    (allKind_const (fun _ => rfl) G.c₁) ⟨hG.kindJ, allKind_const (fun _ => rfl) G.s₂⟩
    (allKind_const (fun _ => rfl) G.c₃) C.d₀ C.d₁ hk.know₁ hk.know₂ hk.know₃ hk.hands₁ hk.hands₂
    rfl HEq.rfl hd

end Early

/-! ## The list and the top: a part of the instance is bound in a later round of the first chain -/

/-- **Owed of the description, where the query of round n takes in the rest of the instance**: the
first chain's soundness clause in the joint form (`KnowLate`, CompileK/Joined/ExtractKnow.lean): up
to round n one set of bad verifier messages serves all instances with one early part. The other
four as in `Links.Knows`. -/
structure Links.KnowsLate {G : Chains} {Y : Type} {E : ExtSpec} (C : Links G (Y × E.Str))
    (early : Y → Y) (n : ℕ) : Prop where
  /-- the first chain's soundness clause, jointly up to round n -/
  know₁ : KnowLate C.K₁ C.on₀ C.R₀ C.R₁ C.e₁ C.ε₁ early n
  /-- the second chain's -/
  know₂ : C.K₂.Know C.on₁ C.R₁ C.R₂ C.e₂ C.ε₂
  /-- the third chain's: it ends in the trivial statement -/
  know₃ : C.K₃.Know C.on₂ C.R₂ (fun _ _ => True) C.e₃ C.ε₃
  /-- what the first chain hands on is a statement of which the second's clause speaks -/
  hands₁ : ∀ a τ b, C.on₀ a → C.K₁.out a τ = some b → C.on₁ b
  /-- what the second chain hands on is a statement of which the third's clause speaks -/
  hands₂ : ∀ a τ b, C.on₁ a → C.K₂.out a τ = some b → C.on₂ b

/-- **All that is owed for a file** F over the rounds G, where the first query holds `early x` of an
instance x and the query of round n, a round of the first chain, holds x. The language and the tie
to the file's decision speak of x itself. The rest as in `FileHoles`. -/
structure FileHolesLate {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec}
    (F : FileW W G Y E) (C : Links G (Y × E.Str)) (prjE : Body L → Option E.Sym) (early : Y → Y)
    (n : ℕ) : Prop extends FileLaws F prjE where
  /-- THE DESCRIPTION: each chain's soundness clause, the first chain's jointly up to round n -/
  knows : C.KnowsLate early n
  /-- THE DESCRIPTION AND THE FILE'S DECISION: where the file's verifier accepts, none of the three
  chains in a row rejects -/
  decides : ∀ x y (τ : Tr G.sh), F.D.accept x y τ = true → (C.all.out (x, y) τ).isSome = true
  /-- THE INSTANCE: the early part of an early part is itself -/
  idem : ∀ x, early (early x) = early x
  /-- THE ROUND n is not the front round -/
  pos : 0 < n
  /-- THE ROUND n is a round of the first chain -/
  inFirst : n ≤ G.s₁.length

section Late
variable {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec} {F : FileW W G Y E}
  {C : Links G (Y × E.Str)} {prjE : Body L → Option E.Sym} {early : Y → Y} {n : ℕ}

/-- The three chains' clauses give round-by-round soundness of the joined protocol, in the form in
which the query of round n takes in the rest of the instance. -/
theorem FileHolesLate.joins (H : FileHolesLate F C prjE early n) (N : ℕ) :
    ∃ ε : Err G.sh, Err.Below ε (C.worst N) ∧ F.D.batch.SndBL N early (some n) (C.Lg id) ε :=
  sndBL_of_three_late F.D.batch N early n (C.Lg id) C.K₁ C.K₂ C.K₃ G.A₁ G.A₂ G.A₃
    (allKind_const (fun _ => rfl) G.c₁) ⟨H.laws.kindJ, allKind_const (fun _ => rfl) G.s₂⟩
    (allKind_const (fun _ => rfl) G.c₃) C.d₀ C.d₁ H.idem (Nat.le_succ_of_le H.inFirst)
    ⟨H.pos, G.ann_localTo n H.inFirst⟩ H.knows.know₁ H.knows.know₂ H.knows.know₃ H.knows.hands₁
    H.knows.hands₂ rfl HEq.rfl H.decides fun _ _ h => h

/-- **The verifier of a file, which walks its three chains, is sound, given the list**, in the case
hl: the query of round n takes in the rest of the instance. The language speaks of the whole
instance. -/
theorem sound_verifyFile_late (F : FileW W G Y E) (sMT sFS : ℕ) (R : ReadBack F.written early)
    (H : FileHolesLate F C prjE early n) (hl : L.late = some n) :
    SoundAt W (F.verify sMT sFS) (UnderTwo F.wq.ext) (C.Lg id) (extStr F.wq.ext prjE)
      (C.worst (2 ^ W.dReq F.t)) :=
  H.toFileLaws.sound sMT sFS R (hl ▸ H.joins (2 ^ W.dReq F.t))

/-- **The same with the event in the open.** -/
theorem lane_verifyFile_late (F : FileW W G Y E) (sMT sFS : ℕ) (R : ReadBack F.written early)
    (H : FileHolesLate F C prjE early n) (hl : L.late = some n) :
    SoundLane W F.t (F.verify sMT sFS) (UnderTwo F.wq.ext) (C.Lg id) (extStr F.wq.ext prjE)
      (C.worst (2 ^ W.dReq F.t)) :=
  H.toFileLaws.lane sMT sFS R (hl ▸ H.joins (2 ^ W.dReq F.t))

/-- **The joined protocol is sound round by round, with a witness**, where the query of round n, a
round of the first chain, takes in the rest of the instance: relation and witness map speak of the
whole instance. -/
theorem row_sndBKT_late (D : _root_.Compile.Joined.Desc G Y E) (hG : G.Laws)
    (hk : C.KnowsLate early n)
    (hd : ∀ x y (τ : Tr G.sh), D.accept x y τ = true → (C.all.out (x, y) τ).isSome = true)
    (idem : ∀ x, early (early x) = early x) (pos : 0 < n) (inFirst : n ≤ G.s₁.length) (N : ℕ) :
    D.batch.SndBKT N early (some n) (fun x y w => C.on₀ (x, y) → C.R₀ (x, y) w)
      (fun x y τ => C.ext (x, y) τ ()) (C.errN N) :=
  sndBKT_of_three_late D.batch N early C.K₁ C.K₂ C.K₃ G.A₁ G.A₂ G.A₃
    (allKind_const (fun _ => rfl) G.c₁) ⟨hG.kindJ, allKind_const (fun _ => rfl) G.s₂⟩
    (allKind_const (fun _ => rfl) G.c₃) C.d₀ C.d₁ n idem (Nat.le_succ_of_le inFirst)
    ⟨pos, G.ann_localTo n inFirst⟩ hk.know₁ hk.know₂ hk.know₃ hk.hands₁ hk.hands₂ rfl HEq.rfl hd

end Late

end TypedOracleCompiler.Joined
