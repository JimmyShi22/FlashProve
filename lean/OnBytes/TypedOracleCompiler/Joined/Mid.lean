-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Mid.lean: "the proof file's protocol is sound", where the soundness clause of the
file's second chain is given in the form for the statements of a batch, with its own list of errors.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Joined/TwoChains.lean has this statement from clauses on one slot, and counts the second
chain's errors itself: all of them once for each slot. The library's chains of links for a batch
(`IOR.KnowB`, Ior/BatchSeq.lean) come with lists of errors in which each link says what is counted
how often. Here the second chain's clause is taken in that form (`KnowJ`,
CompileK/Joined/ExtractKnow.lean; at the reduction of an IOR it is `IOR.KnowB`: `knowJ_iff_knowB`,
CompileK/Joined/BatchMid.lean), and its list as it is.

Main names:
  `Links.KnowsMid C N key`: THE LIST: the clause `Know` of the first and of the third chain; `mid`:
    the second chain's clause for the vectors of statements with one key; the two hand-overs;
    `oneKey`: for slots with one external string the statements that the first chain hands on have
    one key.
  `row_sndBKT_mid`: then the joined batch protocol is sound round by round, with a witness, where no
    later query takes in more of the instance; the errors are `Links.err`: the three lists in a row.
  `sndB_of_file_mid`: the clause `sndB` of `SoundAtR` (Hiop/RecInterface.lean), record by record.
  `proofSound_of_chains_mid`, `proofSound_at_mid`: the proof file's statement with its bound.

The list is asked record by record: of the description with the record rec in all slots. So the key
may read the record.

Limits: nothing here shows a hypothesis of any description. Only the case in which no later query
takes in more of the instance. The relation of the description speaks of `early x` alone: what
`early` drops is reached only through tieB | tieR, from the verifier's yes at x and the transcript.
At a description whose conditions on₀, on₁, on₂ hold of no statement, `know₁`, `know₃`, the two
hand-overs and the first half of `mid` hold emptily (the bound on `mid`'s sets of bad values and
`oneKey` are still asked); tieB | tieR then ask their conclusion from the verifier's yes alone.
Nothing here says that `worstMid` is below 1. Other files of the library use `KnowsMid`, `worstMid`
and `below_errMid` of this file; no other file uses its four theorems on the protocol yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.TwoChains
import CompileK.Joined.BatchMid

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc worst below_worst)
open _root_.CompileK.Joined (KnowJ OneKey₁ allKind_const sndBKT_of_mid)
open scoped ENNReal

/-- **All that is owed of a description whose second chain has a clause for the statements of a
batch.** N: the number of slots; key: the key of a statement that the first chain hands on. -/
structure Links.KnowsMid {G : Chains} {Y : Type} {E : ExtSpec} (C : Links G (Y × E.Str)) (N : ℕ)
    {κ : Type} (key : C.A₁ → κ) : Prop where
  /-- the first chain's soundness clause -/
  know₁ : C.K₁.Know C.on₀ C.R₀ C.R₁ C.e₁ C.ε₁
  /-- the second chain's, for the vectors of statements with one key, with its own list of errors -/
  mid : KnowJ C.K₂ G.A₂ N (IOR.SameKey key) C.on₁ C.R₁ C.R₂ C.e₂ C.ε₂
  /-- the third chain's -/
  know₃ : C.K₃.Know C.on₂ C.R₂ (fun _ _ => True) C.e₃ C.ε₃
  hands₁ : ∀ a τ b, C.on₀ a → C.K₁.out a τ = some b → C.on₁ b
  hands₂ : ∀ a τ b, C.on₁ a → C.K₂.out a τ = some b → C.on₂ b
  /-- for slots with one external string the statements that the first chain hands on have one key
  -/
  oneKey : OneKey₁ N C.K₁ G.A₁ key

/-- the greatest error of a round, as a probability, of the three lists as they are -/
noncomputable def Links.worstMid {G : Chains} {A : Type} (C : Links G A) : ℝ≥0∞ :=
  max (_root_.Compile.Joined.worst C.ε₁)
    (max (_root_.Compile.Joined.worst C.ε₂) (_root_.Compile.Joined.worst C.ε₃))

theorem below_errMid {G : Chains} {A : Type} (C : Links G A) : Err.Below C.err C.worstMid :=
  Err.Below.app (Err.Below.mono_bound (le_max_left _ _) (below_worst C.ε₁))
    (Err.Below.app
      (Err.Below.mono_bound (le_trans (le_max_left _ _) (le_max_right _ _)) (below_worst C.ε₂))
      (Err.Below.mono_bound (le_trans (le_max_right _ _) (le_max_right _ _)) (below_worst C.ε₃)))

/-- **The joined protocol is sound round by round, with a witness**, where no later query takes in
more of the instance: the errors are the three lists in a row, as they are. -/
theorem row_sndBKT_mid {G : Chains} {Y : Type} {E : ExtSpec} {C : Links G (Y × E.Str)} {N : ℕ}
    {κ : Type} {key : C.A₁ → κ} (D : Desc G Y E) (early : Y → Y) (hk : C.KnowsMid N key)
    (hd : ∀ x y (τ : Tr G.sh),
      D.accept x y τ = true → (C.all.out (early x, y) τ).isSome = true) :
    D.batch.SndBKT N early none (fun x y w => C.on₀ (early x, y) → C.R₀ (early x, y) w)
      (fun x y τ => C.ext (early x, y) τ ()) C.err :=
  sndBKT_of_mid D.batch N early C.K₁ C.K₂ C.K₃ G.A₁ G.A₂ G.A₃ (allKind_const (fun _ => rfl) G.c₁)
    (allKind_const (fun _ => rfl) G.c₃) C.d₀ C.d₁ hk.know₁ key hk.mid hk.know₃ hk.hands₁ hk.hands₂
    hk.oneKey rfl HEq.rfl hd

section Files
variable {I X Wn : Type} (L : HolographicProtocol I X) {G : Chains} (D : Desc G (X × L.Rec) (oneExternalString L.wordLength L.Symbol))
  {C : Links G ((X × L.Rec) × (oneExternalString L.wordLength L.Symbol).Str)} {κ : Type} {key : C.A₁ → κ}
  (Rno : I → X → Wn → Prop)

/-- **The clause on a session's protocol of the compiler with a record**, for each record. -/
theorem sndB_of_file_mid (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr G.sh → Wn) (N : ℕ)
    (early : X → X)
    (knows : ∀ rec, (C.comap fun x : X => (x, rec)).KnowsMid N key)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((early x, rec), y) τ).isSome = true)
    (tieB : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.on₀ ((early x, rec), y) → C.R₀ ((early x, rec), y) (C.ext ((early x, rec), y) τ ())) →
      L.relB Rno rec x y (wit (x, rec) y τ)) (rec : L.Rec) :
    (D.batch.comap fun x => (x, rec)).SndBKT N early none (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) C.err :=
  sndBKT_conseq X C.W₀ Wn _ (D.batch.comap fun x => (x, rec)) N early none _ _ _ _ _
    (fun x y τ ha h => tieB x rec y τ ha h)
    (sndBKT_of_mid (D.batch.comap fun x => (x, rec)) N early
      (C.comap fun x : X => (x, rec)).K₁ (C.comap fun x : X => (x, rec)).K₂
      (C.comap fun x : X => (x, rec)).K₃ G.A₁ G.A₂ G.A₃ (allKind_const (fun _ => rfl) G.c₁)
      (allKind_const (fun _ => rfl) G.c₃) C.d₀ C.d₁ (knows rec).know₁ key (knows rec).mid
      (knows rec).know₃ (knows rec).hands₁ (knows rec).hands₂ (knows rec).oneKey rfl HEq.rfl
      fun x y τ ha => decides x rec y τ ha)

variable (toW : C.W₀ → Wn)

/-- **The proof file's protocol is sound, with a witness**, with each round's error at most εs. The
witness map is the three extractors in a row, then toW. -/
theorem proofSound_of_chains_mid (N : ℕ) (early : X → X)
    (knows : ∀ rec, (C.comap fun x : X => (x, rec)).KnowsMid N key)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((early x, rec), y) τ).isSome = true)
    (tieR : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.on₀ ((early x, rec), y) → C.R₀ ((early x, rec), y) (C.ext ((early x, rec), y) τ ())) →
      L.relB Rno rec x y (toW (C.ext ((early x, rec), y) τ ()))) {εs : ℝ≥0∞}
    (worst : C.worstMid ≤ εs) :
    ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr D.batch.loc.shape → Wn)
      (ε : Err D.batch.loc.shape), Err.Below ε εs ∧
      ∀ rec, (D.batch.comap fun x => (x, rec)).SndBKT N early none (L.relB Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  ⟨fun a y τ => toW (C.ext ((early a.1, a.2), y) τ ()), C.err,
    Err.Below.mono_bound worst (below_errMid C),
    sndB_of_file_mid L D Rno (fun a y τ => toW (C.ext ((early a.1, a.2), y) τ ())) N early knows
      decides tieR⟩

/-- **The proof file's hole, at an interface L** whose `onlineBatch` is the file's batch protocol (hB),
where no later query takes in more of the instance (hl). -/
theorem proofSound_at_mid (hB : L.onlineBatch = D.batch) (hl : L.late = none)
    (knows : ∀ rec, (C.comap fun x : X => (x, rec)).KnowsMid L.maxBatchSize key)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((L.early x, rec), y) τ).isSome = true)
    (tieR : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.on₀ ((L.early x, rec), y) →
        C.R₀ ((L.early x, rec), y) (C.ext ((L.early x, rec), y) τ ())) →
      L.relB Rno rec x y (toW (C.ext ((L.early x, rec), y) τ ()))) {εs : ℝ≥0∞}
    (worst : C.worstMid ≤ εs) :
    ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (ε : Err L.onlineBatch.loc.shape), Err.Below ε εs ∧
      ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε := by
  have key' : ∀ B : BatchInteractiveOracleProof (X × L.Rec) (oneExternalString L.wordLength L.Symbol), B = D.batch →
      ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr B.loc.shape → Wn) (ε : Err B.loc.shape),
        Err.Below ε εs ∧ ∀ rec, (B.comap fun x => (x, rec)).SndBKT L.maxBatchSize L.early none
          (L.relB Rno rec) (fun x y τ => wit (x, rec) y τ) ε := by
    rintro _ rfl
    exact proofSound_of_chains_mid L D Rno toW L.maxBatchSize L.early knows decides tieR worst
  rw [hl]
  exact key' L.onlineBatch hB

end Files

end TypedOracleCompiler.Joined
