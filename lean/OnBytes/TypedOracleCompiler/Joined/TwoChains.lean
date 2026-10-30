-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/TwoChains.lean: "the key file's protocol is sound" and "the proof file's protocol
is sound", each with its bound on the errors, from the soundness clause of each of the file's three
chains.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Joined/LandRec.lean has the two clauses on round-by-round soundness of the compiler with
a record, with the lists of errors by name. A statement over whole files asks each with its bound:
there is a list of errors, each at most εs as a probability, with which the clause holds; in a key
file the errors of the shared rounds are first counted once for each leaf of the request tree
(`Err.timesShared`, Iop/BatchSound.lean). Here both are had in this form.

Main names:
  `timesShared_app`, `timesShared_lo`, `timesShared_sh`: counting the shared rounds' errors N times:
    over two lists of rounds in a row; over local rounds nothing changes; over shared rounds all
    are counted.
  `timesShared_err`: so for a file's three chains it turns `Links.err` into `Links.errN N`.
  `below_errN`: each entry of `Links.errN N` is at most `Links.worst N`.
  `keySound_of_chains`: the key file.
  `proofSound_of_chains`, `proofSound_of_chains_late`: the proof file, where no later query takes in
    more of the instance, and where the query of round n of the first chain does.

  `keySound_at`, `proofSound_at`, `proofSound_at_late`: the same three at an interface `L` whose
    `offline` and `onlineBatch` are the two files' protocols, in L's own terms.

What is asked, by name: as in LandRec.lean (knows, decides, laws, tieT; idem, pos, inFirst); the
bound `worst`: εs lies above `Links.worst N`, the greatest error of a round as a probability, the
second chain's counted N times; and in the place of tieB:
  toW, tieR   a map from the description's witnesses to those of the relation: where the verifier
              accepts and the three extractors' value is a witness in the description's relation,
              its image is one in `L.relB`. At a statement of which the first chain's clause does
              not speak (on₀ fails) tieR asks `L.relB` outright: so on₀ must hold wherever the
              word decodes with the record to an index; where it does not, `L.relB` holds by its
              first case.

Limits: nothing here shows a hypothesis of any description. The statement over whole files for which
these forms are made lies outside this folder; no file of this folder is compiled against it. Where
Johnson/TypedOracleCompiler/Joined/FieldsAtSizes.lean [not in this library] is part of the library, it calls
`keySound_at` against it; the forms on the proof file have no such call. In the four statements on
the proof file the witness map stands under "there is": the form with the map by name is
LandRec.lean's. Where no later query takes in more of the instance, tieR must reach `L.relB` at x
from the description's relation at `early x`, with the verifier's yes at x and the transcript to
help: that this can be met where `early` drops something that the relation reads is shown at no real
file (at a small test object in
Johnson/TypedOracleCompiler/Joined/ToyEarlyTie.lean [not in this library], where that file is part of the library).
The key's shared rounds are counted 2 ^ dT times, the proof's N or `L.maxBatchSize` times: that `L.maxBatchSize` is the
number of leaves of the session's request tree is a law of the wire record, not asked here.
"Sound" of the key file is for the language "the record's seed is a collision seed of the word, or
word and record decode to something": a word and a record whose seed is a collision seed of it are
in that language.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.LandRec

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open scoped ENNReal

/-! ## The shared rounds' errors, counted N times -/

theorem timesShared_app (N : ℕ) :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ε : Err s) (δ : Err t),
      Err.timesShared N (RoundSplits.app A B) (Err.app ε δ) =
        Err.app (Err.timesShared N A ε) (Err.timesShared N B δ)
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (a, A), B, (e, ε), δ => by
    show ((match a.kind with | .lo => e | .sh => N * e),
      Err.timesShared N (RoundSplits.app A B) (Err.app ε δ)) = _
    rw [timesShared_app N A B ε δ]
    rfl

theorem timesShared_lo (N : ℕ) :
    ∀ {s : Shape} (A : RoundSplits s) (ε : Err s), RoundSplits.AllKind .lo A → Err.timesShared N A ε = ε
  | [], _, _, _ => rfl
  | _ :: _, (a, A), (e, ε), h => by
    show ((match a.kind with | .lo => e | .sh => N * e), Err.timesShared N A ε) = (e, ε)
    rw [timesShared_lo N A ε h.2, h.1]

theorem timesShared_sh (N : ℕ) :
    ∀ {s : Shape} (A : RoundSplits s) (ε : Err s),
      RoundSplits.AllKind .sh A → Err.timesShared N A ε = Err.times N ε
  | [], _, _, _ => rfl
  | _ :: _, (a, A), (e, ε), h => by
    show ((match a.kind with | .lo => e | .sh => N * e), Err.timesShared N A ε) =
      (N * e, Err.times N ε)
    rw [timesShared_sh N A ε h.2, h.1]

section Err
variable {G : Chains} {A : Type} (C : Links G A)

/-- Counting the shared rounds' errors N times turns the three chains' errors in a row into those
with the second chain's N times. -/
theorem timesShared_err (hG : G.Laws) (N : ℕ) :
    Err.timesShared N G.ann C.err = C.errN N := by
  show Err.timesShared N (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃))
    (Err.app C.ε₁ (Err.app C.ε₂ C.ε₃)) = Err.app C.ε₁ (Err.app (Err.times N C.ε₂) C.ε₃)
  rw [timesShared_app, timesShared_app,
    timesShared_lo N G.A₁ C.ε₁ (RoundSplits.allKind_const .lo _ (fun _ => rfl) G.c₁),
    timesShared_sh N G.A₂ C.ε₂ ⟨hG.kindJ, RoundSplits.allKind_const .sh _ (fun _ => rfl) G.s₂⟩,
    timesShared_lo N G.A₃ C.ε₃ (RoundSplits.allKind_const .lo _ (fun _ => rfl) G.c₃)]

/-- each entry of `Links.errN N`, as a probability, is at most `Links.worst N` -/
theorem below_errN (N : ℕ) : Err.Below (C.errN N) (C.worst N) :=
  Err.Below.app (_root_.Compile.Joined.below_worst3_fst N C.ε₁ C.ε₂ C.ε₃)
    (Err.Below.app
      (Err.Below.mono_bound (_root_.Compile.Joined.le_worst3_snd N C.ε₁ C.ε₂ C.ε₃)
        (_root_.CompileK.Joined.below_times N (_root_.Compile.Joined.below_worst C.ε₂)))
      (_root_.Compile.Joined.below_worst3_thd N C.ε₁ C.ε₂ C.ε₃))

end Err

/-! ## The two files -/

section Files
variable {I X Wn : Type} (L : HolographicProtocol I X) {G : Chains}

/-- **The key file's protocol is sound**, with each round's error at most εs, a shared round's
counted once for each of the 2 ^ dT leaves of the request tree. -/
theorem keySound_of_chains (D : Desc G L.Rec (oneExternalString L.wordLength L.Symbol))
    {C : Links G (L.Rec × (oneExternalString L.wordLength L.Symbol).Str)} (laws : G.Laws) (knows : C.Knows)
    (decides : ∀ x y (τ : Tr G.sh), D.accept x y τ = true → (C.all.out (x, y) τ).isSome = true)
    (tieT : ∀ rec y, C.Lg id rec y → L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) (dT : ℕ) {εs : ℝ≥0∞}
    (worst : C.worst (2 ^ dT) ≤ εs) :
    ∃ ε : Err D.proto.shape, Err.Below (Err.timesShared (2 ^ dT) G.ann ε) εs ∧
      D.proto.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) ε :=
  ⟨C.err, by
    rw [timesShared_err C laws]
    exact Err.Below.mono_bound worst (below_errN C _), sndT_of_file L D knows decides tieT⟩

variable (D : Desc G (X × L.Rec) (oneExternalString L.wordLength L.Symbol))
  {C : Links G ((X × L.Rec) × (oneExternalString L.wordLength L.Symbol).Str)} (Rno : I → X → Wn → Prop) (toW : C.W₀ → Wn)
  (N : ℕ) (early : X → X)

/-- **The proof file's protocol is sound, with a witness**, with each round's error at most εs,
where no later query takes in more of the instance. The witness map is the three extractors in a
row, then toW. -/
theorem proofSound_of_chains (laws : G.Laws) (knows : C.Knows)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((early x, rec), y) τ).isSome = true)
    (tieR : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.on₀ ((early x, rec), y) → C.R₀ ((early x, rec), y) (C.ext ((early x, rec), y) τ ())) →
      L.relB Rno rec x y (toW (C.ext ((early x, rec), y) τ ()))) {εs : ℝ≥0∞}
    (worst : C.worst N ≤ εs) :
    ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr D.batch.loc.shape → Wn)
      (ε : Err D.batch.loc.shape), Err.Below ε εs ∧
      ∀ rec, (D.batch.comap fun x => (x, rec)).SndBKT N early none (L.relB Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  ⟨fun a y τ => toW (C.ext ((early a.1, a.2), y) τ ()), C.errN N,
    Err.Below.mono_bound worst (below_errN C N),
    sndB_of_file L D Rno (fun a y τ => toW (C.ext ((early a.1, a.2), y) τ ())) N early laws knows
      decides tieR⟩

/-- **The same where the query of round n of the first chain takes in the rest of the instance.** -/
theorem proofSound_of_chains_late (laws : G.Laws) (n : ℕ)
    (knows : C.KnowsLate (fun a : X × L.Rec => (early a.1, a.2)) n)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((x, rec), y) τ).isSome = true)
    (idem : ∀ x, early (early x) = early x) (pos : 0 < n) (inFirst : n ≤ G.s₁.length)
    (tieR : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.on₀ ((x, rec), y) → C.R₀ ((x, rec), y) (C.ext ((x, rec), y) τ ())) →
      L.relB Rno rec x y (toW (C.ext ((x, rec), y) τ ()))) {εs : ℝ≥0∞}
    (worst : C.worst N ≤ εs) :
    ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr D.batch.loc.shape → Wn)
      (ε : Err D.batch.loc.shape), Err.Below ε εs ∧
      ∀ rec, (D.batch.comap fun x => (x, rec)).SndBKT N early (some n) (L.relB Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  ⟨fun a y τ => toW (C.ext (a, y) τ ()), C.errN N,
    Err.Below.mono_bound worst (below_errN C N),
    sndB_of_file_late L D Rno (fun a y τ => toW (C.ext (a, y) τ ())) N early laws n knows decides
      idem pos inFirst tieR⟩

end Files

/-! ## The same at an interface whose protocols are the two files' -/

section At
variable {I X Wn : Type} (L : HolographicProtocol I X) {G : Chains}

/-- **The key file's hole, at an interface L** whose `offline` is the file's protocol (hT) and at marks
aT that are the file's annotation (ha). Where both are so by unfolding: rfl and HEq.rfl. -/
theorem keySound_at (D : Desc G L.Rec (oneExternalString L.wordLength L.Symbol)) (aT : RoundSplits L.offline.shape)
    (hT : L.offline = D.proto) (ha : HEq aT G.ann) {C : Links G (L.Rec × (oneExternalString L.wordLength L.Symbol).Str)}
    (laws : G.Laws) (knows : C.Knows)
    (decides : ∀ x y (τ : Tr G.sh), D.accept x y τ = true → (C.all.out (x, y) τ).isSome = true)
    (tieT : ∀ rec y, C.Lg id rec y → L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) (dT : ℕ) {εs : ℝ≥0∞}
    (worst : C.worst (2 ^ dT) ≤ εs) :
    ∃ ε : Err L.offline.shape, Err.Below (Err.timesShared (2 ^ dT) aT ε) εs ∧
      L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) ε := by
  have key : ∀ (Q : InteractiveOracleProof L.Rec (oneExternalString L.wordLength L.Symbol)) (a : RoundSplits Q.shape), Q = D.proto → HEq a G.ann →
      ∃ ε : Err Q.shape, Err.Below (Err.timesShared (2 ^ dT) a ε) εs ∧
        Q.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) ε := by
    rintro _ a rfl h
    obtain rfl : a = G.ann := eq_of_heq h
    exact keySound_of_chains L D laws knows decides tieT dT worst
  exact key L.offline aT hT ha

variable (D : Desc G (X × L.Rec) (oneExternalString L.wordLength L.Symbol)) (hB : L.onlineBatch = D.batch)
  {C : Links G ((X × L.Rec) × (oneExternalString L.wordLength L.Symbol).Str)} (Rno : I → X → Wn → Prop) (toW : C.W₀ → Wn)

include hB in
/-- **The proof file's hole, at an interface L** whose `onlineBatch` is the file's batch protocol (hB),
where no later query takes in more of the instance (hl). -/
theorem proofSound_at (hl : L.late = none) (laws : G.Laws) (knows : C.Knows)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((L.early x, rec), y) τ).isSome = true)
    (tieR : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.on₀ ((L.early x, rec), y) →
        C.R₀ ((L.early x, rec), y) (C.ext ((L.early x, rec), y) τ ())) →
      L.relB Rno rec x y (toW (C.ext ((L.early x, rec), y) τ ()))) {εs : ℝ≥0∞}
    (worst : C.worst L.maxBatchSize ≤ εs) :
    ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (ε : Err L.onlineBatch.loc.shape), Err.Below ε εs ∧
      ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε := by
  have key : ∀ B : BatchInteractiveOracleProof (X × L.Rec) (oneExternalString L.wordLength L.Symbol), B = D.batch →
      ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr B.loc.shape → Wn) (ε : Err B.loc.shape),
        Err.Below ε εs ∧ ∀ rec, (B.comap fun x => (x, rec)).SndBKT L.maxBatchSize L.early none
          (L.relB Rno rec) (fun x y τ => wit (x, rec) y τ) ε := by
    rintro _ rfl
    exact proofSound_of_chains L D Rno toW L.maxBatchSize L.early laws knows decides tieR worst
  rw [hl]
  exact key L.onlineBatch hB

include hB in
/-- **The same where the query of round n of the first chain takes in the rest of the instance**
(hl). -/
theorem proofSound_at_late (n : ℕ) (hl : L.late = some n) (laws : G.Laws)
    (knows : C.KnowsLate (fun a : X × L.Rec => (L.early a.1, a.2)) n)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((x, rec), y) τ).isSome = true)
    (idem : ∀ x, L.early (L.early x) = L.early x) (pos : 0 < n) (inFirst : n ≤ G.s₁.length)
    (tieR : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.on₀ ((x, rec), y) → C.R₀ ((x, rec), y) (C.ext ((x, rec), y) τ ())) →
      L.relB Rno rec x y (toW (C.ext ((x, rec), y) τ ()))) {εs : ℝ≥0∞}
    (worst : C.worst L.maxBatchSize ≤ εs) :
    ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (ε : Err L.onlineBatch.loc.shape), Err.Below ε εs ∧
      ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε := by
  have key : ∀ B : BatchInteractiveOracleProof (X × L.Rec) (oneExternalString L.wordLength L.Symbol), B = D.batch →
      ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr B.loc.shape → Wn) (ε : Err B.loc.shape),
        Err.Below ε εs ∧ ∀ rec, (B.comap fun x => (x, rec)).SndBKT L.maxBatchSize L.early (some n)
          (L.relB Rno rec) (fun x y τ => wit (x, rec) y τ) ε := by
    rintro _ rfl
    exact proofSound_of_chains_late L D Rno toW L.maxBatchSize L.early laws n knows decides idem pos inFirst
      tieR worst
  rw [hl]
  exact key L.onlineBatch hB

end At

end TypedOracleCompiler.Joined
