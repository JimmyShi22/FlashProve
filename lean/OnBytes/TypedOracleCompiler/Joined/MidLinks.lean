-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/MidLinks.lean: "the proof file's protocol is sound", where each of the file's
three chains is a link with keys for the statements of a batch, with its own list of errors.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Joined/Mid.lean takes the second chain's clause in the form for a batch. The library's
test for linear claims on the stored table for a batch runs across all three chains of a file: its
first steps stand at the end of the first chain, its shared part is the second chain, its last test
the third. So here all three chains are links with keys (`LinkJ`, OnBytes/TypedOracleCompiler/Joined/LinkJ.lean):
the first from the external string to a key k₁, the second from k₁ to k₂, the third from k₂ on.

Main names:
  `LinkJ.silentLo`, `LinkJ.silentSh`: a round that no step reads, as a link: the key is carried, the
    error is 0 (under shared verifier messages: N times 0).
  `Links.KnowsJ C N k₁ k₂`: THE LIST: the three links and the two hand-overs.
  `Links.KnowsMid.toJ`: the list of Mid.lean gives it.
  `row_sndBKT_links`, `sndB_of_file_links`, `proofSound_of_chains_links`, `proofSound_at_links`: as
    in Mid.lean. The errors are `Links.err`: the three lists in a row, as they are.

The list is asked record by record: of the description with the record rec in all slots. So the keys
may read the record.

Limits: nothing here shows a hypothesis of any description. Only the case in which no later query
takes in more of the instance. The relation of the description speaks of `early x` alone: what
`early` drops is reached only through tieB | tieR, from the verifier's yes at x and the transcript.
In `proofSound_of_chains_links` and `proofSound_at_links` the witness map stands under "there is":
the form with the map by name is `sndB_of_file_links`.
Nothing here says that `worstMid` (OnBytes/TypedOracleCompiler/Joined/Mid.lean) is below 1. All of a link's content
hangs on its keys (the Limits of OnBytes/TypedOracleCompiler/Joined/LinkJ.lean).
No other file of the library uses `LinkJ.silentLo`, `LinkJ.silentSh` or `Links.KnowsMid.toJ` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Mid
import OnBytes.TypedOracleCompiler.Joined.LinkJ
import CompileK.Joined.Silent

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (KnowJ OneKey₁ allKind_const knowJ_lo silentAt silentAt_know)
open scoped ENNReal

/-! ## A round that no step reads -/

section Silent
variable {A κ WA : Type}

/-- A local round that no step reads, as a link: the key is carried; the error is 0. -/
theorem LinkJ.silentLo (r : Round) (a : RAnn r) (ha : a.kind = .lo) (N : ℕ) (key : A → κ)
    (on : A → Prop) (R : A → WA → Prop) :
    LinkJ (silentAt A r) ((a, PUnit.unit) : RoundSplits [r]) N key key on R R (fun _ _ w => w) (0, ()) :=
  LinkJ.ofLocal (K := silentAt A r) (An := ((a, PUnit.unit) : RoundSplits [r])) ⟨ha, trivial⟩ N
    (silentAt_know r on R) id fun _ _ _ hb => congrArg key (Option.some.inj hb).symm

/-- The same under a shared verifier message: N times 0. -/
theorem LinkJ.silentSh (r : Round) (a : RAnn r) (ha : a.kind = .sh) (N : ℕ) (key : A → κ)
    (on : A → Prop) (R : A → WA → Prop) :
    LinkJ (silentAt A r) ((a, PUnit.unit) : RoundSplits [r]) N key key on R R (fun _ _ w => w)
      (Err.times N (0, ())) :=
  LinkJ.ofShared (K := silentAt A r) (An := ((a, PUnit.unit) : RoundSplits [r])) ⟨ha, trivial⟩ N
    (silentAt_know r on R) id fun _ _ _ hb => congrArg key (Option.some.inj hb).symm

end Silent

/-! ## The list -/

/-- **All that is owed of a description whose three chains are links with keys.** N: the number of
slots; k₁, k₂: the keys of the statements that the first and the second chain hand on. -/
structure Links.KnowsJ {G : Chains} {Y : Type} {E : ExtSpec} (C : Links G (Y × E.Str)) (N : ℕ)
    {κ₁ κ₂ : Type} (k₁ : C.A₁ → κ₁) (k₂ : C.A₂ → κ₂) : Prop where
  /-- the first chain: from the external string to k₁ -/
  l₁ : LinkJ C.K₁ G.A₁ N (Prod.snd : Y × E.Str → E.Str) k₁ C.on₀ C.R₀ C.R₁ C.e₁ C.ε₁
  /-- the second chain: from k₁ to k₂ -/
  l₂ : LinkJ C.K₂ G.A₂ N k₁ k₂ C.on₁ C.R₁ C.R₂ C.e₂ C.ε₂
  /-- the third chain: from k₂ on -/
  l₃ : LinkJ C.K₃ G.A₃ N k₂ (fun _ : Unit => ()) C.on₂ C.R₂ (fun _ _ => True) C.e₃ C.ε₃
  hands₁ : ∀ a τ b, C.on₀ a → C.K₁.out a τ = some b → C.on₁ b
  hands₂ : ∀ a τ b, C.on₁ a → C.K₂.out a τ = some b → C.on₂ b

/-- The list of Mid.lean gives this one, at the trivial key behind the second chain. -/
theorem Links.KnowsMid.toJ {G : Chains} {Y : Type} {E : ExtSpec} {C : Links G (Y × E.Str)} {N : ℕ}
    {κ : Type} {key : C.A₁ → κ} (h : C.KnowsMid N key) :
    C.KnowsJ N key (fun _ : C.A₂ => ()) where
  l₁ := ⟨(knowJ_lo (allKind_const (fun _ => rfl) G.c₁) N h.know₁).adm fun _ _ => trivial, h.oneKey⟩
  l₂ := ⟨h.mid, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  l₃ := ⟨(knowJ_lo (allKind_const (fun _ => rfl) G.c₃) N h.know₃).adm fun _ _ => trivial,
    fun _ _ _ _ _ _ _ _ _ => rfl⟩
  hands₁ := h.hands₁
  hands₂ := h.hands₂

/-- **The joined protocol is sound round by round, with a witness**, where no later query takes in
more of the instance: the errors are the three lists in a row, as they are. -/
theorem row_sndBKT_links {G : Chains} {Y : Type} {E : ExtSpec} {C : Links G (Y × E.Str)} {N : ℕ}
    {κ₁ κ₂ : Type} {k₁ : C.A₁ → κ₁} {k₂ : C.A₂ → κ₂} (D : Desc G Y E) (early : Y → Y)
    (hk : C.KnowsJ N k₁ k₂)
    (hd : ∀ x y (τ : Tr G.sh),
      D.accept x y τ = true → (C.all.out (early x, y) τ).isSome = true) :
    D.batch.SndBKT N early none (fun x y w => C.on₀ (early x, y) → C.R₀ (early x, y) w)
      (fun x y τ => C.ext (early x, y) τ ()) C.err :=
  sndBKT_of_links D.batch N early C.K₁ C.K₂ C.K₃ G.A₁ G.A₂ G.A₃ C.d₀ C.d₁ k₁ k₂ hk.l₁ hk.l₂ hk.l₃
    hk.hands₁ hk.hands₂ rfl HEq.rfl hd

section Files
variable {I X Wn : Type} (L : HolographicProtocol I X) {G : Chains} (D : Desc G (X × L.Rec) (oneExternalString L.wordLength L.Symbol))
  {C : Links G ((X × L.Rec) × (oneExternalString L.wordLength L.Symbol).Str)} {κ₁ κ₂ : Type} {k₁ : C.A₁ → κ₁}
  {k₂ : C.A₂ → κ₂} (Rno : I → X → Wn → Prop)

/-- **The clause on a session's protocol of the compiler with a record**, for each record. -/
theorem sndB_of_file_links (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr G.sh → Wn) (N : ℕ)
    (early : X → X)
    (knows : ∀ rec, (C.comap fun x : X => (x, rec)).KnowsJ N k₁ k₂)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((early x, rec), y) τ).isSome = true)
    (tieB : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.on₀ ((early x, rec), y) → C.R₀ ((early x, rec), y) (C.ext ((early x, rec), y) τ ())) →
      L.relB Rno rec x y (wit (x, rec) y τ)) (rec : L.Rec) :
    (D.batch.comap fun x => (x, rec)).SndBKT N early none (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) C.err :=
  sndBKT_conseq X C.W₀ Wn _ (D.batch.comap fun x => (x, rec)) N early none _ _ _ _ _
    (fun x y τ ha h => tieB x rec y τ ha h)
    (sndBKT_of_links (D.batch.comap fun x => (x, rec)) N early
      (C.comap fun x : X => (x, rec)).K₁ (C.comap fun x : X => (x, rec)).K₂
      (C.comap fun x : X => (x, rec)).K₃ G.A₁ G.A₂ G.A₃ C.d₀ C.d₁ k₁ k₂ (knows rec).l₁
      (knows rec).l₂ (knows rec).l₃ (knows rec).hands₁ (knows rec).hands₂ rfl HEq.rfl
      fun x y τ ha => decides x rec y τ ha)

variable (toW : C.W₀ → Wn)

/-- **The proof file's protocol is sound, with a witness**, with each round's error at most εs. The
witness map is the three extractors in a row, then toW. Under knows, decides, tieR and worst, which
are hypotheses. -/
theorem proofSound_of_chains_links (N : ℕ) (early : X → X)
    (knows : ∀ rec, (C.comap fun x : X => (x, rec)).KnowsJ N k₁ k₂)
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
    sndB_of_file_links L D Rno (fun a y τ => toW (C.ext ((early a.1, a.2), y) τ ())) N early knows
      decides tieR⟩

/-- **The proof file's hole, at an interface L** whose `onlineBatch` is the file's batch protocol (hB),
where no later query takes in more of the instance (hl). -/
theorem proofSound_at_links (hB : L.onlineBatch = D.batch) (hl : L.late = none)
    (knows : ∀ rec, (C.comap fun x : X => (x, rec)).KnowsJ L.maxBatchSize k₁ k₂)
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
    exact proofSound_of_chains_links L D Rno toW L.maxBatchSize L.early knows decides tieR worst
  rw [hl]
  exact key' L.onlineBatch hB

end Files

end TypedOracleCompiler.Joined
