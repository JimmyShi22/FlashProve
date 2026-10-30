-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/LandRec.lean: from the typed descriptions of a key file and of a proof file, each
three joined chains, to the premise on round-by-round soundness of the compiler with a record.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The compiler with a record takes an interface `L : Iop.HolographicProtocol I X` (Hiop/RecInterface.lean) and asks of
it `L.SoundAtR`: among its clauses, `sndT`, plain round-by-round soundness of `L.offline`, the protocol
of a key; and `sndB`, for each record, round-by-round soundness with a witness of `L.onlineBatch`, the
protocol of a session, with this record in all slots. Here both are had where `L.offline` and `L.onlineBatch`
are the joined protocols of two files (`Desc`, Compile/Joined/Types.lean), from the soundness clause
of each chain (`Links.Knows`, `Links.KnowsLate`, OnBytes/TypedOracleCompiler/Joined/Top.lean).

Main names:
  `Links.comap C f`: the description C with the instance read through f; `Knows.comap`,
    `KnowsLate.comap`: the clauses carry over.
  `sndT_of_file`: the key: `InteractiveOracleProof.Sound` of the joined protocol for the language of `sndT`.
  `sndB_of_file`, `sndB_of_file_late`: the proof: `SndBKT` of the joined protocol at each record,
    for the relation and the witness map of `sndB`; where no later query takes in more of the
    instance, and where the query of round n of the first chain does.
  `soundAtR_of_files`, `soundAtR_of_files_late`: `L.SoundAtR`.

What is asked, by name, beside the chains' clauses:
  decides   where a file's verifier accepts, none of its three chains in a row rejects;
  tieT      a key's statement in the language of its description is in the language of `sndT`;
  tieB      where the session's verifier accepts and the three extractors in a row give a witness in
            the description's relation, the witness map gives one in `L.relB`. The witness map
            wit is a letter: whoever uses the theorem makes it from the three extractors;
  hT, hB    `L.offline` and `L.onlineBatch` are the two files' protocols. Where they are so by unfolding, both
            are rfl and the casts in the conclusion are the identity;
  noneColl, rcd, sndL   three clauses of `SoundAtR` that do not speak of the two files: they are
            handed through as they stand.
  laws      the laws of the joining round's annotation in the proof file's chains (`Chains.Laws`):
            it is a shared round, and its data fit together;
  hl        which case it is: `L.late` is none, or some n;
  idem, pos, inFirst   in the late forms: `early` is idempotent; n is not 0 and is at most the
            number of the first chain's rounds.

Limits: nothing here shows a hypothesis of any description. The errors of the key are the three
chains' in a row, uncounted: the compiler with a record counts its shared rounds itself. Those of
the proof have the second chain's N times.
Where no later query takes in more of the instance, the description's relation speaks of `early x`
alone: what `early` drops is reached only through tieB, from the verifier's yes at x and the
transcript. At a statement of which the first chain's clause does not speak (on₀ fails) tieB asks
`L.relB` outright.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Top
import Hiop.RecInterface

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (AllKind allKind_const KnowLate sndBKT_of_three sndBKT_of_three_late)

/-! ## A description with the instance read through a map -/

section Comap
variable {G : Chains} {Y Y' S : Type}

/-- the description C with the instance read through f -/
def Links.comap (C : Links G (Y × S)) (f : Y' → Y) : Links G (Y' × S) where
  A₁ := C.A₁
  A₂ := C.A₂
  W₀ := C.W₀
  W₁ := C.W₁
  W₂ := C.W₂
  out₁ := fun a => C.out₁ (f a.1, a.2)
  out₂ := C.out₂
  out₃ := C.out₃
  on₀ := fun a => C.on₀ (f a.1, a.2)
  on₁ := C.on₁
  on₂ := C.on₂
  R₀ := fun a => C.R₀ (f a.1, a.2)
  R₁ := C.R₁
  R₂ := C.R₂
  e₁ := fun a => C.e₁ (f a.1, a.2)
  e₂ := C.e₂
  e₃ := C.e₃
  ε₁ := C.ε₁
  ε₂ := C.ε₂
  ε₃ := C.ε₃
  d₀ := C.d₀
  d₁ := C.d₁

theorem Links.Knows.comap {C : Links G (Y × S)} (h : C.Knows) (f : Y' → Y) : (C.comap f).Knows :=
  ⟨fun a ha => h.know₁ (f a.1, a.2) ha, h.know₂, h.know₃,
    fun a τ b ha hb => h.hands₁ (f a.1, a.2) τ b ha hb, h.hands₂⟩

end Comap

theorem Links.KnowsLate.comap {G : Chains} {Y Y' : Type} {E : ExtSpec}
    {C : Links G (Y × E.Str)} {early : Y → Y} {n : ℕ} (h : C.KnowsLate early n) (f : Y' → Y)
    (early' : Y' → Y') (hf : ∀ x, early (f x) = f (early' x)) :
    (C.comap f).KnowsLate early' n :=
  ⟨fun x₀ y =>
      JDoomed.comap (Φ := {x : Y // early x = f x₀}) (Ψ := {x : Y' // early' x = x₀})
        (fun ψ => ⟨f ψ.1, by rw [hf, ψ.2]⟩) n G.c₁ C.ε₁ (h.know₁ (f x₀) y),
    h.know₂, h.know₃, fun a τ b ha hb => h.hands₁ (f a.1, a.2) τ b ha hb, h.hands₂⟩

/-! ## The two clauses -/

section Clauses
variable {I X Wn : Type} (L : HolographicProtocol I X)

/-- **The key.** Plain round-by-round soundness of the joined protocol of a key file, for the
language of `SoundAtR.sndT`, with the three chains' errors in a row. -/
theorem sndT_of_file {G : Chains} (D : Desc G L.Rec (oneExternalString L.wordLength L.Symbol))
    {C : Links G (L.Rec × (oneExternalString L.wordLength L.Symbol).Str)} (knows : C.Knows)
    (decides : ∀ x y (τ : Tr G.sh), D.accept x y τ = true → (C.all.out (x, y) τ).isSome = true)
    (tieT : ∀ rec y, C.Lg id rec y → L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) :
    D.proto.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) C.err :=
  fun rec y hL => row_sound D knows decides rec y fun h => hL (tieT rec y h)

variable {G : Chains} (D : Desc G (X × L.Rec) (oneExternalString L.wordLength L.Symbol))
  {C : Links G ((X × L.Rec) × (oneExternalString L.wordLength L.Symbol).Str)} (Rno : I → X → Wn → Prop)
  (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr G.sh → Wn) (N : ℕ) (early : X → X)

/-- **The proof, where no later query takes in more of the instance.** For each record:
round-by-round soundness with a witness of the joined protocol of a proof file with this record in
all slots, for the relation and the witness map of `SoundAtR.sndB`. -/
theorem sndB_of_file (laws : G.Laws) (knows : C.Knows)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((early x, rec), y) τ).isSome = true)
    (tieB : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.on₀ ((early x, rec), y) → C.R₀ ((early x, rec), y) (C.ext ((early x, rec), y) τ ())) →
      L.relB Rno rec x y (wit (x, rec) y τ)) (rec : L.Rec) :
    (D.batch.comap fun x => (x, rec)).SndBKT N early none (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) (C.errN N) := by
  have hk := knows.comap fun x : X => (x, rec)
  refine sndBKT_conseq X C.W₀ Wn _ (D.batch.comap fun x => (x, rec)) N early none _ _ _ _ _
    (fun x y τ ha h => tieB x rec y τ ha h)
    (sndBKT_of_three (D.batch.comap fun x => (x, rec)) N early
      (C.comap fun x : X => (x, rec)).K₁ (C.comap fun x : X => (x, rec)).K₂
      (C.comap fun x : X => (x, rec)).K₃ G.A₁ G.A₂ G.A₃
      (allKind_const (fun _ => rfl) G.c₁) ⟨laws.kindJ, allKind_const (fun _ => rfl) G.s₂⟩
      (allKind_const (fun _ => rfl) G.c₃) C.d₀ C.d₁ hk.know₁ hk.know₂ hk.know₃ hk.hands₁ hk.hands₂
      rfl HEq.rfl fun x y τ ha => decides x rec y τ ha)

/-- **The proof, where the query of round n of the first chain takes in the rest of the instance.**
The tie to the file's decision, the relation and the witness map speak of the whole instance. -/
theorem sndB_of_file_late (laws : G.Laws) (n : ℕ)
    (knows : C.KnowsLate (fun a : X × L.Rec => (early a.1, a.2)) n)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((x, rec), y) τ).isSome = true)
    (idem : ∀ x, early (early x) = early x) (pos : 0 < n) (inFirst : n ≤ G.s₁.length)
    (tieB : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.on₀ ((x, rec), y) → C.R₀ ((x, rec), y) (C.ext ((x, rec), y) τ ())) →
      L.relB Rno rec x y (wit (x, rec) y τ)) (rec : L.Rec) :
    (D.batch.comap fun x => (x, rec)).SndBKT N early (some n) (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) (C.errN N) := by
  have hk := knows.comap (fun x : X => (x, rec)) early fun _ => rfl
  refine sndBKT_conseq X C.W₀ Wn _ (D.batch.comap fun x => (x, rec)) N early (some n) _ _ _ _ _
    (fun x y τ ha h => tieB x rec y τ ha h)
    (sndBKT_of_three_late (D.batch.comap fun x => (x, rec)) N early
      (C.comap fun x : X => (x, rec)).K₁ (C.comap fun x : X => (x, rec)).K₂
      (C.comap fun x : X => (x, rec)).K₃ G.A₁ G.A₂ G.A₃
      (allKind_const (fun _ => rfl) G.c₁) ⟨laws.kindJ, allKind_const (fun _ => rfl) G.s₂⟩
      (allKind_const (fun _ => rfl) G.c₃) C.d₀ C.d₁ n idem (Nat.le_succ_of_le inFirst)
      ⟨pos, G.ann_localTo n inFirst⟩ hk.know₁ hk.know₂ hk.know₃ hk.hands₁ hk.hands₂
      rfl HEq.rfl fun x y τ ha => decides x rec y τ ha)

end Clauses

/-! ## The premise of the compiler with a record -/

section Assembly
variable {I X Wn : Type} (L : HolographicProtocol I X)

/-- a clause on a protocol that is equal to P₀, from the clause on P₀ -/
theorem sound_cast {Y : Type} {E : ExtSpec} {P₀ : InteractiveOracleProof Y E} {Lg : Y → E.Str → Prop}
    {ε : Err P₀.shape} (h : P₀.Sound Lg ε) :
    ∀ (P : InteractiveOracleProof Y E) (e : P = P₀),
      P.Sound Lg (cast (congrArg (fun Q => Err Q.shape) e.symm) ε) := by
  rintro _ rfl
  exact h

/-- the same for the clause with a witness, at each value of a parameter of the instance -/
theorem sndBKT_cast {Y Z W : Type} {E : ExtSpec} {Q₀ : BatchInteractiveOracleProof (Y × Z) E} {N : ℕ}
    {early : Y → Y} {late : Option ℕ} {R : Z → Y → E.Str → W → Prop}
    {wit : Y × Z → E.Str → Tr Q₀.loc.shape → W} {ε : Err Q₀.loc.shape}
    (h : ∀ z,
      (Q₀.comap fun x => (x, z)).SndBKT N early late (R z) (fun x y τ => wit (x, z) y τ) ε) :
    ∀ (Q : BatchInteractiveOracleProof (Y × Z) E) (e : Q = Q₀) (z : Z),
      (Q.comap fun x => (x, z)).SndBKT N early late (R z)
        (fun x y τ => wit (x, z) y (cast (congrArg (fun Q => Tr Q.loc.shape) e) τ))
        (cast (congrArg (fun Q => Err Q.loc.shape) e.symm) ε) := by
  rintro _ rfl z
  exact h z

variable {GT GB : Chains} (DT : Desc GT L.Rec (oneExternalString L.wordLength L.Symbol))
  (DB : Desc GB (X × L.Rec) (oneExternalString L.wordLength L.Symbol)) {CT : Links GT (L.Rec × (oneExternalString L.wordLength L.Symbol).Str)}
  {CB : Links GB ((X × L.Rec) × (oneExternalString L.wordLength L.Symbol).Str)} (Rno : I → X → Wn → Prop)
  (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr GB.sh → Wn) (eR : ℕ) (εL : Err L.link.shape)
  (hT : L.offline = DT.proto) (hB : L.onlineBatch = DB.batch)

/-- **The premise of the compiler with a record, from the descriptions of a key file and of a proof
file**, where no later query takes in more of the instance (hl). -/
theorem soundAtR_of_files (hl : L.late = none)
    (noneColl : ∀ y (rec : L.Rec), L.hasCollisionAt y rec.1 → L.decodeIndex y rec = none)
    (rcd : ∀ y, Prob.cnt (fun s => L.hasCollisionAt y s) ≤ eR)
    (sndL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (knowsT : CT.Knows)
    (decidesT : ∀ x y (τ : Tr GT.sh),
      DT.accept x y τ = true → (CT.all.out (x, y) τ).isSome = true)
    (tieT : ∀ rec y, CT.Lg id rec y → L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none)
    (lawsB : GB.Laws) (knowsB : CB.Knows)
    (decidesB : ∀ x rec y (τ : Tr GB.sh), DB.accept (x, rec) y τ = true →
      (CB.all.out ((L.early x, rec), y) τ).isSome = true)
    (tieB : ∀ x rec y (τ : Tr GB.sh), DB.accept (x, rec) y τ = true →
      (CB.on₀ ((L.early x, rec), y) →
        CB.R₀ ((L.early x, rec), y) (CB.ext ((L.early x, rec), y) τ ())) →
      L.relB Rno rec x y (wit (x, rec) y τ)) :
    L.SoundAtR Rno
      (fun a y τ => wit a y (cast (congrArg (fun Q : BatchInteractiveOracleProof _ _ => Tr Q.loc.shape) hB) τ)) eR
      (cast (congrArg (fun Q : InteractiveOracleProof _ _ => Err Q.shape) hT.symm) CT.err) εL
      (cast (congrArg (fun Q : BatchInteractiveOracleProof _ _ => Err Q.loc.shape) hB.symm) (CB.errN L.maxBatchSize)) :=
  ⟨noneColl, rcd, sound_cast (sndT_of_file L DT knowsT decidesT tieT) L.offline hT, sndL,
    fun rec => hl ▸ sndBKT_cast (R := L.relB Rno)
      (sndB_of_file L DB Rno wit L.maxBatchSize L.early lawsB knowsB decidesB tieB) L.onlineBatch hB rec⟩

/-- **The same where the query of round n of the proof's first chain takes in the rest of the
instance** (hl). -/
theorem soundAtR_of_files_late (n : ℕ) (hl : L.late = some n)
    (noneColl : ∀ y (rec : L.Rec), L.hasCollisionAt y rec.1 → L.decodeIndex y rec = none)
    (rcd : ∀ y, Prob.cnt (fun s => L.hasCollisionAt y s) ≤ eR)
    (sndL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (knowsT : CT.Knows)
    (decidesT : ∀ x y (τ : Tr GT.sh),
      DT.accept x y τ = true → (CT.all.out (x, y) τ).isSome = true)
    (tieT : ∀ rec y, CT.Lg id rec y → L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none)
    (lawsB : GB.Laws) (knowsB : CB.KnowsLate (fun a : X × L.Rec => (L.early a.1, a.2)) n)
    (decidesB : ∀ x rec y (τ : Tr GB.sh), DB.accept (x, rec) y τ = true →
      (CB.all.out ((x, rec), y) τ).isSome = true)
    (idem : ∀ x, L.early (L.early x) = L.early x) (pos : 0 < n) (inFirst : n ≤ GB.s₁.length)
    (tieB : ∀ x rec y (τ : Tr GB.sh), DB.accept (x, rec) y τ = true →
      (CB.on₀ ((x, rec), y) → CB.R₀ ((x, rec), y) (CB.ext ((x, rec), y) τ ())) →
      L.relB Rno rec x y (wit (x, rec) y τ)) :
    L.SoundAtR Rno
      (fun a y τ => wit a y (cast (congrArg (fun Q : BatchInteractiveOracleProof _ _ => Tr Q.loc.shape) hB) τ)) eR
      (cast (congrArg (fun Q : InteractiveOracleProof _ _ => Err Q.shape) hT.symm) CT.err) εL
      (cast (congrArg (fun Q : BatchInteractiveOracleProof _ _ => Err Q.loc.shape) hB.symm) (CB.errN L.maxBatchSize)) :=
  ⟨noneColl, rcd, sound_cast (sndT_of_file L DT knowsT decidesT tieT) L.offline hT, sndL,
    fun rec => hl ▸ sndBKT_cast (R := L.relB Rno)
      (sndB_of_file_late L DB Rno wit L.maxBatchSize L.early lawsB n knowsB decidesB idem pos inFirst tieB)
      L.onlineBatch hB rec⟩

end Assembly

end TypedOracleCompiler.Joined
