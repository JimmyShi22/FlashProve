-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/ToyLate.lean: a test: the list of hypotheses of the soundness theorem for a file
is met together also in the form in which a later query takes in the rest of the instance.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The rounds and their wire records are those of OnBytes/TypedOracleCompiler/Joined/ToyFile.lean. The instance is two
bits. The first query holds the first bit alone (`early`); the query of round 1, chain 1's round,
holds both (`late` is `some 1`). The verifier accepts if both bits are true and chain 1's string
holds true at the place that chain 1's own block names and at the place that chain 3's block names.

Main names:
  `early`, `DL`, `LL`, `WL`, `FL`, `RL`   what of an instance the first query holds; the verifier;
                 the interface record, the wire record, the written file, the read-back.
  `CL`           the three chains' descriptions, made of the verifier's tests.
  `knowsL`       the five clauses, the first in the joint form, with all errors 0.
  `holesL`       THE LIST in the late form, every field proved.
  `soundL`, `laneL`   the soundness theorem in the late form, at this file, without a hypothesis.
  `lgL_iff`      the language: both bits are true: so the language speaks of the bit that enters
                 late (that it is bound would be `soundL`'s to say, which says nothing here:
                 Limits).

Limits: a test. As in OnBytes/TypedOracleCompiler/Joined/Toy.lean all errors are 0, for the same plain reason, and
there are no external strings; and digests have one bit, so the theorem's bound is at least 1: the
CONCLUSION (`soundL`, `laneL`) says nothing at this file. What the test shows is `holesL`: the
hypotheses can hold together. That the list can be met says nothing on whether it is met at a real
file.
`acceptsL` shows that the decision accepts one transcript: that the compiled verifier accepts any
proof string is not shown. No theorem here shows the list failing at a spoilt value.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Toy

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.Toy
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (KnowLate)
open scoped ENNReal

/-- instances: two bits -/
abbrev Y2 : Type := Bool × Bool

/-- what of an instance the first query holds: the first bit -/
def early (x : Y2) : Y2 := (x.1, false)

theorem early_idem (x : Y2) : early (early x) = early x := rfl

/-- The file's verifier: both bits are true, and chain 1's string holds true at both places. -/
@[reducible] def DL : Desc G Y2 (oneExternalString 0 Unit) where
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ => {p₁ ρ, p₃ ρ}
  accept := fun x _ τ =>
    x.1 && x.2 && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)

theorem isLocalL : DL.proto.IsLocal := by
  intro x y y' τ τ' hρ _ _ hr
  have h1 : str₁ τ (bit (G.rho₁ τ.rho).1) = str₁ τ' (bit (G.rho₁ τ.rho).1) :=
    hr _ (Finset.mem_insert_self _ _)
  have h3 : str₁ τ (bit (G.rho₃ τ.rho).1) = str₁ τ' (bit (G.rho₃ τ.rho).1) :=
    hr _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  show (x.1 && x.2 && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)) =
    (x.1 && x.2 && str₁ τ' (bit (G.rho₁ τ'.rho).1) && str₁ τ' (bit (G.rho₃ τ'.rho).1))
  rw [h1, h3, hρ]

theorem acceptsL :
    DL.accept (true, true) (fun p => p.elim0) (trOf (fun _ => true) fun _ _ => false) = true := rfl

/-- the bit that enters late counts -/
theorem rejectsL (b : Bool) (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh) :
    DL.accept (b, false) y τ = false := by
  show (b && false && _ && _) = false
  rw [Bool.and_false]
  rfl

/-- The interface record: the first query holds `early x`, the query of round 1 holds x. -/
@[reducible] def LL : BatchProtocolWithLeafBody Unit Y2 where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  decodeIndex := fun _ => some ()
  offline := pT
  link := pK
  maxBatchSize := 2
  onlineBatch := DL.batch
  honestOfflineProver := _root_.Run.dummyH pT fun _ _ => ()
  honestLinkProver := _root_.Run.dummyH pK fun _ => (fun _ => (), fun _ => ())
  honestOnlineBatchProver := _root_.Run.dummyB DL.batch fun _ _ => ()
  early := early
  late := some 1
  Bd := Option (Σ p : OPos G.sh, OSym G.sh p)
  annT := PUnit.unit
  annL := PUnit.unit

def wqL : ProtocolQueryLayout 1 1 DL.batch := V.qb DL we1 decO 2 1

theorem wqL_okg : wqL.OKG :=
  V.qb_okg DL we1 decO 2 1 V_okg we1_ok
    (fun _ _ _ => by
      show (({_, _} : Finset (OPos G.sh))).card + (∅ : Finset (Fin 0)).card ≤ 2
      rw [Finset.card_empty, Nat.add_zero]
      exact Finset.card_le_two)
    V_depthLe

@[reducible] def WL : QueryLayout 1 LL where
  K := 1
  T := ⟨(), we1, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  Lk := ⟨(), we2, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := wqL
  depth := 0
  depthReq := 1
  depthReqT := 0
  depthReqL := 0
  embE := fun _ => none
  prjE := fun _ => some ()
  embT := fun p => nomatch p
  prjT := fun p => nomatch p
  embL := fun p => nomatch p
  prjL := fun p => nomatch p
  embB := fun p a => some ⟨p, a⟩
  prjB := fun p b => match b with
    | some z => if h : z.1 = p then some (h ▸ z.2) else none
    | none => none

@[reducible] def FL : FileW WL G Y2 (oneExternalString 0 Unit) where
  D := DL
  t := .onl
  wq := wqL
  embS := fun p a => some ⟨p, a⟩
  embP := fun z => z
  xin := some
  embE := fun _ => none

def prjEL : Body LL → Option (oneExternalString 0 Unit).Sym := fun _ => some ()

/-- The read-back: up to round 0 the queries hold `early x`, from round 1 on x. -/
def RL : ReadBack FL.written early where
  prjS := fun p b => match b with
    | some z => if h : z.1 = p then some (h ▸ z.2) else none
    | none => none
  prjP := some
  xout := id
  prjS_emb := fun _ _ => dif_pos rfl
  prjP_emb := fun _ => rfl
  xout_in := fun x i => by
    show (if 1 ≤ i then some x else (some x).map early) = some (if 1 ≤ i then x else early x)
    split <;> rfl

/-- statements: the instance and the external strings -/
abbrev StL : Type := Y2 × (oneExternalString 0 Unit).Str

/-- The three chains' descriptions, made of the verifier's tests. The relation of the file's
statements: both bits are true. -/
@[reducible] def CL : Links G StL where
  A₁ := Fin 2 → Bool
  A₂ := Fin 2 → Bool
  W₀ := Unit
  W₁ := Unit
  W₂ := Unit
  out₁ := fun a τ => if a.1.1 && a.1.2 && sOf τ (bit (bOf₁ τ)) then some (sOf τ) else none
  out₂ := fun o _ => some o
  out₃ := fun o τ => if o (bit (bOf₃ τ)) then some () else none
  on₀ := fun _ => True
  on₁ := fun _ => True
  on₂ := fun _ => True
  R₀ := fun a _ => a.1.1 = true ∧ a.1.2 = true
  R₁ := fun _ _ => True
  R₂ := fun _ _ => True
  e₁ := fun _ _ _ => ()
  e₂ := fun _ _ _ => ()
  e₃ := fun _ _ _ => ()
  ε₁ := err0 _
  ε₂ := err0 _
  ε₃ := err0 _
  d₀ := ()
  d₁ := ()

theorem knowsL : CL.KnowsLate early 1 where
  know₁ := fun _ y => JDoomed.of_forall _ _ _ fun φ τ _ b _ h _ => by
    have h' : (if (φ.1.1 && φ.1.2 && sOf τ (bit (bOf₁ τ))) = true then some (sOf τ) else none) =
        some b := h
    by_cases hc : (φ.1.1 && φ.1.2 && sOf τ (bit (bOf₁ τ))) = true
    · exact Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hc).1
    · rw [if_neg hc] at h'
      cases h'
  know₂ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  know₃ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  hands₁ := fun _ _ _ _ _ => trivial
  hands₂ := fun _ _ _ _ _ => trivial

/-- No chain of the description rejects exactly where the file's verifier accepts. -/
theorem isSome_allL_iff (x : Y2) (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh) :
    (CL.all.out (x, y) τ).isSome = true ↔ FL.D.accept x y τ = true := by
  show ((if (x.1 && x.2 && str₁ τ (bit (G.rho₁ τ.rho).1)) = true then some (str₁ τ) else none).bind
      fun b => (some b).bind fun c =>
        if c (bit (G.rho₃ τ.rho).1) = true then some () else none).isSome = true ↔
    (x.1 && x.2 && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)) = true
  cases hp : (x.1 && x.2 && str₁ τ (bit (G.rho₁ τ.rho).1)) <;>
    cases hq : str₁ τ (bit (G.rho₃ τ.rho).1) <;> simp [hq]

theorem fileLawsL : FileLaws FL prjEL := ⟨isLocalL, laws, wqL_okg, fun _ => rfl⟩

/-- **The list in the late form, every field proved.** -/
theorem holesL : FileHolesLate FL CL prjEL early 1 :=
  ⟨fileLawsL, knowsL, fun x y τ h => (isSome_allL_iff x y τ).2 h, early_idem, Nat.one_pos, le_rfl⟩

/-- **The soundness theorem in the late form applies at this file, with nothing left open.** -/
theorem soundL (sMT sFS : ℕ) :
    SoundAt WL (FL.verify sMT sFS) (UnderTwo FL.wq.ext) (CL.Lg id) (extStr FL.wq.ext prjEL)
      (CL.worst (2 ^ WL.dReq FL.t)) :=
  sound_verifyFile_late FL sMT sFS RL holesL rfl

/-- The same with the event in the open. -/
theorem laneL (sMT sFS : ℕ) :
    SoundLane WL FL.t (FL.verify sMT sFS) (UnderTwo FL.wq.ext) (CL.Lg id) (extStr FL.wq.ext prjEL)
      (CL.worst (2 ^ WL.dReq FL.t)) :=
  lane_verifyFile_late FL sMT sFS RL holesL rfl

/-- The language of the file, by its description: both bits are true. -/
theorem lgL_iff (x : Y2) (y : (oneExternalString 0 Unit).Str) : CL.Lg id x y ↔ x.1 = true ∧ x.2 = true :=
  ⟨fun h => (h trivial).elim fun _ hw => hw, fun h _ => ⟨(), h⟩⟩

theorem worstL_eq (N : ℕ) : CL.worst N = 0 := by
  show max (_root_.Compile.Joined.worst (err0 G.c₁))
    (max ((N : ℝ≥0∞) * _root_.Compile.Joined.worst (err0 G.c₂))
      (_root_.Compile.Joined.worst (err0 G.c₃))) = 0
  simp only [worst_err0, mul_zero, max_self]

end TypedOracleCompiler.Joined.Toy
