-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/KeyDeliversL.lean: the key's file in the shape of OnBytes/TypedOracleCompiler/Slice/Shapes.lean,
WITH THE JUDGE WITHOUT THE TEST OF THE STRICT FORMAT: OnBytes/TypedOracleCompiler/Slice/KeyDelivers.lean said again
at `judgeEL` (OnBytes/TypedOracleCompiler/Slice/JudgeE.lean).

WHY. `judgeOff` (OnBytes/TypedOracleCompiler/Slice/JudgeOff.lean) runs the compiled verifier with the strict format:
one merged walk a tree. A typing that hands whole paths would owe that merged walk; the key's third
chain opens trees of the first two, so a tree is read at two lists. At the verifier without that
test nothing of the kind is owed, and the analysis is for that verifier in any case.

THIS IS WHAT FILLING THE SHAPE LOOKS LIKE; NOTHING IS DELIVERED: the hypotheses are met by nobody.
The letters are `KeyAt`'s.

Main definitions.
 `KeyAt.ZE`             the protocol in three stretches with instances as a `WrittenE` at `ext1R`:
                        the fields of `KeyAt.Z`.
 `KeyAt.JL`, `KeyAt.preL`   the judge: `judgeEL` at one root, `pack1`, at the record's own terms;
                        what is asked first: `preE`.
 `KeyAt.baseL`, `keySpecL`   the part but for its checker; THE KEY'S FILE: `FileSpec.ofTyping` at
                        it, a typing, `preE`, and n = 2. What a checker returns has a LIST of roots
                        in front (`OutE`).
Main theorems.
 `KeyAt.ZE_ok`          `WrittenE.OK`, from `ZX3_ok` (OnBytes/TypedOracleCompiler/Slice/Plain3X.lean).
 `key_judge_recordL`    THE KEY'S JUDGE AT THE RECORD'S OWN TERMS: `JudgeAtAsk`, under the
                        hypotheses of `x3_judge_record_chalP` (OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean).
                        By `judgeAtAsk_EL`, `stLawsE_reply`, `jointE_reply`, `hpr_record`.
 `key_deliversL`        `(keySpecL ..).Delivers S₀ S₁ rd b`, under hypotheses with the names of
                        `key_delivers`.
 `langK_of_judgeE`      from the judge's language, in the form of the language of a part over the
                        one oracle, to the join's `DecR.LangK` at `wayColl`.

HAD and OWED: as the head of KeyDelivers.lean lists them, with `preE_noCoin`, `preE_queries`,
`preE_blind` for the three clauses on what is asked first; `okT` asks beside that what the typing
returns has ONE root. THE PRICE: the count, the judge's own among it, is multiplied by 3.

Not claimed. NO TYPING, NO PAGE, NO STRETCHES, NO DECISION IS GIVEN. What the judge's run computes
under a family of oracle functions (for `judgeOff`: OnBytes/TypedOracleCompiler/Slice/JudgeOffRun.lean; for the
comparisons: `cmpT_det_true`, `cmpT_det_of`, OnBytes/TypedOracleCompiler/Slice/EntryXRun.lean). That the seeds in
the instance are the seeds under an oracle, at this judge. Nothing on proof of work beside the
counts. NO SOUNDNESS IS PROVED. What the heads of KeyDelivers.lean, JudgeE.lean, SeedsBridge.lean,
ShapesTyping.lean and Shapes.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.KeyDelivers
import OnBytes.TypedOracleCompiler.Slice.JudgeE

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP chalP)
open OnBytes.Slice (DecR decRec recZ seedBS seedOfDrawn GE NZ seedEntry dsOf_seedEntry
  chalP_unif_seeds replySt below_timesShared_one Tab NoClash Raw lenB)
open OnBytes.Slice.Shapes (Files FileSpec chkT chkT_det chkT_noCoin chkT_queries)
open scoped ENNReal

variable {An : Type} {lg s : ℕ} {d : SdK lg s}

/-- The protocol in three stretches with instances, as a written batch protocol on external
strings of the kind "one string": the fields of `KeyAt.Z` (`ZXo`,
OnBytes/TypedOracleCompiler/Slice/Plain3XOff.lean). -/
def KeyAt.ZE (x : KeyAt An lg s d) :
    WrittenE x.W (ext1R (LXs (atBlocks x.G) x.dec d (seedEntry lg s))) where
  t := Tag.onl
  Q := BatchInteractiveOracleProof.ofProto (Plain3X (atBlocks x.G) x.dec)
  wq := wq3X (atBlocks x.G) x.dec x.K (chalP .two x.K) x.o
  embS := (atBlocks x.G).embS x.salt
  prjS := (atBlocks x.G).prjS x.salt
  embP := id
  prjP := some

/-- It meets what is asked of one, if the wiring is lawful and no tree is deeper than 63. -/
theorem KeyAt.ZE_ok (x : KeyAt An lg s d) (hs : (atBlocks x.G).Shallow)
    (hw : (wq3X (atBlocks x.G) x.dec x.K (chalP .two x.K) x.o).OKG) : x.ZE.OK :=
  have h := ZX3_ok (atBlocks x.G) x.dec x.K (chalP .two x.K) x.o x.salt (earlyWith d)
    (TS (atBlocks x.G) (seedEntry lg s)) x.embE x.prjE
    (wTS (atBlocks x.G) x.K (chalP .two x.K) (seedEntry lg s))
    (embST (ckP .two) (seedEntry lg s) _) (prjST (ckP .two) (seedEntry lg s) _) hs hw
  ⟨h.backS, h.backP, h.wire, h.loc, h.coh, h.late, h.extDepth, h.ext⟩

variable [DecidableEq (SdK lg s)] {X : Type} (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
  (A : (decRec T v eM lg s).Claims X)

/-- The key's judge WITHOUT the test of the strict format: `judgeEL` (OnBytes/TypedOracleCompiler/Slice/JudgeE.lean)
at one root, at the record's own terms. -/
def KeyAt.JL (x : KeyAt An lg s d) : Judge x.W (OutE x.ZE) :=
  judgeEL x.ZE x.ZT [] default [] (plainsT (ckP .two) (dSeed (seedEntry lg s)) _)
    (seedOfS (atBlocks x.G) (seedEntry lg s) (seedOfDrawn lg s)) (pack1 _) x.R
    (DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A)
    (DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id)

/-- What is asked first. -/
def KeyAt.preL (x : KeyAt An lg s d) :=
  preE x.ZT [] default [] (plainsT (ckP .two) (dSeed (seedEntry lg s)) _) x.ZE

/-- THE KEY'S JUDGE WITHOUT THE STRICT FORMAT, AT THE RECORD'S OWN TERMS: the like of
`x3_judge_record_chalP` (OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean) for `judgeEL`, under the same
hypotheses. -/
theorem key_judge_recordL (x : KeyAt An lg s d) (hs0 : 0 < s) (hK : (seedBS lg s).b ≤ x.K)
    (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a) (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (ε : Err (atBlocks x.G).sh) (εs : ℝ≥0∞)
    (hS : ∀ i, (Plain3 (atBlocks x.G) (x.dec i)).Sound
      (fun _ => DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A i) ε)
    (hb : Err.Below ε εs) (hs : (atBlocks x.G).Shallow)
    (hw : (wq3X (atBlocks x.G) x.dec x.K (chalP .two x.K) x.o).OKG)
    (hε : kapSl 128 ^ (seedBS lg s).b *
      ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
        ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) ≤ εs) :
    JudgeAtAsk x.W (x.JL T v eM an A) εs x.preL := by
  have h1 : Err.Below (Err.timesShared 1 (RoundSplits.allLocal (atBlocks x.G).sh) ε)
      (((1 : ℕ) : ℝ≥0∞) * εs) := below_timesShared_one le_rfl _ ε εs hb
  rw [Nat.cast_one, one_mul] at h1
  obtain ⟨c1, c2⟩ := countOK_of_pr (PQ.s0 (ckP .two)).up
    (PQ.roundS (ckP .two) (dSeed (seedEntry lg s))).up
    (fun (y : Fin (2 ^ (atBlocks x.G).a) → PQ.SgX) ρ =>
      DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id y
        (seedOfS (atBlocks x.G) (seedEntry lg s) (seedOfDrawn lg s) ρ)) εs
    fun y c0 => (hpr_record T v eM lg s (ckP .two) rfl _ ha hk he hJ h3 hl (seedEntry lg s)
      (dsOf_seedEntry lg s hs0) y c0).trans hε
  exact judgeAtAsk_EL x.ZE x.ZT [] default [] (plainsT (ckP .two) (dSeed (seedEntry lg s)) _)
    (seedOfS (atBlocks x.G) (seedEntry lg s) (seedOfDrawn lg s)) (pack1 _) x.R
    (DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A)
    (DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id) id d
    (Err.timesShared 1 (RoundSplits.allLocal (atBlocks x.G).sh) ε)
    (replySt (Plain3X (atBlocks x.G) x.dec) ε id
      (DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A)) _ εs h1
    (jointE_reply x.ZE _ ε)
    (stLawsE_reply x.ZE _ ε ((plain3X_sound_iff (atBlocks x.G) x.dec _ ε).2 hS))
    (x.ZE_ok hs hw) rfl rfl (show 1 ≤ 2 by decide) (fun _ => rfl) rfl
    (show Tag.test ≠ Tag.onl by decide) (seedsT_ne (ckP .two) (dSeed (seedEntry lg s)) _)
    (fun _ => rfl)
    (lane_stBad_ok (TS (atBlocks x.G) (seedEntry lg s))
      (wqT_okg (ckP .two) x.K (chalP .two x.K) (dSeed (seedEntry lg s)) (we1 (atBlocks x.G).a)
        (chalP_unif_seeds lg s x.K (seedEntry lg s) (dsOf_seedEntry lg s hs0) hK) (Nat.zero_le _)
        (we1_ok (atBlocks x.G).a)).sh c1) c2

/-- The key's part but for its checker, with that judge: `KeyAt.base`
(OnBytes/TypedOracleCompiler/Slice/KeyDelivers.lean) with `KeyAt.JL` for its judge; what a checker returns has a
LIST of roots in front. -/
def KeyAt.baseL (x : KeyAt An lg s d) (εs : ℝ≥0∞) : Part 256 Files PQ.SgX where
  I := Unit
  X := XK An lg s
  L := LXs (atBlocks x.G) x.dec d (seedEntry lg s)
  W := x.W
  Out := OutE x.ZE
  J := x.JL T v eM an A
  e := εs
  m := x.m
  chk := fun _ => OComp.pure none
  rts := x.rts
  tR := 0
  a := 1
  u := Equiv.refl _

variable (Θ : Tab → Tab → KeyAt An lg s d) (εs : ℝ≥0∞)

/-- THE KEY'S FILE, BY THE WAY "TYPE, THEN RUN", WITH THE JUDGE WITHOUT THE STRICT FORMAT. What
is asked first: the seeds' chain under the root: at most 2 queries. -/
def keySpecL
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).baseL T v eM an A εs).Out))
    (tT Bk : ℕ) : FileSpec :=
  FileSpec.ofTyping (fun T₀ T₁ => (Θ T₀ T₁).baseL T v eM an A εs) typ
    (fun T₀ T₁ => (Θ T₀ T₁).preL) 2 tT Bk

/-- WHAT IS DELIVERED FOR THE KEY'S FILE, AND WHAT IS STILL OWED, with that judge:
`key_delivers` (OnBytes/TypedOracleCompiler/Slice/KeyDelivers.lean) said again; the hypotheses have its names. -/
theorem key_deliversL
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).baseL T v eM an A εs).Out))
    (tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw PQ.SgX) (b : ℕ → ℝ≥0∞)
    -- the numbers of the record
    (hs0 : 0 < s) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg)
    (hε : kapSl 128 ^ (seedBS lg s).b *
      ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
        ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) ≤ εs)
    -- the stretches, at all tables
    (hK : ∀ T₀ T₁, (seedBS lg s).b ≤ (Θ T₀ T₁).K)
    (hs : ∀ T₀ T₁, (atBlocks (Θ T₀ T₁).G).Shallow)
    (hw : ∀ T₀ T₁, (wq3X (atBlocks (Θ T₀ T₁).G) (Θ T₀ T₁).dec (Θ T₀ T₁).K
      (chalP .two (Θ T₀ T₁).K) (Θ T₀ T₁).o).OKG)
    -- soundness record by record
    (ε : ∀ T₀ T₁, Err (atBlocks (Θ T₀ T₁).G).sh)
    (hS : ∀ T₀ T₁ x, (Plain3 (atBlocks (Θ T₀ T₁).G) ((Θ T₀ T₁).dec x)).Sound
      (fun _ => DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A x) (ε T₀ T₁))
    (hb : ∀ T₀ T₁, Err.Below (ε T₀ T₁) εs)
    -- the page
    (one : ∀ T₀ T₁, OneBlock (Θ T₀ T₁).m)
    (reads : ∀ T₀ T₁ σ, NoClash σ → ∀ cm,
      ((keySpecL T v eM an A Θ εs typ tT Bk).part T₀ T₁).raw σ cm = rd T₀ T₁ σ cm)
    (blocks : ∀ T₀ T₁ o, (Θ T₀ T₁).m.blocks o ≤ Bk)
    (clean : ∀ T₀ T₁ (F : Fam (typedOracleFamily 256 ((Θ T₀ T₁).baseL T v eM an A εs).W.K
        ((Θ T₀ T₁).baseL T v eM an A εs).L)) (o : ((Θ T₀ T₁).baseL T v eM an A εs).Out),
      ∀ e ∈ ((((Θ T₀ T₁).baseL T v eM an A εs).J.run o).withTrace.det F).2,
        ∀ j, ((Θ T₀ T₁).baseL T v eM an A εs).m.code e.1 e.2.1 j ∉ S₀ ∪ S₁ T₀)
    -- the numbers of the bound
    (flat : ∀ T₀ T₁ t, ((keySpecL T v eM an A Θ εs typ tT Bk).toO S₀ S₁ T₀ T₁).bound t ≤ b t)
    -- the typing
    (typNoCoin : ∀ T₀ T₁ x, (typ T₀ T₁ x).NoCoin)
    (typQueries : ∀ T₀ T₁ x, (typ T₀ T₁ x).QueryBound tT)
    (few : ∀ T₀ T₁ x, ((Θ T₀ T₁).rts x).length ≤ 1)
    (typNamed : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files)
      (o : ((Θ T₀ T₁).baseL T v eM an A εs).Out), (typ T₀ T₁ x).det g = some o →
      ∀ r ∈ ((Θ T₀ T₁).baseL T v eM an A εs).J.roots o, r ∈ (Θ T₀ T₁).rts x)
    (okT : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files)
      (o : ((Θ T₀ T₁).baseL T v eM an A εs).Out), (typ T₀ T₁ x).det g = some o →
      ((Θ T₀ T₁).baseL T v eM an A εs).J.ok o) :
    (keySpecL T v eM an A Θ εs typ tT Bk).Delivers S₀ S₁ rd b where
  judge := fun T₀ T₁ => key_judge_recordL T v eM an A (Θ T₀ T₁) hs0 (hK T₀ T₁) ha hk he hJ h3 hl
    (ε T₀ T₁) εs (hS T₀ T₁) (hb T₀ T₁) (hs T₀ T₁) (hw T₀ T₁) hε
  preNoCoin := fun T₀ T₁ o q => preE_noCoin (Θ T₀ T₁).ZT [] default [] _ (Θ T₀ T₁).ZE o q
  preQueries := fun T₀ T₁ o q => preE_queries (Θ T₀ T₁).ZT [] default [] _ (Θ T₀ T₁).ZE o q
  blind := fun T₀ T₁ F tr cm =>
    preE_blind (Θ T₀ T₁).ZE (Θ T₀ T₁).ZT [] default [] _ (Θ T₀ T₁).R F tr cm
  one := one
  reads := reads
  flat := flat
  noCoin := fun T₀ T₁ x => chkT_noCoin _ (typ T₀ T₁) (typNoCoin T₀ T₁) x
  queries := fun T₀ T₁ x => chkT_queries _ (typ T₀ T₁) tT Bk (typQueries T₀ T₁) (blocks T₀ T₁) x
  few := few
  named := fun T₀ T₁ g x o h => typNamed T₀ T₁ g x o (chkT_det _ (typ T₀ T₁) x g o h).1
  fit := fun T₀ T₁ g x o _ h =>
    FileSpec.ofTyping_fit (fun T₀ T₁ => (Θ T₀ T₁).baseL T v eM an A εs) typ S₀ S₁ clean okT
      T₀ T₁ g x o h

omit [DecidableEq (SdK lg s)] in
/-- From the language of the key's judge, in the form of the language of a part over the one
oracle, to the join's language of the key (`DecR.LangK` at `wayColl`), at the record that stands
in the instance. -/
theorem langK_of_judgeE {n : ℕ} (i : XK An lg s) (Y : Raw PQ.SgX)
    (h : ∃ ys : List (Fin n → PQ.SgX), [Y] = ys.map (OnBytes.Slice.rawOf (Equiv.refl _)) ∧
      ∀ f : ℕ → Fin n → PQ.SgX, (∀ j, j < 1 → ys[j]? = some (f j)) →
        DecR.LgK (D := decRec T v eM lg s) (Equiv.refl _) an id A i (f 0) ∧ ∀ j, j < 1 →
          DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id (f j) ((pack1 _).get i.2 j) =
            false) :
    DecR.LangK A (DecR.wayColl (decRec T v eM lg s)) (i.2, an i.1) Y := by
  obtain ⟨ys, e, h⟩ := h
  match ys, e, h with
  | [y], e, h =>
    rw [(List.cons.inj e).1]
    obtain ⟨h1, h2⟩ := h (fun _ => y) (fun j hj => by
      obtain rfl : j = 0 := by omega
      rfl)
    exact DecR.langK_of_typed (D := decRec T v eM lg s) (Equiv.refl _) an id A i y
      ⟨h1, h2 0 (by decide)⟩

end TypedOracleCompiler.Slice
