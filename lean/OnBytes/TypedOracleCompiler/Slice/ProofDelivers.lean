-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ProofDelivers.lean: the proof's file in the shape of
OnBytes/TypedOracleCompiler/Slice/Shapes.lean, AT LETTERS: its part by the way "type, then run", one theorem that
has all twelve clauses of `FileSpec.Delivers`, and what its judge hands to the join and to a yes.

THIS IS WHAT FILLING THE SHAPE LOOKS LIKE; NOTHING IS DELIVERED: the hypotheses are met by nobody.
The like of OnBytes/TypedOracleCompiler/Slice/KeyDelivers.lean and EntryDelivers.lean; but here the interface, the
wiring, the written protocol AND the second protocol are letters: no frame for the proof's file is
written.

Main definitions.
 `SdF`                  the seeds of the copy's record.
 `ProofAt`              what the proof's part is made of, at one pair of tables: all letters. An
                        instance is a pair "a first part; the copy's seeds"; e says what a first
                        query holds of the first part. With `ProofAt.pre`.
 `ProofAt.Lg`           the proof's language of a typed world, `DecR.LgP`
                        (OnBytes/Slice/DecoderRecTyped.lean), at the claim that `xOf` and the
                        answers that `an` read off an instance's first part.
 `ProofAt.base`, `proofSpec`   the part but for its checker (judge: `judgeEL`,
                        OnBytes/TypedOracleCompiler/Slice/JudgeE.lean, at one root); THE PROOF'S FILE:
                        `FileSpec.ofTyping` at it, a typing, `preE`, and n = 2.
Main theorems.
 `proof_delivers`       `(proofSpec ..).Delivers S₀ S₁ rd b`.
 `langP_of_judgeE`      from the judge's language, in the form of the language of a part over the
                        one oracle, to the join's `DecR.LangP` at `wayColl`.
 `proof_run_seed`       if the judge's run says yes under the family read out of g, the seeds in its
                        instance are the seed under g of a key k, IF what the second protocol's
                        chain yields there is that seed.

HAD, of the twelve clauses: `preNoCoin`, `preQueries` at 2, `blind`; `noCoin`, `queries`, `named`,
`fit` from what is asked of the typing and the page; `judge` by `judgeAtAsk_EL`
(OnBytes/TypedOracleCompiler/Slice/JudgeE.lean) with `stLawsE_reply_e`, `jointE_reply_e`
(OnBytes/TypedOracleCompiler/Slice/WrittenE.lean).

OWED, AS HYPOTHESES. OF THE INTERACTIVE PROTOCOL, ONE STATEMENT: `lost`: `ReplyLost`
(OnBytes/Slice/ReplyState.lean) at the early part (e x.1, x.2), for `ProofAt.Lg`; with hb: the
counts' shares are at most εs. OF THE INTERFACE AND THE WRITING: hn: a string has 2 ^ a symbols
(used by no step of the proof: at another length the language holds of everything,
`DecR.lgP_of_len`, and the statement is true for free); hZ, hN, hE, hl (NO LATER QUERY HOLDS THE
INSTANCE: the interface takes it in at the first query alone). OF THE SECOND PROTOCOL AND ITS LANE:
another tag; two rounds; what it writes of a plain part is read back; the lane whose state is
`DecR.badK` obeys the laws of a lane, with counts at most εs (for the key and the entry these come
from `hpr_record`, OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean: here the second protocol is a letter, so they
are asked). OF THE PAGE: `one`, `reads`, `blocks`, `clean`. OF THE NUMBERS: `flat`. OF THE TYPING:
no coin; at most tT strings; `few`; `typNamed`; `okT`.

THE PRICE. The count is multiplied by 3; the checker's count of strings takes in the judge's typed
queries, Bk strings each.

Not claimed. NO INTERFACE, NO PROTOCOL, NO TYPING, NO PAGE IS GIVEN. That the hypotheses can be met
together. That `ReplyLost` holds of any protocol. `pageSeed` of `proof_run_seed` is a hypothesis.
The judge's run has the compiled verifier without the test of the strict format (whole paths). THE
SECOND LANE'S FRUIT IS NOT READ BY THE JOIN: `langP_of_judgeE` takes the first half of the judge's
language alone; that the copy's record singles one table out is the entry's to show: at a test that
is false everywhere the debts on that lane should fall: untried. Nothing on proof of work beside the
counts. NO SOUNDNESS IS PROVED. What the heads of JudgeE.lean, WrittenE.lean, ShapesTyping.lean and
Shapes.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is
made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryXRun
import OnBytes.TypedOracleCompiler.Slice.ShapesTyping

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX)
open OnBytes.Slice (DecR decRec GE NZ Tab NoClash Raw rawOf lenB ReplyLost seedUnder)
open OnBytes.Slice.Shapes (Files FileSpec chkT chkT_det chkT_noCoin chkT_queries)
open scoped ENNReal

variable (A : Type) (lg s : ℕ)

/-- The seeds of the copy's record. -/
abbrev SdF : Type := Fin s → (Fin lg → GE) × NZ

/-- What the proof's part is made of, at one pair of tables: an interface whose instances are
pairs "a first part; the copy's seeds"; a wiring; the proof's protocol, written on ONE external
string; a second protocol, written, with the one fixed string at which its chain is run and the
value that is read off its verifier's messages; what a first query holds of an instance's first
part; a reading; an implementation; the roots, read off the files; the match of symbols. ALL ARE
LETTERS. -/
structure ProofAt where
  /-- the first of the two types over which the interface is stated -/
  I : Type
  /-- the interface -/
  L : BatchProtocolWithLeafBody I (A × SdF lg s)
  /-- its wiring -/
  W : QueryLayout 256 L
  /-- the proof's protocol, as written -/
  Z : WrittenE W (ext1R L)
  /-- the second protocol, as written -/
  ZT : Written W
  /-- the fixed string's salt -/
  saltT : Bits
  /-- its request root -/
  rtT : Dig 256
  /-- its roots -/
  rootsT : List (Dig 256)
  /-- its plain parts -/
  plainsT : Plains ZT.P.shape
  /-- the value off the second protocol's verifier's messages -/
  seedOf : Rho ZT.P.shape → SdF lg s
  /-- what a first query holds of an instance's first part -/
  e : A → A
  /-- the reading of the string under a root -/
  R : Reading L W.embE
  /-- the implementation of the typed oracles by one oracle -/
  m : OracleCoding (typedOracleFamily 256 W.K L) 256
  /-- the roots, read off the files -/
  rts : Files → List (Dig 256)
  /-- the match of symbols -/
  u : L.Symbol ≃ SgX

variable {A lg s} [DecidableEq (SdF lg s)] {Xi : Type} (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : A → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
  (Ac : (decRec T v eM lg s).Claims Xi) (xOf : A → Xi)

/-- The proof's language of a typed world at an instance: `DecR.LgP`
(OnBytes/Slice/DecoderRecTyped.lean) at the claim that `xOf` reads off the instance's first part and
the record "the seeds in the instance; the answers that `an` reads off its first part". -/
def ProofAt.Lg (x : ProofAt A lg s) (i : A × SdF lg s) (y : Fin x.L.wordLength → x.L.Symbol) : Prop :=
  DecR.LgP (D := decRec T v eM lg s) x.u an id Ac (xOf i.1) i y

/-- The proof's part but for its checker: interface, wiring, judge (`judgeEL` at one root),
error, implementation, roots, symbols. Its checker and the count of the checker's strings are
placeholders: `FileSpec.ofTyping` does not read them. -/
def ProofAt.base (x : ProofAt A lg s) (εs : ℝ≥0∞) : Part 256 Files SgX where
  I := x.I
  X := A × SdF lg s
  L := x.L
  W := x.W
  Out := OutE x.Z
  J := judgeEL x.Z x.ZT x.saltT x.rtT x.rootsT x.plainsT x.seedOf (pack1 _) x.R
    (x.Lg T v eM an Ac xOf) (DecR.badK (D := decRec T v eM lg s) x.u id)
  e := εs
  m := x.m
  chk := fun _ => OComp.pure none
  rts := x.rts
  tR := 0
  a := 1
  u := x.u

/-- What is asked first, at these data. -/
def ProofAt.pre (x : ProofAt A lg s) := preE x.ZT x.saltT x.rtT x.rootsT x.plainsT x.Z

variable (Θ : Tab → Tab → ProofAt A lg s) (εs : ℝ≥0∞)

/-- THE PROOF'S FILE, BY THE WAY "TYPE, THEN RUN": at all tables the part of `ProofAt.base` with
the checker "the typing `typ`, then the judge's run over the one oracle through the implementation".
What is asked first: the second protocol's chain under the root: at most 2 queries. -/
def proofSpec
    (typ : ∀ T₀ T₁, Files →
      OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an Ac xOf εs).Out))
    (tT Bk : ℕ) : FileSpec :=
  FileSpec.ofTyping (fun T₀ T₁ => (Θ T₀ T₁).base T v eM an Ac xOf εs) typ
    (fun T₀ T₁ => (Θ T₀ T₁).pre) 2 tT Bk

/-- WHAT IS DELIVERED FOR THE PROOF'S FILE, AND WHAT IS STILL OWED. All twelve clauses of
`FileSpec.Delivers` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean). `judge` is drawn from ONE hypothesis on the
interactive protocol, `ReplyLost` (by `stLawsE_reply_e`, `jointE_reply_e`, `judgeAtAsk_EL`), and
from laws on the letters. OWED, as hypotheses under their names: see the file's head. -/
theorem proof_delivers
    (typ : ∀ T₀ T₁, Files →
      OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an Ac xOf εs).Out))
    (tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX) (b : ℕ → ℝ≥0∞) (d₁ : SdF lg s)
    -- the interactive protocol
    (ε : ∀ T₀ T₁, Err (Θ T₀ T₁).Z.Q.loc.shape)
    (lost : ∀ T₀ T₁, ReplyLost (Θ T₀ T₁).Z.Q.loc (ε T₀ T₁)
      (fun x => ((Θ T₀ T₁).e x.1, x.2)) ((Θ T₀ T₁).Lg T v eM an Ac xOf))
    (hb : ∀ T₀ T₁, Err.Below
      (Err.timesShared (Θ T₀ T₁).L.maxBatchSize (Θ T₀ T₁).Z.Q.ann (ε T₀ T₁)) εs)
    -- the interface and the writing
    (hn : ∀ T₀ T₁, (Θ T₀ T₁).L.wordLength = 2 ^ T.a)
    (hZ : ∀ T₀ T₁, (Θ T₀ T₁).Z.OK)
    (hN : ∀ T₀ T₁, (Θ T₀ T₁).L.maxBatchSize = 2 ^ ((Θ T₀ T₁).W.dReq (Θ T₀ T₁).Z.t))
    (hE : ∀ T₀ T₁ x, (Θ T₀ T₁).L.early x = ((Θ T₀ T₁).e x.1, d₁))
    (hl : ∀ T₀ T₁, (Θ T₀ T₁).L.late = none)
    -- the second protocol and its lane
    (hne : ∀ T₀ T₁, (Θ T₀ T₁).ZT.t ≠ (Θ T₀ T₁).Z.t)
    (hT2 : ∀ T₀ T₁, (Θ T₀ T₁).ZT.P.shape.length = 2)
    (hP : ∀ T₀ T₁ z, (Θ T₀ T₁).ZT.prjP ((Θ T₀ T₁).ZT.embP z) = some z)
    (εT : ∀ T₀ T₁, Err (Θ T₀ T₁).ZT.P.shape)
    (oT : ∀ T₀ T₁, ((Θ T₀ T₁).ZT.laneBad (Θ T₀ T₁).R (εT T₀ T₁) fun y ρ =>
      DecR.badK (D := decRec T v eM lg s) (Θ T₀ T₁).u id y ((Θ T₀ T₁).seedOf ρ)).OK
        (2 ^ ((Θ T₀ T₁).W.dReq (Θ T₀ T₁).ZT.t)))
    (bT : ∀ T₀ T₁, Err.Below (εT T₀ T₁) εs)
    -- the page
    (one : ∀ T₀ T₁, OneBlock (Θ T₀ T₁).m)
    (reads : ∀ T₀ T₁ σ, NoClash σ → ∀ cm,
      ((proofSpec T v eM an Ac xOf Θ εs typ tT Bk).part T₀ T₁).raw σ cm = rd T₀ T₁ σ cm)
    (blocks : ∀ T₀ T₁ o, (Θ T₀ T₁).m.blocks o ≤ Bk)
    (clean : ∀ T₀ T₁ (F : Fam (typedOracleFamily 256 ((Θ T₀ T₁).base T v eM an Ac xOf εs).W.K
        ((Θ T₀ T₁).base T v eM an Ac xOf εs).L))
      (o : ((Θ T₀ T₁).base T v eM an Ac xOf εs).Out),
      ∀ e ∈ ((((Θ T₀ T₁).base T v eM an Ac xOf εs).J.run o).withTrace.det F).2,
        ∀ j, ((Θ T₀ T₁).base T v eM an Ac xOf εs).m.code e.1 e.2.1 j ∉ S₀ ∪ S₁ T₀)
    -- the numbers of the bound
    (flat : ∀ T₀ T₁ t,
      ((proofSpec T v eM an Ac xOf Θ εs typ tT Bk).toO S₀ S₁ T₀ T₁).bound t ≤ b t)
    -- the typing
    (typNoCoin : ∀ T₀ T₁ x, (typ T₀ T₁ x).NoCoin)
    (typQueries : ∀ T₀ T₁ x, (typ T₀ T₁ x).QueryBound tT)
    (few : ∀ T₀ T₁ x, ((Θ T₀ T₁).rts x).length ≤ 1)
    (typNamed : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files)
      (o : ((Θ T₀ T₁).base T v eM an Ac xOf εs).Out), (typ T₀ T₁ x).det g = some o →
      ∀ r ∈ ((Θ T₀ T₁).base T v eM an Ac xOf εs).J.roots o, r ∈ (Θ T₀ T₁).rts x)
    (okT : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files)
      (o : ((Θ T₀ T₁).base T v eM an Ac xOf εs).Out), (typ T₀ T₁ x).det g = some o →
      ((Θ T₀ T₁).base T v eM an Ac xOf εs).J.ok o) :
    (proofSpec T v eM an Ac xOf Θ εs typ tT Bk).Delivers S₀ S₁ rd b where
  judge := fun T₀ T₁ => have _ := hn T₀ T₁
    judgeAtAsk_EL (Θ T₀ T₁).Z (Θ T₀ T₁).ZT (Θ T₀ T₁).saltT (Θ T₀ T₁).rtT (Θ T₀ T₁).rootsT
    (Θ T₀ T₁).plainsT (Θ T₀ T₁).seedOf (pack1 _) (Θ T₀ T₁).R ((Θ T₀ T₁).Lg T v eM an Ac xOf)
    (DecR.badK (D := decRec T v eM lg s) (Θ T₀ T₁).u id) (Θ T₀ T₁).e d₁ _ _ (εT T₀ T₁) εs
    (hb T₀ T₁) (jointE_reply_e (Θ T₀ T₁).Z (Θ T₀ T₁).e _ (ε T₀ T₁))
    (stLawsE_reply_e (Θ T₀ T₁).Z (Θ T₀ T₁).e _ (ε T₀ T₁) (lost T₀ T₁)) (hZ T₀ T₁) (hN T₀ T₁) rfl
    (show 1 ≤ 2 by decide) (hE T₀ T₁) (hl T₀ T₁) (hne T₀ T₁)
    (fun h => by
      have h2 := hT2 T₀ T₁
      rw [h] at h2
      cases h2)
    (hP T₀ T₁) (oT T₀ T₁) (bT T₀ T₁)
  preNoCoin := fun T₀ T₁ o q => preE_noCoin (Θ T₀ T₁).ZT _ _ _ _ (Θ T₀ T₁).Z o q
  preQueries := fun T₀ T₁ o q =>
    ((preE_bound (Θ T₀ T₁).ZT _ _ _ _ (Θ T₀ T₁).Z o q).mono (by
      show 1 * (Θ T₀ T₁).ZT.P.shape.length ≤ 2
      rw [hT2 T₀ T₁])).queryBound
  blind := fun T₀ T₁ F tr cm =>
    preE_blind (Θ T₀ T₁).Z (Θ T₀ T₁).ZT _ _ _ _ (Θ T₀ T₁).R F tr cm
  one := one
  reads := reads
  flat := flat
  noCoin := fun T₀ T₁ x => chkT_noCoin _ (typ T₀ T₁) (typNoCoin T₀ T₁) x
  queries := fun T₀ T₁ x => chkT_queries _ (typ T₀ T₁) tT Bk (typQueries T₀ T₁) (blocks T₀ T₁) x
  few := few
  named := fun T₀ T₁ g x o h => typNamed T₀ T₁ g x o (chkT_det _ (typ T₀ T₁) x g o h).1
  fit := fun T₀ T₁ g x o _ h =>
    FileSpec.ofTyping_fit (fun T₀ T₁ => (Θ T₀ T₁).base T v eM an Ac xOf εs) typ S₀ S₁ clean
      okT T₀ T₁ g x o h

/-! ## What the judge hands to the join and to a yes -/

omit [DecidableEq (SdF lg s)] in
/-- From the language of the proof's judge, in the form of the language of a part over the one
oracle, to the join's language of the proof (`DecR.LangP` at `wayColl`), at the claim and the
record that are read off the instance. -/
theorem langP_of_judgeE (x : ProofAt A lg s) (i : A × SdF lg s) (Y : Raw SgX)
    (h : ∃ ys : List (Fin x.L.wordLength → x.L.Symbol), [Y] = ys.map (rawOf x.u) ∧
      ∀ f : ℕ → Fin x.L.wordLength → x.L.Symbol, (∀ j, j < 1 → ys[j]? = some (f j)) →
        x.Lg T v eM an Ac xOf i (f 0) ∧ ∀ j, j < 1 →
          DecR.badK (D := decRec T v eM lg s) x.u id (f j) ((pack1 _).get i.2 j) = false) :
    DecR.LangP Ac (DecR.wayColl (decRec T v eM lg s)) (xOf i.1) (i.2, an i.1) Y := by
  obtain ⟨ys, e, h⟩ := h
  match ys, e, h with
  | [y], e, h =>
    rw [(List.cons.inj e).1]
    exact (h (fun _ => y) (fun j hj => by
      obtain rfl : j = 0 := by omega
      rfl)).1

/-- IF THE PROOF'S JUDGE'S RUN SAYS YES UNDER THE FAMILY READ OUT OF g, THE SEEDS IN ITS INSTANCE
ARE THE SEED UNDER g of a key k, IF what the second protocol's chain yields under the output's
root, in that family, is that seed (`pageSeed`: for the key and the entry it follows from a law on a
page: `seedUnderF_eq`, `entry_chain_seed`). -/
theorem proof_run_seed (x : ProofAt A lg s) (k : OnBytes.Tie.IdKey) (g : Fam (rom 256))
    (o : OutE x.Z) (hlen : o.1.length = 1)
    (pageSeed : ∀ y, (x.ZT.chainT x.saltT x.rtT x.rootsT x.plainsT [o.1.getD 0 default]).det
      (readBlocks x.m g) = some y → seedUnder lg s k g = some (x.seedOf y.1))
    (h : (judgeRunEL x.Z x.ZT x.saltT x.rtT x.rootsT x.plainsT x.seedOf (pack1 _) o).det
      (readBlocks x.m g) = true) : seedUnder lg s k g = some o.2.1.2 := by
  have hc := ((judgeRunEL_det x.ZT x.saltT x.rtT x.rootsT x.plainsT x.seedOf (pack1 _) x.Z
    (readBlocks x.m g) o).1 h).1
  have hk : (ext1R x.L).k = 1 := rfl
  have htake : o.1.take 1 = o.1 := by rw [← hlen, List.take_length]
  rw [hk, htake] at hc
  obtain ⟨y, hy, hs⟩ := cmpT_det_true (Ex := ext1R x.L) x.ZT x.saltT x.rtT x.rootsT x.plainsT
    x.seedOf (pack1 _) (readBlocks x.m g) o.1 0 o.2.1.2 hc 0 (by omega)
  rw [pageSeed y hy, hs]
  rfl

end TypedOracleCompiler.Slice
