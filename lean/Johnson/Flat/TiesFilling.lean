-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TiesFilling.lean: a rider on the sheets Johnson/Flat/ProofOfRow.lean and
Johnson/Flat/TiesSheet.lean: two named conditions on whoever fills their letters, and the list of
three reductions with the record fixed. A SHEET OF STATEMENTS: definitions, and propositions written
as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

Why. (1) A description of a file reads an instance through its public part alone, but for its last
test. The sheets speak of `early`, a map on instances. What ties the two is owed by whoever lays a
description in: `PubEarly`: `early` keeps the public part; `PubKeeps`: the public part keeps all
that the first relation of TiesSheet.lean (`firstRel`) reads of an instance and its record: the
early part, whole, and the record. (2) `proofSound_top_links` asks the list for the statements of a
batch record by record. A rule for the three chains may be called at the part x of an instance, the
record being fixed: `LinksAtRec` says that the list with the instance read through (·, rec) IS the
list of that row.

The letters, beside those of the two sheets. Pb: the public parts. pub: an instance's, with its
record. back: from a public part to the early part and the record: A NAMED FUNCTION, so that "keeps"
has no "there is". r₁: the first run as a function of the public part.

Main names. `PubEarly`, `PubKeeps`: the two conditions. `KeptOfPub`: `EarlyKept` from `PubEarly`,
where the first run reads the instance through pub. `FirstRelOfPub`: under `PubKeeps` the first
relation at the early part is a function of the public part, the word and the witness. `EarlyIdem`:
the two conditions make `early` idempotent. `rowAt`, `sndAt`: the row and the clauses' letters with
the record fixed. `LinksAtRec`; `KnowsAtRec`: the list record by record, as the top asks it, from
the list at each such row.

Every "there is", walked. None of the statements has one.

Limits. NO VALUE OF THESE LETTERS IS LAID: no description is named, and no field of one. `PubKeeps`
is stronger than "pub determines what is read": it names the way back. At a pub that keeps the whole
instance `PubEarly` forces `early` to be the identity on what pub tells apart. Nothing on
acceptance, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TiesSheet

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (Row)

variable {a : ℕ} (Kc : ConfLetters a) (DP : WholeD)
  {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (early : Kc.conf.X → Kc.conf.X)
  (L₁ L₂ : List LeftT) {X₁ X₂ : Type}
  (run₁ : Kc.conf.X × Kc.conf.Rec → PQ.View → Option X₁) (run₂ : X₁ → PQ.View → Option X₂)
  (run₃ : X₂ → PQ.View → Bool)
  (S : (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).Snd)

/-! ## 1 Two conditions on the filling -/

section Pub
variable {Pb : Type} (pub : Kc.conf.X × Kc.conf.Rec → Pb) (back : Pb → Kc.conf.X × Kc.conf.Rec)

/-- `early` keeps the public part. -/
def PubEarly : Prop := ∀ x rec, pub (early x, rec) = pub (x, rec)

/-- The public part keeps the early part, whole, and the record: `back` reads them off it. -/
def PubKeeps : Prop := ∀ x rec, back (pub (x, rec)) = (early x, rec)

/-- Where the first run reads the instance through pub, `PubEarly` gives `EarlyKept`. -/
def KeptOfPub (r₁ : Pb → PQ.View → Option X₁) : Prop :=
  (∀ b v, run₁ b v = r₁ (pub b) v) → PubEarly Kc early pub → EarlyKept Kc early run₁

/-- Under `PubKeeps` the first relation at the early part of x is the first relation at what `back`
reads off the public part of x. -/
def FirstRelOfPub {Tok W₀ : Type} (put : Kc.conf.X → Tok → Kc.conf.X) (tok : W₀ → Tok)
    (cells : W₀ → Kc.conf.Cells) : Prop :=
  PubKeeps Kc early pub back →
  ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str) (w : W₀),
    firstRel Kc DP put tok cells ((early x, rec), y) w ↔
      firstRel Kc DP put tok cells (back (pub (x, rec)), y) w

/-- The two conditions make `early` idempotent. -/
def EarlyIdem : Prop :=
  Nonempty Kc.conf.Rec → PubEarly Kc early pub → PubKeeps Kc early pub back →
    ∀ x, early (early x) = early x

end Pub

/-! ## 2 The list with the record fixed -/

/-- The proof file's three stages in a row at the part x of an instance: the record is fixed. -/
abbrev rowAt (rec : Kc.conf.Rec) : Row (chainsOf (ckP .two) (DP.at a) tFp tJp t3p) Kc.conf.X
    (oneExternalString (2 ^ (DP.at a).a) SgX) :=
  rowOf (ckP .two) (DP.at a) tFp tJp t3p L₁ L₂ (fun _ _ => true) (fun _ _ => true)
    (fun _ _ => true) (fun x => run₁ (x, rec)) run₂ run₃

/-- The clauses' letters there: those of S, the first chain's read at (·, rec). -/
def sndAt (rec : Kc.conf.Rec) : (rowAt Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ rec).Snd where
  W₀ := S.W₀
  W₁ := S.W₁
  W₂ := S.W₂
  on₀ := fun b => S.on₀ ((b.1, rec), b.2)
  on₁ := S.on₁
  on₂ := S.on₂
  R₀ := fun b => S.R₀ ((b.1, rec), b.2)
  R₁ := S.R₁
  R₂ := S.R₂
  e₁ := fun b => S.e₁ ((b.1, rec), b.2)
  e₂ := S.e₂
  e₃ := S.e₃
  ε₁ := S.ε₁
  ε₂ := S.ε₂
  ε₃ := S.ε₃
  d₀ := S.d₀
  d₁ := S.d₁

/-- **The list with the instance read through (·, rec) is the list of the row at that record.** -/
def LinksAtRec : Prop :=
  ∀ rec : Kc.conf.Rec,
    (linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).comap (fun x : Kc.conf.X => (x, rec)) =
      (rowAt Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ rec).links
        (sndAt Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S rec)

/-- The premise `knows` of `ProofSoundOfRow`, from the list at each row with its record fixed. -/
def KnowsAtRec (N : ℕ) {κ₁ κ₂ : Type}
    (k₁ : X₁ × (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).E₁.Str → κ₁)
    (k₂ : X₂ × (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).E₂.Str → κ₂) : Prop :=
  (∀ rec, ((rowAt Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ rec).links
    (sndAt Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S rec)).KnowsJ N k₁ k₂) →
  ∀ rec, ((linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).comap
    fun x : Kc.conf.X => (x, rec)).KnowsJ N k₁ k₂

end VerifiableInference.OnPublicFiles
