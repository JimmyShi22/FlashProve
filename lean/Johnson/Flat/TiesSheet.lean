-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TiesSheet.lean: what `RowTies` (Johnson/Flat/ProofOfRow.lean) rests on, premise by
premise. A SHEET OF STATEMENTS: definitions, and propositions written as `def … : Prop`. NOTHING IS
PROVED IN THIS FILE.

Why. `RowTies` is the half of the proof file's hypothesis on soundness in which the meaning sits:
under the file's verifier's yes at an instance x, what the three chains' extractors give, if it is a
witness of the first relation at the part of x that the queries hold (`early x`), must give the
object's relation at x itself. What `early` drops is what is asked of the proof: the reply's token.
The premise knows the transcript through one term alone, the extractors' yield. So the token that
was sent has to be a component of the first relation's witnesses, the extractors have to read it off
the transcript, and the first relation has to speak of the public part with that token put in. A toy
of the library proves the premise in just this way (Johnson/TypedOracleCompiler/Joined/ToyLinksTie.lean).

The letters, beside those of ProofOfRow.lean. Tok: the tokens. drop: what `early` drops of an
instance. put: an instance with a token put in. tokW: the token in a witness of the first relation.
said: the token that a transcript of the whole file names, if it names one. said₁: the same of the
first chain's transcript.

Main names. The five premises at letters: `TieGlue`, `TieOnOk`, `TieTells`, `TieReads`, `TieFins`.
`TiesOfFive`: they give `RowTies`. `firstRel`: the plainest first relation that meets `TieTells`.
`FirstReads`, `ReadsOfFirst`: `TieReads` from a law on the first chain's extractor alone. `SetsOf`,
`PassesOf`: how a block's clause is carried to witnesses with a token: the block of the reply's
round lays it, every block in front of it hands it on; both are meant as one call of the frame rule
for reductions (`Iop.Spec.know_frame`, Ior/Frame.lean). Two closed statements on the side:
`DecodedInRange` (at the configuration of a stored table, what decodes is in range), `TokenOfReply`
(at the integer model's instances, the reply's element read as a token is the instance's own). NO
STATEMENT HERE JOINS EITHER TO THE FIVE. Where each is to be spent: `DecodedInRange` by whoever
shows the first chain's clause at `firstRel` at the frame's configuration, whose relation begins
"the index is in range": the side of `knows`; `TokenOfReply` in `TieFins` at the integer model,
where said reads an element as a token.

Every "there is", walked. None of the statements has one beside `RowTies`' own, in which
`TiesOfFive` ends ("there is an index i with D y rec = some i": walked in ProofOfRow.lean).
`TieTells` runs over all indices i with D y rec = some i: there is at most one. said and said₁ are
letters for named functions of a transcript.

Limits.
- NO VALUE OF THESE LETTERS IS A FILE OF THE FORMAT's. A decision that never says yes meets
  `TieOnOk`, `TieReads` and `TieFins` for nothing. said stands in no conclusion: all that
  `TiesOfFive` spends of `TieReads` and `TieFins` is that the token in the extractors' yield is what
  `early` dropped.
- `TieFins` is a law on the decision's last test and on two properties of the first chain's fold
  (the reply's block lays what it hears in the state; no later block turns it): these name fields of
  a description and are not stated here: Johnson/Desc/Sound/FoldHeard.lean states them, and
    Johnson/Flat/TiesAtDesc.lean has `TieFins` from them. IT WANTS THAT EVERY HEARD WORD THAT THE
    LAST TEST ACCEPTS READS AS drop x, not the honest writing alone (`TokenOfReply` speaks of that
    one): so the last test has to compare the raw words, or the heard element has to be below the
    prime, and said has to read the same words. Nor is the reply's block's own clause stated here (a
    round that sends
  one plain message and draws nothing).
- `firstRel` holds of every witness where the word does not decode: that is the left arm of the
  object's own relation.
- `PassesOf` asks the clause for all tokens together: the token stands in the witness, under the one
  clause. A clause for each token by itself does not give it. `PassesOf` AND `SetsOf` ARE AT `Know`:
  where a block in front of the reply's round has a promise that can be left (`KnowInto`), they do
  not serve.
- put, drop and `early` are letters: at the integer model's instances `TieGlue` is the record's eta;
  at the requests that the program's reader takes, a subtype, put has a second arm:
  Johnson/Flat/TiesAtReq.lean. What whoever fills the letters owes on the public part:
  Johnson/Flat/TiesFilling.lean.
- Only late = none. Nothing on acceptance, on an honest prover or on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfRow
import Johnson.Flat.LinksAt
import OnBytes.K.ReplyToken
import OnBytes.Slice.ConfOf
import Ior.Frame

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

/-! ## 1 The five premises at letters -/

variable {a : ℕ} (Kc : ConfLetters a) (DP : WholeD)
  {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (runP : Kc.conf.X × Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (early : Kc.conf.X → Kc.conf.X)
  (L₁ L₂ : List LeftT) {X₁ X₂ : Type}
  (run₁ : Kc.conf.X × Kc.conf.Rec → PQ.View → Option X₁) (run₂ : X₁ → PQ.View → Option X₂)
  (run₃ : X₂ → PQ.View → Bool)
  (S : (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).Snd)
  {Tok : Type} (drop : Kc.conf.X → Tok) (put : Kc.conf.X → Tok → Kc.conf.X) (tokW : S.W₀ → Tok)
  (said : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh → Option Tok)
  (toW : S.W₀ → Kc.conf.Cells)

/-- What `early` drops, put back, gives the instance. -/
def TieGlue : Prop := ∀ x, put (early x) (drop x) = x

/-- Under the file's verifier's yes, where the word decodes with the record, the first chain's
clause speaks of the statement at the early part. -/
def TieOnOk : Prop :=
  ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh),
    (reductionOfWholeFile (ckP .two) (DP.at a) tFp tJp t3p silP runP).out (x, rec) y τ = some () →
    Kc.conf.D y rec ≠ none → S.on₀ ((early x, rec), y)

/-- The first relation says the object's relation at the public part WITH THE WITNESS's TOKEN PUT
IN, at whatever index the word decodes to. -/
def TieTells : Prop :=
  ∀ p rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str) w, S.R₀ ((p, rec), y) w →
    ∀ i, Kc.conf.D y rec = some i → Kc.conf.Rno i (put p (tokW w)) (toW w)

/-- Under the yes, the token in what the three extractors give is the token that the transcript
names. -/
def TieReads : Prop :=
  ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh),
    (reductionOfWholeFile (ckP .two) (DP.at a) tFp tJp t3p silP runP).out (x, rec) y τ = some () →
    said τ = some (tokW
      ((linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).ext ((early x, rec), y) τ ()))

/-- Under the yes, the token that the transcript names is the instance's own. -/
def TieFins : Prop :=
  ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh),
    (reductionOfWholeFile (ckP .two) (DP.at a) tFp tJp t3p silP runP).out (x, rec) y τ = some () →
    said τ = some (drop x)

/-- **The five give `RowTies`.** Meant by: cases on D y rec; `TieOnOk`; the premise of
`RowTies`; `TieTells`; `TieReads` with `TieFins`; `TieGlue`. -/
def TiesOfFive : Prop :=
  TieGlue Kc early drop put → TieOnOk Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S →
  TieTells Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S put tokW toW →
  TieReads Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S tokW said →
  TieFins Kc DP tFp tJp t3p silP runP drop said →
  RowTies Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S toW

/-- The plainest first relation that meets `TieTells`: that sentence itself. W₀: any type of
witnesses with a token and an image in the configuration's cells. -/
def firstRel {W₀ : Type} (tok : W₀ → Tok) (cells : W₀ → Kc.conf.Cells) :
    (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str → W₀ → Prop :=
  fun b w => ∀ i, Kc.conf.D b.2 b.1.2 = some i → Kc.conf.Rno i (put b.1.1 (tok w)) (cells w)

/-! ## 2 `TieReads` from a law on the first chain's extractor -/

variable (said₁ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).c₁ → Option Tok)

/-- Where the first chain hands a statement on, its extractor's yield holds the token that the first
chain's own transcript names, WHATEVER THE LATER CHAINS' WITNESS. -/
def FirstReads : Prop :=
  ∀ b τ₁ w₁ b₁, (linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).K₁.out b τ₁ = some b₁ →
    said₁ τ₁ = some (tokW ((linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).e₁ b τ₁ w₁))

/-- `TieReads`, at the token that the first chain's part of the transcript names, from
`FirstReads` and the conclusion of `RowDecides`. Meant by: the composed extractor where the
first reduction yields a statement (`Reduction.extSeq`, Ior/Know.lean). -/
def ReadsOfFirst : Prop :=
  (∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh),
    (reductionOfWholeFile (ckP .two) (DP.at a) tFp tJp t3p silP runP).out (x, rec) y τ = some () →
      (linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).all.out ((early x, rec), y) τ = some ()) →
  FirstReads Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S tokW said₁ →
  TieReads Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S tokW
    (fun τ => said₁ (Tr.fst (s := (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).c₁) τ))

end VerifiableInference.OnPublicFiles

/-! ## 3 A block's clause, carried to witnesses with a token -/

namespace Iop.Reduction

/-- **A block in front of the reply's round hands the token on.** From the block's own clause, which
names no token, and a transport of the token's part of the relations on accepted transcripts: the
clause at witnesses with a token, the extractor leaving it as it is, AT THE SAME ERRORS. -/
def PassesOf : Prop :=
  ∀ (A B WA WB Tok : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop)
    (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape)
    (Φ : A → WA → Tok → Prop) (Φ' : B → WB → Tok → Prop),
    K.Know on RA RB ext ε →
    (∀ a τ b w t, on a → K.out a τ = some b → RB b w → RA a (ext a τ w) →
      Φ' b w t → Φ a (ext a τ w) t) →
    K.Know on (fun a (w : WA × Tok) => RA a w.1 ∧ Φ a w.1 w.2)
      (fun b (w : WB × Tok) => RB b w.1 ∧ Φ' b w.1 w.2) (fun a τ w => (ext a τ w.1, w.2)) ε

/-- **The block of the reply's round lays the token.** saidK: the token that the block's own
transcript names. In front of the block the token is the witness's; behind it the relation Φ' may
read it off the statement that the block hands on, and does not read the witness's. -/
def SetsOf : Prop :=
  ∀ (A B WA WB Tok : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop)
    (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape)
    (Φ : A → WA → Tok → Prop) (Φ' : B → WB → Prop) (saidK : Tr K.shape → Tok),
    K.Know on RA RB ext ε →
    (∀ a τ b w, on a → K.out a τ = some b → RB b w → RA a (ext a τ w) →
      Φ' b w → Φ a (ext a τ w) (saidK τ)) →
    K.Know on (fun a (w : WA × Tok) => RA a w.1 ∧ Φ a w.1 w.2)
      (fun b (w : WB × Tok) => RB b w.1 ∧ Φ' b w.1) (fun a τ w => (ext a τ w.1, saidK τ)) ε

end Iop.Reduction

/-! ## 4 Two closed statements on the side -/

namespace OnBytes.Slice

/-- At the configuration of a stored table with a record, an index that a word decodes to is in
range. -/
def DecodedInRange : Prop :=
  ∀ (D : DecR) (X : Type) (A : D.Claims X) (R : D.RelationsAndEncoding A)
    (y : Fin (2 ^ D.T.a) → Run.PQ.SgX) (rec : D.Rec) (M : A.Mat),
    (DecR.configurationOfStoredTable A R).D y rec = some M → A.inRange M

end OnBytes.Slice

namespace OnBytes.Flat

/-- At the integer model's instances, where the vocabulary is no larger than the field's prime: the
reply as the programs compare it, read as a token, is the instance's own. -/
def TokenOfReply : Prop :=
  ∀ (P : Inst.Model.Params) (x : Instance' P), P.V ≤ pW.toNat →
    OnBytes.K.tokenOf #[replyOf x] = x.y.val

end OnBytes.Flat
