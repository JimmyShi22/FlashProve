-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Meaning/TieAtSome.lean: the letter M of the proof file's plain form as "SOME hidden
values meet the integer model's relation, and their token is whatever reply the first chain's last
record holds", and the premise `tie` of `proofSound_at_descB` (Johnson/Desc/Plain/BothAtDesc.lean)
AT THAT M.

Why. M stands twice among the premises of the rule for a proof file, once each way: the first chain
has to GIVE it ("what it hands on is true, so M"), and `tie` has to SPEND it ("the file's yes and M
give the relation of the top"). A weaker M is easier to give and harder to spend. Two files have
laid an M: at one named reading of the hidden values (`meansM`,
Johnson/Goal/Meaning/SpentAtPlain.lean) and at some witness of a table (`P5J.meansM`). Each should
give the M of this file, by a lemma that is owed and has content: for the first, that its reader of
the token and rep agree; for the second, that the witness's table is what the configuration's
decoder makes of the stored word. Neither needs that all witnesses name one table. Neither M's
own `tie` carries over to it. Here `tie` is shown at it, from two owed fields.
  `meansSome X rep`: THE M. rep: the reader of the reply that was heard, off the first chain's last
  record. "Some" ranges over `Meaning.Hid` (Johnson/Goal/Meaning/Row.lean) alone: the reply's token,
  the lists of integer matrices of the groups of layers, the lists of the attention sub-proofs, the
  stream behind the last layer: THE HIDDEN TRACE; it holds no weight and no table: the weights enter
  as what the configuration's own decoder makes of the stored word with the record.
  `TieOwesSome`: what a description owes for `tie` at it: two fields (see `P5J.tieOwesSome_at`).
      on        where the test on the instance says yes at (x, rec) and the stored word decodes with
      the record, the first chain's first promise holds at x without its reply;
      finReply  where that test and the last test say yes at (x, rec) and a last record s₁ of the
      first chain, rep reads a token off s₁ that, put into x without its reply, gives x.
  `tie_of_some`: in scope, `TieOwesSome` gives the premise `tie`, to the letter, at `meansSome`. The
  premise's clause on the three plain messages (silP) is taken and not used.
  `meansSome_full_unheard`: a control: at a last record off which rep reads nothing, the token's
  clause is idle: M says only that some hidden values meet the relation at the request without its
  reply.
Limits. A RULE AND A LIST: NOTHING PAID HERE; NO MEMBER. All the bite of M against a false reply
is the token's clause, which is an implication: it bites only at a last record off which rep reads a
token; `finReply` is what says that the last test's yes gives such a record. The proof is that of
`tie_of_means` (SpentAtPlain.lean), which spends its named hidden values only as some term. The
full size alone. Nothing on completeness or hiding. No soundness follows from this file alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Plain.BothAtDesc
import Johnson.Goal.Meaning.RowProved

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Road OnBytes.Road.L5
open _root_.Meaning (Hid firstMeans)

variable (N₀ : MatrixNums) (pp : Inst.Model.ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N₀ pp)) (DP : WholeD)
  {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (silP : (kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec → TFp → TJp → T3p → Bool)
  (F : FileDescription ((kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec)) (all : List LeftT)
  {X₁ X₂ W : Type} (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ W)
  (Pl : PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (X : OnBytes.Model.Verify.Public) (rep : F.XiPub × F.S₁ → Option (Fin Inst.Model.ppref.V))

/-- **THE M**: some hidden values meet the relation at the first boundary, and their token is
whatever reply the first chain's last record holds. -/
def meansSome : ((kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec) ×
      (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop :=
  fun a c => ∃ h : Hid, firstMeans X pp putReq ((kcReq N₀ pp E).conf.D a.2 a.1.2) a.1.1 h ∧
    ∀ t, rep c.1 = some t → h.tok = t

/-- **The hypotheses on a description for `tie` at that M**: two fields, which a caller supplies. -/
structure TieOwesSome : Prop where
  on : ∀ (x : Flat.Req) rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) M,
    F.okStart (x, rec) = true → (kcReq N₀ pp E).conf.D y rec = some M →
      Pl.on₁ 0 ((atDesc F T).in₁ (reqWithoutReply x, rec), (y, fun _ => []))
  finReply : ∀ (x : Flat.Req) rec (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃),
    F.okStart (x, rec) = true → F.fin (x, rec) s₁ s₂ s₃ = true →
      ∃ t, rep (F.pub (x, rec), s₁) = some t ∧ putReq (reqWithoutReply x) t = x

/-- **The premise `tie` of `proofSound_at_descB`, to the letter, at `meansSome`.** -/
theorem tie_of_some {Z : VerifierAndGoals.PublicFiles} {lay : Option ByteArray} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    (O : TieOwesSome N₀ pp E DP F all T Pl rep) :
    ∀ x rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).sh) (s₁ : F.S₁) (s₂ : F.S₂)
      (s₃ : F.S₃) (z : (EAll (DP.at frS.P.T.a) all).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).msgF τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F T).in₁ (reqWithoutReply x, rec), (y, fun _ => [])) →
        (meansSome N₀ pp E DP F all X rep) ((reqWithoutReply x, rec), y)
          ((F.pub (x, rec), s₁), z)) →
      (kcReq N₀ pp E).conf.D y rec = none ∨
        ∃ i, (kcReq N₀ pp E).conf.D y rec = some i ∧ (kcReq N₀ pp E).conf.Rno i x () := by
  intro x rec y τ s₁ s₂ s₃ z hs _ hf hM
  cases hD : (kcReq N₀ pp E).conf.D y rec with
  | none => exact Or.inl rfl
  | some Mx =>
    refine Or.inr ⟨Mx, rfl, ?_⟩
    obtain ⟨w, hm, ht⟩ := hM (O.on x rec y Mx hs hD)
    obtain ⟨t, e1, e2⟩ := O.finReply x rec s₁ s₂ s₃ hs hf
    have hm' : firstMeans X pp putReq ((kcReq N₀ pp E).conf.D y rec) (reqWithoutReply x) w := hm
    have hIn := _root_.Meaning.inRange_of_letters (claimsReqAt (frS.toDecR frZ 402653181) N₀ pp)
      (relationsAndEncodingOfClaims _ E) DP y rec Mx hD
    have f := _root_.Meaning.frameRel_of_firstMeans _root_.Meaning.layersSay hR h
      (Hd.core_of_scope hZ hR h) hm' Mx hD hIn
    rw [ht t e1, e2] at f
    exact f

/-- **A control: where no reply is read, the token's clause is idle.** -/
theorem meansSome_full_unheard
    (a : ((kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec) ×
      (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
    (c : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str) (hc : rep c.1 = none) :
    meansSome N₀ pp E DP F all X rep a c ↔
      ∃ w : Hid, firstMeans X pp putReq ((kcReq N₀ pp E).conf.D a.2 a.1.2) a.1.1 w :=
  ⟨fun ⟨w, hw, _⟩ => ⟨w, hw⟩, fun ⟨w, hw⟩ => ⟨w, hw, fun t ht => by rw [hc] at ht; cases ht⟩⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.tie_of_some
#print axioms VerifiableInference.OnPublicFiles.meansSome_full_unheard
