-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TopPlain.lean: THE END THEOREM ON THE PLAIN ROAD, ITS MEANING BEING THE INTEGER
MODEL'S. One definition and six theorems. NO RESULT ON THE PROTOCOL: a rule, of whose premises no
description of the protocol is shown to meet one.

WHAT IS STILL A LETTER, FIRST: all that Johnson/P5J/TopMeans.lean names (hid, dec, req; the table's
`Meaning`; get); repS, the reader of the reply that was heard, off the first chain's record;
Ex, the first chain's extractors as functions of a block's two statements; THE SECOND AND THE THIRD
CHAIN'S CONDITIONS AND RELATIONS (Pl₀), the truths L₁, L₂ behind the first and the second chain, the
keys.

What is said. `proofSound_at_descB` (Johnson/Desc/Plain/BothAtDesc.lean) gives the
proof file's named hypothesis on soundness at a description's own decision from one plain law a
block, three implications at the chains' ends (`Glues`), one key, three bounds, and ONE PREMISE
"tie": from the public tests, the last test's yes and M (what the first chain's yes means, between
the file's statement and the chain's last one) to the object's relation AT THE REQUEST WITH ITS OWN
REPLY.

Main names:
  `meansM`: M := some witness meets the integer model's relation (`firstAt`) at the file's
    statement, AND ITS TOKEN IS WHATEVER REPLY THE CHAIN'S LAST RECORD HOLDS. (That the record holds
    one is asked of nobody: who knows it, the last test's yes, spends it.)
  `tie_at_means`: **"tie", PAID**: from first_border_on; hd, hp; the joint `firstRel_of_firstAt`;
    the last test's yes gives "the reply heard is the request's own" (finReply); the reply put back
    gives the request (`glueReq`).
  `means_of_steps`: the second half of the first glue: along the first chain's steps (`QE` with
    `TokStep`, Johnson/Desc/Sound/LeadsE.lean) a witness at the chain's last statement gives M, if
    no reply is heard at the start (`steps_token_all`, Johnson/Desc/Sound/LeadsAll.lean).
  `glue_first_at_means`: the first glue WHOLE, as a term, from the two halves of the joint with the
    shared chain said apart, and h0. `glues_at_means`: Lean holds it against the field's own type.
    THESE TWO AND `means_of_steps` STAND AT A DESCRIPTION OVER ANY TYPE OF INSTANCES.
  `proofSound_plain_at_means`: **THE END THEOREM**: `proofSound_at_descB` at the full size's frame,
    at the first chain's conditions and relations from the table of joints, its first premise from
    `EachGoodIn` and `EachE` (`eachLeadsE`), "tie" paid.

THE PREMISES THAT ARE LEFT, EACH WITH ITS OWNER. LS, hR, h, A: the integer model's files' · hO, hf,
fit: the pieces are the description's blocks, tiled, and the data fit: paid elsewhere from two tests
on the description (`paidAtDesc`): not called here · good₁: the kinds' files, through the table ·
eachE: the table's extractor's make, and "what was heard of the reply stays": this folder's ·
e₂: the shared chain's files · e₃: the third chain's files · G: the three glues: this folder's; its
first's second half by `means_of_steps`, WHICH ASKS h0 (at the chain's first record no reply is
heard: by the make of the description's start) and hw (the truth L₁ behind the first chain gives a
witness of the table's last relation) · first_border_on: nobody's yet · hd, hp: what dec and req
read off the chain's first record are the decoder's value at the record and the request without its
reply: by the make of dec, req, get, and a fact on the description's own `pub` and start (no map
back from the public part is asked) · pubEarly: the reply's word is no part of what the chains are
started from: the description's files · finReply: the last test compares the reply heard with the
request's own: the description's files · oneKey · b₁, b₂, b₃: numbers · `H.seams` (a law inside the
record H): the three seams of the model's relation, at every witness.

Silly members (thoughts; no `example` yet). A last test that says yes to all: with pubEarly,
finReply asks one term to be two requests' replies: no member. One that says no to all: finReply
and the third glue are free, and the end sentence holds for nothing: rightly. At repS := fun _ =>
none finReply forces the last test never to say yes.

Limits: those of TopMeans.lean, LeadsE.lean and BothAtDesc.lean; ft is idle, as there. A statement
in other files over `proofSound_at_descB` with the pieces and the data paid is not called: it
was not in the build on which this file was written.
Nothing on completeness; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TopJoint
import Johnson.Desc.Plain.BothAtDesc
import Johnson.Desc.Sound.LeadsAll

set_option autoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.First (ModelPart Numbers)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ

/-- **What the first chain's yes means, between the file's statement and the chain's last one**:
some witness meets the integer model's relation at the file's statement, AND ITS TOKEN IS WHATEVER
REPLY THE CHAIN'S LAST RECORD HOLDS. repS: the reader of the reply that was heard. AT ANY TYPE OF
INSTANCES Xi: at a description laid on another type along a map f (`FileDescription.pull`) it is this
relation at f's values, by unfolding. -/
def meansM {X : Model.Verify.Public} (pp : ScalesAndPolicy) (N : MatrixNums) (DP : WholeD) {Xi : Type}
    (F : FileDescription Xi) (all : List LeftT) {W P : Type} (H : HidAt X P W N.rows (colsAt N))
    (get : F.XiPub × F.S₁ → P × TS) (ft : ℕ) (repS : F.XiPub × F.S₁ → Option (Fin ppref.V)) :
    Xi × (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str →
      (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop :=
  fun a b => ∃ w₀, firstAt (D := DP.at frS.P.T.a) (all := all) pp putReq H ft get
    ((F.pub a.1, F.start₁ (F.pub a.1)), (a.2, fun _ => [])) w₀ ∧
      ∀ t, repS b.1 = some t → (H.hid w₀).tok = t

/-- At a description laid on another type of instances, M is M at the map's values. -/
theorem meansM_pull {X : Model.Verify.Public} (pp : ScalesAndPolicy) (N : MatrixNums) (DP : WholeD)
    {Xi Xi' : Type} (f : Xi' → Xi) (F : FileDescription Xi) (all : List LeftT) {W P : Type}
    (H : HidAt X P W N.rows (colsAt N)) (get : F.XiPub × F.S₁ → P × TS) (ft : ℕ)
    (repS : F.XiPub × F.S₁ → Option (Fin ppref.V))
    (a : Xi' × (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
    (b : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str) :
    meansM pp N DP (F.pull f) all H get ft repS a b =
      meansM pp N DP F all H get ft repS (f a.1, a.2) b := rfl

section Gen

/-! ## 1 The first chain's steps give M, and the first glue: over any type of instances -/

variable {pp : ScalesAndPolicy} {X : Model.Verify.Public} (N : MatrixNums) (DP : WholeD) {Xi : Type}
  (F : FileDescription Xi) (all : List LeftT) {W P : Type} (H : HidAt X P W N.rows (colsAt N))
  (get : F.XiPub × F.S₁ → P × TS) (ft : ℕ) (repS : F.XiPub × F.S₁ → Option (Fin ppref.V))
  (Q₀ : PlacesAt (DP.at frS.P.T.a) all F W) (Nn : Numbers)
  (Mg : VerifiableInference.Desc.First.Meaning P W) (links : List ModelPart) (ps : List Place)
  (Ex : ℕ → (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → W → W)

set_option quotPrecheck false in
/-- The file's conditions and relations: the first chain's from the table of joints, with the
integer model's relation in front. -/
local notation "QM" => placesM (D := DP.at frS.P.T.a) (all := all) ft Nn Mg links ps get
  (firstAt pp putReq H ft get) Q₀

set_option quotPrecheck false in
/-- The relation of a block's two statements: the promise behind; one witness carried, by the
extractor as a function of the two statements; what is sure of the reply. -/
local notation "Q1" => QE (F := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (QM).on₁
  (QM).R₁ Ex (TokStep Ex (fun w => (H.hid w).tok) fun b => repS b.1)

/-- **The second half of the plain road's first glue**: along the first chain's steps, from a
witness at the chain's last statement: M. h0: at the start no reply is heard. -/
theorem means_of_steps (x : Xi)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
    (b : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str) (m : ℕ)
    (hs : steps Q1 0 m ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])) b)
    (h0 : repS (F.pub x, F.start₁ (F.pub x)) = none)
    (hw : ∃ w, (QM).R₁ (0 + 1 + m) b w) : meansM pp N DP F all H get ft repS (x, y) b := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨w₀, h₁, h₂⟩ := steps_token_all (QM).on₁ (QM).R₁ Ex (fun w => (H.hid w).tok)
    (fun b => repS b.1) m 0 _ b hs w hw
  exact ⟨w₀, h₁, h₂ h0⟩

#print axioms means_of_steps

variable {X₁ X₂ : Type} (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ W)
  (Pl₀ : PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → Prop)

set_option quotPrecheck false in
/-- The plain road's conditions and relations: the first chain's from the table. -/
local notation "PL" => ({ Pl₀ with on₁ := (QM).on₁, Q₁ := Q1 } :
  PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))

/-- **THE PLAIN ROAD'S FIRST GLUE, AS A TERM**: from the two halves of the joint between the first
chain's end and the shared chain's start, said apart (onEnd: the promise; relEnd: the truth behind
the first chain gives a witness of the table's last relation), and h0: at the chain's first record
no reply is heard. MEANT AS the field g₁ of `Glues` at these letters: `glues_at_means` holds it so.
-/
theorem glue_first_at_means
    (onEnd : ∀ b, (QM).on₁ (1 + (atDesc F T).l₁.length) b →
      (PL).on₂ 0 ((atDesc F T).in₂ b.1, b.2))
    (relEnd : ∀ b, L₁ b → ∃ w, (QM).R₁ (1 + (atDesc F T).l₁.length) b w)
    (h0 : ∀ x, repS (F.pub x, F.start₁ (F.pub x)) = none)
    (x : Xi)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
    (b : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str)
    (_ : (PL).on₁ 0 ((atDesc F T).in₁ x, (y, fun _ => [])))
    (hs : steps (PL).Q₁ 0 (atDesc F T).l₁.length ((atDesc F T).in₁ x, (y, fun _ => [])) b) :
    (PL).on₂ 0 ((atDesc F T).in₂ ((atDesc F T).out₁ x b.1), b.2) ∧
      (L₁ ((atDesc F T).out₁ x b.1, b.2) →
        meansM pp N DP F all H get ft repS (x, y) ((atDesc F T).out₁ x b.1, b.2)) :=
  ⟨onEnd b (steps_on (QM).on₁ (QM).R₁ Ex (fun w => (H.hid w).tok) (fun b => repS b.1) _ 0 _ b hs),
    fun hL => means_of_steps N DP F all H get ft repS Q₀ Nn Mg links ps Ex x y b _ hs (h0 x)
      (relEnd b hL)⟩

#print axioms glue_first_at_means

/-- **The three glues with the first one paid**: the second and the third name no M: they are taken
from any record of glues at these places. (So Lean holds `glue_first_at_means` against the field's
own type.) -/
theorem glues_at_means {M₀ : Xi × (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop}
    (G₀ : Glues (atDesc F T) PL M₀ L₁ L₂)
    (onEnd : ∀ b, (QM).on₁ (1 + (atDesc F T).l₁.length) b →
      (PL).on₂ 0 ((atDesc F T).in₂ b.1, b.2))
    (relEnd : ∀ b, L₁ b → ∃ w, (QM).R₁ (1 + (atDesc F T).l₁.length) b w)
    (h0 : ∀ x, repS (F.pub x, F.start₁ (F.pub x)) = none) :
    Glues (atDesc F T) PL (meansM pp N DP F all H get ft repS) L₁ L₂ :=
  ⟨glue_first_at_means N DP F all H get ft repS Q₀ Nn Mg links ps Ex T Pl₀ L₁ onEnd relEnd h0,
    G₀.g₂, G₀.g₃⟩

#print axioms glues_at_means

end Gen

section Plain

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (N : MatrixNums) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
  (F : FileDescription ((kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)) (all : List LeftT)
  {W P : Type} (H : HidAt X P W N.rows (colsAt N)) (get : F.XiPub × F.S₁ → P × TS) (ft : ℕ)
  (repS : F.XiPub × F.S₁ → Option (Fin ppref.V))

/-- **THE PLAIN ROAD'S PREMISE "tie", AT THE MEANING.** -/
theorem tie_at_means (LS : LayersSay) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (A : Hd.PublicCore X.P)
    (on0 : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
    (first_border_on : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str), F.okStart x = true →
      (kcReq N pp E).conf.D y x.2 ≠ none →
      on0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])))
    (hd : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      H.dec (get (F.pub x, F.start₁ (F.pub x)))
        (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (y, fun _ => [])) =
        (kcReq N pp E).conf.D y x.2)
    (hp : ∀ x, H.req (get (F.pub x, F.start₁ (F.pub x))) = reqWithoutReply x.1)
    (pubEarly : ∀ x rec, F.pub (reqWithoutReply x, rec) = F.pub (x, rec))
    (finReply : ∀ x rec s₁ s₂ s₃, F.fin (x, rec) s₁ s₂ s₃ = true →
      repS (F.pub (x, rec), s₁) = some (dropReq x))
    (x : (kcReq N pp E).conf.X) (rec : (kcReq N pp E).conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
    (z : (EAll (DP.at frS.P.T.a) all).Str) (hok : F.okStart (x, rec) = true)
    (hfin : F.fin (x, rec) s₁ s₂ s₃ = true)
    (hM : on0 ((F.pub (reqWithoutReply x, rec), F.start₁ (F.pub (reqWithoutReply x, rec))),
        (y, fun _ => [])) →
      meansM pp N DP F all H get ft repS ((reqWithoutReply x, rec), y) ((F.pub (x, rec), s₁), z)) :
    (kcReq N pp E).conf.D y rec = none ∨
      ∃ i, (kcReq N pp E).conf.D y rec = some i ∧ (kcReq N pp E).conf.Rno i x () := by
  cases hD : (kcReq N pp E).conf.D y rec with
  | none => exact Or.inl rfl
  | some i =>
    refine Or.inr ⟨i, rfl, ?_⟩
    have hon := first_border_on (x, rec) y hok (by
      show (kcReq N pp E).conf.D y rec ≠ none
      rw [hD]; exact Option.some_ne_none i)
    rw [← pubEarly x rec] at hon
    obtain ⟨w₀, hw, ht⟩ := hM hon
    have et : (H.hid w₀).tok = dropReq x := ht _ (finReply x rec s₁ s₂ s₃ hfin)
    rw [pubEarly x rec] at hw
    have hrel := firstRel_of_firstAt LS hR h A N E DP H ft get _ w₀
      ((reqWithoutReply x, rec), y) (hd (x, rec) y) (hp (x, rec)) hw
    have h3 := hrel i hD
    have h4 : putReq (reqWithoutReply x) (H.hid w₀).tok = x := by
      rw [et]; exact glueReq N pp E x
    exact h4 ▸ h3

#print axioms meansM_pull
#print axioms tie_at_means

/-! ## 2 "tie"'s letters go on: the table's -/

variable (Q₀ : PlacesAt (DP.at frS.P.T.a) all F W) (Nn : Numbers)
  (Mg : VerifiableInference.Desc.First.Meaning P W) (links : List ModelPart) (ps : List Place)
  (Ex : ℕ → (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → W → W)

set_option quotPrecheck false in
/-- The file's conditions and relations: the first chain's from the table of joints, with the
integer model's relation in front. -/
local notation "QM" => placesM (D := DP.at frS.P.T.a) (all := all) ft Nn Mg links ps get
  (firstAt pp putReq H ft get) Q₀

set_option quotPrecheck false in
/-- The relation of a block's two statements: the promise behind; one witness carried, by the
extractor as a function of the two statements; what is sure of the reply. -/
local notation "Q1" => QE (F := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (QM).on₁
  (QM).R₁ Ex (TokStep Ex (fun w => (H.hid w).tok) fun b => repS b.1)

/-! ## 3 The end theorem, on the plain road -/

variable (DK : WholeD) {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k)
  (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (silK : (kcReq N pp E).conf.Rec → TFk → TJk → T3k → Bool)
  (runK : (kcReq N pp E).conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding (kcReq N pp E).conf.Rec frS.P.T.a) (n : ℕ) {X₁ X₂ κ : Type}
  (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ W)
  (Pl₀ : PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₁)
  (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₂)
  (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₃)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → κ)
  (Pv : (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL n
    reqWithoutReply none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                    eL n reqWithoutReply none) Pv)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                     eL n reqWithoutReply none) Pv)

set_option quotPrecheck false in
/-- The plain road's conditions and relations: the first chain's from the table. -/
local notation "PL" => ({ Pl₀ with on₁ := (QM).on₁, Q₁ := Q1 } :
  PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))

/-- **THE PROOF FILE'S NAMED HYPOTHESIS ON SOUNDNESS, AT A DESCRIPTION'S OWN DECISION, ON THE PLAIN
ROAD, ITS MEANING BEING THE INTEGER MODEL'S.** -/
theorem proofSound_plain_at_means (LS : LayersSay) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (A : Hd.PublicCore X.P)
    (hO : OfDesc F T) (hf : (atDesc F T).Fits) (fit : RowFit (DP.at frS.P.T.a) all all)
    (good₁ : EachGoodIn (QM).on₁ (QM).R₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (eachE : EachE (QM).on₁ Ex (TokStep Ex (fun w => (H.hid w).tok) fun b => repS b.1) 0
      ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (e₂ : EachLeadsBN key (PL).on₂ (PL).Q₂ n 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (e₃ : EachLeads (PL).on₃ (PL).Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
    (G : Glues (atDesc F T) PL (meansM pp N DP F all H get ft repS) L₁ L₂)
    (first_border_on : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str), F.okStart x = true →
      (kcReq N pp E).conf.D y x.2 ≠ none →
      (QM).on₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])))
    (hd : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      H.dec (get (F.pub x, F.start₁ (F.pub x)))
        (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (y, fun _ => [])) =
        (kcReq N pp E).conf.D y x.2)
    (hp : ∀ x, H.req (get (F.pub x, F.start₁ (F.pub x))) = reqWithoutReply x.1)
    (pubEarly : ∀ x rec, F.pub (reqWithoutReply x, rec) = F.pub (x, rec))
    (finReply : ∀ x rec s₁ s₂ s₃, F.fin (x, rec) s₁ s₂ s₃ = true →
      repS (F.pub (x, rec), s₁) = some (dropReq x))
    (F₁ : (kcReq N pp E).conf.Rec → (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP (kcReq N pp E) DP tFp tJp t3p F all T PL h₁ h₂ h₃
        (meansM pp N DP F all H get ft repS) L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
    (b₁ : _root_.Iop.Err.Below
      (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at frS.P.T.a).ds₁ h₁) U.εs)
    (b₂ : _root_.Iop.Err.Below
      (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at frS.P.T.a).ds₂ h₂) U.εs)
    (b₃ : _root_.Iop.Err.Below
      (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at frS.P.T.a).ds₃ h₃) U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK
                                                               runK silP F.run eL n reqWithoutReply none) Pv Tl U) :=
  proofSound_at_descB (Kc := kcReq N pp E) (DK := DK) (DP := DP) (tFk := tFk) (tJk := tJk)
    (t3k := t3k) (tFp := tFp) (tJp := tJp) (t3p := t3p) (silK := silK) (runK := runK)
    (silP := silP) (eL := eL) (N := n) (early := reqWithoutReply) (F := F) (all := all) (T := T)
    (Pl := PL) (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (M := meansM pp N DP F all H get ft repS)
    (L₁ := L₁) (L₂ := L₂) (d := d) (key := key) (P := Pv) (Tl := Tl) (U := U) () hO hf fit
    (eachLeadsE _ _ _ _ _ 0 good₁ eachE) e₂ e₃ G pubEarly F₁ oneKey
    (fun x rec y _ s₁ s₂ s₃ z hok _ hfin hM =>
      tie_at_means N E DP F all H get ft repS LS hR h A ((QM).on₁ 0) first_border_on hd hp
        pubEarly finReply x rec y s₁ s₂ s₃ z hok hfin hM)
    b₁ b₂ b₃

#print axioms proofSound_plain_at_means

end Plain

end P5J
