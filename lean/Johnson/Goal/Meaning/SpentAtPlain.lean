-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/SpentAtPlain.lean: WHERE THE LOWER HALF OF THE MEANING IS SPENT ON THE PLAIN
ROAD, AT ITS USER's OWN LETTERS: the letter M and the premises `tie` and `Glues.g₁` of
`proofSound_at_descB_fin` (Johnson/Desc/Plain/BothAtDescFin.lean), the rule that ends in
`CompilerSoundnessConditionStatements.proofSound`, at the full size's configuration kcReq N₀ pp E.

Why. In that rule M is a free letter: "what is known of the file's statement once the first chain
has handed on b and b is true". The meaning's rows (the kinds' K03_means to K08_means, the join
means_at_each_seat) have a user only if M is laid so that they are needed. On the road with
extractors that was done (RowOwes, TieRow, top_of_row: Johnson/Goal/Meaning/Row.lean, RowTop.lean).
On the plain road nothing lays M. Here it is laid.

Main names.
  `meansM X hid`: THE M: firstMeans (Row.lean) at the request in front (without its reply), at what
    the stored word decodes to with the record, at what hid reads off WHAT THE FIRST CHAIN HANDS ON:
    its last record and all committed strings. It reads both ends, as TieShadow.lean asks.
  `TieOwes`: what a description owes for `tie` at that M: two fields.
      on    where the test on the instance says yes at (x, rec) and the stored word decodes with
            the record, the first chain's first promise holds at x without its reply (the list's
            row first_border_on);
      back  where that test and the last test say yes at (x, rec) and a last record s₁ of the first
            chain, the token that hid reads off s₁, put into x without its reply, gives x
            (putReq_back_iff: it is x's own reply wherever the reply counts).
  `tie_of_means`: in scope, TieOwes gives the premise `tie`, to the letter, at meansM.
  `back_tells`: a control: under `back` one last record passes the last test at one request at most
    among those that differ in the reply alone.
  `hidBy X s seat tokOf msgOf`: hid by the integer model's dictionary hidAtF: a token and, for each
    of the 25 sub-proofs, the messages that it reads, both read off what is handed on.
  `JoinOwes`: what a description owes for `Glues.g₁`'s second half at that M: the test on sizes, two
    inequalities, and, WHERE THE FIRST CHAIN's STEPS HOLD AND WHAT IT HANDS ON IS TRUE (L₁):
      reads   reader's and owner's readings agree (ReadsOne);
      twelve  the twelve clauses (Twelve, HidFirst.lean) at the sub-proofs' own lists, at every
              index that the decoded matrix holds, at the request with the read token put in.
            THIS FIELD IS WHERE K03_means … K08_means ARE SPENT.
  `means_of_join`, `glues_of_join`: JoinOwes gives that half; with the gluing at the trivial M, the
    gluing at meansM.
  `proofSound_of_join`: so `CompilerSoundnessConditionStatements.proofSound`, from the rule's other premises, TieOwes, JoinOwes.

The two silly members. A description whose last test says yes to all: `back` fails wherever two
requests share what is left without the reply and the reply counts (one s₁, two replies). One that
says no to all: TieOwes.back holds for nothing, as every statement on soundness does there; `on`
and JoinOwes read no decision.
Every "there is", walked: none in TieOwes or JoinOwes. tokOf, msgOf, s, seat are letters of the
statement: whoever closes it at a description names them as functions; msgOf may decode by choice:
no verifier reads it.
Limits. A RULE AND TWO LISTS: NOTHING IS PAID HERE; NO MEMBER. `twelve` is asked at all b with the
steps and L₁, without the last test's yes: at a request whose e is before the window's end and a
read token that is not 0, putReq gives the request with the reply 0 (putReq_else,
Johnson/Flat/TiesAtReq.lean): the head's clauses are then owed at the reply 0 whatever was heard.
lay is a free letter. The full size alone. Nothing on completeness or hiding.
-/
import Johnson.Desc.Plain.BothAtDescFin
import Johnson.Goal.Meaning.RowProved
import Johnson.Goal.Meaning.HidFirst

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
open _root_.Compile.Joined (Chains Desc worst_le)
open _root_.CompileK.Joined (Row)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Road OnBytes.Road.L5
open _root_.Iop.Reduction (steps)
open _root_.Meaning (Hid Msgs firstMeans Twelve ReadsOne sizesFit ownAtF hidAtF)

variable (N₀ : MatrixNums) (pp : Inst.Model.ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N₀ pp)) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : (kcReq N₀ pp E).conf.Rec → TFk → TJk → T3k → Bool)
  (runK : (kcReq N₀ pp E).conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : (kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding (kcReq N₀ pp E).conf.Rec frS.P.T.a) (N : ℕ)
  (F : FileDescription ((kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec)) (all : List LeftT) {X₁ X₂ W κ :
             Type}
  (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ W) (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
  (Pl : PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDescFin F g T).p₁ (atDescFin F g T).l₁).shape = uLT (ckP .two) (DP.at
      frS.P.T.a).ds₁)
  (h₂ : (rowIOR (atDescFin F g T).p₂ (atDescFin F g T).l₂).shape = uLT (ckP .two) (DP.at
      frS.P.T.a).ds₂)
  (h₃ : (rowIOR (atDescFin F g T).p₃ (atDescFin F g T).l₃).shape = uLT (ckP .two) (DP.at
      frS.P.T.a).ds₃)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → κ)

variable (X : OnBytes.Model.Verify.Public) (hid : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a)
    all).Str → Hid)

/-- **THE M**: the relation at the first boundary, at what hid reads off what the first chain hands
on. -/
def meansM : ((kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec) × (oneExternalString (2 ^ (DP.at frS.P.T.a).a)
    SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop :=
  fun a b => firstMeans X pp putReq ((kcReq N₀ pp E).conf.D a.2 a.1.2) a.1.1 (hid b)

/-- **What a description owes for `tie` at that M.** -/
structure TieOwes : Prop where
  on : ∀ (x : Flat.Req) rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) M,
    F.okStart (x, rec) = true → (kcReq N₀ pp E).conf.D y rec = some M →
      Pl.on₁ 0 ((atDescFin F g T).in₁ (reqWithoutReply x, rec), (y, fun _ => []))
  back : ∀ (x : Flat.Req) rec (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
    (z : (EAll (DP.at frS.P.T.a) all).Str),
    F.okStart (x, rec) = true → F.fin (x, rec) s₁ s₂ s₃ = true →
      putReq (reqWithoutReply x) (hid ((F.pub (x, rec), s₁), z)).tok = x

/-- **The premise `tie` of `proofSound_at_descB_fin`, to the letter, at meansM.** -/
theorem tie_of_means {Z : VerifierAndGoals.PublicFiles} {lay : Option ByteArray} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    (O : TieOwes N₀ pp E DP F all T g Pl hid) :
    ∀ x rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ :
          F.S₃)
      (z : (EAll (DP.at frS.P.T.a) all).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).msgF τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDescFin F g T).in₁ (reqWithoutReply x, rec), (y, fun _ => [])) →
        (meansM N₀ pp E DP F all X hid) ((reqWithoutReply x, rec), y) ((F.pub (x, rec), s₁), z)) →
      (kcReq N₀ pp E).conf.D y rec = none ∨ ∃ i, (kcReq N₀ pp E).conf.D y rec = some i ∧ (kcReq N₀
          pp E).conf.Rno i x () := by
  intro x rec y τ s₁ s₂ s₃ z hs _ hf hM
  cases hD : (kcReq N₀ pp E).conf.D y rec with
  | none => exact Or.inl rfl
  | some Mx =>
    refine Or.inr ⟨Mx, rfl, ?_⟩
    have hm : firstMeans X pp putReq ((kcReq N₀ pp E).conf.D y rec) (reqWithoutReply x)
        (hid ((F.pub (x, rec), s₁), z)) := hM (O.on x rec y Mx hs hD)
    have hIn := _root_.Meaning.inRange_of_letters (claimsReqAt (frS.toDecR frZ 402653181) N₀ pp)
      (relationsAndEncodingOfClaims _ E) DP y rec Mx hD
    have f := _root_.Meaning.frameRel_of_firstMeans _root_.Meaning.layersSay hR h
      (Hd.core_of_scope hZ hR h) hm Mx hD hIn
    rw [O.back x rec s₁ s₂ s₃ z hs hf] at f
    exact f

/-- **A control: `back` bites.** Under it one last record of the first chain passes the last test at
ONE request at most among those that share what is left without the reply. So a description whose
two tests say yes to all does not meet TieOwes as soon as two requests differ in the reply alone. -/
theorem back_tells (O : TieOwes N₀ pp E DP F all T g Pl hid)
    (pubEarly : ∀ x rec, F.pub (reqWithoutReply x, rec) = F.pub (x, rec)) (x x' : Flat.Req) rec
    (s₁ : F.S₁) (s₂ s₂' : F.S₂) (s₃ s₃' : F.S₃) (z : (EAll (DP.at frS.P.T.a) all).Str)
    (he : reqWithoutReply x' = reqWithoutReply x) (hs : F.okStart (x, rec) = true)
    (hf : F.fin (x, rec) s₁ s₂ s₃ = true) (hs' : F.okStart (x', rec) = true)
    (hf' : F.fin (x', rec) s₁ s₂' s₃' = true) : x' = x := by
  have a := O.back x rec s₁ s₂ s₃ z hs hf
  have b := O.back x' rec s₁ s₂' s₃' z hs' hf'
  have p : F.pub (x', rec) = F.pub (x, rec) := by
    rw [← pubEarly x' rec, ← pubEarly x rec, he]
  rw [p, he] at b
  exact b.symm.trans a

variable (s : ℕ → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
  (tokOf : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Fin Inst.Model.ppref.V)
  (msgOf : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → ℕ → Msgs)

/-- What is hidden, by the integer model's dictionary, read off what the first chain hands on. -/
def hidBy : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Hid :=
  fun b => hidAtF X s seat (tokOf b) (msgOf b)

/-- **What a description owes for the second half of `Glues.g₁` at that M.** -/
structure JoinOwes : Prop where
  fit : sizesFit X s = true
  h0 : ∀ k < 25, (0 : ℤ) < ((s k).beta : ℤ)
  h2 : ∀ k < 25, 2 * ((s k).beta : ℤ) ≤ 2 ^ 18
  reads : ∀ b, L₁ b → ReadsOne X s seat (msgOf b)
  twelve : ∀ (x : (kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) (b : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a)
                     all).Str),
    Pl.on₁ 0 ((atDescFin F g T).in₁ x, (y, fun _ => [])) →
    steps Pl.Q₁ 0 (atDescFin F g T).l₁.length ((atDescFin F g T).in₁ x, (y, fun _ => [])) b →
    L₁ ((atDescFin F g T).out₁ x b.1, b.2) →
    ∀ M (i : Cm.Idx), (kcReq N₀ pp E).conf.D y x.2 = some M → Flat.Holds M i →
      Twelve X i (putReq x.1 (tokOf ((atDescFin F g T).out₁ x b.1, b.2))).val
        (ownAtF s seat (msgOf ((atDescFin F g T).out₁ x b.1, b.2)))

/-- **The second half of `Glues.g₁` at meansM.** -/
theorem means_of_join {Z : VerifierAndGoals.PublicFiles} {lay : Option ByteArray} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    (J : JoinOwes N₀ pp E DP F all T g Pl L₁ X s seat tokOf msgOf)
    (x : (kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) (b : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a)
                     all).Str)
    (ho : Pl.on₁ 0 ((atDescFin F g T).in₁ x, (y, fun _ => [])))
    (hs : steps Pl.Q₁ 0 (atDescFin F g T).l₁.length ((atDescFin F g T).in₁ x, (y, fun _ => [])) b)
    (hl : L₁ ((atDescFin F g T).out₁ x b.1, b.2)) :
    (meansM N₀ pp E DP F all X (hidBy N₀ pp E DP F all X s seat tokOf msgOf)) (x, y) ((atDescFin F g
        T).out₁ x b.1, b.2) :=
  _root_.Meaning.firstMeans_of_twelve_seat hZ hR h J.fit (J.reads _ hl) J.h0 J.h2 putReq _ x.1 _
    (J.twelve x y b ho hs hl)

/-- **The gluing at meansM**, from the gluing at the trivial M and JoinOwes. -/
theorem glues_of_join {Z : VerifierAndGoals.PublicFiles} {lay : Option ByteArray} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    (J : JoinOwes N₀ pp E DP F all T g Pl L₁ X s seat tokOf msgOf)
    (G₀ : Glues (atDescFin F g T) Pl (fun _ _ => True) L₁ L₂) :
    Glues (atDescFin F g T) Pl (meansM N₀ pp E DP F all X (hidBy N₀ pp E DP F all X s seat tokOf
        msgOf)) L₁ L₂ :=
  ⟨fun x y b ho hs => ⟨(G₀.g₁ x y b ho hs).1,
      means_of_join N₀ pp E DP F all T g Pl L₁ X s seat tokOf msgOf hZ hR h J x y b ho hs⟩,
    G₀.g₂, G₀.g₃⟩

variable (P : (filesOf (kcReq N₀ pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N
    reqWithoutReply
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf (kcReq N₀ pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                      eL N reqWithoutReply
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf (kcReq N₀ pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL
                                       N reqWithoutReply
                                     none) P)

/-- **`CompilerSoundnessConditionStatements.proofSound` on the plain road WITH THE MEANING LAID IN**: the rule's other premises,
and
the two lists. -/
theorem proofSound_of_join {Z : VerifierAndGoals.PublicFiles} {lay : Option ByteArray} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    (O : TieOwes N₀ pp E DP F all T g Pl (hidBy N₀ pp E DP F all X s seat tokOf msgOf))
    (J : JoinOwes N₀ pp E DP F all T g Pl L₁ X s seat tokOf msgOf) (hO : OfDesc F T) (hg : FinGives
        F g) (hf :
    (atDescFin F g T).Fits)
    (fit : RowFit (DP.at frS.P.T.a) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDescFin F g T).p₁ :: (atDescFin F g T).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ N 0 ((atDescFin F g T).p₂ :: (atDescFin F g T).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDescFin F g T).p₃ :: (atDescFin F g T).l₃))
    (G₀ : Glues (atDescFin F g T) Pl (fun _ _ => True) L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (reqWithoutReply x, rec) = F.pub (x, rec))
    (F₁ : (kcReq N₀ pp E).conf.Rec → (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainPF (kcReq N₀ pp E) DP tFp tJp t3p F all T g Pl h₁ h₂ h₃
        (meansM N₀ pp E DP F all X (hidBy N₀ pp E DP F all X s seat tokOf msgOf)) L₁ L₂ d).out₁ ((x,
            rec), y) τ = some b →
      key 0 ((atDescFin F g T).in₂ b.1, b.2) = F₁ rec y)
    (b₁ : Err.Below (errOwn (atDescFin F g T).p₁ (atDescFin F g T).l₁ (DP.at frS.P.T.a).ds₁ h₁)
        U.εs)
    (b₂ : Err.Below (errOwn (atDescFin F g T).p₂ (atDescFin F g T).l₂ (DP.at frS.P.T.a).ds₂ h₂)
        U.εs)
    (b₃ : Err.Below (errOwn (atDescFin F g T).p₃ (atDescFin F g T).l₃ (DP.at frS.P.T.a).ds₃ h₃)
        U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf (kcReq N₀ pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK
                                                                 runK silP
                                                               F.run eL N reqWithoutReply none) P Tl U) :=
  proofSound_at_descB_fin (kcReq N₀ pp E) DK DP tFk tJk t3k tFp tJp t3p silK runK silP eL N
      reqWithoutReply F
    all T g Pl h₁ h₂ h₃ (meansM N₀ pp E DP F all X (hidBy N₀ pp E DP F all X s seat tokOf msgOf)) L₁
        L₂ d key P Tl U () hO hg hf fit e₁ e₂ e₃
    (glues_of_join N₀ pp E DP F all T g Pl L₁ L₂ X s seat tokOf msgOf hZ hR h J G₀) pubEarly F₁
    oneKey (tie_of_means N₀ pp E DP tFp tJp t3p silP F all T g Pl X (hidBy N₀ pp E DP F all X s seat
        tokOf msgOf) hZ hR h O) b₁ b₂ b₃

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.tie_of_means
#print axioms VerifiableInference.OnPublicFiles.back_tells
#print axioms VerifiableInference.OnPublicFiles.means_of_join
#print axioms VerifiableInference.OnPublicFiles.glues_of_join
#print axioms VerifiableInference.OnPublicFiles.proofSound_of_join
