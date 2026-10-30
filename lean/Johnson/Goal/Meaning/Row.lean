-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/Row.lean: the meaning's half of the proof file's soundness, in the top
theorem's own type, with the relation at the first boundary named and every premise a named field.

THE ROW. The theorem on the compiled verifier (proofSound_top_links,
Johnson/TypedOracleCompiler/Joined/ProofLinksTop.lean) has a premise tieR; at a description's own decision it is
RowTies (Johnson/Flat/ProofOfRow.lean): under the file's verifier's yes at (x, rec): if what the
three chains' extractors give is a witness of the first relation at the request without its reply
(asked where the first condition holds there), then the stored word does not decode with the record,
or it decodes to a matrix at which the interface's relation holds AT x ITSELF.

WHAT THIS FILE FIXES. The first relation R₀ and its witnesses W₀:
  Hid        what the prover hides: the reply's token; the lists of integer matrices of the 12
             groups of layers and of the 12 attention sub-proofs; the last stream as the head's
             sub-proof holds it.
  Means      what these must say, at an index i and a request x: for each group of layers six named
             clauses (MeansG), for each attention sub-proof six (MeansA), for the head two (MeansH).
             Each clause's docstring names the kinds of block whose text is written to show it.
  Share, MeansFrom   the same cut by sub-proof: MeansFrom k is the shares from sub-proof k on: its
             own share and MeansFrom (k + 1); MeansFrom 0 is Means. IT IS THE MEANING'S CONJUNCT OF
             A BOUNDARY'S RELATION AND NOT THAT RELATION: a sub-proof puts out with claims pending
             (on the carried message, on the weights, for the later chains), and the relation behind
             it has to say that these hold: boundary k = MeansFrom k and what is pending at k, read
             off the statement that is handed on. What is pending is not stated here.
  firstMeans the relation at the first boundary: at every index that the matrix holds to which the
             stored word decodes, Means holds, at the public part of the request with the witness's
             token put in. (That the matrix holds an index is the decoder's own test.)
  RowOwes    R₀ fixed to firstMeans, and what is asked of a description beside: three named fields.
  TieRow     THE ROW, closed: at all public files in the goals' scope, at the full size's frame, for
             every row of three chains: RowOwes gives RowTies.

THE PROOF, and what it rests on. tieRow_of: TieRow from one statement, LayersSay: "the conditions of
the 24 sub-proofs of the layers, with their two kinds of seams and the bound that a head gives, say
that the integer program runs through all 48 layers, and that the stream which the last group's list
holds is the program's". It is stated in Johnson/Goal/Meaning/LayersSayStatement.lean; this file
takes it as a hypothesis by name. The other steps:
says_of_halves (Johnson/Meaning/Halves.lean), frameRel_iff_says (Johnson/Goal/Meaning/Frame.lean),
core_of_scope (Johnson/Goal/Meaning/ScopeCore.lean), and the way of the sheet on ties (tiesOfFive,
Johnson/Flat/TiesSheetProofs.lean): cases on what the word decodes to; onOk; first; back.

THE TOKEN. The sheet asks two things of the token: the extractors' token is the token that the
transcript names (TieReads), and that is the request's own reply (TieFins), both at every request.
The proof needs less: TieBack, "the request without its reply, with the extractors' token put in, is
the request". By putReq_back_iff that asks the token to be the reply only where the reply counts (e
is the window's end: not_before_iff_end); before the window's end the reply is 0, putReq takes no
other, and nothing is asked. So a description whose last test did not look at the named token there
would still meet it. The sheet's two give it (tieBack_of_reads_fins); so do TieReads and the second
asked only where the reply counts (tieBack_of_reads_finsLate): on the sheet's own way too the
hypothesis is the lighter one.

THE KINDS OF BLOCK that the brackets name (the table of kinds of the proof file's description): K1 a
sending of committed arrays · K3 a lookup · K4 the own rounds of a group of layers · K5 those of an
attention sub-proof · K6 those of the head · K7 the round in which the reply is heard · K8 the
smallness test · K11 the merge of the claims on the committed weights. Parts that several kinds
call: P1 a masked sumcheck · P6 a normalisation's row. Other names: cellsA S Za: the library's
reading of an attention sub-proof's cells in its list; dimOf, sclOf, tbOf: the library's sizes,
scales and tables made of the shape S (Johnson/Road/Lane5AttDef.lean); Hd.shapeA X g: the shape of
the attention sub-proof of group g; castT: integers read in the field.

What is not claimed.
- THE WEIGHT: that the row of three chains is knowledge sound from firstMeans ("knows"). It is no
  field of RowOwes. With the lists projected away firstMeans is the interface's relation itself
  (means_iff_true, Johnson/Goal/Meaning/RowGuard.lean), so naming it lowers no difficulty; its worth
  is the cut into 25 shares in the sub-proofs' own terms.
- That any description meets onOk, back.
- That the description which the verifier folds calls the text of the kinds named in the brackets. A
  bracket names the kind whose text is written to show the clause. That the fold seats that kind
  with its claims is shown nowhere here.
- That each block's cells, shapes and tables are those of which Means speaks: the library's
  dictionary (cellsAt, cellsOf, addrA), the record X, the tables tbRef. X is what publicOf returns,
  a reader written after the C++ source; a description's plan calls it
  (Johnson/Meaning/PlanIsPublic.lean). Of the description's own tables at K3: that these are tbRef's
  is shown nowhere; `look_tabs` (Johnson/Goal/Meaning/LookScope.lean: in scope, the files read,
  `publicOf` returns) speaks of X.y.fo alone.
- The two seams LaySeam and AttSeam are asked at all rows and columns, outside the arrays too. The
  proof spends them at the places that are read alone. Lists can be made so that they hold by the
  make (a borrowed array is read in its owner's list); what is then left is that reader and owner
  read one array.
- One index for all clauses is no hypothesis: a matrix holds at most one. The hypothesis is that
every
  sub-proof's weights are what the stored word decodes to: norm, hot take i.mat as a passenger; emb,
  key and MeansH.plain read it.
- lay is a free letter, not Z.lay. Nothing on probabilities or on hiding. The full size alone.
-/
import Johnson.Goal.Meaning.Frame
import Johnson.Goal.Meaning.LayersSayStatement
import Johnson.Goal.Meaning.ScopeCore
import Johnson.Road.Rows.LayerTop
import Johnson.Flat.TiesAtReq
import Johnson.Flat.TiesSheetProofs

set_option autoImplicit false
set_option maxRecDepth 40000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open Inst.Model.AttSeg (Raw Idn idnVal keyVec lut lutSet castT)
open VerifiableInference.OnPublicFiles.Flat (Holds GE Req)

/-- **What the prover hides.** -/
structure Hid where
  /-- the reply's token -/
  tok : Fin ppref.V
  /-- the list of integer matrices of each group of layers -/
  MG : ℕ → Mats ℤ
  /-- the list of each attention sub-proof -/
  MA : ℕ → Zs
  /-- the stream behind the last layer, as the head's sub-proof holds it -/
  Xl : ℕ → Vec

/-! ## The clauses, each by name -/

/-- The stream that comes into a later group is the stream that went out of the group before: number
iXI of group g's list against number iXO of the list of group g - 1, at all rows and columns. -/
def LaySeam (y : Lay) (MG : ℕ → Mats ℤ) (g : ℕ) : Prop :=
  0 < g → ∀ r c, MG g (matIx y).iXI r c = MG (g - 1) (matIx y).iXO r c

/-- The cells of an attention sub-proof are below 2^18. -/
def AttSmall (S : Attention.Shape) (Za : Zs) : Prop :=
  ∀ c : Raw, c.Valid (dimOf S) → |cellsA S Za c| < 2 ^ 18

/-- Every looked-up value of the four calls is an entry of its table. -/
def AttKey (S : Attention.Shape) (Za : Zs) : Prop :=
  ∀ (c : Fin 4) (n : ℕ), n < (dimOf S).used c →
    keyVec (scl := sclOf S) (dimOf S) (tbOf S) (castT (cellsA S Za) : Raw → Cb.Gl.F) c n ∈
      lutSet (lut (scl := sclOf S) (dimOf S) (tbOf S) c)

/-- The bits of the index of a row's largest score are bits. -/
def AttOwn1 (S : Attention.Shape) (Za : Zs) : Prop :=
  ∀ k b g' n, (Idn.at1 k b g' n).Valid (dimOf S) →
    idnVal (dimOf S) (castT (cellsA S Za) : Raw → Cb.Gl.F) (.at1 k b g' n) = 0

/-- The row's largest score is the score at that index. -/
def AttOwn2 (S : Attention.Shape) (Za : Zs) : Prop :=
  ∀ b g' n, (Idn.at2 b g' n).Valid (dimOf S) →
    idnVal (dimOf S) (castT (cellsA S Za) : Raw → Cb.Gl.F) (.at2 b g' n) = 0

/-- The denominator is the sum of the row's weights. -/
def AttRidden (S : Attention.Shape) (Za : Zs) : Prop :=
  ∀ b g' n, (Idn.at3 b g' n).Valid (dimOf S) →
    idnVal (dimOf S) (castT (cellsA S Za) : Raw → Cb.Gl.F) (.at3 b g' n) = 0

/-- An attention sub-proof's copy of the one array qa (number NAs + 3 of its list) is its group's
(number iQA of the group's list), at all rows and columns. -/
def AttSeam (y : Lay) (S : Attention.Shape) (Mg : Mats ℤ) (Za : Zs) : Prop :=
  ∀ r c, Za (S.cf.NAs + 3) r c = Mg (matIx y).iQA r c

/-- The head's last stream is the stream that the last group's list holds behind its last layer. -/
def HeadSeam (y : Lay) (Mg : Mats ℤ) (Xl : ℕ → Vec) : Prop := Agree ppref Xl (lastOf y Mg)

/-- The head's half in plain integers, at the index's own output matrix. -/
def HeadPlain (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref) (Xl : ℕ → Vec) : Prop :=
  SaysHead pp.nf pp.pol i.index.val.H x Xl

/-- **What a group of layers' sub-proof must say**: group g, at its own list MG g (and, for the
seam, the list of the group before). In brackets: the kinds of block whose text is written to show
the clause. -/
structure MeansG (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) (MG : ℕ → Mats ℤ)
    (g : ℕ) : Prop where
  /-- [K8, the smallness test] the entries of the group's matrices are below 2^18 -/
  small : SmallM X.y (MG g)
  /-- [K4 with P6, P1] the 17 identities of each normalisation's row of digits and carries -/
  norm : NormField (layerShape X.P) X.layers.sc X.y g (MG g) i.mat x
  /-- [K4, at K3's point] a router's selector has entries that sum to 1 -/
  hot : HotField (layerShape X.P) X.layers.sc X.y g (MG g) i.mat x
  /-- [K4 with K11] in the first group the stream that comes in is the tokens' embedding -/
  emb : EmbField (layerShape X.P) X.layers.sc X.y g (MG g) i.mat x
  /-- [K3 with K4 and K11] every entry of the eight key vectors, in which every product with a
  weight matrix stands, is an entry of its table -/
  key : KeyField (layerShape X.P) X.layers.sc X.y g (MG g) i.mat
  /-- [the commitments: one array for owner and reader] -/
  seam : LaySeam X.y MG g

/-- **What an attention sub-proof must say**: at its own list Za, of the shape S; Mg: its group's
list. -/
structure MeansA (y : Lay) (S : Attention.Shape) (Mg : Mats ℤ) (Za : Zs) : Prop where
  /-- [K8] -/
  small : AttSmall S Za
  /-- [K3 with K5] the scores and the accumulators stand in these values -/
  key : AttKey S Za
  /-- [K5] -/
  own1 : AttOwn1 S Za
  /-- [K5] -/
  own2 : AttOwn2 S Za
  /-- [at K3's point, by the link's law on guests] -/
  ridden : AttRidden S Za
  /-- [the commitments: one array for owner and reader] -/
  seam : AttSeam y S Mg Za

/-- **What the output head's sub-proof must say.** -/
structure MeansH (X : Model.Verify.Public) (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref) (w : Hid) :
    Prop where
  /-- [the commitments, with the head's reading of the limbs] -/
  seam : HeadSeam X.y (w.MG 11) w.Xl
  /-- [K6 with P6, K3, K8; K7 for the token; K11, the merge and the later chains' linear claims for
  the output matrix, which the head's sub-proof reads in the committed weights and commits nowhere
  itself]. UNLIKE THE OTHER CLAUSES, which are equations of cells and memberships in tables, this
  one is a conclusion: it applies the integer program's own functions to Xl and the output matrix.
  Its clause "form" holds of every request of the frame (head3_of_req). -/
  plain : HeadPlain pp i x w.Xl

/-- **What the hidden values must say**, at the public part X, the settings pp, the index i and the
request x: 12 groups of layers, 12 attention sub-proofs, the head. -/
structure Means (X : Model.Verify.Public) (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref) (w : Hid) :
    Prop where
  layers : ∀ g < 12, MeansG X i x w.MG g
  attention : ∀ g < 12, MeansA X.y (Hd.shapeA X g) (w.MG g) (w.MA g)
  head : MeansH X pp i x w

/-- The share of sub-proof k: 2 g is group g of layers, 2 g + 1 its attention, 24 the head. -/
def Share (X : Model.Verify.Public) (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref) (w : Hid) (k : ℕ) :
    Prop :=
  if k = 24 then MeansH X pp i x w
  else if k % 2 = 0 then MeansG X i x w.MG (k / 2)
  else MeansA X.y (Hd.shapeA X (k / 2)) (w.MG (k / 2)) (w.MA (k / 2))

/-- The shares from sub-proof k on: the meaning's conjunct of the relation at the boundary in front
of sub-proof k. -/
def MeansFrom (X : Model.Verify.Public) (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref) (w : Hid)
    (k : ℕ) : Prop :=
  ∀ k', k ≤ k' → k' < 25 → Share X pp i x w k'

section
variable {X : Model.Verify.Public} {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref} {w : Hid}

/-- **Means is the 25 shares.** -/
theorem means_iff_from : Means X pp i x w ↔ MeansFrom X pp i x w 0 := by
  constructor
  · intro M k _ hk
    unfold Share
    split
    · exact M.head
    · split
      · exact M.layers _ (by omega)
      · exact M.attention _ (by omega)
  · intro H
    refine ⟨fun g hg => ?_, fun g hg => ?_, ?_⟩
    · have h := H (2 * g) (Nat.zero_le _) (by omega)
      unfold Share at h
      rwa [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega] at h
    · have h := H (2 * g + 1) (Nat.zero_le _) (by omega)
      unfold Share at h
      rwa [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega] at h
    · have h := H 24 (Nat.zero_le _) (by omega)
      unfold Share at h
      rwa [if_pos rfl] at h

/-- In front of sub-proof k: its own share, and what is to be shown behind it. -/
theorem meansFrom_succ (k : ℕ) (hk : k < 25) :
    MeansFrom X pp i x w k ↔ Share X pp i x w k ∧ MeansFrom X pp i x w (k + 1) :=
  ⟨fun H => ⟨H k le_rfl hk, fun k' h1 h2 => H k' (by omega) h2⟩,
    fun H k' h1 h2 => by
      rcases Nat.eq_or_lt_of_le h1 with rfl | h
      · exact H.1
      · exact H.2 k' h h2⟩

/-- Behind the last sub-proof no share is left. (Claims are: see the head of this file.) -/
theorem meansFrom_end : MeansFrom X pp i x w 25 := fun _ h1 h2 => absurd h2 (by omega)

theorem MeansG.ord {MG : ℕ → Mats ℤ} {g : ℕ} (M : MeansG X i x MG g) :
    LayerOrd (layerShape X.P) X.layers.sc X.y g (MG g) i.mat x :=
  layer_start M.small M.norm M.hot M.emb M.key

theorem MeansA.ord {y : Lay} {S : Attention.Shape} {Mg : Mats ℤ} {Za : Zs}
    (M : MeansA y S Mg Za) : AttOrd S Za :=
  ⟨⟨M.small, M.key, fun j hj => by
    cases j with
    | at1 k b g' n => exact M.own1 k b g' n hj
    | at2 b g' n => exact M.own2 b g' n hj
    | at3 b g' n => exact M.ridden b g' n hj⟩⟩

/-- **The 14 clauses give the plain statements.** -/
theorem says_of_means (LS : LayersSay) {Z : VerifierAndGoals.PublicFiles} {lay : Option ByteArray}
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (A : Hd.PublicCore X.P) (M : Means X pp i x w) :
    Says pp i.index.val x (streamOf pp i.index.val x) := by
  have h0 : (0 : ℤ) ≤ pp.nf.eps := le_trans (by norm_num) (lawful_of_read hR).nf.1
  have hb : ∀ pos < ppref.T, ∀ j < ppref.d, |lastOf X.y (w.MG 11) pos j| < 2 ^ 39 :=
    fun pos hp j hj => by
      rw [← M.head.seam pos hp j hj]
      exact last_bound h0 M.head.plain.normOK pos hp j hj
  obtain ⟨L, hA⟩ := LS Z pp lay X hR h A i x w.MG w.MA (fun g hg => (M.layers g hg).ord)
    (fun g hg => (M.attention g hg).ord) (fun g h0 hg => (M.layers g hg).seam h0)
    (fun g hg => (M.attention g hg).seam) hb
  exact says_of_halves L M.head.plain
    (fun pos hp j hj => (M.head.seam pos hp j hj).trans (hA pos hp j hj)) (fun _ _ _ => rfl)

end

/-- **The relation at the first boundary.** dec: what the stored word decodes to. put: the public
part of a request with a token put in. It is asked at every index that the decoded matrix holds:
that the matrix holds one is the decoder's own test (it yields matrices in range alone), so no block
has to show it. -/
def firstMeans {rows cols : ℕ} (X : Model.Verify.Public) (pp : ScalesAndPolicy)
    (put : Req → Fin ppref.V → Req) (dec : Option (Fin rows → Fin cols → GE)) (p : Req) (w : Hid) :
    Prop :=
  ∀ M (i : Cm.Idx), dec = some M → Holds M i → Means X pp i (put p w.tok).val w

/-- It tells the interface's relation. -/
theorem frameRel_of_firstMeans (LS : LayersSay) {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy}
    {lay : Option ByteArray} {X : Model.Verify.Public} (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (A : Hd.PublicCore X.P) {rows cols : ℕ}
    {put : Req → Fin ppref.V → Req} {dec : Option (Fin rows → Fin cols → GE)} {p : Req} {w : Hid}
    (H : firstMeans X pp put dec p w) (M : Fin rows → Fin cols → GE) (hM : dec = some M)
    (hIn : VerifiableInference.OnPublicFiles.Flat.InRange M) : frameRel pp M (put p w.tok).val := by
  obtain ⟨i, hi⟩ := hIn
  exact (frameRel_iff_says (lawful_of_read hR) (polCond_of_read hR) M _).2
    ⟨i, hi, _, says_of_means LS hR h A (H M i hM hi)⟩

/-- Every request of the frame has its form. -/
theorem head3_of_req (x : Req) : Head3 x.val :=
  ⟨x.property.1, x.val.e_le, x.property.2⟩

end Meaning

namespace Meaning

open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open _root_.Iop (oneExternalString Tr)
open _root_.Run _root_.Run.PQ
open _root_.CompileK.Joined (Row)

/-- **The request without its reply, with a token put in, is the request itself** exactly if the
token is the request's own reply or the reply does not count: e is before the window's end, where
the reply is 0 and putReq takes no other. -/
theorem putReq_back_iff (x : Flat.Req) (t : Fin ppref.V) :
    putReq (reqWithoutReply x) t = x ↔ (¬ x.val.e < ppref.T → t = x.val.y) := by
  constructor
  · intro h hT
    have hv := putReq_val (reqWithoutReply x) t (fun he => absurd he hT)
    rw [h] at hv
    exact (congrArg (fun q : Instance ppref => q.y) hv).symm
  · intro h
    by_cases hT : x.val.e < ppref.T
    · have e0 : (⟨0, ppref_V_pos⟩ : Fin ppref.V) = x.val.y := Fin.ext (x.property.2 hT).symm
      by_cases ht : t.val = 0
      · have e1 : t = dropReq x := Fin.ext (ht.trans (x.property.2 hT).symm)
        rw [e1]
        exact putReq_glue x
      · rw [putReq_else (reqWithoutReply x) t hT ht]
        refine Subtype.ext ?_
        show ({ x.val with y := ⟨0, ppref_V_pos⟩ } : Instance ppref) = x.val
        rw [e0]
    · rw [h hT]
      exact putReq_glue x

/-- A request's e is not before the window's end exactly if it is the window's end: no instance has
it behind. -/
theorem not_before_iff_end (x : Flat.Req) : ¬ x.val.e < ppref.T ↔ x.val.e = ppref.T :=
  ⟨fun h => le_antisymm x.val.e_le (not_lt.1 h), fun h => by rw [h]; exact lt_irrefl _⟩

section
variable (pp : ScalesAndPolicy) (N : MatrixNums)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
  {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (silP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → TFp → TJp → T3p → Bool)
  (runP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (L₁ L₂ : List LeftT) {X₁ X₂ : Type}
  (run₁ : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → PQ.View → Option X₁)
  (run₂ : X₁ → PQ.View → Option X₂) (run₃ : X₂ → PQ.View → Bool)
  (S : (rowP (kcReq N pp E) DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).Snd) (hid : S.W₀ → Hid)

/-- **Under the file's verifier's yes, the request without its reply, with the token put in that the
three extractors give, is the request itself.** -/
def TieBack : Prop :=
  ∀ (x : Flat.Req) rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).sh),
    (reductionOfWholeFile (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p silP runP).out (x, rec) y τ = some () →
    putReq (reqWithoutReply x)
      (hid ((linksP (kcReq N pp E) DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).ext
        ((reqWithoutReply x, rec), y) τ ())).tok = x

/-- What it asks: under the yes, where the reply counts, the extractors' token is the request's own
reply. Before the window's end nothing. -/
theorem tieBack_iff :
    TieBack pp N E DP tFp tJp t3p silP runP L₁ L₂ run₁ run₂ run₃ S hid ↔
      ∀ (x : Flat.Req) rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
        (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).sh),
        (reductionOfWholeFile (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p silP runP).out (x, rec) y τ = some () →
        ¬ x.val.e < ppref.T →
        (hid ((linksP (kcReq N pp E) DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).ext
          ((reqWithoutReply x, rec), y) τ ())).tok = x.val.y :=
  ⟨fun H x rec y τ hy => (putReq_back_iff x _).1 (H x rec y τ hy),
    fun H x rec y τ hy => (putReq_back_iff x _).2 (H x rec y τ hy)⟩

/-- **The sheet's two ties on the token give it.** said: the token that a transcript of the whole
file names. -/
theorem tieBack_of_reads_fins
    (said : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).sh → Option (Fin ppref.V))
    (reads : TieReads (kcReq N pp E) DP tFp tJp t3p silP runP reqWithoutReply L₁ L₂ run₁ run₂ run₃ S
      (fun w => (hid w).tok) said)
    (fins : TieFins (kcReq N pp E) DP tFp tJp t3p silP runP dropReq said) :
    TieBack pp N E DP tFp tJp t3p silP runP L₁ L₂ run₁ run₂ run₃ S hid := by
  intro x rec y τ hy
  have ht := Option.some.inj ((reads x rec y τ hy).symm.trans (fins x rec y τ hy))
  exact (congrArg (putReq (reqWithoutReply x)) ht).trans (putReq_glue x)

/-- **The lighter hypothesis on the sheet's own way**: the sheet's tie on the extractors' token, and
its
tie on the named token asked only where the reply counts, give it. -/
theorem tieBack_of_reads_finsLate
    (said : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).sh → Option (Fin ppref.V))
    (reads : TieReads (kcReq N pp E) DP tFp tJp t3p silP runP reqWithoutReply L₁ L₂ run₁ run₂ run₃ S
      (fun w => (hid w).tok) said)
    (fins : ∀ (x : Flat.Req) rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p).sh),
      (reductionOfWholeFile (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p silP runP).out (x, rec) y τ = some () →
      ¬ x.val.e < ppref.T → said τ = some x.val.y) :
    TieBack pp N E DP tFp tJp t3p silP runP L₁ L₂ run₁ run₂ run₃ S hid :=
  (tieBack_iff pp N E DP tFp tJp t3p silP runP L₁ L₂ run₁ run₂ run₃ S hid).2
    fun x rec y τ hy hT =>
      Option.some.inj ((reads x rec y τ hy).symm.trans (fins x rec y τ hy hT))

end

/-- **What is asked of a description**, at the full size's frame. S: the relations, conditions and
extractors of the row of three chains. hid: what a witness of its first relation hides. -/
structure RowOwes (X : Model.Verify.Public) (pp : ScalesAndPolicy) (N : MatrixNums)
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
    {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp) (t3p : T3p)
    (silP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → TFp → TJp → T3p → Bool)
    (runP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
    (L₁ L₂ : List LeftT) {X₁ X₂ : Type}
    (run₁ : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → PQ.View → Option X₁)
    (run₂ : X₁ → PQ.View → Option X₂) (run₃ : X₂ → PQ.View → Bool)
    (S : (rowP (kcReq N pp E) DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).Snd) (hid : S.W₀ → Hid) :
    Prop where
  /-- [whoever lays the row's relations] THE FIRST RELATION IS firstMeans at what the witness hides.
  No law: it fixes the letter R₀. The weight lies where the row is shown knowledge sound FROM this
  relation: "knows", a premise of the top theorem and no field here. -/
  first : ∀ (p : Flat.Req) rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) (w : S.W₀),
    S.R₀ ((p, rec), y) w ↔ firstMeans X pp putReq ((kcReq N pp E).conf.D y rec) p (hid w)
  /-- [the rule of composition] under the yes, where the word decodes, the first chain's clause
  speaks of the statement at the request without its reply -/
  onOk : TieOnOk (kcReq N pp E) DP tFp tJp t3p silP runP reqWithoutReply L₁ L₂ run₁ run₂ run₃ S
  /-- [K7, every block behind it and the last test; every kind of the first chain, on its
  extractor's text] under the yes, where the reply counts, the token in what the extractors give is
  the request's own reply (tieBack_iff) -/
  back : TieBack pp N E DP tFp tJp t3p silP runP L₁ L₂ run₁ run₂ run₃ S hid

/-- **THE ROW.** -/
def TieRow : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (pp : ScalesAndPolicy) (lay : Option ByteArray) (X : Model.Verify.Public),
    VerifierAndGoals.InScope Z = true → VerifierAndGoals.readFiles Z = .ok pp → publicOf Z.pol Z.KL lay = .ok X →
    ∀ (N : MatrixNums) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
      (TFp TJp T3p : Type) (tFp : TFp) (tJp : TJp) (t3p : T3p)
      (silP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → TFp → TJp → T3p → Bool)
      (runP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec →
        PQ.View → PQ.View → PQ.View → Bool)
      (L₁ L₂ : List LeftT) (X₁ X₂ : Type)
      (run₁ : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → PQ.View → Option X₁)
      (run₂ : X₁ → PQ.View → Option X₂) (run₃ : X₂ → PQ.View → Bool)
      (S : (rowP (kcReq N pp E) DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).Snd) (hid : S.W₀ → Hid),
      RowOwes X pp N E DP tFp tJp t3p silP runP L₁ L₂ run₁ run₂ run₃ S hid →
      RowTies (kcReq N pp E) DP tFp tJp t3p silP runP reqWithoutReply L₁ L₂ run₁ run₂ run₃ S
        (fun _ => ())

/-- What a word decodes to, at the letters of a stored table's configuration, is in range. -/
theorem inRange_of_letters {D : DecR} {X : Type} (A : D.Claims X) (R : D.RelationsAndEncoding A) (DP : WholeD)
    (y : (oneExternalString (2 ^ (DP.at D.T.a).a) SgX).Str) (rec : (lettersAt A R).conf.Rec)
    (M : (lettersAt A R).conf.I) (h : (lettersAt A R).conf.D y rec = some M) : A.inRange M :=
  decodedInRange D X A R y rec M h

/-- **The row, from what the layers' 24 sub-proofs say.** -/
theorem tieRow_of (LS : LayersSay) : TieRow := by
  intro Z pp lay X hZ hR h N E DP TFp TJp T3p tFp tJp t3p silP runP L₁ L₂ X₁ X₂ run₁ run₂ run₃ S
    hid O x rec y τ hyes hr
  have A := Hd.core_of_scope hZ hR h
  by_cases hn : (kcReq N pp E).conf.D y rec = none
  · exact Or.inl hn
  · obtain ⟨M, hM⟩ := Option.ne_none_iff_exists'.1 hn
    refine Or.inr ⟨M, hM, ?_⟩
    have hs := frameRel_of_firstMeans LS hR h A
      ((O.first (reqWithoutReply x) rec y _).1 (hr (O.onOk x rec y τ hyes hn))) M hM
      (inRange_of_letters (claimsReqAt (frS.toDecR frZ 402653181) N pp) (relationsAndEncodingOfClaims _ E) DP y rec M hM)
    rw [O.back x rec y τ hyes] at hs
    exact hs

end Meaning

#print axioms Meaning.says_of_means
#print axioms Meaning.frameRel_of_firstMeans
#print axioms Meaning.putReq_back_iff
#print axioms Meaning.tieBack_iff
#print axioms Meaning.not_before_iff_end
#print axioms Meaning.tieBack_of_reads_fins
#print axioms Meaning.tieBack_of_reads_finsLate
#print axioms Meaning.tieRow_of
