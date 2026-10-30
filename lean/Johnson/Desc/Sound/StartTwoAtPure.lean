-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/StartTwoAtPure.lean: **AT THE FOLD's PURE DESCRIPTION OF THE PROOF FILE THE VERIFIER's FIRST STATE ON THE SHARED CHAIN READS OF THE INSTANCE THE TABLE's KEY ALONE.** Statements and proofs.
A word on words: "rec" below is the second part of a top's pair (statement, rec): the stored table's key with what the top lays beside it.

What for. "A round shared by the batch is charged once" wants that all slots of a batch have ONE key at the shared chain's head (proofSound_at_descB: the premise oneKey). By
Johnson/Desc/Sound/KeysByMake.lean's oneKeyByMake that comes down, at a description F, to one equation: F.start₂ (F.pub x) is a function of rec (the stored table's key) alone. Here it is shown at the description that is seated.
  start₂_fileDescBy   the description that ProofFile.fileDescBy makes at a shared seat A starts its shared chain at A.start x.pub: by rfl.
  start₂_seatOf       at the seat Desc.K14.sharedSeatOf …: at Desc.K14.first (p14Of c before).codes x.pub.key.
  start₂_pureTail     so for every description G that ProofFile.onlineDescriptionAfterTests Z T P gives, where T's shared seat is Desc.K14.sharedSeatAt Z's: two instances with one key have one first state.
  start₂_pureZ · **start₂_descPure**   and for every description that ProofFile.onlineDescription o pol lay KL gives: NO PREMISE BUT onlineDescription's RETURN.
  request_idle        said the other way: the request's bytes and the reply's are not read.
  s₂Of G k            the first state at the key k, as a term. one_pull: at G.pull f, f a laying of pairs (statement, rec) onto instances whose key is a function k of rec alone: (G.pull f).start₂ ((G.pull f).pub (x, rec)) =
                      s₂Of G (k rec): oneKeyByMake's one premise.
  **oneKey_pull**     the premise oneKey (Johnson/Desc/Plain/BothAtDesc.lean: proofSound_at_descB), TO THE LETTER, at F := G.pull f, key := keyAt Prod.snd (DP.at a).t₁ p₂ l₂ and
                      F₁ rec y := (s₂Of G (k rec), y, fun _ _ => none): from StartTwoByKey G · the laying's equation · OfDesc · Fits.
  one_full | one_small   the laying's equation at the two layings that are seated (LPFD.Full.instanceAsPlainRecord | LPFD.Small.instOf: instOf_key in Johnson/Desc/Laid/ProofFullLaw.lean | ProofSmallLaw.lean, by rfl there): so at both sizes oneKeyByMake's premise holds of
                      (G.pull instOf) FOR EVERY G THAT onlineDescription GIVES.
  **seated_pull**     OfDesc · Fits · RowFit · ONE KEY, TOGETHER AT ONE VALUE: at F := G.pull f and T := the maker's pieces (piecesAt, Johnson/Desc/Sound/PaidAtDesc.lean: paidAtDesc), from: StartTwoByKey G · the laying's equation · G.data file =
                      .ok D · G.planOk = true (its last conjunct is sealLast) · the three flat lists' heads.
  **seated_full | seated_small**   AT WHAT IS LAID: laidPOf o pol lay KL = .ok (D, r) ⟹ there is the G that onlineDescription gives, r is (G.pull instOf).run, AND ALL THAT seated_pull ASKS OF G AND OF THE LAYING HOLDS: NO PREMISE BUT "IT IS LAID". (Left
                      to seated_pull's caller: the three flat lists' heads: that there are such is flatSome, Johnson/Desc/Sound/TilesDataProofs.lean.)
  opens_all           "the shared rounds open no tree below t₁", at every D that G.data gives: opens_own_stretch (Johnson/Desc/K12/Law/OpensOwn.lean) at the whole list.
  **field_at_laid**   THE ROW shared_joint_count's FIELD AND THE FIELD shared_start_is_the_records TOGETHER, AT THE TOP's OWN LETTERS (F := G.pull f · all := allOf (DP.at a) · T := piecesAt (ckP .two) F (DP.at a) … · key := keyAt …): FROM
                      each block's law for N slots (EachLawsBN) and Glues ALONE, beside facts on what is laid: field_of_laws' premises OfDesc · Fits · opens are struck.
  **field_of_debts_at_laid**   THE WHOLE ROAD FROM THE KINDS' PLAIN LAWS TO THE TWO FIELDS, AT THE TOP's OWN LETTERS, AS ONE TERM: the ledger's debts (at each block behind "LIN point" a PLAIN law for ONE statement at the kind's own errors:
                      EachPlainShOwn · EachRides · "LIN point"'s LeadsB with own 1 pt = δK + N · δO · the front block's two · EachOwnBelow 128 · EachCapped 128 · ExtNamed) and the places' two equations and Glues ⟹ field_at_laid's
                      conclusion. INSIDE IT: rowGOfLedger (so ledgerPaysOwn · eachLawsBNOwn_plain · leadsK_of_hands (Johnson/Desc/Plain/KeyAlone.lean) · LeadsK.bothN: εO := 0 behind the point) · rowG_gives_E (eachLawsBN_atCap) · field_of_laws. N STANDS IN ONE
                      PREMISE: own 1 pt = δK + N · δO.
Limits. Of the FIRST STATE alone: that no later block of the shared chain reads a slot's own part is by type (each is lifted from a block at the chain's own state). The instance here is ProofFile.Inst (request · key · reply): how a top's pair
(statement, rec) is laid onto it is that top's. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.OnlineDescription
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.Laid.ProofSmallLaw
import Johnson.Desc.Sound.KeysByMake
import Johnson.Desc.Plain.BothAtDesc
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Desc.Sound.SharedJointCountAtField
import Johnson.Desc.Sound.SharedJointCountLedgerOwn
import Johnson.Desc.K12.Law.OpensOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LT28
open OnBytes VerifiableInference.Desc
open Desc.K14 (St P14 first p14Of sharedSeatOf sharedSeatAt)

/-- Two instances with one key have one first state of the shared chain. -/
def StartTwoByKey (G : FileDescription ProofFile.Inst) : Prop :=
  ∀ x x' : ProofFile.Inst, x.pub.key = x'.pub.key → G.start₂ (G.pub x) = G.start₂ (G.pub x')

theorem start₂_fileDescBy {σ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (get : σ → First.S) (start : ProofFile.InstPub → σ)
    (c : Chain σ ProofFile.Cl) (x : ProofFile.Inst) :
    (ProofFile.fileDescBy o mk Z A B get start c).start₂ ((ProofFile.fileDescBy o mk Z A B get start c).pub x) =
      A.start x.pub := rfl

theorem start₂_seatOf {σ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (cc : Model.Verify.Chains) (before : List (Nat × Nat)) (tests : P14 → List (Block St Unit))
    (standIns : List String) (last : List (Block St Unit) → Block St Unit) (fileOk : Bool)
    (B : ProofFile.SecondSeat) (get : σ → First.S) (start : ProofFile.InstPub → σ) (c : Chain σ ProofFile.Cl)
    (x : ProofFile.Inst) :
    (ProofFile.fileDescBy o mk Z (sharedSeatOf cc before tests standIns last fileOk) B get start c).start₂
      ((ProofFile.fileDescBy o mk Z (sharedSeatOf cc before tests standIns last fileOk) B get start
        c).pub x) = first (p14Of cc before).codes x.pub.key := rfl

theorem start₂_pureTail (Z : ProofFile.Pub) (T : ProofFile.PureSeat) (P : ProofFile.PureParts)
    (G : FileDescription ProofFile.Inst) (h : ProofFile.onlineDescriptionAfterTests Z T P = .ok G) (hT : T.shared = sharedSeatAt Z) :
    StartTwoByKey G := by
  unfold ProofFile.onlineDescriptionAfterTests at h
  cases hb : P.base with
  | error e => rw [hb] at h; cases h
  | ok base =>
    rw [hb] at h
    have h1 : ((ProofFile.chainBy Z base P.frames P.road).bind fun c =>
        match T.shared, T.second with
        | some A, some B =>
          Except.ok (ProofFile.fileDescBy T.older T.links Z A B (fun s => s) (ProofFile.startS Z) c)
        | _, _ => .error "no description: nothing usable is supplied for: a later chain") = .ok G := h
    cases hc : ProofFile.chainBy Z base P.frames P.road with
    | error e => rw [hc] at h1; cases h1
    | ok c =>
      rw [hc] at h1
      have h2 : (match T.shared, T.second with
        | some A, some B =>
          Except.ok (ProofFile.fileDescBy T.older T.links Z A B (fun s => s) (ProofFile.startS Z) c)
        | _, _ => .error "no description: nothing usable is supplied for: a later chain") = .ok G := h1
      rw [hT] at h2
      unfold sharedSeatAt at h2
      cases hN : H2U.placesOfMade Z.made with
      | error e => rw [hN] at h2; cases h2
      | ok N =>
        rw [hN] at h2
        cases hS : T.second with
        | none => rw [hS] at h2; cases h2
        | some B =>
          rw [hS] at h2
          cases h2
          intro x x' hk
          show first _ x.pub.key = first _ x'.pub.key
          rw [hk]

theorem start₂_pureZ (Z : ProofFile.Pub) (T : ProofFile.PureSeat) (G : FileDescription ProofFile.Inst)
    (h : ProofFile.onlineDescriptionFromPublicPart Z T = .ok G) (hT : T.shared = sharedSeatAt Z) : StartTwoByKey G := by
  unfold ProofFile.onlineDescriptionFromPublicPart at h
  cases hB : ProofFile.baseOf Z T with
  | error e => rw [hB] at h; cases h
  | ok B =>
    rw [hB] at h
    have h1 : (if !(ProofFile.faultsAt T B).isEmpty then
        Except.error ("no description: the supplied blocks are inconsistent: " ++
          "; ".intercalate (ProofFile.faultsAt T B))
      else if !(ProofFile.lackingAt T (ProofFile.partsAt T B)).isEmpty then
        .error ("no description: nothing usable is supplied for: " ++
          ", ".intercalate (ProofFile.lackingAt T (ProofFile.partsAt T B)))
      else ProofFile.onlineDescriptionAfterTests Z T (ProofFile.partsAt T B)) = .ok G := h
    split at h1
    · cases h1
    · split at h1
      · cases h1
      · exact start₂_pureTail Z T _ G h1 hT

/-- **AT THE DESCRIPTION THAT IS SEATED.** -/
theorem start₂_descPure (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (G : FileDescription ProofFile.Inst)
    (h : ProofFile.onlineDescription o pol lay KL = .ok G) : StartTwoByKey G := by
  unfold ProofFile.onlineDescription ProofFile.onlineDescriptionFromBlockTables at h
  cases hZ : ProofFile.pureRoad.pub o pol lay KL with
  | error e => rw [hZ] at h; cases h
  | ok Z =>
    rw [hZ] at h
    exact start₂_pureZ Z _ G h rfl

/-- Said the other way: the request's bytes and the reply's are not read. -/
theorem request_idle (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (G : FileDescription ProofFile.Inst)
    (h : ProofFile.onlineDescription o pol lay KL = .ok G) (key : OnBytes.TableKey) (r r' y y' : ByteArray) :
    G.start₂ (G.pub ⟨⟨r, key⟩, y⟩) = G.start₂ (G.pub ⟨⟨r', key⟩, y'⟩) :=
  start₂_descPure o pol lay KL G h _ _ rfl

/-- The first state at a key. -/
def s₂Of (G : FileDescription ProofFile.Inst) (k : OnBytes.TableKey) : G.S₂ :=
  G.start₂ (G.pub ⟨⟨ByteArray.empty, k⟩, ByteArray.empty⟩)

/-- **oneKeyByMake's one premise**, at a laying whose key is a function of rec alone. -/
theorem one_pull {X Rec : Type} (f : X × Rec → ProofFile.Inst) (k : Rec → OnBytes.TableKey)
    (hk : ∀ x rec, (f (x, rec)).pub.key = k rec) (G : FileDescription ProofFile.Inst) (h : StartTwoByKey G)
    (x : X) (rec : Rec) :
    (G.pull f).start₂ ((G.pull f).pub (x, rec)) = s₂Of G (k rec) :=
  h (f (x, rec)) ⟨⟨ByteArray.empty, k rec⟩, ByteArray.empty⟩ (hk x rec)

section
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.Maker

/-- **At the full size's laying**: the right side names rec alone. -/
theorem one_full (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (G : FileDescription ProofFile.Inst)
    (h : ProofFile.onlineDescription o pol lay KL = .ok G) (x : LPFD.Full.XF) (rec : RecFull) :
    (G.pull LPFD.Full.instanceAsPlainRecord).start₂ ((G.pull LPFD.Full.instanceAsPlainRecord).pub (x, rec)) =
      s₂Of G (keyOf (fun β : NZ => β.val) rec) :=
  one_pull LPFD.Full.instanceAsPlainRecord (fun rec => keyOf (fun β : NZ => β.val) rec)
    (fun x rec => LPFD.Full.instOf_key (x, rec)) G (start₂_descPure o pol lay KL G h) x rec

/-- **At the small size's laying.** -/
theorem one_small (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (G : FileDescription ProofFile.Inst)
    (h : ProofFile.onlineDescription o pol lay KL = .ok G) (x : LPFD.Small.XS) (rec : RecSmall) :
    (G.pull LPFD.Small.instOf).start₂ ((G.pull LPFD.Small.instOf).pub (x, rec)) =
      s₂Of G (keyOf (fun β : NZ => β.val) rec) :=
  one_pull LPFD.Small.instOf (fun rec => keyOf (fun β : NZ => β.val) rec)
    (fun x rec => LPFD.Small.instOf_key (x, rec)) G (start₂_descPure o pol lay KL G h) x rec

end

section
open VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Flat OnBytes.Maker _root_.Run _root_.Run.PQ _root_.Iop

variable {a : ℕ} (Kc : ConfLetters a) (DP : WholeD) {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (f : Kc.conf.X × Kc.conf.Rec → ProofFile.Inst) (k : Kc.conf.Rec → OnBytes.TableKey)
  (G : FileDescription ProofFile.Inst) (all : List LeftT) {X₁ X₂ W : Type}
  (T : ThreeAt (ckP .two) (DP.at a) all (G.pull f) X₁ X₂ W)
  (Pl : PPlaces (DP.at a) all ((G.pull f).XiPub × (G.pull f).S₁)
    (((G.pull f).XiPub × (G.pull f).S₁) × (G.pull f).S₂)
    (((G.pull f).XiPub × (G.pull f).S₁ × (G.pull f).S₂) × (G.pull f).S₃))
  (h₁ : (rowIOR (atDesc (G.pull f) T).p₁ (atDesc (G.pull f) T).l₁).shape =
    uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂).shape =
    uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDesc (G.pull f) T).p₃ (atDesc (G.pull f) T).l₃).shape =
    uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    ((G.pull f).XiPub × (G.pull f).S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₁ : ((G.pull f).XiPub × (G.pull f).S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₂ : ((G.pull f).XiPub × (G.pull f).S₁ × (G.pull f).S₂) × (EAll (DP.at a) all).Str → Prop)
  (d : ((G.pull f).XiPub × (G.pull f).S₁) × (EAll (DP.at a) all).Str)

/-- **THE PREMISE oneKey OF proofSound_at_descB, TO THE LETTER.** -/
theorem oneKey_pull (hk : ∀ x rec, (f (x, rec)).pub.key = k rec) (hG : StartTwoByKey G)
    (hO : OfDesc (G.pull f) T) (hf : (atDesc (G.pull f) T).Fits) :
    ∀ x rec y τ b,
      (plainP Kc DP tFp tJp t3p (G.pull f) all T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁ ((x, rec), y) τ =
        some b →
      keyAt Prod.snd (DP.at a).t₁ (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ 0
          ((atDesc (G.pull f) T).in₂ b.1, b.2) =
        ((s₂Of G (k rec) : (G.pull f).S₂), y, fun _ _ => none) :=
  oneKeyByMake (ckP .two) (DP.at a) all Kc.conf.X Kc.conf.Rec X₁ X₂ W TFp TJp T3p tFp tJp t3p
    (G.pull f) T (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) h₁ h₂ h₃
    (fun rec => s₂Of G (k rec)) hO hf (one_pull f k hk G hG)

end

section
open VerifiableInference.Desc.Sound OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (oneExternalString)

/-- **OfDesc · Fits · RowFit · ONE KEY, TOGETHER AT ONE VALUE.** -/
theorem seated_pull {X Rec W : Type} (f : X × Rec → ProofFile.Inst) (k : Rec → OnBytes.TableKey)
    (hk : ∀ x rec, (f (x, rec)).pub.key = k rec) (G : FileDescription ProofFile.Inst) (hG : StartTwoByKey G)
    (file : String) (D : WholeD) (hD : G.data file = .ok D) (hp : G.planOk = true) (C : CK)
    (b₁ : Block (G.pull f).S₁ (G.pull f).Cl) (l₁ : List (Block (G.pull f).S₁ (G.pull f).Cl))
    (b₂ : Block (G.pull f).S₂ (G.pull f).Cl) (l₂ : List (Block (G.pull f).S₂ (G.pull f).Cl))
    (b₃ : Block (G.pull f).S₃ (G.pull f).Cl) (l₃ : List (Block (G.pull f).S₃ (G.pull f).Cl))
    (e₁ : (G.pull f).first.blocksInOrder = b₁ :: l₁) (e₂ : (G.pull f).shared.blocksInOrder = b₂ :: l₂)
    (e₃ : (G.pull f).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d wEnd : W) :
    OfDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd) ∧
    (atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).Fits ∧
    RowFit D (allOf D) (allOf D) ∧
    ∀ (TF TJ T3 : Type) (tF : TF) (tJ : TJ) (t3 : T3) (okF : X × Rec → TF → Bool)
      (okJ : (G.pull f).XiPub × (G.pull f).S₁ → TJ → Bool)
      (ok3 : (G.pull f).XiPub × (G.pull f).S₁ × (G.pull f).S₂ → T3 → Bool)
      (_ : (rowIOR (atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).p₁ (atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).l₁).shape = uLT C D.ds₁)
      (_ : (rowIOR (atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).p₂ (atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).l₂).shape = uLT C D.ds₂)
      (_ : (rowIOR (atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).p₃ (atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).l₃).shape = uLT C D.ds₃) x rec y τ b,
      ((atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).row tF
        tJ t3 okF okJ ok3).S₁.ior.red.out ((x, rec), y) τ = some b →
      keyAt Prod.snd D.t₁
          (atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂
          (atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂ 0
          ((atDesc (G.pull f) (piecesAt C (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
            wEnd)).in₂ b.1, b.2) =
        ((s₂Of G (k rec) : (G.pull f).S₂), y, fun _ _ => none) := by
  have hs : (G.pull f).sealLast = true := by
    have h' : (G.planOkCore && G.sealLast) = true := hp
    exact (Bool.and_eq_true_iff.1 h').2
  have hD' : (G.pull f).data file = .ok D := hD
  obtain ⟨hO, hF, hR⟩ := paidAtDesc (X × Rec) W (G.pull f) file D hD' hs C b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃
    rest₁ rest₂ rest₃ d wEnd
  exact ⟨hO, hF, hR, fun TF TJ T3 tF tJ t3 okF okJ ok3 s₁ s₂ s₃ =>
    oneKeyByMake C D (allOf D) X Rec _ _ W TF TJ T3 tF tJ t3 (G.pull f) _ okF okJ ok3 s₁ s₂ s₃
      (fun rec => s₂Of G (k rec)) hO hF (one_pull f k hk G hG)⟩

end

section
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.Maker

/-- **AT WHAT IS LAID, the full size**: what seated_pull asks of G. -/
theorem seated_full {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
    (h : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ G, ProofFile.onlineDescription o pol lay KL = .ok G ∧ r = (G.pull LPFD.Full.instanceAsPlainRecord).run ∧ StartTwoByKey G ∧
      G.data "proof file" = .ok D ∧ G.planOk = true ∧
      ∀ x rec, (LPFD.Full.instanceAsPlainRecord (x, rec)).pub.key = keyOf (fun β : NZ => β.val) rec := by
  obtain ⟨G, hd, hp, hD, -, hr⟩ := LPFD.Full.laidPOf_ok h
  exact ⟨G, hd, hr, start₂_descPure o pol lay KL G hd, hD, hp,
    fun x rec => LPFD.Full.instOf_key (x, rec)⟩

/-- **AT WHAT IS LAID, the small size.** -/
theorem seated_small {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD}
    {r : LPFD.Small.RunPS} (h : LPFD.Small.laidPOf o pol lay KL = .ok (D, r)) :
    ∃ G, ProofFile.onlineDescription o pol lay KL = .ok G ∧ r = (G.pull LPFD.Small.instOf).run ∧ StartTwoByKey G ∧
      G.data "proof file" = .ok D ∧ G.planOk = true ∧
      ∀ x rec, (LPFD.Small.instOf (x, rec)).pub.key = keyOf (fun β : NZ => β.val) rec := by
  obtain ⟨G, hd, hp, hD, -, hr⟩ := LPFD.Small.laidPOf_ok h
  exact ⟨G, hd, hr, start₂_descPure o pol lay KL G hd, hD, hp,
    fun x rec => LPFD.Small.instOf_key (x, rec)⟩

end

section
open VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Flat OnBytes.Maker _root_.Run _root_.Run.PQ _root_.Iop

/-- The shared rounds open no tree below t₁. -/
theorem opens_all {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) : ∀ r ∈ D.ds₂, ∀ j ∈ r.opens, D.t₁ ≤ j := by
  intro r hr
  refine H2K.JointK.opens_own_stretch F file D h 0 D.ds₂.length r ?_
  rw [List.drop_zero, List.take_length]
  exact hr

variable {a : ℕ} (Kc : ConfLetters a) (DP : WholeD) {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (N : ℕ) (f : Kc.conf.X × Kc.conf.Rec → ProofFile.Inst) (k : Kc.conf.Rec → OnBytes.TableKey)
  (G : FileDescription ProofFile.Inst) {W : Type}
  (T : ThreeAt (ckP .two) (DP.at a) (allOf (DP.at a)) (G.pull f)
    ((G.pull f).XiPub × (G.pull f).S₁) ((G.pull f).XiPub × (G.pull f).S₁ × (G.pull f).S₂) W)
  (Pl : PPlaces (DP.at a) (allOf (DP.at a)) ((G.pull f).XiPub × (G.pull f).S₁)
    (((G.pull f).XiPub × (G.pull f).S₁) × (G.pull f).S₂)
    (((G.pull f).XiPub × (G.pull f).S₁ × (G.pull f).S₂) × (G.pull f).S₃))
  (h₁ : (rowIOR (atDesc (G.pull f) T).p₁ (atDesc (G.pull f) T).l₁).shape =
    uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂).shape =
    uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDesc (G.pull f) T).p₃ (atDesc (G.pull f) T).l₃).shape =
    uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    ((G.pull f).XiPub × (G.pull f).S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (L₁ : ((G.pull f).XiPub × (G.pull f).S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (L₂ : ((G.pull f).XiPub × (G.pull f).S₁ × (G.pull f).S₂) ×
    (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (d : ((G.pull f).XiPub × (G.pull f).S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str)

/-- **THE TWO FIELDS AT THE TOP's OWN LETTERS, FROM THE BLOCKS' LAWS AND Glues ALONE.** -/
theorem field_at_laid (hk : ∀ x rec, (f (x, rec)).pub.key = k rec) (hG : StartTwoByKey G)
    (file : String) (hD : G.data file = .ok (DP.at a)) (hp : G.planOk = true)
    (b₁ : Block (G.pull f).S₁ (G.pull f).Cl) (l₁ : List (Block (G.pull f).S₁ (G.pull f).Cl))
    (b₂ : Block (G.pull f).S₂ (G.pull f).Cl) (l₂ : List (Block (G.pull f).S₂ (G.pull f).Cl))
    (b₃ : Block (G.pull f).S₃ (G.pull f).Cl) (l₃ : List (Block (G.pull f).S₃ (G.pull f).Cl))
    (e₁ : (G.pull f).first.blocksInOrder = b₁ :: l₁) (e₂ : (G.pull f).shared.blocksInOrder = b₂ :: l₂)
    (e₃ : (G.pull f).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d₀ wEnd : W)
    (hT : T = piecesAt (ckP .two) (G.pull f) (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)
    (laws : EachLawsBN (keyAt Prod.snd (DP.at a).t₁ (atDesc (G.pull f) T).p₂
      (atDesc (G.pull f) T).l₂) Pl.on₂ Pl.Q₂ N 0
      ((atDesc (G.pull f) T).p₂ :: (atDesc (G.pull f) T).l₂))
    (Gl : Glues (atDesc (G.pull f) T) Pl M L₁ L₂) :
    (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).K₂.LeadsBN
      (fun c => keyAt Prod.snd (DP.at a).t₁ (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ 0
        ((atDesc (G.pull f) T).in₂ c.1, c.2))
      (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₁
      (fun c e =>
        (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₂ e ∧
        ((plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).L₂ e →
          (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).L₁ c))
      N (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).ε₂ ∧
    ∀ x rec y τ b,
      (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁
        ((x, rec), y) τ = some b →
      keyAt Prod.snd (DP.at a).t₁ (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ 0
          ((atDesc (G.pull f) T).in₂ b.1, b.2) =
        ((s₂Of G (k rec) : (G.pull f).S₂), y, fun _ _ => none) := by
  have hs := seated_pull f k hk G hG file (DP.at a) hD hp (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ rest₁
    rest₂ rest₃ d₀ wEnd
  rw [← hT] at hs
  obtain ⟨hO, hF, -, -⟩ := hs
  exact ⟨field_of_laws Kc DP tFp tJp t3p N (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d hO hF
      laws (opens_all (G.pull f) file (DP.at a) hD) Gl,
    oneKey_pull Kc DP tFp tJp t3p f k G (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d hk hG hO hF⟩

open VerifiableInference.Desc.Shared in
/-- **FROM THE KINDS' PLAIN LAWS TO THE TWO FIELDS, AT THE TOP's OWN LETTERS.** -/
theorem field_of_debts_at_laid (hk : ∀ x rec, (f (x, rec)).pub.key = k rec) (hG : StartTwoByKey G)
    (file : String) (hD : G.data file = .ok (DP.at a)) (hp : G.planOk = true)
    (b₁ : Block (G.pull f).S₁ (G.pull f).Cl) (l₁ : List (Block (G.pull f).S₁ (G.pull f).Cl))
    (b₂ : Block (G.pull f).S₂ (G.pull f).Cl) (l₂ : List (Block (G.pull f).S₂ (G.pull f).Cl))
    (b₃ : Block (G.pull f).S₃ (G.pull f).Cl) (l₃ : List (Block (G.pull f).S₃ (G.pull f).Cl))
    (e₁ : (G.pull f).first.blocksInOrder = b₁ :: l₁) (e₂ : (G.pull f).shared.blocksInOrder = b₂ :: l₂)
    (e₃ : (G.pull f).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d₀ wEnd : W)
    (hT : T = piecesAt (ckP .two) (G.pull f) (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)
    (Ns : NumbersS) (Mg : MeaningS (G.pull f).S₂ ((G.pull f).XiPub × (G.pull f).S₁) W)
    (Pm : PromMeaning (G.pull f).S₂) (Oc : (G.pull f).XiPub × (G.pull f).S₁ → Strs → Prop)
    (split : Bool)
    (pt q : Piece (ckP .two) (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc (G.pull f) T).ft₂) (((G.pull f).XiPub × (G.pull f).S₁) × (G.pull f).S₂) (G.pull f).Cl W)
    (r : List (Piece (ckP .two) (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc (G.pull f) T).ft₂) (((G.pull f).XiPub × (G.pull f).S₁) × (G.pull f).S₂) (G.pull f).Cl W))
    (e₀ : ℕ → ActV (G.pull f).S₂ (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc (G.pull f) T).ft₂) → W → W)
    (same : Comp → W → W → Prop)
    (own : OwnErrs (ckP .two) (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc (G.pull f) T).ft₂) (((G.pull f).XiPub × (G.pull f).S₁) × (G.pull f).S₂) (G.pull f).Cl W)
    (δK δO : (p : Piece (ckP .two) (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc (G.pull f) T).ft₂) (((G.pull f).XiPub × (G.pull f).S₁) × (G.pull f).S₂) (G.pull f).Cl
      W) → Err (uLT (ckP .two) p.ds))
    (hN : 1 ≤ N) (hlo : Ns.lo = (DP.at a).t₁) (hl : (atDesc (G.pull f) T).l₂ = pt :: q :: r)
    (hc : EachCapped 128 ((atDesc (G.pull f) T).p₂ :: pt :: q :: r))
    (hok : ∀ s rs gs, b₂.decide s rs gs = .ok s) (hrd : b₂.rounds = [])
    (hx : ExtNamed split (extOf Ns (atDesc (G.pull f) T).p₂ (pt :: q :: r) e₀) same)
    (hbel : EachOwnBelow 128 own 0 ((atDesc (G.pull f) T).p₂ :: pt :: q :: r))
    (f4 : ∀ s, Pm.shape 0 s = true → Pm.shape 1 s = true)
    (f5 : FrontRides Ns Mg Pm Oc split (atDesc (G.pull f) T).p₂ (pt :: q :: r))
    (hown : own 1 pt = Err.add (δK pt) (Err.times N (δO pt)))
    (hB : pt.ior.red.LeadsB (keyAt Prod.snd Ns.lo (atDesc (G.pull f) T).p₂ (pt :: q :: r) 1)
      (onQ₂ Ns Pm Oc split (atDesc (G.pull f) T).p₂ (pt :: q :: r) 1)
      (stepAt Ns Mg Pm Oc split (atDesc (G.pull f) T).p₂ (pt :: q :: r)
        (extOf Ns (atDesc (G.pull f) T).p₂ (pt :: q :: r) e₀) 1) (δK pt) (δO pt))
    (plain : EachPlainShOwn Ns Mg Pm Oc split (atDesc (G.pull f) T).p₂ (pt :: q :: r) e₀ own 2
      (q :: r))
    (rides : EachRides Ns Mg Pm Oc split (atDesc (G.pull f) T).p₂ (pt :: q :: r) e₀ 2 (q :: r))
    (hon : Pl.on₂ = onQ₂ Ns Pm Oc split (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂)
    (hQ : Pl.Q₂ = stepAt Ns Mg Pm Oc split (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂
      (extOf Ns (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ e₀))
    (Gl : Glues (atDesc (G.pull f) T) Pl M L₁ L₂) :
    (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).K₂.LeadsBN
      (fun c => keyAt Prod.snd (DP.at a).t₁ (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ 0
        ((atDesc (G.pull f) T).in₂ c.1, c.2))
      (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₁
      (fun c e =>
        (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₂ e ∧
        ((plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).L₂ e →
          (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).L₁ c))
      N (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).ε₂ ∧
    ∀ x rec y τ b,
      (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁
        ((x, rec), y) τ = some b →
      keyAt Prod.snd (DP.at a).t₁ (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ 0
          ((atDesc (G.pull f) T).in₂ b.1, b.2) =
        ((s₂Of G (k rec) : (G.pull f).S₂), y, fun _ _ => none) := by
  have hs := seated_pull f k hk G hG file (DP.at a) hD hp (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ rest₁
    rest₂ rest₃ d₀ wEnd
  rw [← hT] at hs
  obtain ⟨hO, hF, -, -⟩ := hs
  have row := rowGOfLedger (ckP .two) (DP.at a) (allOf (DP.at a)) Kc.conf.X Kc.conf.Rec _ _ W
    (G.pull f) T Ns Mg Pm Oc split N pt q r e₀ same own δK δO b₂ l₂ hN hO hF
    (opens_all (G.pull f) file (DP.at a) hD) hlo hl hc e₂ hok hrd hx hbel f4 f5 hown hB plain rides
  have rowE := (rowG_gives_E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ row).2
  exact field_at_laid Kc DP tFp tJp t3p N f k G T Pl h₁ h₂ h₃ M L₁ L₂ d hk hG file hD hp b₁ l₁ b₂ l₂
    b₃ l₃ e₁ e₂ e₃ rest₁ rest₂ rest₃ d₀ wEnd hT (by rw [hon, hQ]; exact rowE.2.2.2) Gl

end

end LT28

#print axioms LT28.field_of_debts_at_laid
#print axioms LT28.opens_all
#print axioms LT28.field_at_laid
#print axioms LT28.seated_full
#print axioms LT28.seated_small
#print axioms LT28.seated_pull
#print axioms LT28.one_pull
#print axioms LT28.one_full
#print axioms LT28.one_small
#print axioms LT28.oneKey_pull
#print axioms LT28.start₂_pureTail
#print axioms LT28.start₂_descPure
#print axioms LT28.request_idle
