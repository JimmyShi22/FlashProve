-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Left15H.lean: THE FIELD r1_15 OF THE KEY FILE's TABLES FROM WHAT IS LEFT, WITH THE HISTORY KEPT IN FRONT: «gives» MAY SPEND "the record in front of the test was reached".
OBJECT. `LPFD.The21`'s field r1_15 (Johnson/Top/Fire/Code/The35.lean): it stands at On₁' := On₁ ∧ Hist₁ (Johnson/Top/Fire/Code/KeyTablesR.lean). USER. The21's filler.
LETTERS. The35.lean's.
WHY. Facts that row 1.15 wants of the record in front (what the claims' mask forms read · the shape of the tree that holds the lookups' own message · that message's shape · the form of its one sample row · no open row is marked as a sample row) stand in no promise of the tables; each is earned at a sending or a laying and kept by every block since: so each can be had of a REACHED record.
  OnH: OnH k IS On₁ k BUT AT 15: there it holds the history besides. (Pays, K12AtField.lean, has ONE letter for the promise at both borders: the guard "k = 15 →" gives it two faces: in front it is spent; behind, at 16, the clause is empty: it earns nothing and is asked nothing. KeepsAt … 15 reads the promise at 15 and 16 alone.)
  r1_15_atH: THE FIELD's VERY TYPE from q₁, hl and Left15JG at OnH: by keeps_reached (Johnson/Top/Fire/Code/Reached.lean: "a law may spend the history in front and need not earn it behind").
  gives_of_halvesH: Left15JG OnH's field «gives» from the two halves, each with the history in front.
  Left15JG.ofHalvesH: so that theorem's conclusion IS the field's type, by Lean.
  Left15J.toJG | Left15JG.toJ: Left15J (K12Left15J.lean) IS Left15JG at on := On₁, field by field, both ways.
IT PAYS NO FIELD: NO MEMBER OF Left15JG IS SHOWN.
Limits. As empty as Left15JG. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Left15JG
import Johnson.RunOne.Law.K12Left15J

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace Johnson.RunOne.Law.K12AtThe21
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open OnBytes.Slice (Sg)
open H2K.Pin (NTuple)
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt johOk batV0 codes_of_johOk)
open H2K.First (batOneOk)
open Johnson.G.OfPlan (rootsOf)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ R₁ open₁)
open LPFD

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (notBad : List OnBytes.E → Strs → Prop) (off₂ off₃ : ℕ → ℕ)

/-- **OnH k is On₁ k but at 15**, where it holds besides: the record was reached. -/
abbrev OnH : ℕ → (Xi × FirstState) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop :=
  fun k x => On₁ X N P (DK.at frS.P.T.a) B at_ R coll k x ∧ (k = 15 → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 x.1)

/-- **THE FIELD r1_15 OF The21 AT THE KEY FILE's OWN DESCRIPTION, FROM WHAT IS LEFT, WITH THE HISTORY IN FRONT.** -/
theorem r1_15_atH (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (H : Left15JG X N P DK c₁ k₁ rest₁ B at_ R (OnH X N P DK B at_ R coll)) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15 :=
  fun p hp => keeps_reached _ _ 15 p (rowBlocksF₁ q₁ 15 p hp) ((On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 15) ((On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 16)
    ((Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 15) ((Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 16)
    (Iop.Reduction.Leads.conseq
      (r1_15_atJG X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R (OnH X N P DK B at_ R coll) q₁ hl H p hp)
      (fun _ ha => ⟨ha.1, fun _ => ha.2⟩) (fun _ _ _ _ _ hq => ⟨hq.1.1, hq.2⟩))

/-- **«gives» from the two halves, each of which may spend the history in front.** gives_of_halves (K12GivesHalves.lean) with one premise more in fwd and in back: the record in front was reached. -/
theorem gives_of_halvesH (dB : RDT) (dt : List RDT) (nl : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (tbl : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str → Wit Cells Unit M → M)
    (hbase : ∀ k ∈ pinned (open₁ (n₁ (oneAt X)) 15), (at_ k).1 < (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15))
    (fwd : ∀ a b rs gs, (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 → (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b.1 →
      StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) (strsOf (fr₁ (DK.at frS.P.T.a)) b.2) → (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 16 b)
    (back : ∀ a b rs gs t t' w, (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 → (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b.1 →
      StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) (strsOf (fr₁ (DK.at frS.P.T.a)) b.2) → (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 16 b →
      enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t → leaveRanges a.1.2 t' = .ok b.1.2 → b.1.1 = a.1.1 →
      QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2) →
      R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R 16 b w → R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R 15 a (layAt at_ [1] (fun _ => tbl a w) w)) :
    ∀ a τ b, (OnH X N P DK B at_ R coll) 15 a →
      (pieceOf (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15) (dB :: dt) [] (rest₁ 15 (dB :: dt))).ior.red.out a τ = some b →
      (∃ t t', enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t ∧
        (leaveRanges a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2)) →
      (OnH X N P DK B at_ R coll) 16 b ∧ ((Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 16 b → (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 15 a) := by
  intro a τ b ha hout ⟨t, t', h1, ⟨h2, h3⟩, hq⟩
  have hd := piece_decides_at _ a τ b hout
  have Hy := strsStay_of_out (Fk X N P) (fr₁ (DK.at frS.P.T.a)) at_ _ (open₁ (n₁ (oneAt X)) 15) hbase a b τ hout
  have hb := fwd a b _ _ ha.1 (ha.2 rfl) hd Hy
  exact ⟨⟨hb, fun e => absurd e (by decide)⟩, fun ⟨w, hw⟩ => ⟨_, back a b _ _ t t' w ha.1 (ha.2 rfl) hd Hy hb h1 h2 h3 hq hw⟩⟩


/-- «gives» laid by the two halves: it typechecks only because gives_of_halvesH's conclusion is the field's type. -/
def Left15JG.ofHalvesH (H : Left15JG X N P DK c₁ k₁ rest₁ B at_ R (OnH X N P DK B at_ R coll))
    (tbl : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str → Wit Cells Unit M → M) :=
  fun hbase fwd back => ({ H with gives := gives_of_halvesH X N P DK c₁ k₁ rest₁ B at_ R coll H.dB H.dt H.nl (fun s => H.stageRad s.st) H.rd tbl hbase fwd back } : Left15JG X N P DK c₁ k₁ rest₁ B at_ R (OnH X N P DK B at_ R coll))

/-- Left15J is Left15JG at the tables' own promise: forth. -/
def Left15J.toJG (H : Left15J X N P DK c₁ k₁ rest₁ B at_ R coll) : Left15JG X N P DK c₁ k₁ rest₁ B at_ R (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) where
  file := H.file
  dB := H.dB
  dt := H.dt
  post := H.post
  r₀ := H.r₀
  writtenHead := H.writtenHead
  writtenTail := H.writtenTail
  stageRad := H.stageRad
  batErr := H.batErr
  nl := H.nl
  rd := H.rd
  data := H.data
  stretch := H.stretch
  behind := H.behind
  plan := H.plan
  arm := H.arm
  written := H.written
  free := H.free
  joh := H.joh
  batOne := H.batOne
  labels := H.labels
  bat := H.bat
  le := H.le
  gives := H.gives

/-- And back. -/
def Left15JG.toJ (H : Left15JG X N P DK c₁ k₁ rest₁ B at_ R (On₁ X N P (DK.at frS.P.T.a) B at_ R coll)) : Left15J X N P DK c₁ k₁ rest₁ B at_ R coll where
  file := H.file
  dB := H.dB
  dt := H.dt
  post := H.post
  r₀ := H.r₀
  writtenHead := H.writtenHead
  writtenTail := H.writtenTail
  stageRad := H.stageRad
  batErr := H.batErr
  nl := H.nl
  rd := H.rd
  data := H.data
  stretch := H.stretch
  behind := H.behind
  plan := H.plan
  arm := H.arm
  written := H.written
  free := H.free
  joh := H.joh
  batOne := H.batOne
  labels := H.labels
  bat := H.bat
  le := H.le
  gives := H.gives

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.r1_15_atH
#print axioms Johnson.RunOne.Law.K12AtThe21.gives_of_halvesH
#print axioms Johnson.RunOne.Law.K12AtThe21.Left15JG.ofHalvesH
#print axioms Johnson.RunOne.Law.K12AtThe21.Left15J.toJG
#print axioms Johnson.RunOne.Law.K12AtThe21.Left15JG.toJ
