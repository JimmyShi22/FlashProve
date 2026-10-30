-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieBehindK3.lean: THE
TABLE'S PROMISE BEHIND THE KIND'S OWN BLOCK, FROM THE PIECE'S YES: at the maker's own pieces 4 and
10 of the key file's first chain: the table's promise with its history in front, and the piece's
yes, give the table's promise behind (borders 5 and 11): the third of the four implications that a
tie by Leads.conseq asks at the fields r1_4 and r1_10.

Main names:
  yes_ledger: the kind's block's yes from s to s': s' is s with what was heard and a ledger G put; G
    is sized, has the place's room, and as many slots more are taken as the face has.
  on_behind_k3: On₁' … (2 + 6 l + 2) a, the piece's out a τ = some b ⊢ On₁ … (2 + 6 l + 3) b, l < 2.

Object: the kind's own block at its places in Key.descriptionFromSource X N P; the table's promise on₁.
User: FieldR14.lean, FieldR14W.lean and FieldR110.lean (Johnson/RunOne/Law/) call on_behind_k3.
Letters: the table's B, at_, R, coll; the frame's heads, tails and rests. Premises: those of
rec_of_hist · the first flat list's head and tail · the two pinned trees lie below the piece's place
· coll reads the stored table's cells alone (CollCell).

Limits. The history behind is not added here (Reached.lean's keeps_reached does). Nothing on the
claims. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieBehind
import Johnson.RunOne.Law.KeepsAtRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieBehindK3
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open OnBytes.Model (Fork)
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where lookupSeat pinned)
open Johnson.RunOne.Sound (FK fk_K3_at)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁)
open Johnson.RunOne.KeyRows1 (open₁ CollCell)
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.WalkAtFK
open Johnson.RunOne.Law.RecOfHist
open Johnson.RunOne.Law.TieBehind
open LPFD (On₁')

/-- **What the kind's block's yes says of the ledger behind.** -/
theorem yes_ledger {S Cl : Type} {σ : SeatG S Cl} {p : PG} {A : Lk6.Dat GE} {st : A.St}
    {o k home : ℕ → Slot} (before : List (ℕ × ℕ)) (bits : ℕ)
    (guests : List (VerifiableInference.Desc.First.Look.Guest S Cl)) (hf : FaceIs A st p.face)
    (hadm : A.toPub.Adm Cb.Gl.p) (hh : HomeIs p.face p.first o k home) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hS : ∀ F0, σ.fork s = some F0 → PscRun.Sized F0)
    (hd : (lookupKind σ before bits guests p).decide s rs gs = .ok s') :
    ∃ g G, s' = σ.put s g G ∧ G.next = p.first + p.face.slots ∧ G.ns = p.ns ∧ PscRun.Sized G := by
  obtain ⟨F0, g, G, es, e1, e2, e3, -, e5, rfl⟩ := block_law σ before bits guests p hd
  obtain ⟨hok, t, -, hm⟩ := hearE_inv e5
  have hal : Al home o k (fromKeys p.face) F0.next 0 0 := by
    rw [e2]
    exact al_of_homeIs hh
  obtain ⟨-, -, -, c4, c5, c6, -, -⟩ := hear_course ⟨fun _ => 0⟩ hf hadm hok hm (hS F0 e1) hal
  exact ⟨g, G, rfl, by rw [c6, e2], by rw [c4.ns, e3], c5⟩

variable {W Cells Mm Smp Rec : Type} (X : Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (D : WholeD) (B : BaseSt Cells Mm Smp Rec)
  (at_ : Where) (R : KRead Cells Mm) (coll : Strs → Rec → Prop)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0)
    (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
  (dW wEnd : W)

/-- **THE TABLE'S PROMISE BEHIND THE KIND'S OWN BLOCK.** -/
theorem on_behind_k3 (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hcoll : CollCell coll) (l : ℕ) (hl : l < 2) (p)
    (hq : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃
        dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[2 + 6 * l + 2]? = some p)
    (hbase : ∀ j ∈ [0, 1], (at_ j).1 < p.base) (a b : (Xi × FirstState) × (fr₁ D).E.Str)
    (τ : Iop.Tr (uLT (ckP .two) p.ds)) (hon : On₁' X N P D B at_ R coll (2 + 6 * l + 2) a)
    (hout : p.ior.red.out a τ = some b) : On₁ X N P D B at_ R coll (2 + 6 * l + 3) b := by
  have hl' : l < X.Y.k.oneTime.ranges.lookups.length := by rw [hn]; exact hl
  have hW := fk_admitted X N P hp
  have hadm := Lk6.adm_of_tests X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) _
    (tests_at hW hl').2.1 (tests_at hW hl').2.2
  have hpb : p.b = held (lookupKind lookupSeat [(1, 0), (1, 1)] 0 []
      (VerifiableInference.Desc.Key.lookupPlace X.set l (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
          (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l)))) := by
    have h1 := LPFD.rowBlocks₁ (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (2 + 6 * l + 2) p hq
    have h2 : (c₁ :: k₁)[2 + 6 * l + 2]? =
        some (lookupKind lookupSeat [(1, 0), (1, 1)] 0 []
          (VerifiableInference.Desc.Key.lookupPlace X.set l (Wf.lookupOf
              X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                  l)))) := by
      rw [← q₁, Nat.add_assoc]
      exact fk_K3_at X N P l _ (look_at X.Y.k.oneTime l hl')
    rw [List.getElem?_map, h2] at h1
    exact (Option.some.inj h1).symm
  have hrec := rec_of_hist D a.2 hp hR ha (2 + 6 * l + 2) (by rw [hn]; omega) a.1 hon.2
  rw [Nat.add_assoc] at hrec
  obtain ⟨⟨hS, hI⟩, -⟩ := (recAt_link X l 2 (by omega) a.1.2).1 hrec
  have hd := piece_decides_at p a τ b hout
  rw [hpb] at hd
  obtain ⟨e1, hd'⟩ := VerifiableInference.Desc.Plain.held_decide _ _ _ _ _ hd
  obtain ⟨g, G, e2, g1, g2, g3⟩ := yes_ledger (σ := lookupSeat)
    (p := VerifiableInference.Desc.Key.lookupPlace X.set l (Wf.lookupOf
        X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l)))
    (A := datK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime l) [])
    (st := ()) [(1, 0), (1, 1)] 0 []
    (faceIsK Unit _ _ _ [] () hadm (d_le (tests_at hW hl').2.1)) hadm
    (homeIs_of_size _ _ _ hI.2.2.2.2) hS hd'
  have hb1 : b.1 = (a.1.1, lookupSeat.put a.1.2 g G) := Prod.ext e1 e2
  have g1' : G.next = Johnson.RunOne.KeyRows1.slots₁ X.Y.k.oneTime l := by
    rw [slots₁_eq _ l hl', g1]
    exact Nat.zero_add _
  have g2' : G.ns = Johnson.RunOne.KeyRows1.slots₁ X.Y.k.oneTime l := by
    rw [slots₁_eq _ l hl', g2]
    rfl
  have c2 : l = 0 ∨ l = 1 := by omega
  rcases c2 with rfl | rfl
  · exact on_4_5 (Fk X N P) (fr₁ D) B.h₁ at_ X.Y.k.oneTime R coll (samePins_put B) p hbase hcoll a b
      τ
      hout g G hb1 g1' g2' g3 hon.1
  · exact on_10_11 (Fk X N P) (fr₁ D) B.h₁ at_ X.Y.k.oneTime R coll (samePins_put B) p hbase hcoll a
      b
      τ hout g G hb1 g1' g2' g3 hon.1

end Johnson.RunOne.Law.TieBehindK3

#print axioms Johnson.RunOne.Law.TieBehindK3.yes_ledger
#print axioms Johnson.RunOne.Law.TieBehindK3.on_behind_k3
