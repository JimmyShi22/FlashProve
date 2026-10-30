-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.K13LawCap
import Johnson.Desc.K13.Law.AtTableRow
import Johnson.Desc.K13.Law.Tile
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.K13.Law.FillM3Paid6
/-
K13's SHARE OF THE CHAIN OF PROMISES' FIELD: THE TOP, WITH EVERY LEMMA THAT IS THROUGH LEAN CALLED BY NAME.
  k13_law_top : KindTied N Mg Sound.linksFull (flatPlacesOf Sound.linksFull true) ‹the table's own extractor› (T.p₁ :: T.l₁) KindName.K13
AT: the file's data D := dataOf a R₁ R₂ R₃ · W := Desc.Wit Cells Tok MsgT · E := extQAt · rw := rwBook arr mat.
DISCHARGED BY NAME: hE (extQAt_355: extQ_id at place355 · lays355, by the kernel) · Declared and the stretch at block 355
(declared_of_written: from WrittenAs: NO NUMBER OF A PLAN IS NAMED) · the piece's letters (cutRow_at), AT THE CAP
(herr: the family of rests lays Err.cap 128 at 355; tiedAt_err; err_le_cap from three comparisons capB) · hx · hlen · the room behind (
cutBlocks; K13_sits at 355 and 357) · RowM3 (rowM3_of_test) · FillM3 (fillM3_paid6: at K13's layer and a door with «K12.bookFits»).
NO SOUNDNESS.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)

open _root_.Desc.K14.Law (roundsIn)
open OnBytes.Params (Rounds)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (Pub)

/-- The rounds that the first 355 blocks of the chain's flat list declare, counted. -/
def inFront355 (c : Chain S Cl) : ℕ := ((c.blocksInOrder.take 355).map (·.rounds.length)).sum

set_option maxRecDepth 1000000 in
theorem place355 : (flatPlacesOf Sound.linksFull true)[355]? = some ⟨1, none, 3, .K13⟩ := by
  decide +kernel

theorem lays355 : (First.rowOf Sound.linksFull ⟨1, none, 3, .K13⟩).lays = false := by decide +kernel

section
variable {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
  {T : ThreeAt (ckP .two) D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) X₁ X₂ W}

/-- **The maker's blocks are the description's.** -/
theorem blocks_of_cut (hT : OfDesc _ T)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) W ds} {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 D.ds₁ b₁ l₁) :
    b₁ :: l₁ = (c.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)) := by
  have h := cutBlocks _ _ _ _ _ rest₁ [r] l₁ b₁ 0 0 D.ds₁
  rw [← hC] at h
  exact h.symm.trans hT.b₁

theorem roundsIn_of_cut {bs : List (Block (ProofFile.InstPub × S) Cl)}
    (h : bs = (c.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s))) :
    roundsIn (bs.take 355) = inFront355 c := by
  subst h
  unfold roundsIn inFront355
  rw [← List.map_take, ← List.map_take, List.map_map, List.map_map]
  rfl
end


section
variable (cs : OnBytes.Codes) {A Xi Pp Cells Tok : Type} {Fr : Frame} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (c₀ : Cells)
  (tokOf : Pp × S → Tok)

/-- **The table's own extractor lays nothing at K13's row.** -/
theorem extQAt_355 (N : Numbers) (get : A → Pp × S) (a b : A × Fr.E.Str)
    (w : Desc.Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true) get 355 a b w =
      w := by
  unfold extQAt
  rw [place355]
  exact extQ_id cs G arr smp ms decT c₀ tokOf N Sound.linksFull _ lays355 _ _ _ w
end


/-- Two constants bear the name: Sound's (Johnson/Desc/Sound/AtDriver.lean) and this namespace's own
(Johnson/Desc/K13/Law/AtTableRow.lean). They are one list. THE TOP IS STATED AT Sound's. -/
theorem linksFull_one : K13.Law.linksFull = Sound.linksFull := rfl

/-- **The top.** -/
theorem k13_law_top {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {a : ℕ} {R₁ R₂ R₃ : Rounds} {e₁ : List (List ByteArray × ByteArray)}
    {all : List LeftT} {X₁ X₂ Xi Cells Tok : Type}
    {T : ThreeAt (ckP .two) (dataOf a R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Desc.Wit Cells Tok MsgT)}
    (hT : OfDesc _ T) (N : Numbers) (Mg : Meaning ProofFile.InstPub (Desc.Wit Cells Tok MsgT))
    {cs : Codes} {sh : Params.ReqShape} {ly : Params.ReqLayout} {rest : ProofFile.InstPub × S → Bool}
    {arr : ℕ → ℕ → ℕ} {nR : ℕ}
    {mat : Cells → Fin nR → (Fin (K13.whereOf Z).lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} (c₀ : Cells) (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁)
      (ProofFile.InstPub × S) (Desc.Wit Cells Tok MsgT) ds} {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (herr : ∀ ds : List RDT, (rest₁ 355 ds).err = _root_.Iop.Err.cap 128 (uLT (ckP .two) ds))
    (hCapB : capB (K13.whereOf Z) = true)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hRowB : rowM3B Mg.more Sound.linksFull (flatPlacesOf Sound.linksFull true) 355 = true)
    (hNt : N.treesAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      N.treesAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hNm : N.msgsAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      N.msgsAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hbase : N.index.1 < nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront355 c)))
    (hFl : FillsK13 (K13.whereOf Z) N Mg cs sh ly rest arr mat G smp ms decT M L)
    (hWt : ∀ x, Mg.pub weightsItem x = First.weightsB x.2) (hWP : ∀ x, Mg.pubP weightsItem x)
    (hBk : ∀ x, Mg.pub bookFitsItem x = Sound.bookFitsB x.2.book)
    (hBP : ∀ x, Mg.pubP bookFitsItem x)
    (hPl : PlanM3 L M ms cs N)
    (hIn : bookItem ∈ (First.pubSets Mg.more Sound.linksFull (flatPlacesOf Sound.linksFull true))[355]?.getD [] ∧
      seatsItem ∈ (First.pubSets Mg.more Sound.linksFull (flatPlacesOf Sound.linksFull true))[355]?.getD [] ∧
      shapesItem ∈ (First.pubSets Mg.more Sound.linksFull (flatPlacesOf Sound.linksFull true))[355]?.getD [])
    (hQ : ∀ q ∈ (First.pubSets Mg.more Sound.linksFull (flatPlacesOf Sound.linksFull true))[355]?.getD [],
      q ∈ knownK13 ∨ q = weightsItem ∨ q = pileWithinItem ∨ q = oneRowItem ∨ q = bookFitsItem)
    (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl (K13.whereOf Z) x x' → rest x = true → rest x' = true) :
    KindTied N Mg Sound.linksFull (flatPlacesOf Sound.linksFull true)
      (fun k => extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) (T.p₁ :: T.l₁) KindName.K13 := by
  have hb := blocks_of_cut hT hC
  have hn := roundsIn_of_cut hb
  obtain ⟨⟨e, hflat, _, hu⟩, _⟩ := k13_sits_flat hS hR O
  obtain ⟨e7, hflat7, _, hu7⟩ := k13_sits_flat357 hS hR O
  have hx : (b₁ :: l₁)[355]? = some ((below e).lift Prod.snd fun t s => (t.1, s)) := by
    rw [hb]
    simp only [List.getElem?_map, hflat, Option.map_some]
  have hx7 : (b₁ :: l₁)[357]? = some ((below e7).lift Prod.snd fun t s => (t.1, s)) := by
    rw [hb]
    simp only [List.getElem?_map, hflat7, Option.map_some]
  have hlen : 355 < l₁.length := by
    have h7 : 357 < (b₁ :: l₁).length := (List.getElem?_eq_some_iff.1 hx7).1
    rw [List.length_cons] at h7
    omega
  have hr : ((below e).lift Prod.snd fun (t : ProofFile.InstPub × S) s => (t.1, s)).rounds =
      battRounds (K13.whereOf Z) := by
    show e.rounds = _
    rw [hu.1]
    exact atM3_rounds _
  have hr7 : 0 < ((below e7).lift Prod.snd fun (t : ProofFile.InstPub × S) s => (t.1, s)).rounds.length := by
    show 0 < e7.rounds.length
    rw [hu7.1]
    exact Nat.zero_lt_one
  have hfl : (b₁ :: l₁).flatMap (·.rounds) = c.blocksInOrder.flatMap (·.rounds) := by
    rw [hb, List.map_map, List.flatMap_map]
    rfl
  obtain ⟨dZ, d0, ds, hds, hD, hK⟩ := declared_of_written a R₁ R₂ R₃ (b₁ :: l₁) (e := e₁)
    (by rw [hfl]; exact hWr) 355 _ hx (room_of_later _ 355 357 _ _ hx hx7 (by omega) hr7)
    (K13.whereOf Z) hr
  exact k13_law_cap hS hR O hT N Mg _
    (fun a b w => extQAt_355 cs G arr smp ms decT c₀ tokOf N (fun a => a) a b w) _ dZ d0 ds hD
    (err_le_cap _ dZ d0 ds hD hK hCapB) (rwBook arr mat) (rowM3_of_test _ _ _ _ hRowB N hNt hNm)
    (fillM3_paid6 _ hFl hWt hWP hBk hBP hPl hIn hQ hsmp hdec hrest) (by rw [hn]; exact hbase)
    fun q hq => hasM3Cap_of_cut rest₁ [r] l₁ b₁ _ 355 _ hx hlen (K13.whereOf Z) dZ d0 ds hds
      (herr _) q (by rw [← hC]; exact hq)

end VerifiableInference.Desc.K13.Law
