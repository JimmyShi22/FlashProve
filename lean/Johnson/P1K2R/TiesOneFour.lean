-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/TiesOneFour.lean: code switching (K2): THE FIELDS THAT THE FIRST AND THE
FOURTH TIE SPEND (k02_t1R | k02_t4R, K2Caller/TieOneR.lean | TieFourR.lean), IN THE LETTERS OF
K2Short (Johnson/P1K2R/Shorter.lean), AT THE CLOSED CONSTANT's OWN PARAMETERS (P5J.At,
Johnson/P5J/LettersAt.lean), AT EACH OF THE 25 PLACES, IN ONE LEMMA.
  T14Fields    26 fields of K2Short, cut by program out of its text: cs · named · fit · oldsLen ·
               newOff · hnd · h0f · hcs · hpub · hkA · hbB · hsB · hSF · hB · hal · hN · hNd · hAl ·
               hAl_t1 · C · horc · hT1 · hBook · hOld · hsh · hsn
  k2NoAt · WayAt the number of the switch into group m + 1; the place's sort and its way in, by m
  T14Left      WHAT IS LEFT, each by name (below)
  t14_fields_const  T14Left ⟹ T14Fields, at r := tableFullLit[m] · f₀ := fxAt r · seat := seatOld N
               m r · seatN := seatNew N m r · news := N.sent (m + 1) 0 · olds := K2.oldsAt (m + 1) ·
               n0 := K2.n0At (m + 1) · grp := m + 1 · rows := 0 · trees := 83 · seats := At.seats
               Z ·
               iJ | iQ := iJW | iQW off the written frame · N := At.N Z c · links | ps := the
               constant's · k := k2NoAt m
  K2Rest · k2Short_of_t14  «rest → condition»: the other 36 fields of K2Short, cut by program;
               K2Short from the 26 and the 36: SO LEAN ITSELF HOLDS THE 26 FIELDS' LETTERS TO
               K2Short's, and through k2AllOwes_of_short (Shorter.lean) to the two ties' binders
CLOSED FACTS BY LEAN's KERNEL, NEW HERE (negative tests: see below): pinKept_full (pinKept m is open
at border k2NoAt m) · k2Place_full (the place at k2NoAt m is of the kind K2, its row lays, its
segment is m + 1), each with a negative test · keptNodup_full (no tenant twice in a segment): none.
hAl_t1 («each typed kept member has a member of the table's list that is alike it») HAD NO PAYER: IT
FOLLOWS FROM hAl (t14_hAl_t1): by «as many kept tenants as kept members» and «no kept tenant twice».
WHAT IS LEFT (T14Left), BY NAME. THE HEAD: scope · reads · laid (P5J.LaidAt) · opened. THREE
NAMED TESTS OF THE FOLD's SIDE: pinned (madePinnedAt) · cut · sendsB (sendsAreB). FIVE MORE ON
PUBLIC DATA: laidL (laidAtCodes names L) · trees83 (the laid data's first chain has 83 trees) ·
seatsFit (the head's test PlanOk.fit) · members (THE TEST membersPlanB: NO THEOREM HAS ITS VALUE:
evaluated only. Since this was written: under the wider head P5J.AtMgA (its field opts, its entry
tests) a theorem: membersPlan_ofHead (Johnson/Top/H0/K2Ties/AtHead3.lean; see the rider in its
head)) · keptSeats (the test keptSeatsB: its payer was unwritten. Since this was written:
t14_keptSeats, under premises of its own: Johnson/P1K2R/KeptSeatsLeft.lean). THE PARAMETERS ARE THE
CONSTANT's: dN · dcs · darr · dms · named · frameAll · frameKey. THE PLACE: row · frameW · way ·
firstTree · place. reach: what Rch holds is reached.
LIMITS. Joins, and closed facts by the kernel. No premise is shown met at a real value: no example.
The full size alone. No probability; no soundness is claimed.
-/
import Johnson.P1K2R.BookTight
import Johnson.P1K2R.Shorter
import Johnson.Top.H0.K2Ties.ClosedAtConst
import Johnson.Top.H0.K2Ties.NumbersFitAt
import Johnson.Top.H0.K2Ties.OrcAtLaid
import Johnson.Top.H0.K2Caller.KeptShownAt
import Johnson.Top.H0.K2Caller.TieFourPadsAt
import Johnson.Top.H0.K2Caller.MembersAtHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit smpHeld)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sampledIn sameMembers)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece MembersLike SmpLike SeedReads)
open VerifiableInference.Desc.First.K2Ties (Wq K2Owes DecBlind Left saidBehindB pubP_behind
    hheld_paid hrowM_paid hshown_of_cs hpin_of_cs hpin3_of_cs hnc_of_cs)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt LeftDoor)
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

open VerifiableInference.Desc.First.K2Ties (AtWritten at_written)
open Johnson.G (fxAt front_tests_full keptShape_full bits_at_made wAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB laidAtCodes)
open P5J (LaidAt F0T fullLinks)

variable {F : Frame}

/-! ## The 26 fields -/

/-- **The fields of K2Short that the first and the fourth tie spend.** Cut by program. -/
structure T14Fields {P Tok XiD : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public}
    {r : SwRow} (D : MgData XiD P Tok rws cls nR X) (Rch : ℕ → (P × First.S) × F.E.Str → Prop)
    (h : r.ok = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
      (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J →
      (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
      (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
      (sigOf r.cs r.l).Ent)
    (seat : Fin r.lo.length → ℕ × ℕ) (seatN : Fin r.l.length → ℕ × ℕ) (seats : List (ℕ × ℕ))
    (pAt : ℕ → K2.P2) (m : ℕ) (enter : Rec → Except String Rec) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (k : ℕ) (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame)
    (n0 grp rows : ℕ) (olds : List ℕ) (L : Laid) (trees : ℕ) (news : List (ℕ × ℕ))
    (pl : VerifiableInference.Desc.Place) : Prop where
  cs : r.cs = D.cs
  named : D.smp = smpNamed D.cs seats
  fit : fitAt r W = true
  oldsLen : olds.length = r.kept.length
  newOff : ∀ i, seatN i ∉ (minePadAt D.ms D.N links pl).map seatOf
  hnd : olds.Nodup
  h0f : K2.frameAt f₀ = some W
  hcs : f₀.st.codes = r.cs
  hpub : frontPubB r.l.length f₀ = true
  hkA : r.keptAt W = true
  hbB : keptBitsB r W = true
  hsB : keptShapeB r = true
  hSF : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, SeatFitAt D.G r.cs r.lo seat κ.1.1
  hB : keptSeatsB D.G r.cs L seats trees r.lo seat r.kept olds = true
  hal : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, ∃ v, news[1 + r.kept.idxOf κ.1.1.val]? = some v
      ∧ D.arr (seat κ.1.1).1 (seat κ.1.1).2 = D.arr v.1 v.2
  hN : ∀ (n : ℕ) (ho : 1 + n < r.l.length), news[1 + n]? = some (seatN ⟨_, ho⟩)
  hNd : ((minePadAt D.ms D.N links pl).map seatOf).Nodup
  hAl : ∀ q ∈ D.N.keptOf m, (∃ x ∈ D.ms, SitsAt x q.1 q.2) ∧ ∀ x ∈ D.ms, SitsAt x q.1 q.2 → x ∈
      (minePadAt D.ms D.N links pl) ∧ ∃ κ : {a // (plainHd r (r.ok_says h)).cl a},
      VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, κ.1.1⟩
  hAl_t1 : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, ∃ q ∈ D.N.keptOf m, ∃ x ∈ D.ms, SitsAt x q.1
      q.2 ∧ VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, κ.1.1⟩
  C : ∀ W₀, Renumbered W W₀ → CallerAt (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK
      rowK (plK W₀) W₀
  horc : ∀ y j, j < trees → ∀ x, K2.orcY F.all F.key y j x = y.col j x
  hT1 : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx → frontB2 f₀
      W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st
      ∧ storedB r (placeFrame W n0 olds) fx = true ∧ a.1.st.oracles = fx.st.oracles
  hBook : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → VerifiableInference.Desc.K12.Door.atFirstBook
      (K2.par9 (pAt m)).firstTree t = true ∧ VerifiableInference.Desc.K12.Door.atFirstSeats L t =
      true ∧ VerifiableInference.Desc.K12.Door.atFirstFits t = true
  hOld : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx → ∀ κ : {a
      // (plainHd r (r.ok_says h)).cl a}, (keptK2 r (r.ok_says h) (placeFrame W n0 olds) κ).old <
      t.book.place.size
  hsh : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none → ∀
      q ∈ D.N.keptOf m, shownJT r.cs D.G D.ms q.1 q.2 (strsOf F a.2)
  hsn : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none → ∀
      q ∈ D.N.keptOf m, shownJT r.cs D.G D.ms q.1 q.2 (strsOf F a.2) ∧ noCollJT r.cs D.G (smpNamed
      r.cs seats) D.ms q.1 q.2 (z, a.1) (strsOf F a.2)

/-! ## The numbers and the ways in -/

/-- The number of the switch into group m + 1 in the first chain's flat list. -/
def k2NoAt (m : ℕ) : ℕ := if m < 23 then 14 * (m + 1) + 2 else if m = 23 then 339 else 353

/-- The place's sort and its way in, by m. -/
def WayAt (m : ℕ) (enter : Rec → Except String Rec) (q : K2.P2) : Prop :=
  (m < 23 ∧ q.stands = .link ∧ ∀ s t, enter s = .ok t → t = s) ∨
  (m = 23 ∧ q.stands = .head ∧ ∀ s t, enter s = .ok t → t = s) ∨
  (m = 24 ∧ q.stands = .finish ∧ ∀ s t, enter s = .ok t → K2.finishFrontQ s = .ok t)

theorem WayAt.keeps {m : ℕ} {enter : Rec → Except String Rec} {q : K2.P2}
    (w : WayAt m enter q) : DoorKeepsBook enter := by
  rcases w with ⟨-, -, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩
  · exact P1K2.keeps_id e
  · exact P1K2.keeps_id e
  · exact P1K2.keeps_fin e

theorem WayAt.isNo {m : ℕ} {enter : Rec → Except String Rec} {q : K2.P2}
    (w : WayAt m enter q) : P1K2.IsSwitchNo (k2NoAt m) := by
  rcases w with ⟨h, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
  · exact Or.inl ⟨m, h, by unfold k2NoAt; rw [if_pos h]⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-! ## Closed facts by the kernel -/

set_option maxRecDepth 1000000 in
/-- **pinKept m is open at border k2NoAt m**, at the 25. -/
theorem pinKept_full : (List.range 25).all (fun m => decide (Item.pinKept m ∈
    (First.openSets fullLinks P5J.At.ps (First.start fullLinks))[k2NoAt m]?.getD [])) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one border further on it is open no more. -/
theorem pinKept_can_fail : decide (Item.pinKept 0 ∈
    (First.openSets fullLinks P5J.At.ps (First.start fullLinks))[k2NoAt 0 + 1]?.getD []) =
    false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The place at k2NoAt m**: of the kind K2; its row lays; its segment is m + 1. -/
theorem k2Place_full : (List.range 25).all (fun m => (P5J.At.ps[k2NoAt m]?).any fun p =>
    p.kind == .K2 && (First.rowOf fullLinks p).lays && p.link.getD 25 == m + 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the place one further on. -/
theorem k2Place_can_fail : ((P5J.At.ps[k2NoAt 0 + 1]?).any fun p =>
    p.kind == .K2 && (First.rowOf fullLinks p).lays && p.link.getD 25 == 1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The written table keeps no tenant twice in a segment.** -/
theorem keptNodup_full :
    (List.range 25).all (fun m => decide (P5T.N0Full.keptOf m).Nodup) = true := by
  decide +kernel

theorem k2Place_at {m : ℕ} (hm : m < 25) {pl : VerifiableInference.Desc.Place}
    (hp : P5J.At.ps[k2NoAt m]? = some pl) :
    pl.kind = .K2 ∧ (First.rowOf fullLinks pl).lays = true ∧
      pl.link.getD fullLinks.length = m + 1 := by
  have k := List.all_eq_true.1 k2Place_full m (List.mem_range.2 hm)
  rw [hp] at k
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at k
  exact ⟨k.1.1, k.1.2, k.2⟩

/-! ## At the written entries -/

section
variable {m : ℕ} {r : SwRow} {W : SwitchFrame}

theorem t14_six (hrw : tableFullLit[m]? = some r) (h0f : K2.frameAt (fxAt r) = some W) :
    (fxAt r).st.codes = r.cs ∧ frontPubB r.l.length (fxAt r) = true ∧ r.keptAt W = true ∧
      codesAt r W = true ∧ fitAt r W = true := by
  obtain ⟨W', hW', a, b, -, c, d, e⟩ := front_tests_full (List.mem_of_getElem? hrw)
  obtain rfl : W' = W := Option.some.inj (hW'.symm.trans h0f)
  exact ⟨a, b, c, d, e⟩

theorem t14_bits (hrw : tableFullLit[m]? = some r) (h0f : K2.frameAt (fxAt r) = some W) :
    keptBitsB r W = true := by
  have hr := List.mem_of_getElem? hrw
  have k := List.all_eq_true.1 bits_at_made r (List.mem_append_left _ hr)
  cases hW : wAt r with
  | none => rw [hW] at k; cases k
  | some W' =>
    rw [hW] at k
    obtain rfl : W' = W := Option.some.inj
      ((Johnson.G.frameIs_at (List.all_eq_true.1 Johnson.G.frB_full r hr) W' hW).symm.trans h0f)
    exact k

theorem t14_lt (hrw : tableFullLit[m]? = some r) : m < 25 := by
  have := (List.getElem?_eq_some_iff.1 hrw).1
  have e : tableFullLit.length = 25 := congrArg Prod.fst seats25_counts
  omega

theorem t14_nodup (hm : m < 25) : (K2.oldsAt (m + 1)).Nodup := by
  have k := List.all_eq_true.1 K2.olds_nodup (m + 1) (by simp [List.mem_range'_1]; omega)
  exact of_decide_eq_true k

/-- A held member's number is kept. -/
theorem t14_kept (h : r.ok = true) (κ : {a // (plainHd r (r.ok_says h)).cl a}) :
    κ.1.1.val ∈ r.kept := κ.2.snd

/-- **hAl_t1 FROM hAl**: general in the numbers and the list of members. -/
theorem t14_hAl_t1 (h : r.ok = true) {N : Numbers} {ms mp : List Mem}
    (hlen : r.kept.length = (N.keptOf m).length) (hnd : (N.keptOf m).Nodup)
    (hAl : ∀ q ∈ N.keptOf m, (∃ x ∈ ms, SitsAt x q.1 q.2) ∧ ∀ x ∈ ms, SitsAt x q.1 q.2 →
      x ∈ mp ∧ ∃ κ : {a // (plainHd r (r.ok_says h)).cl a},
        VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seatOld N m r⟩, κ.1.1⟩) :
    ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, ∃ q ∈ N.keptOf m, ∃ x ∈ ms, SitsAt x q.1 q.2 ∧
      VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seatOld N m r⟩, κ.1.1⟩ := by
  have seatIs : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
      ∃ ha : r.kept.idxOf κ.1.1.val < (N.keptOf m).length,
        seatOld N m r κ.1.1 = (N.keptOf m)[r.kept.idxOf κ.1.1.val] := by
    intro κ
    have ha : r.kept.idxOf κ.1.1.val < (N.keptOf m).length := by
      rw [← hlen]
      exact List.idxOf_lt_length_iff.2 (t14_kept h κ)
    refine ⟨ha, ?_⟩
    unfold seatOld
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]
    rfl
  intro κ
  obtain ⟨ha, es⟩ := seatIs κ
  obtain ⟨⟨x, hx, hs⟩, hall⟩ := hAl _ (List.getElem_mem ha)
  obtain ⟨-, κ', hA⟩ := hall x hx hs
  obtain ⟨ha', es'⟩ := seatIs κ'
  have e1 : (N.keptOf m)[r.kept.idxOf κ'.1.1.val] = (N.keptOf m)[r.kept.idxOf κ.1.1.val] := by
    have h2 : x.1.seat x.2 = seatOld N m r κ'.1.1 := hA.2
    rw [← es', ← h2]
    exact hs
  have e2 : r.kept.idxOf κ'.1.1.val = r.kept.idxOf κ.1.1.val :=
    (List.Nodup.getElem_inj_iff hnd).1 e1
  have e3 : κ'.1.1 = κ.1.1 := by
    apply Fin.ext
    have g1 := List.getElem_idxOf (List.idxOf_lt_length_iff.2 (t14_kept h κ'))
    have g2 := List.getElem_idxOf (List.idxOf_lt_length_iff.2 (t14_kept h κ))
    rw [← g1, ← g2]
    simp only [e2]
  exact ⟨_, List.getElem_mem ha, x, hx, hs, by rw [← e3]; exact hA⟩

end

/-- hsn | hsh carried along «the typed structure's codes are D's» and «the reader is the named
one». -/
theorem t14_sn_of_cs {Xi P Tok : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (D : MgData Xi P Tok rws cls nR X) {c₁ : OnBytes.Codes} (e : c₁ = D.cs) (seats : List (ℕ × ℕ))
    (hD : D.smp = smpNamed D.cs seats) {j t : ℕ} {a : P × First.S} {y : Strs}
    (H : shownJT D.cs D.G D.ms j t y ∧ noCollJT D.cs D.G D.smp D.ms j t a y) :
    shownJT c₁ D.G D.ms j t y ∧ noCollJT c₁ D.G (smpNamed c₁ seats) D.ms j t a y := by
  subst e
  rw [← hD]
  exact H

/-! ## The fold's side, uniform in m -/

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {Fd : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block Rec Cl)} {c : VerifiableInference.Desc.Chain Rec Cl}
  {A : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}
  {Rch : ℕ → (ProofFile.InstPub × First.S) × F.E.Str → Prop} {m : ℕ} {r : SwRow} {W : SwitchFrame}
  {enter : Rec → Except String Rec} {q : K2.P2}

theorem t14_hT1 (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL Fd Z Bs base c A B')
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL = .ok Fd) (hpl : Fd.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (w : WayAt m enter q) (hrw : tableFullLit[m]? = some r)
    (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : Rec × F.E.Str, Rch (k2NoAt m) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx →
      frontB2 (fxAt r) W (m + 1) 0 (K2.n0At (m + 1)) (K2.oldsAt (m + 1)) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W (K2.n0At (m + 1)) (K2.oldsAt (m + 1))) fx = true ∧
        a.1.st.oracles = fx.st.oracles := by
  rcases w with ⟨h23, hq, he⟩ | ⟨rfl, hq, he⟩ | ⟨rfl, hq, he⟩
  · have e : k2NoAt m = 14 * (m + 1) + 2 := by unfold k2NoAt; rw [if_pos h23]
    rw [e]
    exact P1K2.hT1_link_plain hS hR O hF hpl hy hcut hB hRch h23 he hq hrw h0f
  · exact P1K2.hT1_head_plain hS hR O hF hpl hy hcut hB hRch he hq hrw h0f
  · exact P1K2.hT1_fin_plain hS hR O hF hpl hy hcut hB hRch he hq hrw h0f

theorem t14_hOld {Wt : Type} (N : Numbers) (Mg : Meaning ProofFile.InstPub Wt) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL Fd Z Bs base c A B')
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL = .ok Fd) (hpl : Fd.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (w : WayAt m enter q) (h : r.ok = true) (hrw : tableFullLit[m]? = some r)
    (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : Rec × F.E.Str, onQ N Mg links ps (fun s => (z, s)) (k2NoAt m) a →
      Rch (k2NoAt m) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx → ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
        (keptK2 r (r.ok_says h) (placeFrame W (K2.n0At (m + 1)) (K2.oldsAt (m + 1))) κ).old <
          t.book.place.size := by
  rcases w with ⟨h23, hq, he⟩ | ⟨rfl, hq, he⟩ | ⟨rfl, hq, he⟩
  · have e : k2NoAt m = 14 * (m + 1) + 2 := by unfold k2NoAt; rw [if_pos h23]
    rw [e]
    exact P1K2.hOld_link_plain N Mg links ps hS hR O hF hpl hy hcut hB hRch h23 he hq h hrw h0f
  · exact P1K2.hOld_head_plain N Mg links ps hS hR O hF hpl hy hcut hB hRch he hq h hrw h0f
  · exact P1K2.hOld_fin_plain N Mg links ps hS hR O hF hpl hy hcut hB hRch he hq h hrw h0f

end

/-! ## What is left, and the one lemma -/

/-- **WHAT IS LEFT**, each by name. -/
structure T14Left {Tok : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (D : MgData ProofFile.Inst ProofFile.InstPub Tok rws cls nR X)
    (Rch : ℕ → (ProofFile.InstPub × First.S) × F.E.Str → Prop) (Pb : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (Dw : WholeD) (rn : LPFD.Full.RunPF) (Z : ProofFile.Pub) (Np : H2U.Places4)
    (c : VerifiableInference.Desc.Chain Rec Cl) (Bs : ProofFile.PureBase) (base : List (Block Rec Cl))
    (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat) (m : ℕ) (r : SwRow) (W : SwitchFrame) (L : Laid)
    (pAt : ℕ → K2.P2) (enter : Rec → Except String Rec)
    (pl : VerifiableInference.Desc.Place) : Prop where
  /-- the head -/
  scope : VerifierAndGoals.InScope Pb = true
  reads : VerifierAndGoals.readFiles Pb = .ok pp
  laid : LaidAt OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL Dw rn Z Np c
  opened : IM.Open OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL (F0T OnBytes.secondHashFunction Z Np c) Z Bs base c A B'
  /-- three named tests of the fold's side -/
  pinned : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true
  cut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull
  sendsB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true
  /-- five more on public data -/
  laidL : laidAtCodes Z.first.codes Z.made.proof.1 = some L
  trees83 : Dw.t₁ = 83
  seatsFit : P5T.seatsFitP D.G (P5J.At.cs Z) (P5J.At.pseats Z) = true
  members : membersPlanB Z (P5J.At.rad Z Pb.lay) (P5J.At.N Z c) (m + 1) r = true
  keptSeats : keptSeatsB D.G r.cs L (P5J.At.seats Z) 83 r.lo (seatOld (P5J.At.N Z c) m r) r.kept
    (K2.oldsAt (m + 1)) = true
  /-- the parameters are the constant's -/
  dN : D.N = P5J.At.N Z c
  dcs : D.cs = P5J.At.cs Z
  darr : D.arr = P5J.At.arr Z
  dms : D.ms = P5J.At.ms Z Pb.lay
  named : D.smp = smpNamed D.cs (P5J.At.seats Z)
  frameAll : F.all = ProofFile.allAt Z
  frameKey : F.key = ProofFile.keyAt Z
  /-- the place -/
  row : tableFullLit[m]? = some r
  frameW : K2.frameAt (fxAt r) = some W
  way : WayAt m enter (pAt m)
  firstTree : (K2.par9 (pAt m)).firstTree = 0
  place : P5J.At.ps[k2NoAt m]? = some pl
  /-- what Rch holds is reached -/
  reach : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1

section
variable {Tok : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {D : MgData ProofFile.Inst ProofFile.InstPub Tok rws cls nR X}
  {Rch : ℕ → (ProofFile.InstPub × First.S) × F.E.Str → Prop} {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
  {Dw : WholeD} {rn : LPFD.Full.RunPF} {Z : ProofFile.Pub} {Np : H2U.Places4}
  {c : VerifiableInference.Desc.Chain Rec Cl} {Bs : ProofFile.PureBase} {base : List (Block Rec Cl)}
  {A : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat} {m : ℕ} {r : SwRow} {W : SwitchFrame} {L : Laid}
  {pAt : ℕ → K2.P2} {enter : Rec → Except String Rec} {pl : VerifiableInference.Desc.Place}

theorem T14Left.kA (T : T14Left D Rch Pb pp Dw rn Z Np c Bs base A B' m r W L pAt enter pl) :
    r.keptAt W = true := (t14_six T.row T.frameW).2.2.1

theorem T14Left.fitW (T : T14Left D Rch Pb pp Dw rn Z Np c Bs base A B' m r W L pAt enter pl) :
    fitAt r W = true := (t14_six T.row T.frameW).2.2.2.2

set_option maxHeartbeats 1000000 in
/-- **THE FIRST AND THE FOURTH TIE's FIELDS, AT THE CONSTANT's LETTERS.** -/
theorem t14_fields_const
    (T : T14Left D Rch Pb pp Dw rn Z Np c Bs base A B' m r W L pAt enter pl) (h : r.ok = true) :
    T14Fields D Rch h (iJW (r.ok_says h) T.kA T.fitW) (iQW (r.ok_says h) T.kA T.fitW)
      (seatOld (P5J.At.N Z c) m r) (seatNew (P5J.At.N Z c) m r) (P5J.At.seats Z) pAt m enter
      fullLinks P5J.At.ps (k2NoAt m) (fxAt r) W (K2.n0At (m + 1)) (m + 1) 0 (K2.oldsAt (m + 1)) L 83
      ((P5J.At.N Z c).sent (m + 1) 0) pl := by
  have Aw : AtWritten Z c := at_written T.scope T.laid T.pinned
  have hm : m < 25 := t14_lt T.row
  obtain ⟨s1, s2, s3, s4, s5⟩ := t14_six T.row T.frameW
  obtain ⟨p1, p2, p3⟩ := k2Place_at hm T.place
  have ecs : r.cs = D.cs := (Aw.rowCs m r T.row).trans T.dcs.symm
  have hO : Item.pinKept m ∈
      (First.openSets fullLinks P5J.At.ps (First.start fullLinks))[k2NoAt m]?.getD [] :=
    of_decide_eq_true (List.all_eq_true.1 pinKept_full m (List.mem_range.2 hm))
  have HP := held_at_plan (Z := Z) (rad := P5J.At.rad Z Pb.lay) (N := P5J.At.N Z c) (r.ok_says h)
    fullLinks pl p1 p2 (by rw [p3]; exact T.members) (seatOld (P5J.At.N Z c) m r)
    (by rw [p3, Nat.add_sub_cancel]; exact seatKept_fits (r.ok_says h) _)
  rw [p3, Nat.add_sub_cancel] at HP
  have hlen : r.kept.length = ((P5J.At.N Z c).keptOf m).length := by
    rw [Aw.keptOf]
    exact keptLen_at25 T.row
  have hndK : ((P5J.At.N Z c).keptOf m).Nodup := by
    rw [Aw.keptOf]
    exact of_decide_eq_true (List.all_eq_true.1 keptNodup_full m (List.mem_range.2 hm))
  have hsn : ∀ z, ∀ a : Rec × F.E.Str,
      onQ D.N (mgAll D mgBase) fullLinks P5J.At.ps (fun s => (z, s)) (k2NoAt m) a →
      ¬ a.1.failed ≠ none → ∀ q ∈ D.N.keptOf m, shownJT r.cs D.G D.ms q.1 q.2 (strsOf F a.2) ∧
        noCollJT r.cs D.G (smpNamed r.cs (P5J.At.seats Z)) D.ms q.1 q.2 (z, a.1) (strsOf F a.2) :=
    fun z a ha hk q hq => t14_sn_of_cs D ecs _ T.named
      (hsn_mgAll D mgBase D.N fullLinks P5J.At.ps (k2NoAt m) m z hO a ha hk q hq)
  exact
    { cs := ecs
      named := T.named
      fit := s5
      oldsLen := olds_at25 T.row
      newOff := by
        rw [T.dN]
        exact seatNew_off_pads D.ms fullLinks pl r (K2Ties.numbersFit_at Aw) hm
          (by rw [p3, Nat.add_sub_cancel]) (by rw [Aw.sent]; exact (len_at25 T.row).le)
      hnd := t14_nodup hm
      h0f := T.frameW
      hcs := s1
      hpub := s2
      hkA := s3
      hbB := t14_bits T.row T.frameW
      hsB := List.all_eq_true.1 keptShape_full r (List.mem_of_getElem? T.row)
      hSF := fun κ =>
        (seats_at_row D.G T.seatsFit (K2Ties.seats25_const Aw) T.row).2 κ.1.1 (t14_kept h κ)
      hB := T.keptSeats
      hal := by
        intro κ
        rw [T.darr]
        unfold seatOld
        rw [Aw.sent, Aw.keptOf, Aw.arr]
        exact hal_at25 T.row κ.1.1 (t14_kept h κ)
      hN := by
        intro n ho
        unfold seatNew
        rw [Aw.sent]
        exact hN_at25 T.row n ho
      hNd := by
        rw [T.dN, T.dms]
        exact HP.2
      hAl := by
        rw [T.dN, T.dms]
        exact HP.1
      hAl_t1 := by
        rw [T.dN, T.dms]
        exact t14_hAl_t1 h hlen hndK HP.1
      C := fun W₀ hW => caller_fam (r.ok_says h) s3 s4 s5 W₀ hW
      horc := fun y j hj x => by
        rw [T.frameAll, T.frameKey]
        exact K2Ties.horc_83 T.laid T.trees83 y j hj x
      hT1 := fun z a _ hr _ => t14_hT1 T.scope T.reads T.opened T.laid.value T.laid.planOk T.pinned
        T.cut T.sendsB T.reach T.way T.row T.frameW z a hr
      hBook := fun z a _ hr _ => P1K2.hBook_plain T.scope T.reads T.opened T.laid.planOk T.sendsB
        T.laidL T.reach T.way.isNo T.way.keeps T.firstTree z a hr
      hOld := fun z a ha hr _ => t14_hOld D.N (mgAll D mgBase) fullLinks P5J.At.ps T.scope T.reads
        T.opened T.laid.value T.laid.planOk T.pinned T.cut T.sendsB T.reach T.way h T.row T.frameW z
        a ha hr
      hsh := fun z a ha hk q hq => (hsn z a ha hk q hq).1
      hsn := hsn }

end

/-! ## «rest → condition»: K2Short from the 26 and the other 36 -/

section
variable {P Tok XiD : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public} {r : SwRow} (D :
    MgData XiD P Tok rws cls nR X) (Rch : ℕ → (P × First.S) × F.E.Str → Prop) (h : r.ok = true) (iJ
    : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM
    (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r
    (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM
    (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent) (seat : Fin
    r.lo.length → ℕ × ℕ) (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ : RDT) (d₂ : RDT) (seats :
    List (ℕ × ℕ)) (c₀ : (CellsQ rws cls)) (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r
    (r.ok_says h)) iJ iQ).sw).X × (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
    iQ).sw).Ex.Str) (y₀ : F.E.Str) (rowAt : ℕ → Option SwRow) (pAt : ℕ → K2.P2) (door : ℕ → First.S
    → Option First.S) (m : ℕ) (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec →
    Rec → Except String Rec) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (k : ℕ)
    (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (n0 : ℕ) (grp : ℕ) (rows : ℕ) (olds : List ℕ) (L :
    Laid) (trees : ℕ) (news : List (ℕ × ℕ)) (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ) (bq :
    Block (P × First.S) Cl) (extq : (P × First.S) × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wq rws
    cls Tok → Wq rws cls Tok) (pl : VerifiableInference.Desc.Place) (MO : List OracleShape) (LO :
    Laid) (Fk : P → ℕ → Rec → Prop)


/-- **The other 36 fields of K2Short.** Cut by program out of its text. -/
structure K2Rest : Prop where
  said : saidBehindB links ps k = true
  w2 : K2Wr r d₁ d₂
  hrow : rowAt m = some r
  hW : r.writtenOK = true
  hz : r.sizedB = true
  ht : r.set.target = 128
  hp : P2At r (pAt m)
  hpl : (K2.codeSwitchKind (Cl := Unit) (pAt m)).planOk = true
  he : [d₁, d₂].map (·.entry) = (K2.rounds (pAt m)).map (·.entry)
  hk : ∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind
  hseat : ∀ i, base ≤ (seatN i).1 ∧ (seatN i).1 - base < d₁.trees.length
  hins : (rowQ links ps k).ins = [.carry m, .pinKept m]
  hctx : (rowQ links ps k).ctx = []
  hoP : Item.pin (m + 1) 0 ∈ (rowQ links ps k).outs
  hoC : Item.row (m + 1) .carried ∈ (rowQ links ps k).outs
  hoR : Item.row (m + 1) .position ∈ (rowQ links ps k).outs
  hsam : sampledIn D.N (openAt links ps (k + 1)) = D.N.index :: D.N.sent (m + 1) 0
  hidx : D.N.index ∈ sampledIn D.N (openAt links ps k)
  M : K2.MembersLike D.ms ⟨r.l, seatN⟩ (D.N.sent (m + 1) 0)
  hkeys : KeysFit (F := F) (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ
      D.G seatN base d₁ F) (pAt m) base idExt
  hSR : SeedReads
  hd : DecBlind D.decT
  hFk : ∀ z (a : Rec × F.E.Str), Rch k ((z, a.1), a.2) → Fk z k a.1
  hHands : ∀ z, HandsR (Fk z) D.N links ps (EQ (mgAll D mgBase) links ps z) F.ft k B
  hBF : ∀ z a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN base d₁ d₂
      pAt m)).ior.red.out a τ = some b → BookFits a.1.book ∧ BookFits b.1.book
  hdoor : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → door m a.1 = some t
  hσ : ∀ z, ∀ a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a →
      ¬ a.1.failed ≠ none → (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁
      d₂ (wordsMade iJ iQ D.G seatN base d₁ F) (pAt m) base idExt) B ((extW (F := F) D d₁ d₂ c₀
      links pl) z)).ior.red.out a τ = some b → K2.SmpLike r.cs (smpNamed (P := P) r.cs seats) (z,
      b.1) ⟨r.l, seatN⟩ (fun o => newSmp n0 b.1 o)
  hshN : ∀ z a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2)
      → ¬ a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN base d₁ d₂
      pAt m)).ior.red.out a τ = some b → ∀ i, ShownAt D.G r.cs r.l seatN (strsOf F b.2) i
  hnew : ∀ z a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2)
      → ¬ a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN base d₁ d₂
      pAt m)).ior.red.out a τ = some b → ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay :
      TreeLay) (n : Nat), K2.frontAt (pAt m) t = some x ∧ layTrees x.st.codes (switchNotices x.T
      x.others) = some lay ∧ sameMembers ((List.range n).map fun i => (t.book.trees.size +
      lay.tree.getD i 0, lay.part.getD i 0)) (D.N.sent (m + 1) 0) = true ∧ ∀ i, i < n → ∃ nt,
      (switchNotices x.T x.others)[i]? = some nt ∧ nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows +
      nt.shape.maskRows
  hAt : ∀ z, ∀ a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a →
      ¬ a.1.failed ≠ none → (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁
      d₂ (wordsMade iJ iQ D.G seatN base d₁ F) (pAt m) base idExt) B ((extW (F := F) D d₁ d₂ c₀
      links pl) z)).ior.red.out a τ = some b → ∀ t t' x y S3 Y rws Gg c, enter a.1 = .ok t → leave
      a.1 t' = .ok b.1 → (vN d₂ τ.2.2.1 τ.2.2.2.1).drawn.poss.length = baseCount r.set .request r.g
      → K2.decideWith _root_.Tw.K2.sendByL8 (pAt m) t [vN d₁ τ.1 τ.2.1, vN d₂ τ.2.2.1 τ.2.2.2.1]
      (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ D.G seatN base d₁ F) (pAt
      m) base idExt (t, a.2) τ) = .ok t' → K2.AtYes (pAt m) t t' (vN d₁ τ.1 τ.2.1) (vN d₂ τ.2.2.1
      τ.2.2.2.1) (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ D.G seatN base
      d₁ F) (pAt m) base idExt (t, a.2) τ) x y S3 Y rws Gg c → K2.SameTables t'.st b.1.st ∧
      (b.1.st.groups[x.f.group]?).map (·.rows) = (t'.st.groups[x.f.group]?).map (·.rows) ∧ T3At
      (r.ok_says h) iJ iQ seatN D.N (m + 1) n0 grp b.1 x rws (vN d₂ τ.2.2.1 τ.2.2.2.1) Gg
  hcar : ∀ z, ∀ s y w, carryK2 rowAt pAt door (K2.orcY F.all F.key) (fun r H => smpK2 r H) m (z, s)
      y w → (mgAll D mgBase).carry m (z, s) y w
  hS : Sits B (K2.codeSwitchKind (pAt m) : Block Rec Unit) enter leave
  leftDoor : LeftDoor enter leave
  hD : DoorKeeps (F := F) (Letters.plain r (r.ok_says h)) iJ iQ (pAt m) leave (fbOf (Letters.plain r
      (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ D.G seatN) (fun _ =>
      ((), ())))
  hbk : ∀ s t, enter s = .ok t → t.book = s.book
  O : ∀ z, K2Owes D mgBase links ps k z (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq
      base d₁ d₂ extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN
      base d₁ d₂ pAt m)) (rchAtZ Rch z k) pl (m + 1) MO LO

variable {D Rch h iJ iQ seat seatN base d₁ d₂ seats c₀ d₀ y₀ rowAt pAt door m B enter leave links ps
    k f₀ W n0 grp rows olds L trees news b₀ bq extq pl MO LO Fk}

/-- **K2Short FROM THE 26 AND THE OTHER 36**: so Lean itself holds the 26 fields' letters to
K2Short's, and through k2AllOwes_of_short to the binders of k02_t1R | k02_t4R. -/
theorem k2Short_of_t14
    (T : T14Fields D Rch h iJ iQ seat seatN seats pAt m enter links ps k f₀ W n0 grp rows olds L
      trees news pl)
    (R : K2Rest D Rch h iJ iQ seatN base d₁ d₂ seats c₀ rowAt pAt door m B enter leave links ps k n0
      grp b₀ bq extq pl MO LO Fk) :
    K2Short D Rch h iJ iQ seat seatN base d₁ d₂ seats c₀ rowAt pAt door m B enter leave links ps k
      f₀ W n0 grp rows olds L trees news b₀ bq extq pl MO LO Fk :=
  { cs := T.cs
    named := T.named
    said := R.said
    fit := T.fit
    oldsLen := T.oldsLen
    newOff := T.newOff
    w2 := R.w2
    hrow := R.hrow
    hW := R.hW
    hz := R.hz
    ht := R.ht
    hp := R.hp
    hpl := R.hpl
    he := R.he
    hk := R.hk
    hseat := R.hseat
    hnd := T.hnd
    h0f := T.h0f
    hcs := T.hcs
    hpub := T.hpub
    hkA := T.hkA
    hbB := T.hbB
    hsB := T.hsB
    hins := R.hins
    hctx := R.hctx
    hoP := R.hoP
    hoC := R.hoC
    hoR := R.hoR
    hsam := R.hsam
    hidx := R.hidx
    hSF := T.hSF
    hB := T.hB
    hal := T.hal
    hN := T.hN
    hNd := T.hNd
    hAl := T.hAl
    hAl_t1 := T.hAl_t1
    M := R.M
    C := T.C
    hkeys := R.hkeys
    horc := T.horc
    hSR := R.hSR
    hd := R.hd
    hFk := R.hFk
    hHands := R.hHands
    hT1 := T.hT1
    hBook := T.hBook
    hOld := T.hOld
    hBF := R.hBF
    hdoor := R.hdoor
    hsh := T.hsh
    hsn := T.hsn
    hσ := R.hσ
    hshN := R.hshN
    hnew := R.hnew
    hAt := R.hAt
    hcar := R.hcar
    hS := R.hS
    leftDoor := R.leftDoor
    hD := R.hD
    hbk := R.hbk
    O := R.O }

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.WayAt.keeps
#print axioms VerifiableInference.Desc.First.K2Caller.WayAt.isNo
#print axioms VerifiableInference.Desc.First.K2Caller.pinKept_full
#print axioms VerifiableInference.Desc.First.K2Caller.pinKept_can_fail
#print axioms VerifiableInference.Desc.First.K2Caller.k2Place_full
#print axioms VerifiableInference.Desc.First.K2Caller.k2Place_can_fail
#print axioms VerifiableInference.Desc.First.K2Caller.keptNodup_full
#print axioms VerifiableInference.Desc.First.K2Caller.k2Place_at
#print axioms VerifiableInference.Desc.First.K2Caller.t14_six
#print axioms VerifiableInference.Desc.First.K2Caller.t14_bits
#print axioms VerifiableInference.Desc.First.K2Caller.t14_lt
#print axioms VerifiableInference.Desc.First.K2Caller.t14_nodup
#print axioms VerifiableInference.Desc.First.K2Caller.t14_kept
#print axioms VerifiableInference.Desc.First.K2Caller.t14_hAl_t1
#print axioms VerifiableInference.Desc.First.K2Caller.t14_sn_of_cs
#print axioms VerifiableInference.Desc.First.K2Caller.t14_hT1
#print axioms VerifiableInference.Desc.First.K2Caller.t14_hOld
#print axioms VerifiableInference.Desc.First.K2Caller.T14Left.kA
#print axioms VerifiableInference.Desc.First.K2Caller.T14Left.fitW
#print axioms VerifiableInference.Desc.First.K2Caller.t14_fields_const
#print axioms VerifiableInference.Desc.First.K2Caller.k2Short_of_t14
