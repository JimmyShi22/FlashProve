-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/TieThreeConst.lean: code switching (K2): THE THIRD TIE's CLAUSE AT
AN ACCEPT, THE FIELD hAt OF K2Short (Johnson/P1K2R/Shorter.lean), AT THE OWN PARAMETERS
OF THE CLOSED CONSTANT (P5J.mgAtAll, Johnson/P5J/MgAtAll.lean), AT EACH OF THE 25 PLACES.
  T3Field      the field hAt, cut by program out of K2Short's text
  t3_hF        the front's notices and codes are the written ones (hAt_…_new's hF)
  t3_hInv      the two invariants' fruits at the front (hone_at_place's hInv)
  t3_front_congr  the front reads of the place's numbers its sort alone
  t3_nums_link · t3_nums_head · t3_nums_fin  the plan's numbers at a switch ARE THERE
               (K2Is.live, Johnson/IMR/K2Seat.lean, under the description's test on the plan)
  t3_xk        the promise's tests in the letters of Johnson/IMR/'s files (xk_of_on, TieTwo.lean)
  linkOfM · WayOut · T3More  WHAT IS LEFT BESIDE T14Left, by name (below)
  t3_hAt_const T14Left · T3More ⟹ T3Field, at TiesOneFour.lean's letters
  K2Rest3 · k2Short_of_t14_t23_t3  «rest → condition»: the other 27 fields of K2Short, cut by
               program; K2Short from the 26, the 8, hAt and the 27: so Lean holds the letters
THE PAYERS. hAt_link_new | hAt_head_new | hAt_finish_new
(Tw/K2C/TieThreeSeatNew.lean), at: sentPlace_… · T14Left's «members» · t3_hF · the way in's
«it leaves the book and the roots» · T14Fields' hBook | hT1 | hnd | h0f | hcs | hpub | hkA | C ·
hL_full (Tw/K2C/TieThreeLengthsLit.lean) · AtWritten.groupAt · hone_at_place
(Tw/K2C/TieThreeOneRow.lean) at keptTyped_at and t3_hInv · THE DEBTS ON THE TABLE's NUMBERS:
d_link_laid | d_head_laid | d_finish_laid (Johnson/P1K2R/DebtsLaid.lean), carried to the front's
letters.
WHAT IS LEFT BESIDE T14Left (T3More), BY NAME. wayOut: the way out, by m: at a link it keeps what
«opened» keeps · at the output head: "H.1.quiet", then the like · at the finish: "F.0.quiet" (the
five real ways out: Tw/K2C/TieThreeDoors.lean) · logN: the place's logN is at most 32 · posIs: the
plan's count of positions at the switch is the typed structure's (baseCount r.set .request r.g).
LIMITS. Joins. No premise is shown met at a real value: no example. It leans on T14Left's «members»,
a test whose value no theorem has. Since this was written: under the wider head P5J.AtMgA (its field
opts, its entry tests) a theorem: membersPlan_ofHead (Johnson/Top/H0/K2Ties/AtHead3.lean; see the
rider in its head). The full size alone. No probability; no soundness is claimed.

-/
import Johnson.P1K2R.TiesTwoThree
import Johnson.Top.H0.Tw.K2C.TieThreeSeatNew
import Johnson.Top.H0.Tw.K2C.TieThreeOneRow
import Johnson.Top.H0.Tw.K2C.TieThreeLengthsLit
import Johnson.P1K2R.DebtsLaid

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

open VerifiableInference.Desc.First.K2Ties (AtWritten AtTold at_written at_told)
open Johnson.G (fxAt)
open Johnson.Desc.First.Walk.Tied (Reach OpenedKeeps)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open P5J (LaidAt F0T fullLinks)

variable {F : Frame}

/-- **The field hAt of K2Short.** Cut by program. -/
structure T3Field {P Tok XiD : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public}
    {r : SwRow} (D : MgData XiD P Tok rws cls nR X) (Rch : ℕ → (P × First.S) × F.E.Str → Prop)
    (h : r.ok = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
      (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J →
      (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
      (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
      (sigOf r.cs r.l).Ent)
    (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT) (c₀ : CellsQ rws cls)
    (pAt : ℕ → K2.P2) (m : ℕ) (B : Block Rec Cl) (enter : Rec → Except String Rec)
    (leave : Rec → Rec → Except String Rec) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (k n0 grp : ℕ)
    (pl : VerifiableInference.Desc.Place) : Prop where
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

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {Fd : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base₀ : List (Block Rec Cl)} {c : VerifiableInference.Desc.Chain Rec Cl}
  {A : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}
  {Rch : ℕ → (ProofFile.InstPub × First.S) × F.E.Str → Prop} {m : ℕ}
  {enter : Rec → Except String Rec} {p : K2.P2}

/-- The front's notices and codes are the written ones: in the letters of hAt_…_new's hF. -/
theorem t3_hF (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL Fd Z Bs base₀ c A B')
    (hsh : Z.first.shape = K2Hands.shW)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (w : WayAt m enter p) :
    ∀ z, ∀ a : Rec × F.E.Str, Rch (k2NoAt m) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt p t = some fx →
      switchNotices fx.T fx.others = (K2Hands.sentW (m + 1)).toArray ∧
        fx.st.codes = Z.first.codes := by
  intro z a hr t he' fx hfx
  have hr' := hRch _ _ hr
  rcases w with ⟨h23, hq, he⟩ | ⟨rfl, hq, he⟩ | ⟨rfl, hq, he⟩
  · have e : k2NoAt m = 14 * (m + 1) + 2 := by unfold k2NoAt; rw [if_pos h23]
    rw [e] at hr'
    obtain rfl := he _ _ he'
    obtain ⟨a1, a2⟩ := P1K2.noticesW_link hS hR O hsh h23 hr' hq hfx
    exact ⟨by rw [← a2], a1⟩
  · obtain rfl := he _ _ he'
    obtain ⟨a1, a2⟩ := P1K2.noticesW_head hS hR O hsh hr' hq hfx
    exact ⟨by rw [← a2], a1⟩
  · obtain ⟨a1, a2⟩ := P1K2.noticesW_fin hS hR O hsh hr' (he _ _ he') hq hfx
    exact ⟨by rw [← a2], a1⟩

/-- The two invariants' fruits at the front. -/
theorem t3_hInv (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL Fd Z Bs base₀ c A B')
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL = .ok Fd) (hpl : Fd.planOk = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (w : WayAt m enter p) :
    ∀ z, ∀ a : Rec × F.E.Str, Rch (k2NoAt m) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt p t = some fx → K2.SampleGoodS fx.st ∧ K2.AnsweredStored fx.st := by
  intro z a hr t he' fx hfx
  have hk : k2NoAt m ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.Carry.front_len hS hR O]
    rcases w with ⟨h23, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · unfold k2NoAt; rw [if_pos h23]; omega
    · decide
    · decide
  obtain ⟨hG, hA⟩ := P1K2.both_at_open O hF hpl hk (hRch _ _ hr)
  have hway : (p.stands ≠ .finish ∧ t = a.1) ∨
      (p.stands = .finish ∧ K2.finishFrontQ a.1 = .ok t) := by
    rcases w with ⟨-, hq, he⟩ | ⟨-, hq, he⟩ | ⟨-, hq, he⟩
    · exact Or.inl ⟨by rw [hq]; decide, he _ _ he'⟩
    · exact Or.inl ⟨by rw [hq]; decide, he _ _ he'⟩
    · exact Or.inr ⟨hq, he _ _ he'⟩
  obtain ⟨w1, w2⟩ := way_tables hway
  obtain ⟨c1, c2, -⟩ := K2Hands.front_of_state hfx
  exact ⟨(K2.sampleGoodS_iff _).2 (K2.rowsInv_congr (Q := K2.QGoodS) (c1.trans w1) (c2.trans w2)
    ((K2.sampleGoodS_iff _).1 hG)), K2.answered_congr (c2.trans w2) hA⟩


/-- The front reads of the place's numbers its sort alone. -/
theorem t3_front_congr {p q : K2.P2} (e : p.stands = q.stands) {s : Rec} {x : _root_.Tw.K2.Front}
    (h : K2.frontAt p s = some x) : K2.frontAt q s = some x := by
  have k := K2.frontOf_iff.2 h
  refine K2.frontOf_iff.1 ?_
  unfold K2.FrontOf at k ⊢
  rw [← e]
  exact k

theorem t3_nums_link (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL Fd Z Bs base₀ c A B')
    (hpl : Fd.planOk = true) {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24) :
    ∃ Pp n, P1K2.prepOf Z Bs.G₀ = some Pp ∧ P1K2.numsAt Pp (some l) = some n := by
  obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_link_sits hS hR O l h1 h24
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
  have hb := P1K2.flat_planOk O hpl b (List.mem_of_getElem? hf)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.framed.laid hb)).1
  obtain ⟨P', n', hP', hn', -⟩ := hi.live hxp
  exact ⟨P', n', hP', hn'⟩

theorem t3_nums_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL Fd Z Bs base₀ c A B')
    (hpl : Fd.planOk = true) :
    ∃ Pp n, P1K2.prepOf Z Bs.G₀ = some Pp ∧ P1K2.numsAt Pp (some 24) = some n := by
  obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_head_of hS hR O
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 1] at hf
  have hb := P1K2.flat_planOk O hpl b (List.mem_of_getElem? hf)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
  obtain ⟨P', n', hP', hn', -⟩ := hi.live hxp
  exact ⟨P', n', hP', hn'⟩

theorem t3_nums_fin
    (O : IM.Open OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL Fd Z Bs base₀ c A B')
    (hpl : Fd.planOk = true) :
    ∃ Pp n, P1K2.prepOf Z Bs.G₀ = some Pp ∧ P1K2.numsAt Pp none = some n := by
  obtain ⟨b, x, e1, hx, ep, hl, -⟩ := IM.k2_finish_of O
  have hi := IM.k2_mem hx
  rw [ep] at hi
  have hb := P1K2.back_planOk O hpl (List.mem_of_getElem? e1)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
  obtain ⟨P', n', hP', hn', -⟩ := hi.live hxp
  exact ⟨P', n', hP', hn'⟩

/-- The promise's tests, in the letters of the files in Johnson/IMR/. -/
theorem t3_xk {Wt : Type} {N : Numbers} {Mg : Meaning ProofFile.InstPub Wt} {k : ℕ} {z : ProofFile.InstPub}
    {a : Rec × F.E.Str} (ha : onQ N Mg fullLinks P5J.At.ps (fun s => (z, s)) k a)
    (hm : ¬ a.1.failed ≠ none) :
    IM.XK N IM.linksW IM.placesW (EQ Mg fullLinks P5J.At.ps z) k a.1 = true := by
  have e1 : IM.linksW = fullLinks := LPFK9.linksW_full
  rw [e1, ← P1K2.ps_written]
  exact P1K2.xk_of_on (y := strsOf F a.2) ha (Classical.byContradiction hm)


end

/-! ## What is left beside T14Left, and the lemma -/

/-- The place's link, by m. -/
def linkOfM (m : ℕ) : Option ℕ := if m < 24 then some (m + 1) else none

/-- The way out, by m. -/
def WayOut (m : ℕ) (leave : Rec → Rec → Except String Rec) : Prop :=
  (m < 23 ∧ ∀ s t' s', leave s t' = .ok s' → OpenedKeeps t' s') ∨
  (m = 23 ∧ ∀ s t' s', leave s t' = .ok s' → ∃ Pq u, K2.headOpenQ Pq t' = .ok u ∧
    OpenedKeeps u s') ∨
  (m = 24 ∧ ∀ s t' s', leave s t' = .ok s' → K2.finishBehindQ t' = .ok s')

/-- **WHAT IS LEFT BESIDE T14Left**, each by name. -/
structure T3More (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (m : ℕ) (r : SwRow) (pAt : ℕ → K2.P2)
    (leave : Rec → Rec → Except String Rec) : Prop where
  wayOut : WayOut m leave
  logN : (pAt m).logN ≤ 32
  posIs : ∀ Pp n, P1K2.prepOf Z Bs.G₀ = some Pp → P1K2.numsAt Pp (linkOfM m) = some n →
    n.positions = baseCount r.set .request r.g

section
variable {Tok : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {D : MgData ProofFile.Inst ProofFile.InstPub Tok rws cls nR X}
  {Rch : ℕ → (ProofFile.InstPub × First.S) × F.E.Str → Prop} {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
  {Dw : WholeD} {rn : LPFD.Full.RunPF} {Z : ProofFile.Pub} {Np : H2U.Places4}
  {c : VerifiableInference.Desc.Chain Rec Cl} {Bs : ProofFile.PureBase} {base₀ : List (Block Rec Cl)}
  {A : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat} {m : ℕ} {r : SwRow} {W : SwitchFrame} {L : Laid}
  {pAt : ℕ → K2.P2} {enter : Rec → Except String Rec} {pl : VerifiableInference.Desc.Place}
  {leave : Rec → Rec → Except String Rec}

set_option maxHeartbeats 4000000 in
/-- **THE FIELD hAt, AT THE CONSTANT's LETTERS.** -/
theorem t3_hAt_const (T : T14Left D Rch Pb pp Dw rn Z Np c Bs base₀ A B' m r W L pAt enter pl)
    (V : T3More Z Bs m r pAt leave) (h : r.ok = true) (B : Block Rec Cl) (base : ℕ) (d₁ d₂ : RDT)
    (c₀ : CellsQ rws cls) :
    T3Field D Rch h (iJW (r.ok_says h) T.kA T.fitW) (iQW (r.ok_says h) T.kA T.fitW)
      (seatNew (P5J.At.N Z c) m r) base d₁ d₂ c₀ pAt m B enter leave fullLinks P5J.At.ps
      (k2NoAt m) (K2.n0At (m + 1)) (m + 1) pl := by
  have Aw : AtWritten Z c := at_written T.scope T.laid T.pinned
  have At' : AtTold Z c := at_told T.cut Aw
  have T4 := t14_fields_const T h
  have hPl := t23_place Aw At' T.way
  obtain ⟨lay₀, hlay⟩ := t23_lay (t23_fit Aw At' T.way)
  have hFz := t3_hF T.scope T.reads T.opened Aw.shape T.reach T.way
  have hIz := t3_hInv T.scope T.reads T.opened T.laid.value T.laid.planOk T.reach T.way
  have h0 : (pAt m).firstTree = 0 := T.firstTree
  refine ⟨fun z => ?_⟩
  have hone := hone_at_place (r := r) (pAt m) enter D.N (mgAll D mgBase) fullLinks P5J.At.ps z
    (rchAtZ Rch z) (k2NoAt m) (K2.n0At (m + 1)) (m + 1) 0 (fxAt r) W (K2.oldsAt (m + 1)) T4.hnd
    T4.h0f T4.hcs T4.hpub (keptTyped_at T.row) T4.hsB
    (fun a ha hr hk t he fx hfx =>
      ⟨(T4.hT1 z a ha hr hk t he fx hfx).1, (T4.hT1 z a ha hr hk t he fx hfx).2.1⟩)
    (fun a _ hr _ => hIz z a hr)
  have way := T.way
  have eN := T.dN
  have hT1' := T4.hT1
  have hBook' := T4.hBook
  rw [eN] at hone hT1' hBook' ⊢
  rcases way with ⟨h23, hq, he⟩ | ⟨e23, hq, he⟩ | ⟨e24, hq, he⟩
  · have hlv : ∀ s t' s', leave s t' = .ok s' → OpenedKeeps t' s' := by
      rcases V.wayOut with ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩
      · exact k
      · omega
      · omega
    have e : k2NoAt m = 14 * (m + 1) + 2 := by unfold k2NoAt; rw [if_pos h23]
    refine hAt_link_new (h := h) (iJ := _) (iQ := _) (ext' := _) (G := D.G) (base := base)
      (d₁ := d₁) (d₂ := d₂) (p := pAt m) (B := B)
      (enter := enter) (leave := leave) (N := P5J.At.N Z c) (Mg := mgAll D mgBase)
      (links := fullLinks) (ps := P5J.At.ps) (z := z) (Rch := rchAtZ Rch z) (k := k2NoAt m) (m := m)
      (n0 := K2.n0At (m + 1)) (grp := m + 1) (codes := Z.first.codes)
      (sent := (K2Hands.sentW (m + 1)).toArray) (lay₀ := lay₀) (Z := Z)
      (rad := P5J.At.rad Z Pb.lay) (ft := 0) (hPl := hPl) (hlay := hlay) (hB := T.members)
      (hF := fun a _ hr _ => hFz z a hr) (h0 := h0) (hen := T.way.keeps)
      (hBook := fun a ha hr hk t he => by
        have k1 := (hBook' z a ha hr hk t he).1
        rwa [T.firstTree] at k1)
      (h32 := V.logN) (hL := hL_full (List.mem_of_getElem? T.row)) (f₀ := fxAt r) (W := W)
      (olds := K2.oldsAt (m + 1)) (hnd := T4.hnd) (h0f := T4.h0f) (hcs := T4.hcs)
      (hpub := T4.hpub) (hkA := T4.hkA) (C := T4.C)
      (hT1 := fun a ha hr hk t he fx hfx =>
        ⟨(hT1' z a ha hr hk t he fx hfx).1, (hT1' z a ha hr hk t he fx hfx).2.1⟩)
      (hgrp := by rw [Aw.groupAt]; rfl) (d := baseCount r.set .request r.g) (hd := rfl)
      (hone := hone) hlv ?_
    intro a ha hr hk t het fx hfx lay hl' W₀ hW₀
    obtain rfl := he _ _ het
    obtain ⟨Pp, n, hP, hn⟩ := t3_nums_link T.scope T.reads T.opened T.laid.planOk (l := m + 1)
      (by omega) (by omega)
    have hp := V.posIs Pp n hP (by unfold linkOfM; rw [if_pos (by omega)]; exact hn)
    have hx := t3_xk ha hk
    have hr' := T.reach _ _ hr
    rw [e] at hx hr'
    have k := P1K2.d_link_laid T.scope T.reads T.laid T.opened T.pinned T.cut T.sendsB h23
      (Fk := fun k s => ∃ z, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s))
      (fun s hs => hs) Pp n a.1 fx W₀ lay hP hn ⟨z, hr'⟩ hx (K2.front_of_link hq hfx) hW₀ hl'
    rw [hp] at k
    exact ⟨_, _, _, k⟩
  · subst e23
    have hlv : ∀ s t' s', leave s t' = .ok s' → ∃ Pq u, K2.headOpenQ Pq t' = .ok u ∧
        OpenedKeeps u s' := by
      rcases V.wayOut with ⟨k, -⟩ | ⟨-, k⟩ | ⟨k, -⟩
      · omega
      · exact k
      · omega
    refine hAt_head_new (h := h) (iJ := _) (iQ := _) (ext' := _) (G := D.G) (base := base)
      (d₁ := d₁) (d₂ := d₂) (p := pAt 23) (B := B)
      (enter := enter) (leave := leave) (N := P5J.At.N Z c) (Mg := mgAll D mgBase)
      (links := fullLinks) (ps := P5J.At.ps) (z := z) (Rch := rchAtZ Rch z) (k := k2NoAt 23)
      (m := 23)
      (n0 := K2.n0At (23 + 1)) (grp := 23 + 1) (codes := Z.first.codes)
      (sent := (K2Hands.sentW (23 + 1)).toArray) (lay₀ := lay₀) (Z := Z)
      (rad := P5J.At.rad Z Pb.lay) (ft := 0) (hPl := hPl) (hlay := hlay) (hB := T.members)
      (hF := fun a _ hr _ => hFz z a hr) (h0 := h0) (hen := T.way.keeps)
      (hBook := fun a ha hr hk t he => by
        have k1 := (hBook' z a ha hr hk t he).1
        rwa [T.firstTree] at k1)
      (h32 := V.logN) (hL := hL_full (List.mem_of_getElem? T.row)) (f₀ := fxAt r) (W := W)
      (olds := K2.oldsAt (23 + 1)) (hnd := T4.hnd) (h0f := T4.h0f) (hcs := T4.hcs)
      (hpub := T4.hpub) (hkA := T4.hkA) (C := T4.C)
      (hT1 := fun a ha hr hk t he fx hfx =>
        ⟨(hT1' z a ha hr hk t he fx hfx).1, (hT1' z a ha hr hk t he fx hfx).2.1⟩)
      (hgrp := by rw [Aw.groupAt]; rfl) (d := baseCount r.set .request r.g) (hd := rfl)
      (hone := hone) hlv ?_
    intro a ha hr hk t het fx hfx lay hl' W₀ hW₀
    obtain rfl := he _ _ het
    obtain ⟨Pp, n, hP, hn⟩ := t3_nums_head T.scope T.reads T.opened T.laid.planOk
    have hp := V.posIs Pp n hP hn
    have k := P1K2.d_head_laid T.scope T.reads T.laid T.opened T.pinned T.cut T.sendsB
      (Fk := fun k s => ∃ z, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s))
      (fun s hs => hs) "" Pp n a.1 fx W₀ lay hP hn ⟨z, T.reach _ _ hr⟩ (t3_xk ha hk)
      (t3_front_congr hq hfx) hW₀ hl'
    rw [hp] at k
    exact ⟨_, _, _, _, k⟩
  · subst e24
    have hlv : ∀ s t' s', leave s t' = .ok s' → K2.finishBehindQ t' = .ok s' := by
      rcases V.wayOut with ⟨k, -⟩ | ⟨k, -⟩ | ⟨-, k⟩
      · omega
      · omega
      · exact k
    refine hAt_finish_new (h := h) (iJ := _) (iQ := _) (ext' := _) (G := D.G) (base := base)
      (d₁ := d₁) (d₂ := d₂) (p := pAt 24) (B := B)
      (enter := enter) (leave := leave) (N := P5J.At.N Z c) (Mg := mgAll D mgBase)
      (links := fullLinks) (ps := P5J.At.ps) (z := z) (Rch := rchAtZ Rch z) (k := k2NoAt 24)
      (m := 24)
      (n0 := K2.n0At (24 + 1)) (grp := 24 + 1) (codes := Z.first.codes)
      (sent := (K2Hands.sentW (24 + 1)).toArray) (lay₀ := lay₀) (Z := Z)
      (rad := P5J.At.rad Z Pb.lay) (ft := 0) (hPl := hPl) (hlay := hlay) (hB := T.members)
      (hF := fun a _ hr _ => hFz z a hr) (h0 := h0) (hen := T.way.keeps)
      (hBook := fun a ha hr hk t he => by
        have k1 := (hBook' z a ha hr hk t he).1
        rwa [T.firstTree] at k1)
      (h32 := V.logN) (hL := hL_full (List.mem_of_getElem? T.row)) (f₀ := fxAt r) (W := W)
      (olds := K2.oldsAt (24 + 1)) (hnd := T4.hnd) (h0f := T4.h0f) (hcs := T4.hcs)
      (hpub := T4.hpub) (hkA := T4.hkA) (C := T4.C)
      (hT1 := fun a ha hr hk t he fx hfx =>
        ⟨(hT1' z a ha hr hk t he fx hfx).1, (hT1' z a ha hr hk t he fx hfx).2.1⟩)
      (hgrp := by rw [Aw.groupAt]; rfl) (d := baseCount r.set .request r.g) (hd := rfl)
      (hone := hone) hlv ?_
    intro a ha hr hk t het fx hfx lay hl' W₀ hW₀
    obtain ⟨Pp, n, hP, hn⟩ := t3_nums_fin T.opened T.laid.planOk
    have hp := V.posIs Pp n hP hn
    have k := P1K2.d_finish_laid T.scope T.reads T.laid T.opened T.pinned T.cut T.sendsB
      (Fk := fun k s => ∃ z, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s))
      (fun s hs => hs) "" Pp n a.1 t fx W₀ lay hP hn ⟨z, T.reach _ _ hr⟩ (t3_xk ha hk)
      (he _ _ het) (t3_front_congr hq hfx) hW₀ hl'
    rw [hp] at k
    exact ⟨_, _, _, _, k⟩

end

/-! ## «rest → condition»: K2Short from the 26, the 8, hAt and the other 27 -/

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


/-- **The other 27 fields of K2Short.** Cut by program out of its text. -/
structure K2Rest3 : Prop where
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
  hins : (rowQ links ps k).ins = [.carry m, .pinKept m]
  hctx : (rowQ links ps k).ctx = []
  hoP : Item.pin (m + 1) 0 ∈ (rowQ links ps k).outs
  hoC : Item.row (m + 1) .carried ∈ (rowQ links ps k).outs
  hoR : Item.row (m + 1) .position ∈ (rowQ links ps k).outs
  hsam : sampledIn D.N (openAt links ps (k + 1)) = D.N.index :: D.N.sent (m + 1) 0
  hidx : D.N.index ∈ sampledIn D.N (openAt links ps k)
  hkeys : KeysFit (F := F) (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ
      D.G seatN base d₁ F) (pAt m) base idExt
  hd : DecBlind D.decT
  hFk : ∀ z (a : Rec × F.E.Str), Rch k ((z, a.1), a.2) → Fk z k a.1
  hHands : ∀ z, HandsR (Fk z) D.N links ps (EQ (mgAll D mgBase) links ps z) F.ft k B
  hdoor : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → door m a.1 = some t
  hcar : ∀ z, ∀ s y w, carryK2 rowAt pAt door (K2.orcY F.all F.key) (fun r H => smpK2 r H) m (z, s)
      y w → (mgAll D mgBase).carry m (z, s) y w
  hS : Sits B (K2.codeSwitchKind (pAt m) : Block Rec Unit) enter leave
  leftDoor : LeftDoor enter leave
  hD : DoorKeeps (F := F) (Letters.plain r (r.ok_says h)) iJ iQ (pAt m) leave (fbOf (Letters.plain r
      (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ D.G seatN) (fun _ =>
      ((), ())))
  O : ∀ z, K2Owes D mgBase links ps k z (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq
      base d₁ d₂ extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN
      base d₁ d₂ pAt m)) (rchAtZ Rch z k) pl (m + 1) MO LO

variable {D Rch h iJ iQ seat seatN base d₁ d₂ seats c₀ d₀ y₀ rowAt pAt door m B enter leave links ps
    k f₀ W n0 grp rows olds L trees news b₀ bq extq pl MO LO Fk}

/-- **K2Short FROM THE 26, THE 8, hAt AND THE OTHER 27.** -/
theorem k2Short_of_t14_t23_t3
    (T : T14Fields D Rch h iJ iQ seat seatN seats pAt m enter links ps k f₀ W n0 grp rows olds L
      trees news pl)
    (U : T23Fields D Rch h iJ iQ seatN base d₁ d₂ seats c₀ pAt m B enter links ps k n0 bq extq pl)
    (V : T3Field D Rch h iJ iQ seatN base d₁ d₂ c₀ pAt m B enter leave links ps k n0 grp pl)
    (R : K2Rest3 D Rch h iJ iQ seatN base d₁ d₂ c₀ rowAt pAt door m B enter leave links ps k
      n0 b₀ bq extq pl MO LO Fk) :
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
    hseat := U.hseat
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
    M := U.M
    C := T.C
    hkeys := R.hkeys
    horc := T.horc
    hSR := U.hSR
    hd := R.hd
    hFk := R.hFk
    hHands := R.hHands
    hT1 := T.hT1
    hBook := T.hBook
    hOld := T.hOld
    hBF := U.hBF
    hdoor := R.hdoor
    hsh := T.hsh
    hsn := T.hsn
    hσ := U.hσ
    hshN := U.hshN
    hnew := U.hnew
    hAt := V.hAt
    hcar := R.hcar
    hS := R.hS
    leftDoor := R.leftDoor
    hD := R.hD
    hbk := U.hbk
    O := R.O }

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.t3_hF
#print axioms VerifiableInference.Desc.First.K2Caller.t3_hInv
#print axioms VerifiableInference.Desc.First.K2Caller.t3_front_congr
#print axioms VerifiableInference.Desc.First.K2Caller.t3_nums_link
#print axioms VerifiableInference.Desc.First.K2Caller.t3_nums_head
#print axioms VerifiableInference.Desc.First.K2Caller.t3_nums_fin
#print axioms VerifiableInference.Desc.First.K2Caller.t3_xk
#print axioms VerifiableInference.Desc.First.K2Caller.t3_hAt_const
#print axioms VerifiableInference.Desc.First.K2Caller.k2Short_of_t14_t23_t3
