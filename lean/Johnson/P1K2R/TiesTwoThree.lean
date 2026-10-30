-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/TiesTwoThree.lean: code switching (K2): EIGHT FIELDS THAT THE SECOND AND THE
THIRD TIE SPEND (k02_t2S | k02_t3R), IN THE LETTERS OF K2Short (Johnson/P1K2R/Shorter.lean), AT THE
CLOSED CONSTANT's OWN PARAMETERS (P5J.At, Johnson/P5J/LettersAt.lean), AT EACH OF THE 25 PLACES, IN
ONE LEMMA. After the pattern of Johnson/P1K2R/TiesOneFour.lean.
  T23Fields    eight fields of K2Short, cut by program out of its text: hSR · hbk · hBF · hnew ·
               hseat · hshN · hσ · M
  T23More      WHAT IS LEFT BESIDE T14Left, each by name (below)
  t23_fields_const  T14Left · T23More ⟹ T23Fields, at TiesOneFour.lean's letters
  newLen_full  a closed fact by Lean's kernel: each written row's new list is one shorter than the
               written list of notices of its switch; newLen_can_fail: a negative test
  t23_fit · t23_place · t23_lay  sentFit_… | sentPlace_… in one form, by the way in; the
               written list of notices can be laid
  t23_hnew     hnew, uniform in m
  K2Rest2 · k2Short_of_t14_t23  «rest → condition»: the other 28 fields of K2Short, cut by program;
               K2Short from the 26, the 8 and the 28: so Lean holds the letters
THE PAYERS. hSR: seedReads · hbk: hbk_id | hbk_fin · hBF: hBF_plain · hnew: hnew_link | _head | _fin
(all: Johnson/P1K2R/TieTwoPays.lean) at sentFit_link | _head | _fin (K2Ties/SentFitAt.lean)
· hseat: hseat_seatNew · hshN: hshN_of (TieTwoPays.lean) at hsent_seatNew (the two …_seatNew:
Tw/K2C/SeatNewTrees.lean), both at sentPlace_… (K2Ties/SentPlaceAt.lean) · hσ:
hσ_at_place (Tw/K2C/TieThreeSmpAt.lean) at newSeats_const (K2Ties/NewSeatsConst.lean) and
T14Fields' hT1 · M: membersLike_plan (Tw/K2C/OneSeat.lean).
WHAT IS LEFT BESIDE T14Left (T23More), BY NAME. frameFt: the frame's first tree is 0 · blockAt: B is
the chain's sub-protocol at the switch's number · sits: B sits over the kind's own sub-protocol
behind the door · keepsOut: the way out keeps what the law reads · w2: the two written rounds fit
the typed structure · baseIs: the piece's base is the table's count of trees in front · treesLen:
the first written round sends as many trees as the written notices' lay has · shownAll:
Piece.ShownAll (Johnson/Desc/Sound/ShownOfData.lean) at the piece.
NOT IN IT: hAt (the third tie's clause at an accept: hAt_…_new (Tw/K2C/TieThreeSeatNew.lean) ask
beside: the debts on the numbers in the front's letters, «one stored row», p.logN ≤ 32, the codes'
lengths, the ways out: a join of its own) · hsam · hidx · said (P1K2R/TableAtConst.lean has them)
· hHands · hFk.
LIMITS. Joins, and one closed fact by the kernel. No premise is shown met at a real value: no
example. M leans on T14Left's «members», a test whose value no theorem has. Since this was written:
under the wider head P5J.AtMgA (its field opts, its entry tests) a theorem: membersPlan_ofHead
(Johnson/Top/H0/K2Ties/AtHead3.lean; see the rider in its head). The full size alone. No
probability; no soundness is claimed.
-/
import Johnson.P1K2R.TiesOneFour
import Johnson.P1K2R.TieTwoPays
import Johnson.Top.H0.K2Ties.SentPlaceAt
import Johnson.Top.H0.K2Ties.NewSeatsConst
import Johnson.Top.H0.Tw.K2C.SeatNewTrees
import Johnson.Top.H0.Tw.K2C.TieThreeSmpAt
import Johnson.Top.H0.Tw.K2C.OneSeat

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

open VerifiableInference.Desc.First.K2Ties (AtWritten AtTold at_written at_told sentFit_link
  sentFit_head sentFit_fin sentPlace_link sentPlace_head sentPlace_fin newSeats_const)
open Johnson.G (fxAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open P5J (LaidAt F0T fullLinks)

variable {F : Frame}

/-! ## The eight fields -/

/-- **Eight fields of K2Short that the second and the third tie spend.** Cut by program. -/
structure T23Fields {P Tok XiD : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public}
    {r : SwRow} (D : MgData XiD P Tok rws cls nR X) (Rch : ℕ → (P × First.S) × F.E.Str → Prop)
    (h : r.ok = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
      (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J →
      (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
      (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
      (sigOf r.cs r.l).Ent)
    (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT) (seats : List (ℕ × ℕ))
    (c₀ : CellsQ rws cls) (pAt : ℕ → K2.P2) (m : ℕ) (B : Block Rec Cl)
    (enter : Rec → Except String Rec) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (k n0 : ℕ) (bq : Block (P × First.S) Cl)
    (extq : (P × First.S) × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wq rws cls Tok →
      Wq rws cls Tok) (pl : VerifiableInference.Desc.Place) : Prop where
  hSR : SeedReads
  hbk : ∀ s t, enter s = .ok t → t.book = s.book
  hBF : ∀ z a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN base d₁ d₂
      pAt m)).ior.red.out a τ = some b → BookFits a.1.book ∧ BookFits b.1.book
  hnew : ∀ z a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2)
      → ¬ a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN base d₁ d₂
      pAt m)).ior.red.out a τ = some b → ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay :
      TreeLay) (n : Nat), K2.frontAt (pAt m) t = some x ∧ layTrees x.st.codes (switchNotices x.T
      x.others) = some lay ∧ sameMembers ((List.range n).map fun i => (t.book.trees.size +
      lay.tree.getD i 0, lay.part.getD i 0)) (D.N.sent (m + 1) 0) = true ∧ ∀ i, i < n → ∃ nt,
      (switchNotices x.T x.others)[i]? = some nt ∧ nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows +
      nt.shape.maskRows
  hseat : ∀ i, base ≤ (seatN i).1 ∧ (seatN i).1 - base < d₁.trees.length
  hshN : ∀ z a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2)
      → ¬ a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN base d₁ d₂
      pAt m)).ior.red.out a τ = some b → ∀ i, ShownAt D.G r.cs r.l seatN (strsOf F b.2) i
  hσ : ∀ z, ∀ a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a →
      ¬ a.1.failed ≠ none → (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁
      d₂ (wordsMade iJ iQ D.G seatN base d₁ F) (pAt m) base idExt) B ((extW (F := F) D d₁ d₂ c₀
      links pl) z)).ior.red.out a τ = some b → K2.SmpLike r.cs (smpNamed (P := P) r.cs seats) (z,
      b.1) ⟨r.l, seatN⟩ (fun o => newSmp n0 b.1 o)
  M : K2.MembersLike D.ms ⟨r.l, seatN⟩ (D.N.sent (m + 1) 0)

/-! ## A closed fact, and sentFit_… | sentPlace_… in one form -/

set_option maxRecDepth 1000000 in
/-- **Each written row's new list is one shorter than its switch's written list of notices.** -/
theorem newLen_full : (List.range 25).all (fun m => (tableFullLit[m]?).any fun r =>
    r.l.length + 1 == (K2Hands.sentW (m + 1)).length) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the rows moved by one against the switches. -/
theorem newLen_can_fail : (List.range 24).all (fun m => (tableFullLit[m]?).any fun r =>
    r.l.length + 1 == (K2Hands.sentW (m + 2)).length) = false := by decide +kernel

section
variable {Z : ProofFile.Pub} {c : VerifiableInference.Desc.Chain Rec Cl} {m : ℕ}
  {enter : Rec → Except String Rec} {q : K2.P2}

theorem t23_fit (Aw : AtWritten Z c) (T : AtTold Z c) (w : WayAt m enter q) :
    K2.sentFitB (P5J.At.N Z c) (m + 1) P5J.At.ps[k2NoAt m]? Z.first.codes
      (K2Hands.sentW (m + 1)).toArray = true := by
  rcases w with ⟨h23, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
  · have e : k2NoAt m = 14 * (m + 1) + 2 := by unfold k2NoAt; rw [if_pos h23]
    rw [e]
    exact sentFit_link Aw T h23
  · rw [show k2NoAt 23 = 339 from rfl]
    exact sentFit_head Aw T
  · rw [show k2NoAt 24 = 353 from rfl]
    exact sentFit_fin Aw T

theorem t23_place (Aw : AtWritten Z c) (T : AtTold Z c) (w : WayAt m enter q) :
    sentPlaceB (P5J.At.N Z c) (m + 1) P5J.At.ps[k2NoAt m]? Z.first.codes
      (K2Hands.sentW (m + 1)).toArray = true := by
  rcases w with ⟨h23, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
  · have e : k2NoAt m = 14 * (m + 1) + 2 := by unfold k2NoAt; rw [if_pos h23]
    rw [e]
    exact sentPlace_link Aw T h23
  · rw [show k2NoAt 23 = 339 from rfl]
    exact sentPlace_head Aw T
  · rw [show k2NoAt 24 = 353 from rfl]
    exact sentPlace_fin Aw T

/-- The written list of notices can be laid: the test sentFitB rejects where it cannot. -/
theorem t23_lay {N : Numbers} {g : ℕ} {pIn : Option VerifiableInference.Desc.Place}
    {codes : OnBytes.Codes} {sent : Array OracleNotice}
    (h : K2.sentFitB N g pIn codes sent = true) : ∃ lay₀, layTrees codes sent = some lay₀ := by
  unfold K2.sentFitB at h
  cases e : layTrees codes sent with
  | none => rw [e] at h; cases h
  | some lay => exact ⟨lay, rfl⟩

end

/-! ## hnew, uniform in m -/

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {Fd : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base₀ : List (Block Rec Cl)} {c : VerifiableInference.Desc.Chain Rec Cl}
  {A : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}
  {Rch : ℕ → (ProofFile.InstPub × First.S) × F.E.Str → Prop} {m : ℕ}
  {enter : Rec → Except String Rec} {leave : Rec → Rec → Except String Rec} {p : K2.P2}
  {C : _root_.Run.PQ.CK} {Wt : Type} {Mg : Meaning ProofFile.InstPub Wt} {links : List ModelPart}
  {q : Piece C F (ProofFile.InstPub × First.S) Cl Wt} {B : Block Rec Cl}
  {ext : ProofFile.InstPub → Rec × F.E.Str → Tr (uLT C q.ds) → Wt → Wt} {err : Err (uLT C q.ds)}

theorem t23_hnew (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL Fd Z Bs base₀ c A B')
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (Aw : AtWritten Z c) (T : AtTold Z c) (w : WayAt m enter p)
    (hSit : Sits B (K2.codeSwitchKind p : Block Rec Unit) enter leave) :
    ∀ z a τ b, onQ (P5J.At.N Z c) Mg links P5J.At.ps (fun s => (z, s)) (k2NoAt m) a →
      Rch (k2NoAt m) ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
        K2.frontAt p t = some x ∧
        layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
        sameMembers ((List.range n).map fun i =>
          (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0))
          ((P5J.At.N Z c).sent (m + 1) 0) = true ∧
        ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
          nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows := by
  rcases w with ⟨h23, hq, he⟩ | ⟨rfl, hq, he⟩ | ⟨rfl, hq, he⟩
  · have e : k2NoAt m = 14 * (m + 1) + 2 := by unfold k2NoAt; rw [if_pos h23]
    rw [e]
    exact P1K2.hnew_link hS hR O hy hRch h23 (sentFit_link Aw T h23) hq hSit he
  · exact P1K2.hnew_head hS hR O hy hRch (sentFit_head Aw T) hq hSit he
  · exact P1K2.hnew_fin hS hR O hy hRch (sentFit_fin Aw T) hq hSit he

end

/-! ## What is left beside T14Left, and the one lemma -/

/-- **WHAT IS LEFT BESIDE T14Left**, each by name. -/
structure T23More {Tok : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (D : MgData ProofFile.Inst ProofFile.InstPub Tok rws cls nR X) (Z : ProofFile.Pub)
    (c : VerifiableInference.Desc.Chain Rec Cl) (m : ℕ) (r : SwRow) (pAt : ℕ → K2.P2)
    (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec) (B : Block Rec Cl)
    (base : ℕ) (d₁ d₂ : RDT) (bq : Block (ProofFile.InstPub × First.S) Cl)
    (extq : (ProofFile.InstPub × First.S) × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wq rws cls Tok →
      Wq rws cls Tok) : Prop where
  frameFt : F.ft = 0
  blockAt : c.blocksInOrder[k2NoAt m]? = some B
  sits : Sits B (K2.codeSwitchKind (pAt m) : Block Rec Unit) enter leave
  keepsOut : KeepsOut leave
  w2 : K2Wr r d₁ d₂
  baseIs : base = (P5J.At.N Z c).treesAt P5J.At.ps[k2NoAt m]?
  treesLen : ∀ lay₀, layTrees Z.first.codes (K2Hands.sentW (m + 1)).toArray = some lay₀ →
    d₁.trees.length = lay₀.shapes.size
  shownAll : (k2Q (P := ProofFile.InstPub) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
    extq).ShownAll D.G r.cs r.l (seatNew (P5J.At.N Z c) m r)

section
variable {Tok : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {D : MgData ProofFile.Inst ProofFile.InstPub Tok rws cls nR X}
  {Rch : ℕ → (ProofFile.InstPub × First.S) × F.E.Str → Prop} {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
  {Dw : WholeD} {rn : LPFD.Full.RunPF} {Z : ProofFile.Pub} {Np : H2U.Places4}
  {c : VerifiableInference.Desc.Chain Rec Cl} {Bs : ProofFile.PureBase} {base₀ : List (Block Rec Cl)}
  {A : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat} {m : ℕ} {r : SwRow} {W : SwitchFrame} {L : Laid}
  {pAt : ℕ → K2.P2} {enter : Rec → Except String Rec} {pl : VerifiableInference.Desc.Place}
  {leave : Rec → Rec → Except String Rec} {B : Block Rec Cl} {base : ℕ} {d₁ d₂ : RDT}
  {bq : Block (ProofFile.InstPub × First.S) Cl}
  {extq : (ProofFile.InstPub × First.S) × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wq rws cls Tok →
    Wq rws cls Tok}

set_option maxHeartbeats 2000000 in
/-- **EIGHT FIELDS OF THE SECOND AND THE THIRD TIE, AT THE CONSTANT's LETTERS.** -/
theorem t23_fields_const (T : T14Left D Rch Pb pp Dw rn Z Np c Bs base₀ A B' m r W L pAt enter pl)
    (U : T23More (F := F) D Z c m r pAt enter leave B base d₁ d₂ bq extq) (h : r.ok = true)
    (c₀ : CellsQ rws cls)
    (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) (iJW (r.ok_says h) T.kA T.fitW)
        (iQW (r.ok_says h) T.kA T.fitW)).sw).X ×
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) (iJW (r.ok_says h) T.kA T.fitW)
        (iQW (r.ok_says h) T.kA T.fitW)).sw).Ex.Str) :
    T23Fields D Rch h (iJW (r.ok_says h) T.kA T.fitW) (iQW (r.ok_says h) T.kA T.fitW)
      (seatNew (P5J.At.N Z c) m r) base d₁ d₂ (P5J.At.seats Z) c₀ pAt m B enter fullLinks P5J.At.ps
      (k2NoAt m) (K2.n0At (m + 1)) bq extq pl := by
  have Aw : AtWritten Z c := at_written T.scope T.laid T.pinned
  have At' : AtTold Z c := at_told T.cut Aw
  have hm : m < 25 := t14_lt T.row
  have T4 := t14_fields_const T h
  have hPl := t23_place Aw At' T.way
  obtain ⟨lay₀, hlay⟩ := t23_lay (t23_fit Aw At' T.way)
  have hl : r.l.length ≤ (K2Hands.sentW (m + 1)).toArray.size - 1 := by
    have k := List.all_eq_true.1 newLen_full m (List.mem_range.2 hm)
    rw [T.row] at k
    simp only [Option.any_some, beq_iff_eq] at k
    rw [List.size_toArray, ← k]
    omega
  exact
    { hSR := P1K2.seedReads
      hbk := fun s t e => (T.way.keeps s t e).1
      hBF := by
        rw [T.dN]
        exact P1K2.hBF_plain T.opened T.laid.planOk T.reach U.frameFt U.blockAt
      hnew := by
        rw [T.dN]
        exact t23_hnew T.scope T.reads T.opened T.pinned T.reach Aw At' T.way U.sits
      hseat := hseat_seatNew hPl hlay r hl U.baseIs (U.treesLen lay₀ hlay)
      hshN := by
        rw [T.dN]
        exact P1K2.hshN_of U.shownAll
          (hsent_seatNew hPl hlay r hl U.baseIs [d₂] (U.treesLen lay₀ hlay))
      hσ := fun z => hσ_at_place (Cl₀ := Unit) h _ _ D.G _ base d₁ d₂ U.w2 (pAt m)
        (fun _ => d₀.2) (fun _ => d₀.1) B enter leave U.sits.rounds U.sits.step _ D.N
        (mgAll D mgBase) fullLinks P5J.At.ps z (rchAtZ Rch z) (k2NoAt m) (K2.n0At (m + 1)) (m + 1) 0
        U.keepsOut (fxAt r) W (K2.oldsAt (m + 1)) T4.hnd T4.h0f T4.hcs T4.hpub
        (fun a ha hr hk t he fx hfx =>
          ⟨(T4.hT1 z a ha hr hk t he fx hfx).1, (T4.hT1 z a ha hr hk t he fx hfx).2.1⟩)
        (P5J.At.seats Z) (newSeats_const Aw T.row)
      M := by
        rw [T.dN, T.dms]
        exact membersLike_plan T.members }

end

/-! ## «rest → condition»: K2Short from the 26, the 8 and the other 28 -/

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


/-- **The other 28 fields of K2Short.** Cut by program out of its text. -/
structure K2Rest2 : Prop where
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
  O : ∀ z, K2Owes D mgBase links ps k z (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq
      base d₁ d₂ extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN
      base d₁ d₂ pAt m)) (rchAtZ Rch z k) pl (m + 1) MO LO

variable {D Rch h iJ iQ seat seatN base d₁ d₂ seats c₀ d₀ y₀ rowAt pAt door m B enter leave links ps
    k f₀ W n0 grp rows olds L trees news b₀ bq extq pl MO LO Fk}

/-- **K2Short FROM THE 26, THE 8 AND THE OTHER 28.** -/
theorem k2Short_of_t14_t23
    (T : T14Fields D Rch h iJ iQ seat seatN seats pAt m enter links ps k f₀ W n0 grp rows olds L
      trees news pl)
    (U : T23Fields D Rch h iJ iQ seatN base d₁ d₂ seats c₀ pAt m B enter links ps k n0 bq extq pl)
    (R : K2Rest2 D Rch h iJ iQ seatN base d₁ d₂ c₀ rowAt pAt door m B enter leave links ps k
      n0 grp b₀ bq extq pl MO LO Fk) :
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
    hAt := R.hAt
    hcar := R.hcar
    hS := R.hS
    leftDoor := R.leftDoor
    hD := R.hD
    hbk := U.hbk
    O := R.O }

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.newLen_full
#print axioms VerifiableInference.Desc.First.K2Caller.newLen_can_fail
#print axioms VerifiableInference.Desc.First.K2Caller.t23_fit
#print axioms VerifiableInference.Desc.First.K2Caller.t23_place
#print axioms VerifiableInference.Desc.First.K2Caller.t23_lay
#print axioms VerifiableInference.Desc.First.K2Caller.t23_hnew
#print axioms VerifiableInference.Desc.First.K2Caller.t23_fields_const
#print axioms VerifiableInference.Desc.First.K2Caller.k2Short_of_t14_t23
