-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FramePileWo.lean: AT THE COMPOSED MEANING `mgAll 𝔇 Mg`
(Johnson/Desc/Sound/MgAll.lean): the three sentences on "in what sense a pending linear
claim holds of a witness, at a state of the verifier" that the link's frame's tie at "cleared" takes
as premises (Johnson/P1L20R/FrameSits.lean: the field pile of FrameOwes; the second half of
ClearOwes; spent by `pileGivesWo_of`, FrameWo.lean).

  holdAt 𝔇 a w r     THE SENSE: the claim r is true of what the pile's own reader 𝔇.rw13 reads of the
                     witness w at the state a: the committed table's matrix off w's cells; the mask
                     entries off w's words, found through the state's own book of trees
  pile_gives_hold    (i) where the chain stands between two links, "pile" gives holdAt of every
                     pending claim: no premise
  D1Fits d built lay lin   three equations on the parameter 𝔇.d1: its layout and its shape of a
                     claim are lay and lin; its number of claims at link l is the planned link's own
  d1Fits_at          THEY CAN BE MET: at the closed term `FillP1.d1At Z` (D1At.lean), at the very
                     letters at which ClearOwes is written
  not_d1Fits         THEY CAN FAIL: a number of claims that is one too high
  hold_gives_wo      (ii) under D1Fits: holdAt of the claim that the frame's reader `rowAt` gives, if
                     it gives one, is "wo l"
  LeavesReader s t   what that reader reads of the state is in t what it is in s: the book of trees,
                     the statement's codes, each oracle message's shape
  leavesReader_cleared, leavesReader_frame   every accepting step of "cleared" is a member; so at a
                     row of the frame's own list (`framesOf`); not_leavesReader: it can fail
  hold_back          (iii) holdAt goes back over every step with `LeavesReader`
  frameOwes_pile, clearOwes_second   (i), and (ii) with (iii), IN THE LETTERS OF FrameOwes.pile AND OF
                     ClearOwes' SECOND HALF, at Hold := holdAt 𝔇; In: a letter (there: FrontAt ...)

How the three bind the sense. At "every claim holds" (i) and (iii) are free and (ii) fails; at "no
claim holds" (ii) and (iii) are free and (i) fails. holdAt is the one sense of which "pile" and "wo"
both speak, by their makes.

Limits. 𝔇 and Mg are letters; of 𝔇 only d1, arr and mat13 are read. The flag "a claim is left" is
not spent here (ClearOwes hands it over; nothing needs it). That "pile" holds anywhere is not shown.
No soundness statement.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Top.H0.Fill.D1At
import Johnson.Top.H0.Walk.FrameTiedRec
import Johnson.Top.H0.Walk.FrameRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll CellsQ mgAll_pile mgAll_wo)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.First.FillP1 (PubData d1At)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.K13.Law (Holds ρg rwBook_same)

/-! ## 0 What the pile's reader reads of the state, and "cleared" -/

/-- **What the pile's reader reads of the verifier's state is in t what it is in s.** -/
structure LeavesReader (s t : S) : Prop where
  book : t.book = s.book
  codes : t.st.codes = s.st.codes
  shapes : ∀ o : Nat, (t.st.oracles[o]?).map (fun a : Oracle => a.shape) =
    (s.st.oracles[o]?).map (fun a : Oracle => a.shape)

/-- It can fail: a statement with one oracle message more. -/
theorem not_leavesReader (s : S) (x : Oracle) :
    ¬ LeavesReader s { s with st := { s.st with oracles := s.st.oracles.push x } } := fun h => by
  have e := h.shapes s.st.oracles.size
  simp at e

/-- **Every accepting step of "cleared" is a member.** -/
theorem leavesReader_cleared {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t) :
    LeavesReader s t := by
  obtain ⟨-, -, -, gbook, -, -, -, -, gcodes, -, -, gmsgs, -⟩ :=
    clearedGives X counts left lay lin s t h
  refine ⟨gbook, gcodes, fun o => ?_⟩
  have e := congrArg (Option.map fun a : Oracle => a.shape) (gmsgs o)
  simpa only [Option.map_map, Function.comp_def] using e

/-- The same at a row of the frame's own list. -/
theorem leavesReader_frame {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List Seat.LinkFrame} {f : Seat.LinkFrame} (hfs : Seat.framesOf built first W = .ok fs)
    (hf : f ∈ fs) {s t : S} (h : f.clear s = .ok t) : LeavesReader s t := by
  obtain ⟨-, X, counts, left, e, -⟩ := Seat.framesOf_row hfs hf
  rw [e] at h
  exact leavesReader_cleared h

/-- Between two links the pending claims are the pile. -/
theorem rows_of_between {s : S} (h : s.atBetween = true) : s.rows = s.out.pending := by
  unfold S.atBetween at h
  unfold S.rows
  cases hh : s.here <;> simp [hh] at h ⊢

/-! ## 1 The three equations on the parameter d1 -/

/-- The parameter's layout and shape of a claim are lay and lin; its number of claims at a link is
the planned link's own. -/
structure D1Fits (d : PubData) (built : Array Stages.LinkH) (lay : WsLay) (lin : Params.LinShape) :
    Prop where
  lay : d.lay = lay
  lin : d.lin = lin
  ncl : ∀ l X', built[l]? = some X' → d.ncl l = X'.NCL

/-- **They can be met**: at the closed term, at the letters at which ClearOwes is written. -/
theorem d1Fits_at (Z : ProofFile.Pub) :
    D1Fits (d1At Z) Z.p.built.links Z.p.X.layers.wsLay Z.first.lin :=
  ⟨rfl, rfl, fun l X' h => by
    show ((Z.p.built.links[l]?).map (·.NCL)).getD 0 = X'.NCL
    rw [h]
    rfl⟩

/-- **They can fail**: a number of claims that is one too high, at a link that is there. -/
theorem not_d1Fits (Z : ProofFile.Pub) (l : Nat) (X' : Stages.LinkH) (h : Z.p.built.links[l]? = some X') :
    ¬ D1Fits { d1At Z with ncl := fun _ => X'.NCL + 1 } Z.p.built.links Z.p.X.layers.wsLay
      Z.first.lin := fun H => by
  have e : X'.NCL + 1 = X'.NCL := H.ncl l X' h
  omega

/-! ## 2 The sense, and the three sentences -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **In what sense a pending linear claim holds of a witness, at a state**: the pile's own. -/
def holdAt (a : P × S) (w : VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT)
    (r : TensorRow) : Prop := Holds ρg (𝔇.rw13 a w) r

/-- **(i)** -/
theorem pile_gives_hold (a : P × S) (y : Strs)
    (w : VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT) (hB : a.2.atBetween = true)
    (h : (mgAll 𝔇 Mg).pile a y w) : ∀ r ∈ a.2.out.pending, holdAt 𝔇 a w r := by
  intro r hr
  rw [mgAll_pile] at h
  exact h r (by rw [rows_of_between hB]; exact hr)

/-- **(ii)** -/
theorem hold_gives_wo {built : Array Stages.LinkH} {lay : WsLay} {lin : Params.LinShape}
    (hd : D1Fits 𝔇.d1 built lay lin) (l : Nat) (X' : Stages.LinkH) (hX : built[l]? = some X')
    (a : P × S) (y : Strs) (w : VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT)
    (h : ∀ r, Law.rowAt lay X'.NCL lin a.2 = some r → holdAt 𝔇 a w r) :
    (mgAll 𝔇 Mg).wo l a y w := by
  rw [mgAll_wo]
  intro r hr
  rw [hd.lay, hd.ncl l X' hX, hd.lin] at hr
  exact h r hr

/-- **(iii)** -/
theorem hold_back (p : P) {s t : S} (hL : LeavesReader s t)
    (w : VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT) (r : TensorRow)
    (h : holdAt 𝔇 (p, t) w r) : holdAt 𝔇 (p, s) w r := by
  unfold holdAt MgData.rw13 at h ⊢
  rw [rwBook_same 𝔇.arr 𝔇.mat13 (p, s) (p, t) hL.book hL.codes hL.shapes w] at h
  exact h

/-! ## 3 In the letters of FrameOwes and ClearOwes -/

/-- FrameOwes' field pile, at Hold := holdAt 𝔇. -/
theorem frameOwes_pile : ∀ (a : P × S) (y : Strs)
    (w : VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT), a.2.atBetween = true →
    (mgAll 𝔇 Mg).pile a y w → ∀ r ∈ a.2.out.pending, holdAt 𝔇 a w r :=
  fun a y w hB h => pile_gives_hold 𝔇 Mg a y w hB h

/-- ClearOwes' second half, at Hold := holdAt 𝔇. -/
theorem clearOwes_second {Z : ProofFile.Pub}
    (hd : D1Fits 𝔇.d1 Z.p.built.links Z.p.X.layers.wsLay Z.first.lin)
    {fs : List Seat.LinkFrame} {f : Seat.LinkFrame}
    (hfs : Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs) (l : Nat) (hf : fs[l]? = some f)
    (In : P × S → Strs → Prop) :
    ∀ X', Z.p.built.links[l]? = some X' → X'.fv = true →
      (∀ a y w, (∀ r, Law.rowAt Z.p.X.layers.wsLay X'.NCL Z.first.lin a.2 = some r →
        holdAt 𝔇 a w r) → (mgAll 𝔇 Mg).wo l a y w) ∧
      ∀ p s t y w r, f.clear s = .ok t → In (p, s) y → holdAt 𝔇 (p, t) w r →
        holdAt 𝔇 (p, s) w r :=
  fun X' hX _ => ⟨fun a y w h => hold_gives_wo 𝔇 Mg hd l X' hX a y w h,
    fun p _ _ _ w r hc _ h =>
      hold_back 𝔇 p (leavesReader_frame hfs (List.mem_of_getElem? hf) hc) w r h⟩

end

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.not_leavesReader
#print axioms Johnson.Desc.First.Walk.Tied.leavesReader_cleared
#print axioms Johnson.Desc.First.Walk.Tied.leavesReader_frame
#print axioms Johnson.Desc.First.Walk.Tied.d1Fits_at
#print axioms Johnson.Desc.First.Walk.Tied.not_d1Fits
#print axioms Johnson.Desc.First.Walk.Tied.pile_gives_hold
#print axioms Johnson.Desc.First.Walk.Tied.hold_gives_wo
#print axioms Johnson.Desc.First.Walk.Tied.hold_back
#print axioms Johnson.Desc.First.Walk.Tied.frameOwes_pile
#print axioms Johnson.Desc.First.Walk.Tied.clearOwes_second
