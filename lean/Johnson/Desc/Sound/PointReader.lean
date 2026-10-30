-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointReader.lean: THE LAW AT "LIN point" AT A FIRST TABLE's MEANING WHOSE SENTENCE ON THE PENDING ROWS (pileOne) IS ITS OWN: THE STRUCTURE JointSays' FIFTH CLAUSE, AN EQUATION, GIVES WAY TO ONE DIRECTION, FENCED. One definition, five lemmas, three theorems. A joint build of files of Johnson/Desc/Sound/ and of Johnson/Desc/K13/ and K14/.
WORDS. "The verifier's state": the value that the verifier carries between two sub-protocols. "Promise": the condition on the state and the oracles under which a sub-protocol's law is asked.
WHY. JointSays (Johnson/Desc/Sound/PointAtLayers.lean) asks Mg₁.pileOne = "all pending rows are true at the reader witOf (matBy kCol (matC cells)) (wordsOn …)". AT THE COMPOSED MEANING THAT COUNTS four clauses hold through Lean; this one does not close: that meaning's own reader cuts the mask entries to the table's size, reads its own matrix and its own number of rows. THE SENTENCE THAT IS MEANT IS THE COMPOSED MEANING's OWN: the shared table's claim is Mg₁.pileOne by the make (tiedMeaning), and the joint back to the first chain wants that term. The other sentence is only what the step back from (Eval) PROVES. AND AN EQUATION IS TOO MUCH: the law must only SHOW the claim IN FRONT, for the extracted witness, inside the promise.
  pileStep stOf₁ tabP₁ Pw matC a w: the sentence that the step back proves (JointSays' fifth clause's right side).
  muQ_claim · relQ₂_two_claim · relQ₂_one_claim: two meanings of the shared table that part at the field claimM alone: the shared items are one; the relation at border 2 is one (the claim is not open there); at border 1 it goes over where the claim does.
  leadsB_claim: so a law towards stepPt at the one is a law towards stepPt at the other, where INSIDE THE PROMISE, AT A WITNESS AT WHICH THE RELATION IN FRONT HOLDS AT THE ONE, the other's claim holds.
  point_leadsB_reader: point_leadsB_reached (Johnson/Desc/Sound/PointReached.lean) CALLED AT { Mg₁ with pileOne := pileStep … } (JointSays holds there from the four; the promise reads no pileOne), then carried to Mg₁. point_leadsBN_cap_reader: the like of point_leadsBN_cap_reached (leadsBN_claim).
  hpile_of_iff: hpile from another form of the clause: "wherever a test T on the state accepts, the two sentences are one", with "T accepts at what R holds of".

Limits. hpile IS A PREMISE, AND IT BEARS WEIGHT. ITS PAYERS ARE THE FILES OF THE LAST SUB-PROTOCOLS OF THE FIRST CHAIN (K13). ITS WHOLE CONTENT IS A QUESTION: "CAN A REACHED STATE, ADVERSARIAL ROUNDS INCLUDED, HOLD A PENDING ROW THAT NAMES A MASK ENTRY BEYOND ITS TABLE?": if none can, the two readers agree at whatever a pending row reads (with the matrix and the number of rows by a choice of parameters); IF ONE CAN, hpile IS FALSE THERE AND THIS LAW SAYS NOTHING. Whether ocEnd, R p and "no mark" can be met together is not shown here. Else as PointReached.lean's. ONE SUB-PROTOCOL's CLAUSE, UNDER PREMISES. NO MEMBER IS SHOWN. It rests, through the count of the key's lost points, on the files under ThirdParty/ (lean/LIMITS.md, L15).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf)
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Chain Strs Wit FileDescription First.S)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound (Frame Piece below onQ₂ actQ stepPt strsOfAct SitsAt extS MsgT Mem Sending CellsOf
  ocEnd ocEnd_pub tiedMeaning tiedNumbers LettersReadBelow ocEndReadsBelow pinJT)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt EvalLaid laidOf laidOf_ok evalLaidB evalLaidB_iff wSitsItem wSitsB wSitsL
  wSeatB wSitsB_gives witOf matBy RowsTrue WRow)

variable {P₁ P₀ Xi Cells Tok Cl' : Type} {F : Frame}

/-- **The sentence on the pending rows that the step back from (Eval) proves.** -/
def pileStep (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (Pw : Where) (matC : Cells → Nat → Nat → GE) (a : P₀ × First.S) (w : Wit Cells Tok MsgT) : Prop :=
  RowsTrue (nR := Pw.lin.matrixRows) (k := Pw.lin.kCol)
    (fun w' : Wit Cells Tok MsgT => witOf (matBy Pw.lin.kCol (matC w'.cells)) (wordsOn (stOf₁ a) (tabP₁ a w')))
    a.2 w

section Claim
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
variable {S₂ Cl Wt : Type} {C : _root_.Run.PQ.CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (c' : P₁ → Strs → Wt → Prop) (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))

/-- The shared items read no claim. -/
theorem muQ_claim : muQ N { Mg with claimM := c' } p l = muQ N Mg p l := by
  funext i k v w
  cases i <;> rfl

/-- **At border 2 the relation is one**: the claim is not open there. -/
theorem relQ₂_two_claim (b : (P₁ × S₂) × Fr.E.Str) (w : Wt)
    (h : relQ₂ N { Mg with claimM := c' } split p l 2 b w) : relQ₂ N Mg split p l 2 b w := by
  unfold relQ₂ at h ⊢
  rw [muQ_claim] at h
  refine ⟨h.1, fun i hi => ?_⟩
  have h1 := h.2 i hi
  cases i with
  | claimM => exact absurd hi (by decide)
  | _ => exact h1

/-- **At border 1 it goes over where the claim does.** -/
theorem relQ₂_one_claim (a : (P₁ × S₂) × Fr.E.Str) (w : Wt) (h : relQ₂ N Mg split p l 1 a w)
    (hc : c' a.1.1 (strsOf Fr a.2) w) : relQ₂ N { Mg with claimM := c' } split p l 1 a w := by
  unfold relQ₂ at h ⊢
  rw [muQ_claim]
  refine ⟨h.1, fun i hi => ?_⟩
  have h1 := h.2 i hi
  cases i with
  | claimM => exact hc
  | _ => exact h1

/-- **A law towards the step at the one meaning is a law towards the step at the other.** -/
theorem leadsB_claim {κ : Type} (K : Iop.Reduction ((P₁ × S₂) × Fr.E.Str) ((P₁ × S₂) × Fr.E.Str))
    (key : (P₁ × S₂) × Fr.E.Str → κ) (on : (P₁ × S₂) × Fr.E.Str → Prop)
    (E : (P₁ × S₂) × Fr.E.Str → Wt → Wt) (εK εO : Iop.Err K.shape)
    (h : K.LeadsB key on (stepPt N Mg Pm Oc split p l E) εK εO)
    (hc : ∀ a w, on a → relQ₂ N Mg split p l 1 a w → c' a.1.1 (strsOf Fr a.2) w) :
    K.LeadsB key on (stepPt N { Mg with claimM := c' } Pm Oc split p l E) εK εO := by
  obtain ⟨lK, lO, h1, h2, h3⟩ := h
  refine ⟨lK, lO, h1, h2, fun a τ b ha hk ho hb => ?_⟩
  obtain ⟨g1, g2⟩ := h3 a τ b ha hk ho hb
  refine ⟨g1, fun w hw => ?_⟩
  have g3 := g2 w (relQ₂_two_claim N Mg c' split p l b w hw)
  exact relQ₂_one_claim N Mg c' split p l a _ g3 (hc a _ ha g3)

/-- The same in the form at one list of errors. -/
theorem leadsBN_claim {κ : Type} (K : Iop.Reduction ((P₁ × S₂) × Fr.E.Str) ((P₁ × S₂) × Fr.E.Str))
    (key : (P₁ × S₂) × Fr.E.Str → κ) (on : (P₁ × S₂) × Fr.E.Str → Prop)
    (E : (P₁ × S₂) × Fr.E.Str → Wt → Wt) (n : ℕ) (ε : Iop.Err K.shape)
    (h : K.LeadsBN key on (stepPt N Mg Pm Oc split p l E) n ε)
    (hc : ∀ a w, on a → relQ₂ N Mg split p l 1 a w → c' a.1.1 (strsOf Fr a.2) w) :
    K.LeadsBN key on (stepPt N { Mg with claimM := c' } Pm Oc split p l E) n ε := by
  obtain ⟨εK, εO, hle, h1⟩ := h
  exact ⟨εK, εO, hle, leadsB_claim N Mg c' Pm Oc split p l K key on E εK εO h1 hc⟩

end Claim

/-- **The debt at "LIN point", at the seated piece, at a first table's meaning with its own sentence on the pending rows.** -/
theorem point_leadsB_reader (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (rg : Wit Cells Tok MsgT → Words GE) (omW : Wit Cells Tok MsgT → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (e' : Nat)
    (base : Nat) (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (err : Err (uLT (ckP .two) [d]))
    (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (split : Bool)
    (f : Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))
    (r : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT)))
    (gOf : P₁ → Nat → GE) (lo : Nat)
    (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (Pw : Where) (hlin : Pw.lin = P.par.S) (matC : Cells → Nat → Nat → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St)
    (stOf₂ : St → OnBytes.Statement) (bookOf₂ : St → OnBytes.TreeBook)
    (ha : P.par.S.fold.index.code.logN ≤ 32) (hix : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hk : 0 < (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l - 1)
    (hr : (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l ≤
      2 ^ (codeOf P.par.S.fold.index.code).a)
    (he : 0 < e') (hle : e' ≤ eM)
    (hM : eM < 2 ^ (codeOf P.par.S.fold.index.code).a -
      ((codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l) + 1)
    (hJ : InJohnson (2 ^ (codeOf P.par.S.fold.index.code).a)
      (2 ^ (codeOf P.par.S.fold.index.code).a -
        ((codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l) + 1) e')
    -- the first table's meaning: FOUR fields are what the joint says; two tests on the table; the letters that the promise reads read below lo
    (hpin : Mg₁.pin = fun j t a y w => pinJT cs G arr smp₁ ms₁ j t a y w)
    (hwrow : Mg₁.wrow = fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w)))
    (hevalLaid : ∀ a, Mg₁.pub .evalLaid a = evalLaidB Pw a.2)
    (hwSits : ∀ a, Mg₁.pub wSitsItem a = (wSitsB cs Pw a.2 && wSeatB N₁.w a.2))
    (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hlo : lo ≤ base) (hw : N₁.w.1 < base) (hi : N₁.index.1 < base)
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N₁.w.1 N₁.w.2)
    -- the filling's letters, each by its make; one equation on the plan
    (hst : ∀ a, stOf₁ a = a.2.st)
    (R : P₁ → Prop)
    (hbook : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed = none → (get p).2.st.codes = cs →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh → tabP₁ (get p) w n = w.tab cs sh (arr j t) j t)
    (htab : ∀ a (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) →
      (∀ j t, w'.pad j t = w.pad j t) → tabP₁ a w' = tabP₁ a w)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hg : ∀ p y' D, ocEnd get N₁ Mg₁ links ps p y' →
      (get p).2.failed = none → laidOf Pw (get p).2 = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hH : HeldTie P.par err₂ eM rank held matC)
    -- THE FIFTH, ONE DIRECTION, FENCED: what the step back from (Eval) proves gives the first table's own sentence on the pending rows
    (hpile : ∀ p y (w : Wit Cells Tok MsgT), ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed = none →
      pileStep stOf₁ tabP₁ Pw matC (get p) w → Mg₁.pileOne (get p) y w) :
    (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ (tiedNumbers N₁ Ns) f (seatedPiece b1 base d ext err :: r) 1).2
      (onQ₂ (tiedNumbers N₁ Ns) (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f
        (seatedPiece b1 base d ext err :: r) 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get Mg₁
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par e' gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f
        (seatedPiece b1 base d ext err :: r) fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ (tiedNumbers N₁ Ns) split 1
          ((actQ (tiedNumbers N₁ Ns) f (seatedPiece b1 base d ext err :: r) 1).2 a).1
          (strsOfAct F ((actQ (tiedNumbers N₁ Ns) f (seatedPiece b1 base d ext err :: r) 1).2 a)) w)
      ((vecMaps d P.par.S.kCol).err ((efIx P.par err₂ eM rank e' * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) := by
  have h := point_leadsB_reached (Cl' := Cl') (F := F) cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ stOf₁ tabP₁ rg omW P
    b1 b2 b3 b4 b5 b6 b7 b8 hbl e' base d hd ext err N₁ Ns links ps split f r gOf lo err₂ eM rank held Pw hlin matC
    { Mg₁ with pileOne := fun a _ w => pileStep stOf₁ tabP₁ Pw matC a w } Mg₀ Pm₀ stOf₂ bookOf₂
    ha hix hroom hk hr he hle hM hJ ⟨hpin, rfl, hwrow, hevalLaid, hwSits⟩ h2 h3 hread hlo hw hi hxW hsW hst R hbook htab
    hsh hg hH
  exact leadsB_claim (tiedNumbers N₁ Ns) _ (fun q => Mg₁.pileOne (get q)) _ _ split f _ _ _ _ _ _ _ h
    (fun a w ha hr => hpile a.1.1 _ w ha.2.1 ha.2.2 (hr.2 .unmarked1 (by decide)) (hr.2 .claimM (by decide)))

/-- **The same at the cap, of the piece that the seat's own list holds at place 1.** -/
theorem point_leadsBN_cap_reader (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (rg : Wit Cells Tok MsgT → Words GE) (omW : Wit Cells Tok MsgT → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (split : Bool)
    (lo : Nat) (f : Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))
    (l : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT)))
    -- THE SEAT: the pieces hold the shared chain's own blocks, as the description lays them: retyped, the test below the prime in front, lifted
    (c : Model.Verify.Chains) (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (hps : (f :: l).map (·.b) = (((chainOf c P tests last).retype (Cl' := Cl')).blocksInOrder.map below).map
      (Block.lift Prod.snd fun t s => (t.1, s)))
    -- the data of the piece at place 1: one written round, none behind; its base
    (hdat : ∀ q, (f :: l)[1]? = some q → q.ds = [d] ∧ q.back = [] ∧ lo ≤ q.base ∧ N₁.w.1 < q.base ∧ N₁.index.1 < q.base)
    (gOf : P₁ → Nat → GE)
    (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (Pw : Where) (hlin : Pw.lin = P.par.S) (matC : Cells → Nat → Nat → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St)
    (stOf₂ : St → OnBytes.Statement) (bookOf₂ : St → OnBytes.TreeBook)
    (ha : P.par.S.fold.index.code.logN ≤ 32) (hix : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hk : 0 < (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l - 1)
    (hr : (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l ≤
      2 ^ (codeOf P.par.S.fold.index.code).a)
    (hle : 2852142980 ≤ eM)
    (hM : eM < 2 ^ (codeOf P.par.S.fold.index.code).a -
      ((codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l) + 1)
    (hJ : InJohnson (2 ^ (codeOf P.par.S.fold.index.code).a)
      (2 ^ (codeOf P.par.S.fold.index.code).a -
        ((codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l) + 1) 2852142980)
    -- the first table's meaning: four fields are what the joint says; two tests on the table; the letters that the promise reads read below lo
    (hpin : Mg₁.pin = fun j t a y w => pinJT cs G arr smp₁ ms₁ j t a y w)
    (hwrow : Mg₁.wrow = fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w)))
    (hevalLaid : ∀ a, Mg₁.pub .evalLaid a = evalLaidB Pw a.2)
    (hwSits : ∀ a, Mg₁.pub wSitsItem a = (wSitsB cs Pw a.2 && wSeatB N₁.w a.2))
    (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N₁.w.1 N₁.w.2)
    -- the filling's letters, each by its make; one equation on the plan
    (hst : ∀ a, stOf₁ a = a.2.st)
    (R : P₁ → Prop)
    (hbook : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed = none → (get p).2.st.codes = cs →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh → tabP₁ (get p) w n = w.tab cs sh (arr j t) j t)
    (htab : ∀ a (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) →
      (∀ j t, w'.pad j t = w.pad j t) → tabP₁ a w' = tabP₁ a w)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hg : ∀ p y' D, ocEnd get N₁ Mg₁ links ps p y' →
      (get p).2.failed = none → laidOf Pw (get p).2 = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hH : HeldTie P.par err₂ eM rank held matC)
    (hpile : ∀ p y (w : Wit Cells Tok MsgT), ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed = none →
      pileStep stOf₁ tabP₁ Pw matC (get p) w → Mg₁.pileOne (get p) y w)
    -- THE ARITHMETIC ON THE TWO LISTS (PointCap, K14PointCap.lean), at the release's numbers
    (Wr : Rounds) (hPC : PointCap P.par.S Wr) (hdW : atW Wr 0 = some (d.entry, d.kind)) (n : ℕ) (hn : n ≤ 64) :
    ∃ (base : Nat) (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (err : Err (uLT (ckP .two) [d])) (r : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))),
      l = seatedPiece b1 base d ext err :: r ∧
      (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsBN
      (actQ (tiedNumbers N₁ Ns) f l 1).2
      (onQ₂ (tiedNumbers N₁ Ns) (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f
        l 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get Mg₁
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par 2852142980 gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f
        l fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ (tiedNumbers N₁ Ns) split 1
          ((actQ (tiedNumbers N₁ Ns) f l 1).2 a).1
          (strsOfAct F ((actQ (tiedNumbers N₁ Ns) f l 1).2 a)) w)
      n (Err.cap 128 (uLT (ckP .two) [d])) := by
  obtain ⟨base, ext, err, r, hl, h⟩ := point_leadsBN_cap_reached (Cl' := Cl') (F := F) cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ stOf₁ tabP₁ rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl d hd N₁ Ns links ps split lo f l c tests last hps hdat gOf err₂ eM rank held Pw hlin matC { Mg₁ with pileOne := fun a _ w => pileStep stOf₁ tabP₁ Pw matC a w } Mg₀ Pm₀ stOf₂ bookOf₂ ha hix hroom hk hr hle hM hJ ⟨hpin, rfl, hwrow, hevalLaid, hwSits⟩ h2 h3 hread hxW hsW hst R hbook htab hsh hg hH Wr hPC hdW n hn
  refine ⟨base, ext, err, r, hl, ?_⟩
  exact leadsBN_claim (tiedNumbers N₁ Ns) _ (fun q => Mg₁.pileOne (get q)) _ _ split f _ _ _ _ _ _ _ h
    (fun a w ha hr => hpile a.1.1 _ w ha.2.1 ha.2.2 (hr.2 .unmarked1 (by decide)) (hr.2 .claimM (by decide)))

/-- **hpile FROM AN "IFF" UNDER A TEST**: where the first table's sentence and the step back's are one wherever a test T on the verifier's state accepts, and T accepts at what R holds of. -/
theorem hpile_of_iff (get : P₁ → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (Pw : Where) (matC : Cells → Nat → Nat → GE) (R : P₁ → Prop) (T : First.S → Bool)
    (hiff : ∀ a y (w : Wit Cells Tok MsgT), T a.2 = true →
      (Mg₁.pileOne a y w ↔ pileStep stOf₁ tabP₁ Pw matC a w))
    (hT : ∀ p, R p → T (get p).2 = true) :
    ∀ p y (w : Wit Cells Tok MsgT), ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed = none →
      pileStep stOf₁ tabP₁ Pw matC (get p) w → Mg₁.pileOne (get p) y w :=
  fun p y w _ hR _ h => (hiff (get p) y w (hT p hR)).2 h

end Desc.K14.Law

#print axioms Desc.K14.Law.point_leadsBN_cap_reader
#print axioms Desc.K14.Law.hpile_of_iff
#print axioms Desc.K14.Law.leadsB_claim
#print axioms Desc.K14.Law.point_leadsB_reader
