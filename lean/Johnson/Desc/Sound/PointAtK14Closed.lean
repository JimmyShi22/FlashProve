-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtK14Closed.lean: THE TIE AT "LIN point": point_leadsB_typed (Johnson/Desc/Sound/PointAtK14Typed.lean) WITH THE DECODER AND THE FOUR ITEMS BEHIND THE POINT FILLED BY TERMS: SO THAT OF THE PREMISES WITH WEIGHT TWO ARE LEFT. Three definitions, small lemmas, one theorem.
(noted IS A TERM: notedU s := the number that the record notes for o_u is a message of the statement; "not yet noted" IS A CLAUSE OF THE BOOK-KEEPING AT BORDERS 1 AND 2; SO (hnot) IS EXCHANGED, NOT PAID: it follows here (linPoint_oU, notedU_point, lifted_point) FROM THE NEW CLAUSE "not yet noted" IN THE PROMISE AT BORDER 1, AND THAT CLAUSE IS OWED BY WHOEVER PAYS THE PROMISE AT BORDER 1: the front block's
row, and at the chain's start: the first record notes no message for o_u: not shown). (Why uAt: nearU, recRow, omU filled at withNext of the record at every border are right behind this block alone: behind o_u's sending withNext names the next message, the wrong one: the table's later rows could then be met
by nobody). A joint build of files of Johnson/Desc/Sound/ and of Johnson/Desc/K14/.

THE FILLING, BESIDE PointAtK14Fill.lean's: decK: THE GUARDED DECODER AT THE LIBRARY's TYPED DATA: decAtRec (decGuard collAt dcdAt held) recAt (Johnson/Desc/K14/Law/CellsTie.lean: the library's collision and decoder with the record at ixOf2, handed the stored table's symbols; the reader of the
  record in the chain's own state; the shapes of Johnson/Desc/Sound/TablePromiseAt.lean); held: a letter (what is made of a decoded table: the cells) · uAt p noted s: THE READER OF THE RECORD for the three items that read u: the record itself where it notes o_u already (notedU: a public test on the record), else withNext · nearU s y w := NearAt at uAt s, the witness's words, the stored table's columns · recRow s w := RecAll at uAt s · omU s w := "Omega is, row by row of M, what
  u gives at the point's low part" at the reader omW of the witness's Omega · dot p s y w := DotEq at gOf p, omW w, the point, the witness's other vector.
PAID HERE: (hcoll) the promise on the table, at the guarded decoder, gives "no collision at the key's seeds" (noColl_of_promise; coll_iff) · (hdk) recAt reads the key alone · (hNear), (hRec): unfoldings, with tabOf_cells · (hDotU): dotU_of (Johnson/Desc/K14/Law/GoodQuiet.lean).
**WHAT STAYS WITH WEIGHT: hbad: THE STATEMENT ON CODES, in the library's own words · s4a: no mark, (Eval), VIs and the index masks' pin give the claim on M at the witness with the decoded cells laid (K13's step back from (Eval); "held").** BESIDE: hbl · hd · three public facts on the shape ·
nine equations of letters (rfl where the letters are so filled) · OcReadsBelow lo Oc · three comparisons of numbers · W's member sits at W's seat.

Limits. As PointAtK14.lean's. rg (the witness's words), omW, vec, gOf, held, get, the codes, arr, the members, the samples' readers, err₂, eM, rank, e', ef are letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtK14Typed
import Johnson.Desc.K14.Law.CellsTie
import Johnson.Desc.K14.Law.GoodQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ promQ actQ shIt ownItem stepPt strsOf strsOfAct OcReadsBelow
  pinJT SitsAt decodesOf pinWOf extS wTab MsgT Mem Sending decAtRec decGuard noColl_of_promise)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning ItemS PromS promsAt)

/-- **The guarded decoder at the library's typed data**, at the record in the chain's own state. -/
noncomputable def decK {Cells : Type} (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells) :
    (Nat → Option (Nat × List UInt64)) → St → Option Cells :=
  decAtRec (decGuard (collAt p err₂ eM rank) (dcdAt p err₂ eM rank) held) (recAt p err₂ eM rank)

/-- **THE READER OF THE RECORD FOR THE THREE ITEMS THAT READ u**: where the record notes o_u already (noted: a public test on the record), the record itself; in front of o_u's sending, the record with o_u noted as the message to come. -/
def uAt (p : Par) (noted : St → Bool) (s : St) : St := if noted s = true then s else withNext p s

/-- It leaves the point that was noted. -/
theorem uAt_psi (p : Par) (noted : St → Bool) (s : St) : (uAt p noted s).loc.psiSh = s.loc.psiSh := by
  unfold uAt
  split <;> rfl

/-- **"THE RECORD NOTES o_u ALREADY"**: the number that it notes for o_u is a message of the statement. -/
def notedU (s : St) : Bool := decide (s.loc.oU.oracle < s.st.oracles.size)

/-- "LIN point" leaves what the record notes for o_u. -/
theorem linPoint_oU (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') :
    d'.loc.oU = d.loc.oU := by
  unfold linPoint at h
  split at h
  · rename_i r
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    obtain ⟨l1, o1, c1⟩ := newGroupP_same d d1 _ _ gU h1
    split at h2
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      obtain ⟨l2, o2, c2⟩ := newGroupP_same d1 d2 _ _ gO h3
      show d2.loc.oU = _
      rw [l2, l1]
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      simp only [Prod.mk.injEq] at h3
      obtain ⟨_, rfl⟩ := h3
      show d1.loc.oU = _
      rw [l1]
  · cases h

/-- So it leaves the test. -/
theorem notedU_point (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') :
    notedU d' = notedU d := by
  obtain ⟨_, _, _, _, ho, _⟩ := linPoint_inv p d d' rs h
  unfold notedU
  rw [linPoint_oU p d d' rs h, ho]

variable {P₁ A₁ Xi Cells Tok : Type} {F : Frame}

/-- A yes of the lifted first block is a yes of "LIN point" at the chain's own record. -/
theorem lifted_point {W : Type} (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (base : Nat) (d : RDT)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W) (err : Err (uLT (ckP .two) [d]))
    (a : (P₁ × St) × F.E.Str) (τ : Tr (uLT (ckP .two) (liftedPiece (W := W) (F := F) b1 base d ext err).ds))
    (b : (P₁ × St) × F.E.Str)
    (hb : (liftedPiece (W := W) (F := F) b1 base d ext err).ior.red.out a τ = some b) :
    ∃ rs, linPoint P.par a.1.2 rs = some b.1.2 := by
  obtain ⟨-, gs, hdc0⟩ := piece_yes (liftedPiece (W := W) (F := F) b1 base d ext err) a τ b hb
  obtain ⟨hdc, -⟩ := lift_ok b1 a.1 b.1 _ gs hdc0
  exact ⟨_, point_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ hdc⟩

/-- **The debt at "LIN point", at the description's piece: two premises with weight.** -/
theorem point_leadsB_closed (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → A₁)
    (smp₁ : A₁ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells) (vec : MsgT → Nat → GE)
    (rg : Wit Cells Tok MsgT → Words GE) (omW : Wit Cells Tok MsgT → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (e' : Nat)
    (base : Nat) (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (err : Err (uLT (ckP .two) [d]))
    (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
    (Oc : P₁ → Strs → Prop) (split : Bool)
    (f : Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT))
    (r : List (Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT)))
    (gOf : P₁ → Nat → GE) (lo ef : Nat)
    (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (ha : P.par.S.fold.index.code.logN ≤ 32) (hix : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    -- THE STATEMENT ON CODES
    (hbad : ∀ t rec, ¬ (ixOf2 P.par.S.fold err₂ eM rank).Coll t rec.1 →
      cnt ((ixOf2 P.par.S.fold err₂ eM rank).Bad t rec e') ≤ ef)
    -- the filling
    (hpin₁ : Mg.pin₁ = fun j t q y w => pinJT cs G arr smp₁ ms₁ j t (get q) y w)
    (hpT : Mg.pinT = pinWOf (decK P.par err₂ eM rank held))
    (hTP : Pm.tablePromise = decodesOf (decK P.par err₂ eM rank held))
    (hS1 : Pm.shape 1 = fun s => shape1 P.par s && !notedU s)
    (hS2 : Pm.shape 2 = fun s => shape2 P.par s && !notedU s)
    (hnU : Mg.nearU = fun s y w =>
      NearAt OnBytes.Model.Reading.gl P.par (uAt P.par notedU s) (rg w) (colsOf y.cell) e')
    (hrR : Mg.recRow = fun s w => RecAll OnBytes.Model.Reading.gl P.par (uAt P.par notedU s) (rg w))
    (hoU : Mg.omU = fun s w => ∀ y < P.par.S.matrixRows, omW w y =
      ∑ t ∈ Finset.range (2 ^ P.par.S.kLo),
        eqK ((s.loc.psiSh.take P.par.S.kLo).map OnBytes.Model.Reading.gl.val) t *
          uOf (uAt P.par notedU s).loc (rg w) (t + 2 ^ P.par.S.kLo * y))
    (hdt : Mg.dot = fun p s _ w => DotEq P.par.S.matrixRows P.par.S.kCol (gOf p) (omW w)
      (s.loc.psiSh.map OnBytes.Model.Reading.gl.val) (vec (wTab cs arr xW w)))
    (hOc : OcReadsBelow lo Oc) (hlo : lo ≤ base) (hw : N.w.1 < base) (hi : N.index.1 < base)
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N.w.1 N.w.2)
    -- THE STEP BACK FROM (Eval)
    (s4a : ∀ a τ b w, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg .unmarked1 b w → ownItem N Mg .ev b w →
      VIs P.par.S (gOf a.1.1) (TabX2 P.par err₂ eM rank (tabOf a.2) a.1.2.loc.key)
        (vec (wTab cs arr xW w)) → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ N split 1
        ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w)) :
    (belowPiece (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ N f (belowPiece b1 base d ext err :: r) 1).2
      (onQ₂ N Pm Oc split f (belowPiece b1 base d ext err :: r) 1)
      (stepPt N Mg Pm Oc split f (belowPiece b1 base d ext err :: r) fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ N split 1
          ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w)
      ((vecMaps d P.par.S.kCol).err ((ef * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) := by
  have hsame : ∀ (a : (P₁ × St) × F.E.Str) τ b,
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → notedU b.1.2 = notedU a.1.2 := by
    intro a τ b hb
    obtain ⟨rs, hl⟩ := lifted_point P b1 b2 b3 b4 b5 b6 b7 b8 hbl base d ext err a τ b hb
    exact notedU_point P.par _ _ rs hl
  have hnot : ∀ a τ b, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → notedU b.1.2 = false := by
    intro a τ b hon hb
    have h1 : Pm.shape 1 a.1.2 = true :=
      hon.1 (.shape 1) (by rw [promsAt_one]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [hS1] at h1
    have h1' : (shape1 P.par a.1.2 && !notedU a.1.2) = true := h1
    have h2 := (Bool.and_eq_true_iff.1 h1').2
    rw [hsame a τ b hb]
    cases hn : notedU a.1.2
    · rfl
    · rw [hn] at h2
      cases h2
  refine point_leadsB_typed cs G arr get smp₁ ms₁ xW smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ vec rg P b1 b2
    b3 b4 b5 b6 b7 b8 hbl e' base d hd ext err N Mg Pm Oc split f r gOf (uAt P.par notedU) lo ef (fun s => !notedU s) (fun s => !notedU s) err₂ eM rank
    ha hix hroom hbad ?hcoll hpin₁ hpT hTP hS1 hS2 ?hx ?hdk hOc hlo hw hi hxW hsW ?hu ?hNear ?hRec ?hDotU s4a
  case hcoll =>
    intro a hon hc
    have h1 : Pm.tablePromise a.1.2 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) :=
      hon.1 .tablePromise (by rw [promsAt_one]; exact List.mem_cons_self)
    rw [hTP] at h1
    exact (noColl_of_promise (collAt P.par err₂ eM rank) (dcdAt P.par err₂ eM rank) held
      (recAt P.par err₂ eM rank) a.1.2 _ h1).1 ((coll_iff P.par err₂ eM rank (a.1.2, a.2)).1 hc)
  case hx =>
    intro a τ b _ hb h
    show (!notedU b.1.2) = true
    rw [hsame a τ b hb]
    exact h
  case hdk =>
    intro c s s' hk
    have e : recAt P.par err₂ eM rank s' = recAt P.par err₂ eM rank s := by
      unfold recAt
      rw [hk]
    show decGuard _ _ held c (recAt P.par err₂ eM rank s') = decGuard _ _ held c (recAt P.par err₂ eM rank s)
    rw [e]
  case hu =>
    intro a τ b hon hb
    unfold uAt
    rw [hnot a τ b hon hb]
    rfl
  case hNear =>
    intro b w h
    have h' : Mg.nearU b.1.2 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 2).2 b)) w := h
    rw [hnU] at h'
    rw [tabOf_cells]
    exact h'
  case hRec =>
    intro b w h
    have h' : Mg.recRow b.1.2 w := h
    rw [hrR] at h'
    exact h'
  case hDotU =>
    intro b w hdot hom
    have hd' : Mg.dot b.1.1 b.1.2 (strsOf F b.2) w := hdot
    rw [hdt] at hd'
    have ho' : Mg.omU b.1.2 w := hom
    rw [hoU] at ho'
    unfold DotUAt
    rw [uAt_psi]
    exact dotU_of P.par.S.matrixRows P.par.S.kCol P.par.S.kLo (gOf b.1.1) (omW w)
      (uOf (uAt P.par notedU b.1.2).loc (rg w)) _ _ _ ho' hd'

end Desc.K14.Law

#print axioms Desc.K14.Law.point_leadsB_closed
