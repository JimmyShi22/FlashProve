-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtK14Typed.lean: THE TIE AT "LIN point": point_leadsB_filled (Johnson/Desc/Sound/PointAtK14Fill.lean) WITH THE KEY's SORT OF LOST POINTS, THE MATRIX AND "THE TABLE DECODES" FILLED BY K14's FILES' TERMS AT THE LIBRARY's OWN TYPED DATA (BadX2, TabX2, DecX2 at
ixOf2: Johnson/Desc/K14/Law/PointKey2.lean), AND CARRIED TO THE PIECE THAT A DESCRIPTION HOLDS (PointBelow.lean). One definition, one theorem. (x1, x2 and (hx) are handed through.) A joint build of files of Johnson/Desc/Sound/ and of Johnson/Desc/K14/.

PAID HERE, OF THE NINE THAT STOOD: (hgood) by good_of_notBad2 (PointKey2.lean) · (hBK) BY MAKE: the key's sort is typed on the acting part's value (tabV: the stored table's columns off that value) and is BadX2 there: rfl · (hkey) from TWO PREMISES IN THE LIBRARY's OWN WORDS:
  **hbad: THE STATEMENT ON CODES**: at every table f and record rec without a collision at the record's seed, no more than ef points are bad: (ixOf2 …).Bad f rec e': NO BLOCK, NO RECORD OF THE PROTOCOL STANDS IN IT · **hcoll**: inside the table's promise the stored table has no collision at the key's seeds.
WHAT STAYS, BY NAME: hbl · hd · three public facts on the shape (logN ≤ 32 · index.ok · the rows' room) · **hbad** · **hcoll** · hNear · hRec · hDotU · **s4a** · and of the filling what PointAtK14Fill.lean names.
THE CONCLUSION: (belowPiece b1 base d ext err).ior.red.LeadsB (the acting part at border 1) (onQ₂ 1) (stepPt E) δK δO, in the list of pieces that holds belowPiece.

Limits. As PointAtK14.lean's. err₂, eM, rank (the typed data's letters), e', ef are free numbers and letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointBelow
import Johnson.Desc.K14.Law.PointKey2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ promQ actQ shIt ownItem stepPt strsOf strsOfAct OcReadsBelow
  pinJT SitsAt decodesOf pinWOf extS wTab MsgT Mem Sending)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning ItemS PromS promsAt)

/-- The stored table's column at a position, off the acting part's value. -/
def tabV {F : Frame} (t : (oneExternalString (2 ^ F.a) _root_.Run.PQ.SgX).Str) (x : Nat) : List UInt64 :=
  if h : x < 2 ^ F.a then (t ⟨x, h⟩).2 else []

variable {P₁ A₁ Xi Cells Tok : Type} {F : Frame}

/-- **The debt at "LIN point", at the description's piece, at the library's typed data.** -/
theorem point_leadsB_typed (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → A₁)
    (smp₁ : A₁ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (decT₂ : (Nat → Option (Nat × List UInt64)) → St → Option Cells) (c₀ : Cells)
    (vec : MsgT → Nat → GE)
    (rg : Wit Cells Tok MsgT → Words GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (e' : Nat)
    (base : Nat) (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (err : Err (uLT (ckP .two) [d]))
    (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
    (Oc : P₁ → Strs → Prop) (split : Bool)
    (f : Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT))
    (r : List (Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT)))
    (gOf : P₁ → Nat → GE) (uRec : St → St) (lo ef : Nat) (x1 x2 : St → Bool)
    -- the typed data
    (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (ha : P.par.S.fold.index.code.logN ≤ 32) (hix : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hbad : ∀ t rec, ¬ (ixOf2 P.par.S.fold err₂ eM rank).Coll t rec.1 →
      cnt ((ixOf2 P.par.S.fold err₂ eM rank).Bad t rec e') ≤ ef)
    (hcoll : ∀ a : (P₁ × St) × F.E.Str, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      ¬ (ixOf2 P.par.S.fold err₂ eM rank).Coll
        (tabF OnBytes.Model.Reading.gl P.par.S.fold.index (tabOf a.2))
        (seedsFn OnBytes.Model.Reading.gl P.par.S.fold.index a.1.2.loc.key))
    -- the filling
    (hpin₁ : Mg.pin₁ = fun j t q y w => pinJT cs G arr smp₁ ms₁ j t (get q) y w)
    (hpT : Mg.pinT = pinWOf decT₂) (hTP : Pm.tablePromise = decodesOf decT₂)
    (hS1 : Pm.shape 1 = fun s => shape1 P.par s && x1 s)
    (hS2 : Pm.shape 2 = fun s => shape2 P.par s && x2 s)
    (hx : ∀ a τ b, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → x1 a.1.2 = true → x2 b.1.2 = true)
    (hdk : ∀ c (s s' : St), s'.loc.key = s.loc.key → decT₂ c s' = decT₂ c s)
    (hOc : OcReadsBelow lo Oc) (hlo : lo ≤ base) (hw : N.w.1 < base) (hi : N.index.1 < base)
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N.w.1 N.w.2)
    -- the bridges, and the step back from (Eval)
    (hu : ∀ a τ b, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → uRec b.1.2 = withNext P.par b.1.2)
    (hNear : ∀ b w, shIt N Mg f (liftedPiece b1 base d ext err :: r) .nearU 2 b w →
      NearAt OnBytes.Model.Reading.gl P.par (uRec b.1.2) (rg w) (tabOf b.2) e')
    (hRec : ∀ b w, shIt N Mg f (liftedPiece b1 base d ext err :: r) .recRow 2 b w →
      RecAll OnBytes.Model.Reading.gl P.par (uRec b.1.2) (rg w))
    (hDotU : ∀ b w, ownItem N Mg .dot b w → shIt N Mg f (liftedPiece b1 base d ext err :: r) .omU 2 b w →
      DotUAt P.par.S (gOf b.1.1) (uRec b.1.2).loc (rg w) (vec (wTab cs arr xW w)))
    (s4a : ∀ a τ b w, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg .unmarked1 b w → ownItem N Mg .ev b w →
      VIs P.par.S (gOf a.1.1) (TabX2 P.par err₂ eM rank (tabOf a.2) a.1.2.loc.key)
        (vec (wTab cs arr xW w)) → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (extS cs G arr smp₂ ms₂ decT₂ c₀ N split 1
        ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w)) :
    (belowPiece (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ N f (belowPiece b1 base d ext err :: r) 1).2
      (onQ₂ N Pm Oc split f (belowPiece b1 base d ext err :: r) 1)
      (stepPt N Mg Pm Oc split f (belowPiece b1 base d ext err :: r) fun a w =>
        extS cs G arr smp₂ ms₂ decT₂ c₀ N split 1
          ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w)
      ((vecMaps d P.par.S.kCol).err ((ef * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) := by
  have hfit : ∀ a : (P₁ × St) × F.E.Str, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      a.1.2.loc.key.fits P.par.S.fold.index = true := by
    intro a hon
    have h1 : Pm.shape 1 a.1.2 = true :=
      hon.1 (.shape 1) (by rw [promsAt_one]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [hS1] at h1
    have h1' : (shape1 P.par a.1.2 && x1 a.1.2) = true := h1
    exact (Bool.and_eq_true_iff.1 h1').1
  refine leadsB_at_desc_piece b1 base d ext err N Mg Pm Oc split f r _ _ _ ?_
  refine point_leadsB_filled cs G arr get smp₁ ms₁ xW smp₂ ms₂ decT₂ c₀ vec rg P b1 b2 b3 b4 b5 b6 b7 b8 hbl e'
    base d hd ext err N Mg Pm Oc split f r gOf uRec
    (fun x => BadX2 P.par err₂ eM rank e' (tabOf x.2) x.1.loc.key)
    (fun v => BadX2 P.par err₂ eM rank e' (tabV (F := F) v.2.1) v.1.loc.key)
    (fun x => TabX2 P.par err₂ eM rank (tabOf x.2) x.1.loc.key)
    (fun x => DecX2 P.par err₂ eM rank (tabOf x.2) x.1.loc.key) lo ef x1 x2 hpin₁ hpT hTP hS1 hS2 hx hdk hOc hlo hw hi
    hxW hsW (fun _ _ h => h) ?_ hu hNear hRec hDotU s4a ?_
  · intro a hon x m gam hnb hg hk _ hnear hrec
    have h := good_of_notBad2 P.par ha err₂ eM rank e' (tabOf a.2) x m gam hix hroom
      (by rw [hk]; exact hfit a hon) (by rw [hk]; exact hnb) hg hnear hrec
    rw [hk] at h
    exact h
  · intro a hon
    exact hbad _ _ (hcoll a hon)

end Desc.K14.Law

#print axioms Desc.K14.Law.point_leadsB_typed
