-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtK14.lean: THE TIE AT "LIN point": THE TABLE's RULE (pointH, Johnson/Desc/Sound/PointTypes.lean) WITH K14's FILES' LAW OF A YES LAID IN (point_yesL, Johnson/Desc/K14/Law/PointLift.lean: what a yes of the shared chain's own first block gives, at the block lifted to the pair
of what was handed and the chain's own record). One definition, three theorems. (The three items that read u are read at a READER uRec OF THE RECORD, which at the border behind this block is "the record with o_u noted as the message to come": (hu); so that one filling
serves all borders at which they are open). A JOINT BUILD OF THIS FOLDER's FILES WITH K14's FILES (Johnson/Desc/K14/Law/).

  psiAtK d k τ: the point that the written round reads as (the carriage vecMaps, Johnson/Desc/K14/Law/ZetaRead.lean); zero where it reads as none.
  point_h_at_k14: AT pt := liftedPiece b1 base d ext err, b1 THE FIRST OF blocks P: for every a τ b: the table's promise at border 1 · a yes · the point's high part is not bad for THE KEY (BadKV: a function of the acting part's value) · the point is not of THE SLOT's
    SORT (BadO at the row weights gOf READ OFF WHAT WAS HANDED, the matrix Tab off the chain's own record and the oracles IN FRONT, and the vector VOf a off the statement IN FRONT) ⟹ stepPt E a b: THE LAST PREMISE OF "a plain law for a batch in two parts, for one
    written round, from two counts", at the real block.
  point_leadsB_at_k14: **THE DEBT ITSELF AT THE REAL BLOCK: LeadsB (the acting part at border 1) (onQ₂ 1) (stepPt E) δK δO**, δK := the written count that bears ef · |K|^kLo · δO := the written count that bears kCol · |K|^(kCol − 1): THE TWO LISTS NAMED. The key's game: "the
    point is not of the key's sort WITH THE GUARD" (GuardK: the key has at most ef bad high parts, and this is one): LOST AT EVERY VALUE OF THE KEY's TYPE, whatever BadKV is (cnt_guardK); the slot's game: BadO: lost at every statement (cnt_badO). ONE PREMISE MORE: (hkey) inside
    the promise the key has at most ef bad high parts [the statement on codes]. doomed_of_cnt: a count of bad points gives the prover's loss at the written round (the carriage vecMaps; the library's CarryS.doomed, Maps.fits).
WHAT IS LAID IN: the two counts · the law of a yes (with chance's two sorts apart) · "what was handed stays" (by the lift).
WHAT STAYS A NAMED PREMISE: (hgood) not bad, near and the record's rows give "u is the fold" [good_of_notBad2, Johnson/Desc/K14/Law/PointKey2.lean] · (hBK) the letter BadKey reads the statement through the acting part · THREE BRIDGES from the table's letters to K14's files' terms: nearU ⟹ NearAt, recRow ⟹
RecAll, dot ∧ omU ⟹ DotUAt (all three at uRec of the record), with (hu): behind a yes of this block uRec is withNext [unfoldings at the filling; dotU_of, Johnson/Desc/K14/Law/GoodQuiet.lean] · (S0) · (hV) [vFixed at the filled pin] · (S4) [K13's step back from (Eval); the cells' pin by make; "held"] · (S5) [pointRiders].

(hBK), (hNear), (hRec), (hDotU) RUN OVER EVERY STATEMENT, WITHOUT A PROMISE: THEY ARE MEANT AS DEFINITIONAL AT THE FILLING: by unfolding or not at all (by reading). (hBK) is to be paid by MAKING BadKV of BadKey at the acting part's value (one term, two readings), never by a union over
statements: a union could make (hkey) false. So they are paid in PointAtK14Typed.lean and PointAtK14Closed.lean.

Limits. A rule with K14's files' law and counts laid in. The letters Mg, Pm, Oc, N, E, rg, wv, gOf, VOf, Tab, Dec, BadKey, BadKV are free.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K14.Law.PointLift
import Johnson.Desc.Sound.PointTypes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ actQ shIt ownItem stepPt pointH)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning ItemS)
open Iop.IOR (drawRound)

/-- The point that the written round reads as. -/
noncomputable def psiAtK (d : RDT) (k : Nat) (τ : Tr (uLT (ckP .two) [d])) : Fin k → GE :=
  match (vecMaps d k).carry.tr τ with
  | some τ' => τ'.2.1
  | none => fun _ => 0

variable {W P₁ : Type} {F : Frame}

/-- **The step at every yes of the real block, off the two sorts of lost points.** -/
theorem point_h_at_k14 (rg : W → Words GE) (wv : W → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (e' : Nat)
    (base : Nat) (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W)
    (err : Err (uLT (ckP .two) [d]))
    (N : NumbersS) (Mg : MeaningS St P₁ W) (Pm : PromMeaning St) (Oc : P₁ → Strs → Prop) (split : Bool)
    (f : Piece (ckP .two) F (P₁ × St) Unit W) (r : List (Piece (ckP .two) F (P₁ × St) Unit W))
    (E : (P₁ × St) × F.E.Str → W → W)
    (gOf : P₁ → Nat → GE) (VOf : (P₁ × St) × F.E.Str → Nat → GE) (uRec : St → St)
    (BadKey : St × F.E.Str → (Fin P.par.S.fold.index.v → GE) → Prop)
    (BadKV : (actQ N f (liftedPiece (W := W) (F := F) (P₁ := P₁) b1 base d ext err :: r) 1).1 →
      (Fin P.par.S.fold.index.v → GE) → Prop)
    (Tab : St × F.E.Str → Nat → Nat → GE) (Dec : St × F.E.Str → Prop)
    (hBK : ∀ (a : (P₁ × St) × F.E.Str) gam, BadKey (a.1.2, a.2) gam →
      BadKV ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a) gam)
    (hgood : ∀ a : (P₁ × St) × F.E.Str, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      ∀ (x : St) (m : Words GE) (gam : Fin P.par.S.fold.index.v → GE),
      ¬ BadKey (a.1.2, a.2) gam →
      (gamma P.par.S x.loc).map OnBytes.Model.Reading.gl.val = List.ofFn gam →
      x.loc.key = a.1.2.loc.key → x.st.codes = a.1.2.st.codes →
      NearAt OnBytes.Model.Reading.gl P.par x m (tabOf a.2) e' →
      RecAll OnBytes.Model.Reading.gl P.par x m →
      Dec (a.1.2, a.2) ∧ UIsFold P.par.S.matrixRows P.par.S.kLo P.par.S.fold.index.v
        (Tab (a.1.2, a.2)) (List.ofFn gam) (uOf x.loc m))
    (hu : ∀ a τ b, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → uRec b.1.2 = withNext P.par b.1.2)
    (hNear : ∀ b w, shIt N Mg f (liftedPiece b1 base d ext err :: r) .nearU 2 b w →
      NearAt OnBytes.Model.Reading.gl P.par (uRec b.1.2) (rg w) (tabOf b.2) e')
    (hRec : ∀ b w, shIt N Mg f (liftedPiece b1 base d ext err :: r) .recRow 2 b w →
      RecAll OnBytes.Model.Reading.gl P.par (uRec b.1.2) (rg w))
    (hDotU : ∀ b w, ownItem N Mg .dot b w →
      shIt N Mg f (liftedPiece b1 base d ext err :: r) .omU 2 b w →
      DotUAt P.par.S (gOf b.1.1) (uRec b.1.2).loc (rg w) (wv w))
    (s0 : ∀ a τ b, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b →
      onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 2 b)
    (hV : ∀ a τ b w, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg .pinV b w →
      wv w = VOf a)
    (s4 : ∀ a τ b w, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg .unmarked1 b w → ownItem N Mg .ev b w →
      VIs P.par.S (gOf a.1.1) (Tab (a.1.2, a.2)) (wv w) → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (E a w) ∧
        shIt N Mg f (liftedPiece b1 base d ext err :: r) .pinT 1 a (E a w))
    (s5 : ∀ a τ b w i, i ∈ [ItemS.unmarked1, .pinI, .pinV] →
      onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg i b w →
      ownItem N Mg i a (E a w)) :
    ∀ a τ b, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b →
      ¬ BadKV ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)
        (gamOf P.par.S.kLo P.par.S.fold.index.v (psiAtK d P.par.S.kCol τ)) →
      ¬ BadO P.par.S (gOf a.1.1) (Tab (a.1.2, a.2)) (VOf a) (psiAtK d P.par.S.kCol τ) →
      stepPt N Mg Pm Oc split f (liftedPiece b1 base d ext err :: r) E a b := by
  refine pointH P₁ St Unit W (Nat → GE) (Fin P.par.S.kCol → GE) (ckP .two) F N Mg Pm Oc split f
    (liftedPiece b1 base d ext err) r E
    (fun k psi => BadKV k (gamOf P.par.S.kLo P.par.S.fold.index.v psi))
    (fun a V => VIs P.par.S (gOf a.1.1) (Tab (a.1.2, a.2)) V)
    (fun a V psi => DotTrue P.par.S (gOf a.1.1) (Tab (a.1.2, a.2)) V psi) VOf wv
    (fun b w => DotUAt P.par.S (gOf b.1.1) (uRec b.1.2).loc (rg w) (wv w))
    (psiAtK d P.par.S.kCol) s0 ?_ hDotU hV s4 s5
  intro a τ b w ha hb hk hn hr hdu
  obtain ⟨τ', htr, hh, -, -, -, -, -, hw⟩ := point_yesL rg wv P b1 b2 b3 b4 b5 b6 b7 b8 hbl (gOf a.1.1) e'
    base d hd ext err BadKey Tab Dec a (hgood a ha) τ b hb
  have hp : psiAtK d P.par.S.kCol τ = τ'.2.1 := by
    unfold psiAtK
    rw [htr]
  have eu := hu a τ b ha hb
  have hn' := hNear b w hn
  have hr' := hRec b w hr
  rw [eu] at hn' hr' hdu
  rw [hh] at hdu
  show DotTrue P.par.S (gOf a.1.1) (Tab (a.1.2, a.2)) (wv w) (psiAtK d P.par.S.kCol τ)
  rw [hp]
  refine (hw w (fun hbad => hk ?_) hn' hr' hdu).2
  show BadKV _ (gamOf P.par.S.kLo P.par.S.fold.index.v (psiAtK d P.par.S.kCol τ))
  rw [hp]
  exact hBK a _ hbad

/-- The prover's loss at one written round that reads as a point, from a count of bad points: by the carriage vecMaps (Johnson/Desc/K14/Law/ZetaRead.lean). -/
theorem doomed_of_cnt (d : RDT) {ns n a0 : Nat} (hd : SendsDraws (toRD d) ns n 0 a0)
    (Bad : (Fin n → GE) → Prop) (e : Nat) (hc : cnt Bad ≤ e) :
    Doomed (uLT (ckP .two) [d]) ((vecMaps d n).err ((e, ()) : Nat × Unit))
      (fun τ => ∀ τ', (vecMaps d n).carry.tr τ = some τ' → ¬ Bad τ'.2.1) := by
  refine CarryS.doomed (vecMaps d n).carry ((e, ()) : Nat × Unit) _
    ((vecMaps d n).fits (vecMaps_ok hd) _) _ (fun τ' => ¬ Bad τ'.2.1) ?_ ?_ ?_
  · intro τ hτ τ' h
    rw [hτ] at h
    cases h
  · intro τ τ' hτ hb τ'' h
    rw [hτ] at h
    obtain rfl := Option.some.inj h
    exact hb
  · intro m
    refine le_trans (cnt_mono fun z hz => ?_) hc
    by_contra hn
    exact hz hn

/-- **THE DEBT AT "LIN point", IN THE PLAIN FORM FOR A BATCH IN TWO PARTS, AT THE REAL BLOCK, WITH THE TWO LISTS OF ERRORS NAMED.** -/
theorem point_leadsB_at_k14 (rg : W → Words GE) (wv : W → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (e' : Nat)
    (base : Nat) (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W)
    (err : Err (uLT (ckP .two) [d]))
    (N : NumbersS) (Mg : MeaningS St P₁ W) (Pm : PromMeaning St) (Oc : P₁ → Strs → Prop) (split : Bool)
    (f : Piece (ckP .two) F (P₁ × St) Unit W) (r : List (Piece (ckP .two) F (P₁ × St) Unit W))
    (E : (P₁ × St) × F.E.Str → W → W)
    (gOf : P₁ → Nat → GE) (VOf : (P₁ × St) × F.E.Str → Nat → GE) (uRec : St → St)
    (BadKey : St × F.E.Str → (Fin P.par.S.fold.index.v → GE) → Prop)
    (BadKV : (actQ N f (liftedPiece (W := W) (F := F) (P₁ := P₁) b1 base d ext err :: r) 1).1 →
      (Fin P.par.S.fold.index.v → GE) → Prop)
    (Tab : St × F.E.Str → Nat → Nat → GE) (Dec : St × F.E.Str → Prop)
    (hBK : ∀ (a : (P₁ × St) × F.E.Str) gam, BadKey (a.1.2, a.2) gam →
      BadKV ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a) gam)
    (hgood : ∀ a : (P₁ × St) × F.E.Str, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      ∀ (x : St) (m : Words GE) (gam : Fin P.par.S.fold.index.v → GE),
      ¬ BadKey (a.1.2, a.2) gam →
      (gamma P.par.S x.loc).map OnBytes.Model.Reading.gl.val = List.ofFn gam →
      x.loc.key = a.1.2.loc.key → x.st.codes = a.1.2.st.codes →
      NearAt OnBytes.Model.Reading.gl P.par x m (tabOf a.2) e' →
      RecAll OnBytes.Model.Reading.gl P.par x m →
      Dec (a.1.2, a.2) ∧ UIsFold P.par.S.matrixRows P.par.S.kLo P.par.S.fold.index.v
        (Tab (a.1.2, a.2)) (List.ofFn gam) (uOf x.loc m))
    (hu : ∀ a τ b, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → uRec b.1.2 = withNext P.par b.1.2)
    (hNear : ∀ b w, shIt N Mg f (liftedPiece b1 base d ext err :: r) .nearU 2 b w →
      NearAt OnBytes.Model.Reading.gl P.par (uRec b.1.2) (rg w) (tabOf b.2) e')
    (hRec : ∀ b w, shIt N Mg f (liftedPiece b1 base d ext err :: r) .recRow 2 b w →
      RecAll OnBytes.Model.Reading.gl P.par (uRec b.1.2) (rg w))
    (hDotU : ∀ b w, ownItem N Mg .dot b w →
      shIt N Mg f (liftedPiece b1 base d ext err :: r) .omU 2 b w →
      DotUAt P.par.S (gOf b.1.1) (uRec b.1.2).loc (rg w) (wv w))
    (s0 : ∀ a τ b, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b →
      onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 2 b)
    (hV : ∀ a τ b w, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg .pinV b w →
      wv w = VOf a)
    (s4 : ∀ a τ b w, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg .unmarked1 b w → ownItem N Mg .ev b w →
      VIs P.par.S (gOf a.1.1) (Tab (a.1.2, a.2)) (wv w) → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (E a w) ∧
        shIt N Mg f (liftedPiece b1 base d ext err :: r) .pinT 1 a (E a w))
    (s5 : ∀ a τ b w i, i ∈ [ItemS.unmarked1, .pinI, .pinV] →
      onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg i b w →
      ownItem N Mg i a (E a w))
    (ef : Nat)
    (hkey : ∀ a, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      cnt (BadKV ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) ≤ ef) :
    (liftedPiece (W := W) (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ N f (liftedPiece b1 base d ext err :: r) 1).2
      (onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1)
      (stepPt N Mg Pm Oc split f (liftedPiece b1 base d ext err :: r) E)
      ((vecMaps d P.par.S.kCol).err ((ef * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) := by
  refine ⟨fun k τ => ∀ τ', (vecMaps d P.par.S.kCol).carry.tr τ = some τ' →
      ¬ GuardK P.par.S.kLo P.par.S.fold.index.v ef (BadKV k) τ'.2.1,
    fun a τ => ∀ τ', (vecMaps d P.par.S.kCol).carry.tr τ = some τ' →
      ¬ BadO P.par.S (gOf a.1.1) (Tab (a.1.2, a.2)) (VOf a) τ'.2.1,
    fun k => doomed_of_cnt d hd _ _ (cnt_guardK P.par.S.kLo P.par.S.fold.index.v ef (BadKV k)),
    fun a _ => doomed_of_cnt d hd _ _ (cnt_badO P.par.S (gOf a.1.1) (Tab (a.1.2, a.2)) (VOf a)),
    fun a τ b ha hk ho hb => ?_⟩
  obtain ⟨τ', htr, -⟩ := point_yesL rg wv P b1 b2 b3 b4 b5 b6 b7 b8 hbl (gOf a.1.1) e'
    base d hd ext err BadKey Tab Dec a (hgood a ha) τ b hb
  have hp : psiAtK d P.par.S.kCol τ = τ'.2.1 := by
    unfold psiAtK
    rw [htr]
  refine point_h_at_k14 rg wv P b1 b2 b3 b4 b5 b6 b7 b8 hbl e' base d hd ext err N Mg Pm Oc split f r E gOf
    VOf uRec BadKey BadKV Tab Dec hBK hgood hu hNear hRec hDotU s0 hV s4 s5 a τ b ha hb ?_ ?_
  · rw [hp]
    exact fun hbad => hk τ' htr ⟨hkey a ha, hbad⟩
  · rw [hp]
    exact ho τ' htr

end Desc.K14.Law

#print axioms Desc.K14.Law.point_h_at_k14
#print axioms Desc.K14.Law.doomed_of_cnt
#print axioms Desc.K14.Law.point_leadsB_at_k14
