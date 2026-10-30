-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtK14Fill.lean: THE TIE AT "LIN point" AT THE REAL BLOCK (point_leadsB_at_k14, Johnson/Desc/Sound/PointAtK14.lean), WITH FOUR OF ITS TWELVE PREMISES PAID BY MAKE AT THE FILLED LETTERS. Small lemmas, one theorem. (The book-keeping at borders 1 and 2 may hold MORE than shape1 | shape2 (Johnson/Desc/K14/Law/PointCounts.lean): two letters x1, x2 for further public clauses, with (hx): at a yes x1 in front gives x2 behind). A joint build of files of
Johnson/Desc/Sound/ and of Johnson/Desc/K14/, as that file.

PAID HERE: (S0) the promise behind: the promise on the table rides (the stored table stays; the decoder reads the record's key alone, and the key stays: the law of a yes point_yesL, Johnson/Desc/K14/Law/PointLift.lean) · the book-keeping 1 hands on to 2 (the same law) · the slot's own condition rides (ocRides)
  · (hV) W's pin fixes the other vector to what the statement IN FRONT decodes to (vFixed) · (S5) no mark and the two pins ride back (pointRiders, pinJT_col, pinJT_extS_one) · (S4)'s second half: the cells' pin at what the extractor lays (pinT_extS).
THE FILLING: pin₁ := pinJT at the first chain's members and samples' reader, through get · pinT := pinWOf decT₂ · tablePromise := decodesOf decT₂ · shape 1 | 2 := shape1 | shape2, each with a further public clause (x1 | x2) · E := the table's extractor at block 1 (extS … 1) at the acting part's value
  · wv w := vec (the witness's table of W's member, through the one accessor) · VOf a := vec (what W's member's committed word decodes to with its sample at the statement in front).
WHAT STAYS, BY NAME: hbl · hd · **hkey** (the statement on codes) · hgood · hBK · hNear · hRec · hDotU · **s4a** ((Eval), VIs and the index masks' pin give the claim on M at the witness with the decoded cells laid: K13's step back from (Eval); "held" stands in it) · AND OF THE
FILLING: five equations of letters (rfl where the letters are so filled) · hdk (the decoder reads the record's key alone) · OcReadsBelow lo Oc · three comparisons of numbers (lo ≤ base; W's and the index masks' trees below base) · W's member is a member and sits at W's seat.

VOf's DEFAULT (the zero table where W's word decodes to nothing at the statement in front) DOES NO HARM: the slot's count holds at every vector; and where nothing is decoded in front no witness has W's pin behind (vFixed): so the step's "for every witness" never meets it.

Limits. As PointAtK14.lean's. vec, get, the codes, arr, the members, the samples' readers, the decoder are letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtK14
import Johnson.Desc.Sound.PointFill
import Johnson.Desc.Sound.ReadsBelowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ promQ actQ shIt ownItem stepPt strsOf strsOfAct OcReadsBelow
  ocRides out_behind pointRiders pinJT SitsAt decodesOf pinWOf extS wTab vOf vFixed pinJT_col pinJT_extS_one
  pinT_extS MsgT Mem Sending)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning ItemS PromS promsAt)
open Iop.IOR (drawRound)

theorem promsAt_one (split : Bool) : promsAt split 1 = [.tablePromise, .shape 1] := by
  cases split <;> rfl

theorem promsAt_two (split : Bool) : promsAt split 2 = [.tablePromise, .shape 2] := by
  cases split <;> rfl

/-- A yes of the lifted piece leaves what was handed. -/
theorem lifted_handed {W P₁ : Type} {F : Frame} (b0 : Block St Unit) (base : Nat) (d : RDT)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W) (err : Err (uLT (ckP .two) [d]))
    (a : (P₁ × St) × F.E.Str) (τ : Tr (uLT (ckP .two) (liftedPiece (W := W) (F := F) b0 base d ext err).ds))
    (b : (P₁ × St) × F.E.Str)
    (hb : (liftedPiece (W := W) (F := F) b0 base d ext err).ior.red.out a τ = some b) : b.1.1 = a.1.1 := by
  obtain ⟨-, gs, hdc⟩ := piece_yes (liftedPiece (W := W) (F := F) b0 base d ext err) a τ b hb
  exact (lift_ok b0 a.1 b.1 _ gs hdc).2

variable {P₁ A₁ Xi Cells Tok : Type} {F : Frame}

/-- **The debt at "LIN point" at the real block, at the filled letters.** -/
theorem point_leadsB_filled (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
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
    (gOf : P₁ → Nat → GE) (uRec : St → St)
    (BadKey : St × F.E.Str → (Fin P.par.S.fold.index.v → GE) → Prop)
    (BadKV : (actQ N f (liftedPiece (F := F) (P₁ := P₁) b1 base d ext err :: r) 1).1 →
      (Fin P.par.S.fold.index.v → GE) → Prop)
    (Tab : St × F.E.Str → Nat → Nat → GE) (Dec : St × F.E.Str → Prop) (lo ef : Nat)
    (x1 x2 : St → Bool)
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
    -- what stays
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
      DotUAt P.par.S (gOf b.1.1) (uRec b.1.2).loc (rg w) (vec (wTab cs arr xW w)))
    (s4a : ∀ a τ b w, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg .unmarked1 b w → ownItem N Mg .ev b w →
      VIs P.par.S (gOf a.1.1) (Tab (a.1.2, a.2)) (vec (wTab cs arr xW w)) → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (extS cs G arr smp₂ ms₂ decT₂ c₀ N split 1
        ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1
        (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w))
    (hkey : ∀ a, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      cnt (BadKV ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) ≤ ef) :
    (liftedPiece (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ N f (liftedPiece b1 base d ext err :: r) 1).2
      (onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1)
      (stepPt N Mg Pm Oc split f (liftedPiece b1 base d ext err :: r) fun a w =>
        extS cs G arr smp₂ ms₂ decT₂ c₀ N split 1
          ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1
          (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w)
      ((vecMaps d P.par.S.kCol).err ((ef * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) := by
  have hK := lifted_handed (W := Wit Cells Tok MsgT) (F := F) (P₁ := P₁) b1 base d ext err
  have hTab : ∀ a, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      decodesOf decT₂ a.1.2 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) := by
    intro a ha
    have h1 : Pm.tablePromise a.1.2
        (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) :=
      ha.1 .tablePromise (by rw [promsAt_one]; exact List.mem_cons_self)
    rw [hTP] at h1
    exact h1
  refine point_leadsB_at_k14 rg (fun w => vec (wTab cs arr xW w)) P b1 b2 b3 b4 b5 b6 b7 b8 hbl e' base d hd
    ext err N Mg Pm Oc split f r _ gOf
    (fun a => vec ((vOf cs G smp₁ xW (get a.1.1) (strsOf F a.2)).getD fun _ _ _ => 0)) uRec
    BadKey BadKV Tab Dec hBK hgood hu hNear hRec hDotU ?s0 ?hV ?s4 ?s5 ef hkey
  case s0 =>
    intro a τ b ha hb
    obtain ⟨τ', -, -, -, hkeyE, -, -, hsh, -⟩ := point_yesL rg (fun w => vec (wTab cs arr xW w)) P b1 b2 b3 b4
      b5 b6 b7 b8 hbl (gOf a.1.1) e' base d hd ext err BadKey Tab Dec a (hgood a ha) τ b hb
    refine ⟨fun c hc => ?_,
      ocRides (P₁ × St) P₁ Unit _ (ckP .two) F Prod.fst lo Oc (liftedPiece b1 base d ext err) hOc hlo hK a τ
        b ha.2 hb⟩
    rw [promsAt_two] at hc
    rcases List.mem_cons.1 hc with rfl | hc
    · show Pm.tablePromise b.1.2
        (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 2).2 b))
      rw [hTP]
      have h1 := hTab a ha
      have ec : (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 2).2 b)).cell =
          (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)).cell := by
        funext x
        show (strsOf F b.2).cell x = (strsOf F a.2).cell x
        rw [out_behind (liftedPiece b1 base d ext err) a b τ hb]
        rfl
      unfold decodesOf at h1 ⊢
      rw [ec, hdk _ a.1.2 b.1.2 hkeyE]
      exact h1
    · obtain rfl := List.mem_singleton.1 hc
      show Pm.shape 2 b.1.2 = true
      rw [hS2]
      have h1 : Pm.shape 1 a.1.2 = true :=
        ha.1 (.shape 1) (by rw [promsAt_one]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      rw [hS1] at h1
      have h1' : (shape1 P.par a.1.2 && x1 a.1.2) = true := h1
      obtain ⟨h1a, h1b⟩ := Bool.and_eq_true_iff.1 h1'
      show (shape2 P.par b.1.2 && x2 b.1.2) = true
      exact Bool.and_eq_true_iff.2 ⟨hsh h1a, hx a τ b ha hb h1b⟩
  case hV =>
    intro a τ b w _ hb hp
    have hp' : Mg.pin₁ N.w.1 N.w.2 b.1.1 (strsOf F b.2) w := hp
    rw [hpin₁] at hp'
    have hx : (xW.1.seat xW.2).1 < (liftedPiece (F := F) (P₁ := P₁) b1 base d ext err).base := by
      have e : (xW.1.seat xW.2).1 = N.w.1 := congrArg Prod.fst hsW
      rw [e]
      exact hw
    have hv := vFixed cs G arr smp₁ (fun s : P₁ × St => get s.1) (liftedPiece b1 base d ext err) xW
      (fun a τ b hb => congrArg get (hK a τ b hb)) hx a τ b hb w (hp'.2 xW hxW hsW)
    show vec (wTab cs arr xW w) = vec ((vOf cs G smp₁ xW (get a.1.1) (strsOf F a.2)).getD fun _ _ _ => 0)
    rw [hv]
    rfl
  case s4 =>
    intro a τ b w ha hb hun hev hvi hpi
    refine ⟨s4a a τ b w ha hb hun hev hvi hpi, ?_⟩
    show Mg.pinT a.1.2 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) _
    rw [hpT]
    exact pinT_extS cs G arr smp₂ ms₂ decT₂ c₀ N split _ _ w (hTab a ha)
  case s5 =>
    intro a τ b w i hi' _ hb h
    refine pointRiders P₁ St Unit _ (ckP .two) F N Mg (liftedPiece b1 base d ext err)
      (fun a w => extS cs G arr smp₂ ms₂ decT₂ c₀ N split 1
        ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1
        (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w)
      hK ?_ hw hi ?_ ?_ a τ b w i hi' hb h
    · intro j t q y y' w' hc hp
      rw [hpin₁] at hp ⊢
      exact pinJT_col cs G arr smp₁ ms₁ j t (get q) y y' w' hc hp
    · intro a' q y w' hp
      rw [hpin₁] at hp ⊢
      exact pinJT_extS_one cs G arr smp₂ ms₂ decT₂ c₀ N split smp₁ ms₁ _ _ (get q) y _ _ w' hp
    · intro a' q y w' hp
      rw [hpin₁] at hp ⊢
      exact pinJT_extS_one cs G arr smp₂ ms₂ decT₂ c₀ N split smp₁ ms₁ _ _ (get q) y _ _ w' hp

end Desc.K14.Law

#print axioms Desc.K14.Law.lifted_handed
#print axioms Desc.K14.Law.point_leadsB_filled
