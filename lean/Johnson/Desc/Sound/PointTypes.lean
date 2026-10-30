-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointTypes.lean: THE TIE AT "LIN point": WHAT MUST BE FIXED BEFORE THE POINT IS DRAWN, SAID IN THE TYPES; AND "W's PIN FIXES THE OTHER VECTOR", BY MAKE. One statement written as def … : Prop with its proof, two definitions, one lemma.


PointYes (Johnson/Desc/Sound/PointTie.lean) stands at one yes; its letters badK and V are free beside a, b, psi. THE COUNTS HOLD ONLY IF THE KEY's SORT OF LOST POINTS IS A FUNCTION OF THE KEY AND THE SLOT's OF THE STATEMENT IN FRONT. HERE THE TYPES SAY SO:
  PointH: BadK : (the acting part's values at border 1) → Pt → Prop · VI, DotT, VOf : functions of THE STATEMENT IN FRONT · psiAt : the transcript's point. Its conclusion is, to the letter, the last premise of "a plain law for a batch in two parts, for one written
    round, from two counts": ∀ a τ b, the promise in front → a yes → ¬ BadK (the key of a) (psiAt τ) → ¬ BadO a (psiAt τ) → stepPt E a b, WITH BadO a psi := ¬ VI a (VOf a) ∧ DotT a (VOf a) psi. No letter is indexed by the statement behind but DotU, which is
    opened and closed inside the step. (So the rule PointLeadsBN, whose middle sentence is indexed by the statement behind, need not be gone through.)
  wTab, vOf, vFixed: AT THE FILLED PIN (pinJT, Johnson/Desc/Sound/MeaningSig.lean): vOf x a := what member x's committed word decodes to with its sample, AT THE STATEMENT IN FRONT (the library's decoder with a sample: decAt, World.lean): no witness is read · wTab x w :=
    the witness's table of that member, through the one accessor · vFixed: at a yes of a piece that leaves what was handed and whose base lies above the member's tree: the member's pin AT THE STATEMENT BEHIND gives vOf x a = some (wTab x w). By dec_of_pin (a pin is
    functional), pinAt_col with colStays, out_behind: CALLED.

Limits. Rules under letters. That "the other vector" of the point's law is read off wTab (entry by entry in the layout's order) is the filling's.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointMake
import Johnson.Desc.Sound.ReadsTreeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared

/-- **The step at every yes off the two sorts of lost points, with what must be fixed in front fixed by type.** -/
def PointH : Prop :=
  ∀ (P₁ S₂ Cl Wt Vec Pt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
    (f pt : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (E : (P₁ × S₂) × Fr.E.Str → Wt → Wt)
    (BadK : (actQ N f (pt :: r) 1).1 → Pt → Prop)
    (VI : (P₁ × S₂) × Fr.E.Str → Vec → Prop) (DotT : (P₁ × S₂) × Fr.E.Str → Vec → Pt → Prop)
    (VOf : (P₁ × S₂) × Fr.E.Str → Vec) (wv : Wt → Vec)
    (DotU : (P₁ × S₂) × Fr.E.Str → Wt → Prop) (psiAt : Iop.Tr (uLT C pt.ds) → Pt),
    (∀ a τ b, onQ₂ N Pm Oc split f (pt :: r) 1 a → pt.ior.red.out a τ = some b →
      onQ₂ N Pm Oc split f (pt :: r) 2 b) →
    (∀ a τ b w, onQ₂ N Pm Oc split f (pt :: r) 1 a → pt.ior.red.out a τ = some b →
      ¬ BadK ((actQ N f (pt :: r) 1).2 a) (psiAt τ) → shIt N Mg f (pt :: r) .nearU 2 b w →
      shIt N Mg f (pt :: r) .recRow 2 b w → DotU b w → DotT a (wv w) (psiAt τ)) →
    (∀ b w, ownItem N Mg .dot b w → shIt N Mg f (pt :: r) .omU 2 b w → DotU b w) →
    (∀ a τ b w, onQ₂ N Pm Oc split f (pt :: r) 1 a → pt.ior.red.out a τ = some b →
      ownItem N Mg .pinV b w → wv w = VOf a) →
    (∀ a τ b w, onQ₂ N Pm Oc split f (pt :: r) 1 a → pt.ior.red.out a τ = some b →
      ownItem N Mg .unmarked1 b w → ownItem N Mg .ev b w → VI a (wv w) → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (E a w) ∧ shIt N Mg f (pt :: r) .pinT 1 a (E a w)) →
    (∀ a τ b w i, i ∈ [ItemS.unmarked1, .pinI, .pinV] → onQ₂ N Pm Oc split f (pt :: r) 1 a →
      pt.ior.red.out a τ = some b → ownItem N Mg i b w → ownItem N Mg i a (E a w)) →
    ∀ a τ b, onQ₂ N Pm Oc split f (pt :: r) 1 a → pt.ior.red.out a τ = some b →
      ¬ BadK ((actQ N f (pt :: r) 1).2 a) (psiAt τ) →
      ¬ (¬ VI a (VOf a) ∧ DotT a (VOf a) (psiAt τ)) →
      stepPt N Mg Pm Oc split f (pt :: r) E a b

theorem pointH : PointH := by
  intro P₁ S₂ Cl Wt Vec Pt C Fr N Mg Pm Oc split f pt r E BadK VI DotT VOf wv DotU psiAt s0 hyes hU hV s4 s5
    a τ b ha hb hK hO
  exact pointYes P₁ S₂ Cl Wt Vec Pt C Fr N Mg Pm Oc split f (pt :: r) E a b (VI a) (DotT a) (VOf a) wv
    (DotU b) (BadK ((actQ N f (pt :: r) 1).2 a)) (psiAt τ) (s0 a τ b ha hb) hK hO
    (fun w hk hn hr hd => hyes a τ b w ha hb hk hn hr hd) (fun w hd ho => hU b w hd ho)
    (fun w hp => hV a τ b w ha hb hp) (fun w h0 h1 h2 h3 => s4 a τ b w ha hb h0 h1 h2 h3)
    (fun w i hi h => s5 a τ b w i hi ha hb h)

section
variable (cs : OnBytes.Codes) {Xi A Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- The witness's table of a member, through the one accessor. -/
def wTab (x : Mem) (w : Wit Cells Tok MsgT) : MsgT :=
  toMsgT cs x.1.l x.2 (msgsOf cs x.1.l x.1.seat arr w x.2)

/-- What a member's committed word decodes to with its sample, at a statement: no witness is read. -/
noncomputable def vOf (x : Mem) (a : A) (y : Strs) : Option MsgT := decAt cs G smp x.1 x.2 a y

/-- **A member's pin behind a block fixes the witness's table to what the statement IN FRONT decodes to.** -/
theorem vFixed {S Cl Wt : Type} {C : CK} {Fr : Frame} (handed : S → A) (pt : Piece C Fr S Cl Wt) (x : Mem)
    (hK : ∀ a τ b, pt.ior.red.out a τ = some b → handed b.1 = handed a.1)
    (hx : (x.1.seat x.2).1 < pt.base) (a : S × Fr.E.Str) (τ : Iop.Tr (uLT C pt.ds)) (b : S × Fr.E.Str)
    (hb : pt.ior.red.out a τ = some b) (w : Wit Cells Tok MsgT)
    (hp : PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 (handed b.1) (strsOf Fr b.2) w) :
    vOf cs G smp x (handed a.1) (strsOf Fr a.2) = some (wTab cs arr x w) := by
  rw [hK a τ b hb] at hp
  have e2 := out_behind pt a b τ hb
  have hp' : PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 (handed a.1) (strsOf Fr a.2) w :=
    pinAt_col G cs x.1.l x.1.seat (fun z => smp z x.1) arr (strsOf Fr b.2) (strsOf Fr a.2) x.2 _ w
      (fun z => by
        rw [e2]
        exact (colStays C Fr pt.base pt.ds a.2 τ _ z hx).symm) hp
  exact dec_of_pin cs G arr smp x.1 x.2 (handed a.1) (strsOf Fr a.2) w hp'

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.pointH
#print axioms VerifiableInference.Desc.Sound.vFixed
