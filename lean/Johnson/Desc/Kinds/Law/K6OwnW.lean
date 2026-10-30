-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6OwnW.lean: Law/K6Own.lean's CALL OF THE BRIDGE AT K6, WITH THE COMPONENTS
THAT THE RULE READS AS ANY FUNCTION comp OF THE TABLE's WITNESS THAT READS PINNED PLACES ALONE: so
that a reading which is typed ON THE WITNESS (in other files: the messages as a segment reads them,
their symbols, the integers whose packing these are) can be laid in AS IT STANDS, with no second
text of it over tables:
STATED AND PROVED. Law/K6Own.lean's k6Own is the case comp := rd6 ∘ the one accessor.
  ReadsPinnedW comp K6's HALF OF (pin), ON WITNESSES: two witnesses that read alike through
      the one accessor memTab at every member of ms, inside its ranges, and have the same cells of
      the stored table, have the same components.
  meansW · the items as in Law/K6Own.lean, at comp; the item that stands on both sides
      (the table's ctx) has a third clause: side w: ANY SENTENCE ON THE WITNESS ALONE: it rides past
      the block for nothing (the extractor is the identity; the sentence reads no statement): so the
      table's "constr 4 small" (the packing) can stand there: Law/K6Own24.lean lays it in. THE LAW
      SPENDS IT
               NOWHERE: side := True gives the sentence without it.
  decW a the components AT THE STATEMENT a: comp of ANY witness that is pinned at a (chosen; a
      default where there is none): A FUNCTION OF THE STATEMENT IN FRONT ALONE. pinW_K6: at every
      witness that is pinned at a, comp w = decW a: two pinned witnesses read alike through the
      accessor (Sound.tab_of_pin | Sound.dec_of_pin) and have one decoding of the stored table.
  k6OwnW       THE CALL.
WHAT IT DOES NOT SAY. All that Law/K6Own.lean does not say, with comp for rd6: **comp IS A LETTER
STILL**; the silly filling (a constant) meets ReadsPinnedW; ms a letter; the premises on the piece;
K6On not inside the table's promise; the items K6's; NO MEMBER. decW is made by choice: it has no
code and needs none: it stands in no statement (p.Own does not name it). NO SOUNDNESS OF A PROTOCOL
OR A VERIFIER.
GENERAL IN THE BLOCK: k6OwnWBy: the call for any block b6, of any type of claims, that meets
Law/K6Steps.lean's record K6Steps Wp b6 on after: p.Own (on) (after) ...; k6OwnW, with its statement
as it was, is its instance at blockOf, K6On and K6After.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Own
import Johnson.Desc.Kinds.Law.K6Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open TypedOracleCompiler.Run.PQ (rvSL)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT memTab decAt PinAt InMsg
    strsOf
  Fenced SmpStays pinWOf ErrBears kitK kitFs)

variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : Nat → Nat →
           Nat)
  (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (Nat → Option (Nat × List UInt64)) → S → Option Cells)
  (ms : List Mem) (comp : Wit Cells Tok MsgT → Pinned) (side : Wit Cells Tok MsgT → Prop)
  (Wp : OnBytes.Model.Verify.Public)

/-- **This kind's half of (pin), on witnesses.** -/
def ReadsPinnedW : Prop :=
  ∀ w w' : Wit Cells Tok MsgT,
    (∀ x ∈ ms, ∀ mask row place, InMsg cs (x.1.l.get x.2).1 mask row place →
      memTab cs arr w x mask row place = memTab cs arr w' x mask row place) →
    w.cells = w'.cells → comp w = comp w'

/-- What each item says of a statement and a witness, at comp. -/
def meansW (Fr : Frame) : K6Item → S × Fr.E.Str → Wit Cells Tok MsgT → Prop
  | .closed, a, w => K6In Wp a.1 (comp w) ∧ a.1.failed = none
  | .opened, b, w => K6Out Wp b.1 (comp w) ∧ b.1.failed = none
  | .pins, a, w => Sound.Pinned cs G arr smp ms a.1 (strsOf Fr a.2) w ∧
      pinWOf decT a.1 (strsOf Fr a.2) w ∧ side w

open Classical in
/-- **The components at the statement**: comp of any witness that is pinned there. -/
def decW (Fr : Frame) (a : S × Fr.E.Str) : Pinned :=
  if h : ∃ w, meansW cs G arr smp decT ms comp side Wp Fr .pins a w then comp h.choose
  else ({ cell := fun _ _ _ => 0, Wh := fun _ _ => 0, stream := fun _ _ => 0 }, fun _ => 0)

namespace Came

/-- **(pin), at one statement: A THEOREM.** -/
theorem pinW_K6 (hloc : ReadsPinnedW cs arr ms comp) (Fr : Frame) (a : S × Fr.E.Str)
    (w : Wit Cells Tok MsgT) (h : meansW cs G arr smp decT ms comp side Wp Fr .pins a w) :
    comp w = decW cs G arr smp decT ms comp side Wp Fr a := by
  have hex : ∃ w, meansW cs G arr smp decT ms comp side Wp Fr .pins a w := ⟨w, h⟩
  unfold decW
  rw [dif_pos hex]
  obtain ⟨hP, hW, _⟩ := h
  obtain ⟨hP', hW', _⟩ := hex.choose_spec
  have e1 : decT (strsOf Fr a.2).cell a.1 = some w.cells := hW
  have e2 : decT (strsOf Fr a.2).cell a.1 = some hex.choose.cells := hW'
  refine hloc _ _ (fun x hx mask row place hin => ?_) (Option.some.inj (e1.symm.trans e2))
  have hd := Sound.dec_of_pin cs G arr smp x.1 x.2 a.1 (strsOf Fr a.2) w (hP x hx)
  exact (Sound.tab_of_pin cs G arr smp x.1 x.2 a.1 (strsOf Fr a.2) w _ hd (hP x hx) mask row place
    hin).trans (Sound.tab_of_pin cs G arr smp x.1 x.2 a.1 (strsOf Fr a.2) hex.choose _ hd
      (hP' x hx) mask row place hin).symm

/-- The pins ride back past the piece. -/
theorem pinsW_back {C : _root_.Run.PQ.CK} {Fr : Frame} {Cl : Type}
    (p : Piece C Fr S Cl (Wit Cells Tok MsgT)) (hF : Fenced p.base ms) (hS : SmpStays cs smp p ms)
    (hD : DecTStays decT p) (a b : S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) (w : Wit Cells Tok MsgT)
    (h : meansW cs G arr smp decT ms comp side Wp Fr .pins b w) :
    meansW cs G arr smp decT ms comp side Wp Fr .pins a w := by
  obtain ⟨hP, hW, hside⟩ := h
  refine ⟨fun x hx => ((Sound.rides cs G arr smp p ms hF hS a b τ hb x hx).1 w).1 (hP x hx), ?_,
      hside⟩
  have hW' : decT (strsOf Fr b.2).cell b.1 = some w.cells := hW
  show decT (strsOf Fr a.2).cell a.1 = some w.cells
  rw [← hD a τ b hb]
  exact hW'

/-- **THE CALL, AT ANY comp THAT READS PINNED PLACES ALONE.** -/
theorem k6OwnWBy (fld : Fmt.Fld) (Fr : Frame)
    {Cl : Type} (p : Piece (_root_.Run.ckP fld) Fr S Cl (Wit Cells Tok MsgT)) (b6 : Block S Cl)
    {on after : S → Prop}
    (hst : K6Steps Wp b6 on after) (hpb : p.b = Sound.below b6) (hback : p.back = [])
    (hext : ∀ a τ w, p.ext a τ w = w) (hloc : ReadsPinnedW cs arr ms comp)
    (hF : Fenced p.base ms) (hS : SmpStays cs smp p ms) (hD : DecTStays decT p)
    (hlog : ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs p.ds) j)) (toRDs p.ds) 0 p.err) :
    p.Own (fun a => on a.1) (fun b => after b.1)
      (meansW cs G arr smp decT ms comp side Wp Fr) InK6 OutK6 := by
  have hstep : ∀ a τ b, p.ior.red.out a τ = some b →
      ∃ cols n, Canonical (rvSL (_root_.Run.ckP fld) (toRDs p.ds) τ) ∧
        b6.step Fr.ft a.1 (rvSL (_root_.Run.ckP fld) (toRDs p.ds) τ) cols = .ok (b.1, n) := by
    intro a τ b hout
    obtain ⟨cols, n, hs⟩ := out_step p a b τ hout
    rw [hback, List.append_nil, hpb] at hs
    exact ⟨cols, n, below_step Fr.ft b6 a.1 _ cols b.1 n hs⟩
  refine Sound.ownOfRuleAtKit S Cl (Wit Cells Tok MsgT) K6Item Pinned fld Fr p _ _ _ _ _
    comp (decW cs G arr smp decT ms comp side Wp Fr) (fun a d => ruleStep Wp a.1 d)
    (priceAt (parOf Wp.hS (workOf Wp))) ?_ hlog hErr ?_ ?_ ?_
  · intro a d g _
    exact ruleStep_length Wp a.1 d g
  · intro a τ b w _ hout hrel
    exact pinW_K6 cs G arr smp decT ms comp side Wp hloc Fr a w
      (pinsW_back cs G arr smp decT ms comp side Wp p hF hS hD a b τ hout w (hrel .pins (Or.inr
          rfl)))
  · intro a τ b ha _ _ hout
    obtain ⟨cols, n, _, hs⟩ := hstep a τ b hout
    exact hst.promise Fr.ft a.1 _ cols b.1 n ha hs
  · intro a τ b w ha _ hnb hout hrel i hi
    obtain ⟨cols, n, hcan, hs⟩ := hstep a τ b hout
    rw [hext]
    rcases hi with rfl | rfl
    · exact ⟨hst.row Fr.ft a.1 (comp w) _ cols b.1 n ha hnb hcan hs
        (hrel .opened (Or.inl rfl)).1, (hst.unmarked Fr.ft a.1 _ cols b.1 n hs).1⟩
    · exact pinsW_back cs G arr smp decT ms comp side Wp p hF hS hD a b τ hout w
        (hrel .pins (Or.inr rfl))

/-- The same at the block at the unit type, under K6On, with K6After behind.
    -/
theorem k6OwnW (fld : Fmt.Fld) (Fr : Frame)
    (p : Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)) (l : Nat) (b6 : Block S Unit)
    (hb6 : blockOf Wp l = some b6) (hpb : p.b = Sound.below b6) (hback : p.back = [])
    (hext : ∀ a τ w, p.ext a τ w = w) (hloc : ReadsPinnedW cs arr ms comp)
    (hF : Fenced p.base ms) (hS : SmpStays cs smp p ms) (hD : DecTStays decT p)
    (hlog : ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs p.ds) j)) (toRDs p.ds) 0 p.err) :
    p.Own (fun a => K6On Wp a.1) (fun b => K6After Wp b.1)
      (meansW cs G arr smp decT ms comp side Wp Fr) InK6 OutK6 :=
  k6OwnWBy cs G arr smp decT ms comp side Wp fld Fr p b6 ((k6Steps_blockOf Wp l b6 hb6).weaken fun _
      h => h.1) hpb
    hback hext hloc hF hS hD hlog hErr

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.pinW_K6
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6OwnWBy
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6OwnW
#check @VerifiableInference.Desc.Kinds.Head.Law.Came.k6OwnW
