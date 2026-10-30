-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7Kind.lean.
IN THE SECOND FORM OF THE CHAIN OF PROMISES: general in a letter Rch; it ends in
KindTiedR (Desc/Sound/TiedR.lean). OLDER WORDS, KEPT BELOW: "block": a sub-protocol ·
"a yes": that it accepts.
WHAT IT DOES NOT SHOW. No soundness. A RULE OVER LETTERS: NO MEMBER. ITS ONE PREMISE IS PAID BY
NOBODY HERE: hAll: AT EVERY NUMBER OF THE ROW AT WHICH THE TABLE's LIST HAS A PLACE OF THE KIND K7,
the piece there holds, beneath the lift over the public part, a block B that narrows what the seat
lays and whose yes bears no mark, and the smaller bill K7Left (Law/K7Seated.lean; its head says
whose each field is) is met at that number. HOW MANY SUCH PLACES A LIST HAS IS NOT SAID: K7Left's
field "place" pins each to piece 1 of the segment hd: so a list with a place of that kind elsewhere
meets hAll nowhere there, and the premise fails: it does not pass in silence.
LETTERS. Under "there is", inside the premise hAll: B, Bst, W, l, name, front, tl, k2, told: the
caller's to name at each number; nothing in the conclusion reads them.
OBJECT. Desc/Sound/TiedR.lean's KindTiedR at the kind K7, at the table's own extractor number by
number (Desc/Sound/BordersFill.lean: extQAt), at any meaning Mg that meets the bill's two fields on
it (constr, decIs).
USER. Desc/Sound/TiedR.lean: eachTiedR_of_kinds: the field, kind by kind.
WHAT IT IS. THE NEXT TOKEN's KIND's SHARE OF THE CHAIN OF PROMISES, FROM THE SMALLER BILL.
  k7_kindTied       the statement: by Came.k7_tied_seat.

-/
import Mathlib
import Johnson.Desc.Sound.TiedR
import Johnson.Desc.Kinds.Law.K7Seated

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (HTailF2)
open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs Place Block FileDescription Oracle KindName)
open VerifiableInference.Desc.First (S Numbers ModelPart Meaning)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

/-- **THE NEXT TOKEN's KIND's SHARE OF THE CHAIN OF PROMISES.** -/
theorem k7_kindTied {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
    (pl : Nat → Nat × Bool × Nat × Nat) {Cl P Xi : Type} {C : CK} {Fr : Frame} (hd : Nat)
    (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × S → Fin ppref.V) (tokOf : P × S → Tok)
    (digitsPart : Nat → P × S → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)
    (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (links : List ModelPart)
    (ps : List Place) (G : FileDescription Xi)
    (smp : P × S → (x : Sending) → (i : Fin x.l.length) →
      Option ((Johnson.Pack.sigOf cs x.l).om i).Smp)
    (ms : List Mem)
    (decT : (Nat → Option (Nat × List UInt64)) → P × S → Option (Fin rows → Fin cols → GE))
    (c₀ : Fin rows → Fin cols → GE) (Rch : Nat → (P × S) × Fr.E.Str → Prop)
    (row : List (Piece C Fr (P × S) Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT)))
    (hAll : ∀ i q a, row[i]? = some q → ps[i]? = some a → a.kind = KindName.K7 →
      ∃ (B Bst : Block S Cl) (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
        (front : Block S Unit) (tl : HTailF2) (k2 : KindName) (told : List (List Oracle)),
        SeatOf Bst B ∧ q.b = (Sound.below B).lift Prod.snd (fun t x => (t.1, x)) ∧
        K7Left cs arr msR N s seat Wp pl hd tab put H tokH tokOf digitsPart Mg links ps i G smp ms
          decT c₀ B q W l name front tl k2 told Rch) :
    KindTiedR N Mg links ps Rch
      (fun i => extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun a => a) i) row .K7 := by
  intro i q a hq ha hk
  obtain ⟨B, Bst, W, l, name, front, tl, k2, told, hS, hb, L⟩ := hAll i q a hq ha hk
  exact Came.k7_tied_seat L Bst hS hb

end VerifiableInference.Desc.Kinds.Head.Law
