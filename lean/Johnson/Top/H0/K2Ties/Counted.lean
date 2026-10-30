-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/Counted.lean: THE CODE SWITCH's SHARE OF THE CHAIN OF PROMISES, WITH
    "REACHED": THE FORM IN WHICH THE KIND's LAW IS COUNTED, AS ONE DEFINITION; AND THAT THE ASSEMBLY
    OF THE TIES ENDS IN IT. Three definitions, two theorems. A law file: no sub-protocol imports it.

Why. The join of the kinds' laws takes each kind's law as a hypothesis in one form. So that the
    sentence which the join's files write for the code switch is the sentence in which this work
    ends, it is written down here, and Lean holds that the assembly (Assembly.lean) ends in it.

What is said.
  `extTab D links ps c₀ tokOf i`: the table's own extractor at border i.
  `K02Counted D Mg₀ Rch links ps c₀ tokOf l`: THE TABLE's OWN DEFINITION `KindTiedR`
      (Johnson/Desc/Sound/TiedR.lean), CALLED, at the kind K2, at N := D.N, the composed meaning
      `mgAll D Mg₀` and E := `extTab`: at every number i at which the list of places has a place of
      the kind K2: the piece that stands at i in the list l, with the table's extractor of border i
      laid in, is tied at i in the form with "reached" (`TiedAtR`,
      Johnson/Desc/Sound/ChainOfPromisesR.lean), at the reader "the identity".
  `k02Counted_is_field`: at Mg₀ := `mgBase` and the written full list of segments it is the field
      written out: HELD BY LEAN (`Iff.rfl`) AGAINST A COPY, typed here, of the end of the
      law of the kind K13 in the tight form (k13_law_atThreeT), with K2 for K13 and l for
      its list of pieces; THE COPY WAS COMPARED WITH THAT FILE's TEXT BY PROGRAM, NOT BY LEAN.
  `K2PlaceOwes … i q`: there are the place's parameters such that q is the piece written out
      (`k2Q`), holds the strict reading of a sub-protocol B lifted over the public part, accepts at
      no marked state, and `K2AllOwes` holds at k := i.
  `k02_counted`: `K2PlaceOwes` at every place of the kind gives `K02Counted`.

WHAT THE CHAIN's RULE ASKS BESIDE IT. `chainOfPromisesR` takes `EachTiedR`: at each member `TiedAtR`
    AND `HandsOn Rch k q` (an accept hands "reached" on). NO FIELD OF `TiesAtR` GIVES `HandsOn`, and
    `K02Counted` does not hold it: it is owed beside, kind-free, by whoever names Rch:
    `eachTiedR_of_kinds` (TiedR.lean) takes it as a premise of its own; at "reached" along the
    description it lies (`handsOn_map`, Johnson/Top/H0/Walk/ReachHands.lean).

Limits. A SENTENCE WITH PREMISES; NO MEMBER OF `K2PlaceOwes` IS SHOWN. The list l is a parameter:
    that the description's own list has such pieces at the 25 places is not said here. The pieces
    are over the two-element field's parameters (`ckP .two`) and the proof file's own type of
    claims. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.TiedR
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.Sound.AtDriver
import Johnson.Top.H0.K2Ties.Assembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece)
open VerifiableInference.Desc.First.K2Ties (Wq)
open _root_.Run (ckP)
open ProofFile (Cl)

variable {F : Frame} {P Tok XiD : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public} (D :
    MgData XiD P Tok rws cls nR X) (Mg₀ : Meaning P (Wq rws cls Tok)) (Rch : ℕ → (P × First.S) ×
    F.E.Str → Prop) (links : List ModelPart) (ps : List Place) (c₀ : CellsQ rws cls) (tokOf : P × First.S
          → Tok)

/-- The table's own extractor at border i. -/
noncomputable abbrev extTab (i : ℕ) : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → Wq rws cls
    Tok → Wq rws cls Tok :=
  extQAt D.cs D.G D.arr D.smp D.ms D.decT c₀ tokOf D.N links ps (fun x => x) i

/-- **THE CODE SWITCH's SHARE OF THE CHAIN OF PROMISES, WITH "REACHED": THE COUNTED FORM.** -/
def K02Counted (l : List (Piece (ckP .two) F (P × First.S) Cl (Wq rws cls Tok))) : Prop :=
  KindTiedR D.N (mgAll D Mg₀) links ps Rch (extTab D links ps c₀ tokOf) l KindName.K2

/-- **It is the field in which the join takes a kind's law**, written out. -/
theorem k02Counted_is_field (l : List (Piece (ckP .two) F (P × First.S) Cl (Wq rws cls Tok))) :
    K02Counted D mgBase Rch linksFull (First.flatPlacesOf linksFull true) c₀ tokOf l ↔
      ∀ i q p, l[i]? = some q → (First.flatPlacesOf linksFull true)[i]? = some p → p.kind =
          KindName.K2 →
        TiedAtR D.N (mgAll D mgBase) linksFull (First.flatPlacesOf linksFull true) (fun a => a) Rch
            i (q.withMap ((fun k => extQAt D.cs D.G D.arr D.smp D.ms D.decT c₀ tokOf D.N linksFull
            (First.flatPlacesOf linksFull true) (fun a => a) k) i)) :=
  Iff.rfl

/-- **What is owed at one place**: the place's parameters, the piece written out, and all the debts.
    -/
def K2PlaceOwes (i : ℕ) (q : Piece (ckP .two) F (P × First.S) Cl (Wq rws cls Tok)) : Prop :=
  ∃ (Cl₀ Cl₁ Xi : Type) (r : SwRow) (h : r.ok = true) (iJ : ((rowsAt r (r.ok_says h) (Letters.plain
      r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says
      h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r (r.ok_says h)
      (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r
      (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent) (G : FileDescription Xi) (seat : Fin
             r.lo.length → ℕ × ℕ) (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ : RDT) (d₂ : RDT) (ext :
             P → Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wq rws cls Tok → Wq rws cls Tok) (arr : ℕ →
             ℕ → ℕ) (seats : List (ℕ × ℕ)) (decT : (ℕ → Option (ℕ × List UInt64)) → P ×
             VerifiableInference.Desc.First.S → Option (CellsQ rws cls)) (_d₀ : (Cb.Pv.SendLoc.stage (selZ
             (Letters.plain r (r.ok_says h)) iJ iQ).sw).X × (Cb.Pv.SendLoc.stage (selZ (Letters.plain r
             (r.ok_says h)) iJ iQ).sw).Ex.Str) (_y₀ : F.E.Str) (rowAt : ℕ → Option SwRow) (pAt : ℕ → K2.P2)
      (door : ℕ → First.S → Option First.S) (m : ℕ) (B : Block Rec Cl) (enter : Rec → Except String
      Rec) (leave : Rec → Rec → Except String Rec) (ms : List Mem) (minePad : List Mem) (f₀ :
      _root_.Tw.K2.Front) (W : SwitchFrame) (n0 : ℕ) (grp : ℕ) (rows : ℕ) (olds : List ℕ) (L : Laid)
      (trees : ℕ) (news : List (ℕ × ℕ)) (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ) (smp : P ×
      First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf r.cs s.l).om i).Smp) (bq :
      Block (P × First.S) Cl) (extq : (P × First.S) × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wq
      rws cls Tok → Wq rws cls Tok) (pl : Place) (MO : List OracleShape) (LO : Laid) (Fk : P → ℕ →
      Rec → Prop), q = (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂ extq) ∧ bq =
      (below B).lift Prod.snd (fun t s => (t.1, s)) ∧ (∀ a τ b, (ownPiece (k2Q (P := P) (Cl := Cl)
      (W := Wq rws cls Tok) bq base d₁ d₂ extq) B (fun _ _ w => w) (k2Q (P := P) (Cl := Cl) (W := Wq
      rws cls Tok) bq base d₁ d₂ extq).err).ior.red.out a τ = some b → a.1.failed = none) ∧
      K2AllOwes Cl₀ Cl₁ D Mg₀ Rch h iJ iQ G seat seatN base d₁ d₂ ext arr seats decT c₀ rowAt pAt
      door m B enter leave links ps i ms minePad f₀ W n0 grp rows olds L trees news b₀ smp bq extq
      pl MO LO Fk

/-- **The assembly ends in the counted form.** -/
theorem k02_counted (l : List (Piece (ckP .two) F (P × First.S) Cl (Wq rws cls Tok))) (H : ∀ i q a,
    l[i]? = some q → ps[i]? = some a → a.kind = KindName.K2 → K2PlaceOwes D Mg₀ Rch links ps c₀ i q)
    :
    K02Counted D Mg₀ Rch links ps c₀ tokOf l := by
  intro i q a hq ha hk
  obtain ⟨Cl₀, Cl₁, Xi, r, h, iJ, iQ, G, seat, seatN, base, d₁, d₂, ext, arr, seats, decT, d₀, y₀,
      rowAt, pAt, door, m, B, enter, leave, ms, minePad, f₀, W, n0, grp, rows, olds, L, trees, news,
      b₀, smp, bq, extq, pl, MO, LO, Fk, rfl, hb, hM, A⟩ := H i q a hq ha hk
  exact k02_tiedAtR (d₀ := d₀) (y₀ := y₀) A hb hM

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02Counted_is_field
#print axioms VerifiableInference.Desc.First.K2Caller.k02_counted
