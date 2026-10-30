-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LeftSeats.lean: `K05_keepsW_all_left`
(Johnson/Desc/First/Att/K05KeepsLeft.lean) at two seats: the hearing's seat `seatSO`
(Johnson/Desc/First/Att/SeatO.lean) and the seat of the lookup on a link's calls, `K3.seatCalls`
(Johnson/Desc/First/Look/K3Seat.lean).

Definitions, statements and proofs.
Main names:
  `laysBack_seatSO`: `LaysBack` seatSO, by the text of the seat's two functions and of
    `First.S.hear5` (Johnson/Desc/First/State.lean).
  `K3LeftOutIs fork heard h lm first ι Q x0 g s`: there are F, F' and rs with Q F, F.next = first,
    `K3LeftIs` h lm F F' g rs, heard s = some g, fork s = some F' and `OutTies` x0 (endsOf h lm
    F.next rs) ι. This is `K3LeftAtIs` (Johnson/Desc/First/Att/K05EntryAt.lean) with the typed
    out-statement tied to the same rounds.
  `K05_keepsW_left_seats`: the law at these seats. Of the lookup's kind it asks `K3LeftOutIs` at
    each statement with "on", at Q := `Room` · ns nx (Forest.elems x.fs + (slotsOf (script p.own) +
    k)), and nothing else: the tie of the two seats' readers is `ledgerO_fork`
    (Johnson/Desc/First/Att/SeatOFork.lean).
Premises: the public ones of `K05_keepsW_all_left`; `K3LeftOutIs` at "on"; the seam; hon';
`BillsLaterJ` with the tie "gL = gOf a"; pin.
Limits: no premise is shown in this file or in what it imports, and no member is shown. The
statement holds for nothing where "on" holds of no statement, where R' holds of no witness or where
out returns nothing. The letter yOf stands in no premise and not in the conclusion. The record tl of
`attBase` and the tl that `GatheredAllJ` says there is are two letters, not tied. No soundness of
the protocol is claimed. Nothing on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05KeepsLeft
import Johnson.Desc.First.Att.K05EntryAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask)

/-- A mark turns no link. -/
theorem here_mark (s : First.S) (n : String) : (s.mark n).here = s.here := by
  unfold First.S.mark
  split <;> rfl

/-- **What the hearing's seat lays as the ledger it reads back as the ledger.** -/
theorem laysBack_seatSO : LaysBack seatSO := by
  intro s h G s' e
  unfold seatSO at e
  simp only at e
  split at e
  · rename_i a ea
    obtain ⟨g0, _, e2⟩ := Option.bind_eq_some_iff.1 e
    cases hu : First.S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } h with
    | error m =>
      rw [hu] at e2
      have e3 : (none : Option First.S) = some s' := e2
      cases e3
    | ok t =>
      rw [hu] at e2
      have e3 : some t = some s' := e2
      obtain rfl : t = s' := Option.some.inj e3
      obtain ⟨e1, _⟩ := (First.S.unmarked_ok _ _).1 hu
      have ht : ∃ a', t.here = .att a' ∧ a'.F = G := by
        rw [← e1]
        unfold First.S.hear5
        simp only
        split
        · exact ⟨_, here_mark _ _, rfl⟩
        · exact ⟨_, rfl, rfl⟩
      obtain ⟨a', h1, h2⟩ := ht
      unfold seatSO
      simp only [h1, h2]
  · cases e

/-- **The lookup's sharp promise, with the typed out-statement tied to the same rounds.** -/
def K3LeftOutIs {S St₀ J₀ : Type} [DecidableEq J₀] (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (h : Forest.Shape) (lm first : ℕ) (ι : Fo.Pl → Option J₀) (Q : Fork → Prop)
    (x0 : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)) (g : Forest.Heard) (s : S) : Prop :=
  ∃ (F F' : Fork) (rs : TwV.Rounds Cb.Gl.E), Q F ∧ F.next = first ∧ K3LeftIs h lm F F' g rs ∧
    heard s = some g ∧ fork s = some F' ∧ OutTies x0 (Fo.endsOf h lm F.next rs) ι

section LeftSeats
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

open Classical in
/-- **The kind's law at the two seats that sit.** -/
theorem K05_keepsW_left_seats {Aa Bb W Cl : Type} (claim : Aff → Cl) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad) (hfs : x.fs = A.fs)
    (hok : planOkAll cf A.S A.fs = true) (p : Par) (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS)
    (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → First.S) (recB : Bb → First.S)
    (x0 : Aa → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (yOf : Aa → Ex.Str) (on : Aa → Prop)
    (gOf : Aa → Forest.Heard) (pl : ℕ → ℕ → JAtt x.ns tl)
    (hleft : ∀ a, on a → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script p.own) + k))) (x0 a) (gOf a) (recA a))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seatSO p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (part : W → (attSg x D rad).Msg) (mOf : Aa → (attSg x D rad).Msg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → out a τ = some b → on' b)
    (hb : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seatSO p.own recA recB x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R'
      (bearErr ds _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) :=
  K05_keepsW_all_left x tl D rad Ex Wp α hA H hfs hok seatSO laysBack_seatSO p hp ns nx k j0 ds out recA recB x0 yOf on
    (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard gOf pl
    (fun a ha => by
      obtain ⟨F, F', rs, q, hn, L, hh, hf, T⟩ := hleft a ha
      exact ⟨F, F', rs, ⟨fun _ h => ledgerO_fork claim h, hf, hh, hn, L, q⟩, T⟩)
    hyes hpass hd he part mOf on' R' hon' hb pin

end LeftSeats

end VerifiableInference.Desc.First.Att.P
