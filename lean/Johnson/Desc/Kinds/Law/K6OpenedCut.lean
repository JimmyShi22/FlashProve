-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6OpenedCut.lean (under the guard "the witness's cells hold an
index": the sentence on the claim on the weights is asked under it; opened_cut is
general in a condition Rch
beside the table's promise; the stated reads are statedAll: with the
planes' three; the table's letter for the stated data is a
LETTER, St, with what is asked of it at the verifier's state: StatedAt): WHAT THE OUTPUT
HEAD'S ROW
OPENS GIVES K6's RELATION
BEHIND THE SUB-PROTOCOL, AT THE COMPONENTS THAT THE LAW READS OFF THE WITNESS (Law/K6Cut.lean:
compCut, at
the terms of Law/PlanK6At.lean): the call of K6's law from the forms' sentences to K6Out
(Law/K6Stated.lean: k6Out_of_items_stated) at d := compCut w, with its premises on the cells, the
stream and the mask row paid by Law/DataMeetsCells.lean and Law/DataMeets.lean; and so the field
"opened" of Law/K6ItemsCut.lean.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law; the theorems in Came and AtTable).
  cellsK6 Wp: the letter "cells" of Law/K6Stated.lean as a term: cellsOfData at Meaning.sizesOf Wp;
      it reads no state.
  statedK6 Wp P8: THE TABLE'S LETTER FOR THE STATED DATA AS A TERM: Stated.of (FormsT.lean) at
      statedAll at cellsK6, the planes' matrix's logarithm of rows and nuK6.
  RecordDue ... s aK cU: WHAT IS ASKED OF THE VERIFIER'S STATE s BEHIND THE SUB-PROTOCOL, GATHERED:
      s shows the open
      segment's part aK; aK's layout is the plan's; DataSeated; the frame names the message with the
      mask rows, the book seats it at a tenant of segment 24's group with the number n, and its bits
      of mask rows are rb; the ledger's list of factors is no longer than the plan's number of mask
      entries in use; the readers at s are the silent reader's; what was heard stands at s
      (K6HeardAt); the link's list names the reads' array cU; StatedAt: the stated data leave the
          mask row, and their cells of that array are K6's stated reads (at K6's own
          term statedK6: where the array is of the second sending: statedAt_k6); two
      facts on the tables; the lookup's last claim names no entry.
  k6Out_cut_of_forms: under RecordDue, the plan's test, one test on N, the sentence on the weights
      and the four sentences on the driver's runs (3, "norm"), (3, "policy"), (3, "logits"), (3,
      "join"): K6Out Wp s (compCut ... w).
  FormsSay ... Mg0: what three of the table's items say at a meaning Mg0, in these sentences' words.
  opened_cut: SO: the field "opened", from FormsSay and "RecordDue holds behind every accept".

Every letter under "there is": in RecordDue: o: pinned by the frame; x: by the book. In opened_cut's
premise hRec: aK: pinned by the verifier's state; cU: by the link's list.
What it does not say. THAT RecordDue HOLDS AT ANY STATE: it is what the table's promise and the
sub-protocol's own accept must give at the border behind the sub-protocol: which clause comes from
which is
not said.
FormsSay: at the filling in the forms' files its first two fields should be unfoldings (the table's
names "own" and "join" at the head stand for just these four runs of the driver's sub-protocol
number 3); its
third needs a filling in which the item "weights" gets WeightAt as
its meaning: NONE OF THE THREE IS TYPED HERE. The items on the planes and "small" are not spent. A
joining: no new mathematics. Nothing on soundness.
-/
import Johnson.Desc.Sound.FormsT
import Johnson.Desc.Kinds.Law.StatedHeadArm
import Johnson.Desc.Kinds.Law.DataMeetsCells
import Johnson.Desc.Kinds.Law.K6ItemsCut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce Piece Frame Sending onQ strsOf meaningSig)
open VerifiableInference.Desc.K9L (Bound)

/-- The head's cells, of the data: no state is read. -/
def cellsK6 (Wp : OnBytes.Model.Verify.Public) : S → Bound Cb.Gl.E → NCells :=
  fun _ D => cellsOfData Wp (Meaning.sizesOf Wp) D

/-- **The stated data, as a term.** -/
def statedK6 (Wp : OnBytes.Model.Verify.Public) (P8 : K8.ReadsQuiet.PH) : Sound.Stated :=
  Sound.Stated.of (statedAll Wp P8 (cellsK6 Wp) Wp.hS.lmbH (nuK6 Wp))

/-- **What is asked of the table's letter for the stated data, at a state of the verifier**: it
leaves the mask
row,
and its cells of the reads' array (row 0) are the kind's stated reads. -/
def StatedAt (Wp : OnBytes.Model.Verify.Public) (P8 : K8.ReadsQuiet.PH) (St : Sound.Stated) (s : S)
    (cU : Nat × String) : Prop :=
  ∀ D : Bound Cb.Gl.E, (∀ j, (St.at1 s D).mask j = D.mask j) ∧
    ∀ pos, (St.at1 s D).cell cU.1 cU.2 0 pos =
      statedAll Wp P8 (cellsK6 Wp) Wp.hS.lmbH (nuK6 Wp) s D cU 0 pos

/-- At K6's own term statedK6, where the array is of the second sending. -/
theorem statedAt_k6 (Wp : OnBytes.Model.Verify.Public) (P8 : K8.ReadsQuiet.PH) (s : S)
    (cU : Nat × String) (h : Sound.second s cU = true) : StatedAt Wp P8 (statedK6 Wp P8) s cU :=
  fun D => ⟨fun _ => rfl, fun pos => Sound.of_second _ s D cU 0 pos h⟩

/-- **What is asked of the verifier's state behind the sub-protocol.** -/
def RecordDue (arr : Nat → Nat → Nat) (N : Numbers) (Wp : OnBytes.Model.Verify.Public)
    (layout : ReqLayout) (num : Nat → Nat → Nat) (n rb : Nat) (P8 : K8.ReadsQuiet.PH)
    (St : Sound.Stated) (states : Nat → List (K9.RunOf S)) (Rd : K9.Readers) (s : S) (aK : K9.Part)
    (cU : Nat × String) : Prop :=
  K9.segAt? s = some aK ∧ aK.L.check.rows.layout = layout ∧
    DataSeated arr N Wp (N.sent 24 0) aK num ∧
    (∃ (o : Nat) (x : Nat × Nat), K9L.maskOracle aK.L.check.frame = some o ∧
      K9.seatAt (N.sent 24 0) aK.d.book o = some x ∧ x ∈ N.group 24 ∧ arr x.1 x.2 = n ∧
      aK.d.st.rowBits o .mask = rb) ∧
    aK.F.mf.size ≤ Wp.H.ns ∧
    (∀ name, K6Name name → Rd.forms 3 name s = k6Silent P8 states 3 name s) ∧
    K6HeardAt Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) s ∧
    aK.L.arrayOf[readsOf Wp]? = some cU ∧ StatedAt Wp P8 St s cU ∧
    (∀ e o tt, withTables P8 s = some e → e.here = .head o → o.t = some tt → TabsApart tt) ∧
    (∀ e o tt F tr, withTables P8 s = some e → e.here = .head o → o.t = some tt →
      e.fork? = some F → F.trees[readsOf Wp]? = some tr → ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ tr.K) ∧
    ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[]

namespace Came

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (Wp : OnBytes.Model.Verify.Public) (layout : ReqLayout)
  (num : Nat → Nat → Nat) (n rb : Nat)

/-- **From the forms' sentences to K6Out, at compCut.** -/
theorem k6Out_cut_of_forms (P8 : K8.ReadsQuiet.PH) (l piece : Nat)
    (states : Nat → List (K9.RunOf S))
    (KS : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l piece states 3)
    (Rd : K9.Readers) (St : Sound.Stated) (s : S) (aK : K9.Part) (cU : Nat × String)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (R : RecordDue arr N Wp layout num n rb P8 St states Rd s aK cU)
    (hok : (parOf Wp.hS (workOf Wp)).ok = true) (h1 : namedOnce arr N 24 n = true)
    (hWt : WeightAt Wp s (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp layout num) Wp (plAt
        n rb) w).1.toCells (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp layout num) Wp
            (plAt n rb) w).2)
    (hf : ∀ r, r = "norm" ∨ r = "policy" ∨ r = "logits" ∨ r = "join" →
      Sound.formsTQ Rd St (N.sent 24 0) 3 r s (Sound.seatTab cs arr msR w)) :
    K6Out Wp s (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp layout num) Wp (plAt n rb) w)
        := by
  obtain ⟨ha, hlay, hD, ⟨o, x, ho, hx, hg, hnx, hrb⟩, hsz, hRd, hT, hArr, hsec, hApart, hBelow,
    hbare⟩ := R
  subst hlay
  subst hrb
  obtain ⟨e1, e2⟩ := comp_of_data cs arr msR N Wp (plAt n (aK.d.st.rowBits o .mask)) (N.sent 24 0)
    aK num w hD
  exact k6Out_of_items_statedAll Wp P8 l piece 3 states KS Rd St (N.sent 24 0) s
    (Sound.seatTab cs arr msR w) _ aK ha hRd hok hT
    (fun j hj => by
      rw [(hsec _).1 j]
      exact mask_of_data cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp aK.L.check.rows.layout num)
        Wp (N.sent 24 0) aK w o n x ho hx hg hnx h1 j (Nat.lt_of_lt_of_le hj hsz))
    (cellsK6 Wp) Wp.hS.lmbH (nuK6 Wp) cU hArr (fun pos => (hsec _).2 pos) e1 e2 hApart hBelow hWt
    hbare (hf _ (Or.inl rfl)) (hf _ (Or.inr (Or.inl rfl))) (hf _ (Or.inr (Or.inr (Or.inl rfl))))
    (hf _ (Or.inr (Or.inr (Or.inr rfl))))

end Came

namespace AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack

variable {rows cols : Nat} (cs : OnBytes.Codes) {Xi P Tok : Type} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Fin rows → Fin cols → GE))
  (msR : List Mem) (N : Numbers) (Wp : OnBytes.Model.Verify.Public) (layout : ReqLayout)
  (num : ℕ → ℕ → ℕ) (n rb : ℕ) (fld : Fmt.Fld) (Fr : Frame)
  (Mg₀ : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (links : List ModelPart)
  (ps : List Place) (k : ℕ)
  (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT))

/-- **What three of the table's items say, in the forms' sentences' words.** -/
structure FormsSay (St : Sound.Stated) (Rd : K9.Readers) : Prop where
  own : ∀ a y w, Mg₀.formsT 24 4 "own" a y w → ∀ r, r = "norm" ∨ r = "policy" ∨ r = "logits" →
    Sound.formsTQ Rd St (N.sent 24 0) 3 r a.2 (Sound.seatTab cs arr msR w)
  join : ∀ a y w, Mg₀.formsT 24 4 "join" a y w →
    Sound.formsTQ Rd St (N.sent 24 0) 3 "join" a.2 (Sound.seatTab cs arr msR w)
  weights : ∀ a y w, VerifiableInference.OnPublicFiles.Flat.InRange w.cells → Mg₀.formsT 24 4 "weights" a
      y w →
    WeightAt Wp a.2 (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp layout num) Wp (plAt n
        rb) w).1.toCells (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp layout num) Wp (plAt
            n rb) w).2

/-- **The field "opened".** -/
theorem opened_cut (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (P8 : K8.ReadsQuiet.PH) (l piece : ℕ)
    (states : ℕ → List (K9.RunOf S))
    (KS : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l piece states 3)
    (Rd : K9.Readers) (St : Sound.Stated) (FS : FormsSay cs arr msR N Wp layout num n rb Mg₀ St Rd)
    (hok : (parOf Wp.hS (workOf Wp)).ok = true) (h1 : namedOnce arr N 24 n = true)
    (hRec : ∀ a τ b,
      onQ (Fr := Fr) N (meaningSig cs G arr smp msR decT Mg₀) links ps (fun a => a) k a → Rch k a →
      a.1.2.failed = none → q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      ∃ aK cU, RecordDue arr N Wp layout num n rb P8 St states Rd b.1.2 aK cU) :
    ∀ a τ b w, onQ (Fr := Fr) N (meaningSig cs G arr smp msR decT Mg₀) links ps (fun a => a) k a →
        Rch k a →
      a.1.2.failed = none → q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      VerifiableInference.OnPublicFiles.Flat.InRange w.cells →
      Mg₀.formsT 24 4 "own" b.1 (strsOf Fr b.2) w →
      Mg₀.formsT 24 3 "planes" b.1 (strsOf Fr b.2) w →
      Mg₀.formsT 24 4 "join" b.1 (strsOf Fr b.2) w →
      Mg₀.formsT 24 4 "weights" b.1 (strsOf Fr b.2) w →
      Mg₀.constr 24 .small b.1 (strsOf Fr b.2) w → K6Out Wp b.1.2 (compCut cs arr msR N
          (Meaning.sizesOf Wp) (seatLay Wp layout num) Wp (plAt n rb) w) := by
  intro a τ b w ha hrc hm hb hA hR ho _ hj hw _
  obtain ⟨aK, cU, R⟩ := hRec a τ b ha hrc hm hb hA
  refine Came.k6Out_cut_of_forms cs arr msR N Wp layout num n rb P8 l piece states KS Rd St b.1.2 aK
    cU w R hok h1 (FS.weights _ _ _ hR hw) fun r hr => ?_
  rcases hr with h | h | h | h
  · exact FS.own _ _ _ ho r (Or.inl h)
  · exact FS.own _ _ _ ho r (Or.inr (Or.inl h))
  · exact FS.own _ _ _ ho r (Or.inr (Or.inr h))
  · rw [h]
    exact FS.join _ _ _ hj

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6Out_cut_of_forms
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.opened_cut
