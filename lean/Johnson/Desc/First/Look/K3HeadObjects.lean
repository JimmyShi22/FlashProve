-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
head_maskRow, calls_objects_head: no state of the verifier and no witness
is shown at which all premises hold.
Johnson/Desc/First/Look/K3HeadObjects.lean: the lookup on THE OUTPUT HEAD's CALLS AT THE TABLE OF
JOINTS: the mask row's dictionary at headNu (Johnson/Desc/First/Look/K3HeadGoodIn.lean), and with it
the sentence "the forms of the run objects give the first item of the lookup's row out" at that
reading of the places; in front of both: that sentence AT A LETTER pc FOR THE PIECE's NUMBER (the
head's calls stand at piece 3; a layers' or an attention link's at 2). Statements and proofs. Ties
of readings: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: Desc.Sound.dataQ | seatTab; OnPublicFiles.headNu; Meaning.formsT at a run "objects".
USER: k03_objects_head (Johnson/P5J/K03HeadObjAt.lean) calls calls_objects_head.
LETTERS: those of K3CallsObjects.lean and K3CallsMask.lean; pc; adr.

Compiled with the whole library.




Main names:
  `calls_objects_pc`: calls_objects_nu (K3CallsObjects.lean) with the piece's number a letter.
  `headNu_maskAt`: the place "mask j" at headNu is what the messages hold at that address's seat.
  `head_maskRow`, `head_maskRow_of`: **THE DICTIONARY AT THE HEAD**: at seatTab; at a letter rd.
  `calls_objects_head`: THE END: at pc := 3 and headNu: typed after the field objects of
    HeadAtTableR (Johnson/Desc/First/Look/K3HeadAtTableR.lean): HELD AGAINST IT BY EYE: no
    file applies the one to the other.

EACH PREMISE, AND WHO COULD PAY IT: as in K3CallsObjects.lean and K3CallsMask.lean.

Limits. At Cl := Desc.Claim. From x.ns on headNu is 0 at a mask, whatever the data read.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsObjects
import Johnson.Desc.First.Look.K3CallsMaskRd
import Johnson.Desc.First.Look.K3HeadGoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Road.Rows (Bare)
open Cb.Fo Cb.Fo.NumsEq
open VerifiableInference.Desc (Wit Link Strs)
open VerifiableInference.Desc.K9 (Readers segAt? readersOfLink statesOfLink LinkHoles)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)
open VerifiableInference.Desc.First.Att.P (ReadMsgOf OneReader)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr)

section
variable {P Cells Tok : Type} {Fr : Frame} (x : Desc.First.Look.Place) (D : Sent)
  (rad : OracleShape → ℕ) (set : Params.Setting)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (claim : Aff → Desc.Claim) (N : Numbers) (Mg Mg₀ : Meaning P (Wit Cells Tok MsgT))
  (links : List ModelPart) (ps : List Desc.Place) (pi : P) (k m : ℕ)
  (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)
  (Rc : Desc.First.S × Fr.E.Str → Prop)
  (ms : List Mem) (Rd : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
  (after : ℕ → Desc.First.S → Except String Desc.First.S)
  (wt : ℕ → P × Desc.First.S → Strs → Wit Cells Tok MsgT → Prop) (rw : ℕ → Desc.First.S → Bool)
  (ah : ℕ → String → Bool) (pr : ℕ) (H : LinkHoles) (l : Link Desc.First.S Desc.Claim)
  (pass : Desc.First.S → Desc.First.S → Prop)

/-- **The sentence at a letter for the piece's number.** -/
theorem calls_objects_pc (pc : ℕ) (ν : Wit Cells Tok MsgT → _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ a' w j, MaskOkCalls x D rad seatT ms (N.sent m 0) a' → j < a'.F.ns →
      (dataQ (N.sent m 0) a' (seatTab D.codes arr ms w)).mask j = ν w (.mask j))
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ runs m pc "objects")
    (hlink : Rd m = readersOfLink H l) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (St.at1 s Dt).mask j = Dt.mask j)
    (hMg : ∀ s y w, Mg.formsT m pc "objects" (pi, s) y w →
      (meaningForms D.codes arr ms Rd runs St after N wt rw ah Mg₀).formsT m pc "objects" (pi, s) y
        w)
    (hOk : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
      a.1.failed = none → Yes a b → SameBut a.1 b.1 →
      onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
      ∀ a', segAt? b.1 = some a' → MaskOkCalls x D rad seatT ms (N.sent m 0) a')
    (hBare : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
      a.1.failed = none → Yes a b →
      ∀ g, (Desc.K3.seatCalls claim).heard b.1 = some g → ∀ f ∈ g.rows.toList, Bare f) :
    ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
      Rc a → a.1.failed = none → Yes a b → SameBut a.1 b.1 →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
      onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
      ∀ w, Mg.formsT m pc "objects" (pi, b.1) (strsOf Fr b.2) w →
      K3Objects (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
        ν b.1 w := by
  intro a b ha hr hu hy hs _ hb w hf g F' hF hg
  exact formsT_objects_bare D.codes arr ms Rd runs St after N wt rw ah Mg₀ m pc pr H l
    (Desc.K3.seatCalls claim) hA x.fs x.lm x.F.next ν
    (MaskOkCalls x D rad seatT ms (N.sent m 0)) hrun hlink pass hpass hfind hSt hν pi b.1
    (strsOf Fr b.2) w (hMg _ _ _ hf) (hOk a b ha hr hu hy hs hb) g F' hF hg
    (hBare a b ha hr hu hy g hg)

variable (adr : HeadAdr) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (msgW : Wit Cells Tok MsgT → oW.Msg)

/-- The lookup's place "mask j" is what the messages hold at that address's seat. -/
theorem headNu_maskAt (w : Wit Cells Tok MsgT) (j : ℕ) (hj : j < x.ns) {z : Seat}
    (hz : seatCalls D x.link (.mask j) = some z) :
    headNu adr x tl D rad oW wOf nr nc seatT arr msgW w (.mask j) =
      (readAt D.codes (sigListCalls D rad x.link)
        (msgsOf D.codes (sigListCalls D rad x.link) seatT arr w) z).getD 0 := by
  have e : lyMask x.ns tl nr nc j = some (Sum.inl (Sum.inl ⟨j, hj⟩)) := by
    unfold lyMask
    rw [finOf_some hj]
    rfl
  show layMu x tl D rad oW wOf nr nc seatT arr msgW w (lyMask x.ns tl nr nc j) = _
  rw [e]
  show (valAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link)
    (msgsOf D.codes (sigListCalls D rad x.link) seatT arr w) (.mask j)).getD 0 = _
  unfold valAt
  rw [hz]
  rfl

variable (hB : maskCallsB D (sigListCalls D rad x.link) x.link x.ns = true)
include hB

/-- **THE MASK ROW's DICTIONARY, AT THE OUTPUT HEAD's LINK.** -/
theorem head_maskRow (own : List (ℕ × ℕ)) (a : Desc.K9.Part)
    (M : MaskOkCalls x D rad seatT ms own a) (w : Wit Cells Tok MsgT) (j : ℕ)
    (hj : j < a.F.ns) :
    (dataQ own a (seatTab D.codes arr ms w)).mask j =
      headNu adr x tl D rad oW wOf nr nc seatT arr msgW w (.mask j) := by
  obtain ⟨z, hz, e⟩ := calls_maskRead x D rad seatT arr ms own hB a M w j hj
  rw [e, headNu_maskAt x D rad seatT arr adr tl oW wOf nr nc msgW w j
    (Nat.lt_of_lt_of_le hj M.ns) hz]

/-- **THE SAME AT A LETTER rd.** -/
theorem head_maskRow_of (own : List (ℕ × ℕ)) (a : Desc.K9.Part)
    (M : MaskFrameCalls x D rad seatT own a) (w : Wit Cells Tok MsgT) (rd : ℕ × ℕ → MsgQ)
    (h1 : OneReader (ReadMsgOf (maskAddr x.ns) (seatCalls D x.link)) D.codes
      (sigListCalls D rad x.link) seatT (msgsOf D.codes (sigListCalls D rad x.link) seatT arr w)
      rd) (j : ℕ) (hj : j < a.F.ns) :
    (dataQ own a rd).mask j = headNu adr x tl D rad oW wOf nr nc seatT arr msgW w (.mask j) := by
  obtain ⟨z, hz, e⟩ := calls_maskRead_of x D rad seatT own hB a M _ rd h1 j hj
  rw [e, headNu_maskAt x D rad seatT arr adr tl oW wOf nr nc msgW w j
    (Nat.lt_of_lt_of_le hj M.ns) hz]

/-- **THE SENTENCE AT THE OUTPUT HEAD's CALLS.** -/
theorem calls_objects_head
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ runs m 3 "objects")
    (hlink : Rd m = readersOfLink H l) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (St.at1 s Dt).mask j = Dt.mask j)
    (hMg : ∀ s y w, Mg.formsT m 3 "objects" (pi, s) y w →
      (meaningForms D.codes arr ms Rd runs St after N wt rw ah Mg₀).formsT m 3 "objects" (pi, s) y
        w)
    (hOk : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
      a.1.failed = none → Yes a b → SameBut a.1 b.1 →
      onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
      ∀ a', segAt? b.1 = some a' → MaskOkCalls x D rad seatT ms (N.sent m 0) a')
    (hBare : ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
      a.1.failed = none → Yes a b →
      ∀ g, (Desc.K3.seatCalls claim).heard b.1 = some g → ∀ f ∈ g.rows.toList, Bare f) :
    ∀ (a b : Desc.First.S × Fr.E.Str) w, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
      a.1.failed = none → Yes a b → SameBut a.1 b.1 →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
      onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
      Mg.formsT m 3 "objects" (pi, b.1) (strsOf Fr b.2) w →
      K3Objects (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
        (headNu adr x tl D rad oW wOf nr nc seatT arr msgW) b.1 w :=
  fun a b w ha hr hu hy hs ho hb hf =>
    calls_objects_pc x D rad set seatT arr claim N Mg Mg₀ links ps pi k m Yes Rc ms Rd runs St
      after wt rw ah pr H l pass 3 (headNu adr x tl D rad oW wOf nr nc seatT arr msgW)
      (fun a' w j M hj =>
        head_maskRow x D rad seatT arr ms adr tl oW wOf nr nc msgW hB (N.sent m 0) a' M w j hj)
      hA hrun hlink hpass hfind hSt hMg hOk hBare a b ha hr hu hy hs ho hb w hf

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_objects_pc
#print axioms VerifiableInference.OnPublicFiles.head_maskRow
#print axioms VerifiableInference.OnPublicFiles.head_maskRow_of
#print axioms VerifiableInference.OnPublicFiles.calls_objects_head
