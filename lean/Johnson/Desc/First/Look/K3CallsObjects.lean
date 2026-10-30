-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
calls_objects_att, calls_objects_lay: no state of the verifier and no
witness is shown at which all premises hold.
Johnson/Desc/First/Look/K3CallsObjects.lean: the lookup on a link's CALLS AT THE TABLE OF JOINTS:
THE FIELD "objects" OF AttAtTableR AND LayAtTableR (Johnson/Desc/First/Look/K3AttAtTableR.lean,
K3LayAtTableR.lean), SIGN FOR SIGN, as a call of formsT_objects_bare
(Johnson/Top/H/Keep/FormsTObjects.lean) at the mask row's dictionary att_maskRow | lay_maskRow
(Johnson/Desc/First/Look/K3CallsMask.lean). Statements and proofs. A joining: no error term. NO
SOUNDNESS IS CLAIMED.

WHAT IT PAYS: formsT_objects_bare's premise hDict ("the one equation on the mask row"), which nobody
had at attNu | layNu. WHAT IT MOVES: see the premises.

OBJECT: Meaning.formsT at a run "objects"; K3Objects at attNu | layNu.
USER: K3CallsObjectsAt.lean, Johnson/Desc/Sound/MgAt/K3CallsObj.lean (the field objects of the two
  structures, and of AttTiesR | LayTiesR).
LETTERS: the structures' own, at Cl := Desc.Claim; the filling's (ms, Rd, runs, St, after, wt, rw,
  ah, Mg₀); pr, H, l, pass.
Main names:
  `calls_objects_nu`: the field's sentence at any reading ν of the places that has the dictionary.
  `calls_objects_att`, `calls_objects_lay`: at attNu, at layNu.

EACH PREMISE, AND WHO COULD PAY IT. hA, hrun, hlink, hpass, hfind, hSt: formsT_objects_bare's own:
they pass through. hMg: the table's meaning says formsT "objects" as the filling meaningForms does:
the composed meaning's lemma at that item. hB: a test on public data: "the mask row reaches the
place's number of slots". hOk: MaskOkCalls at the part of the verifier's state behind: facts along
the fold and a test on the list of members. hBare: the rows that the lookup's verifier keeps name no
entry of an array: a law of the sub-protocol's accepting.

Limits. It moves four debts and pays one.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsMask
import Johnson.Top.H.Keep.FormsTObjects
import Johnson.Desc.First.Look.K3CallsTies
import Johnson.Desc.First.Look.K3LayTies
import Johnson.Desc.First.Look.K3Borders
import Johnson.Desc.First.Look.K3CallsTurns
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc (Wit Link Strs)
open VerifiableInference.Desc.K9 (Readers segAt? readersOfLink statesOfLink LinkHoles)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)

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

/-- **The field's sentence, at any reading of the places that has the dictionary.** -/
theorem calls_objects_nu (ν : Wit Cells Tok MsgT → _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ a' w j, MaskOkCalls x D rad seatT ms (N.sent m 0) a' → j < a'.F.ns →
      (dataQ (N.sent m 0) a' (seatTab D.codes arr ms w)).mask j = ν w (.mask j))
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ runs m 2 "objects")
    (hlink : Rd m = readersOfLink H l) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (St.at1 s Dt).mask j = Dt.mask j)
    (hMg : ∀ s y w, Mg.formsT m 2 "objects" (pi, s) y w →
      (meaningForms D.codes arr ms Rd runs St after N wt rw ah Mg₀).formsT m 2 "objects" (pi, s) y
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
      ∀ w, Mg.formsT m 2 "objects" (pi, b.1) (strsOf Fr b.2) w →
      K3Objects (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
        ν b.1 w := by
  intro a b ha hr hu hy hs _ hb w hf g F' hF hg
  exact formsT_objects_bare D.codes arr ms Rd runs St after N wt rw ah Mg₀ m 2 pr H l
    (Desc.K3.seatCalls claim) hA x.fs x.lm x.F.next ν
    (MaskOkCalls x D rad seatT ms (N.sent m 0)) hrun hlink pass hpass hfind hSt hν pi b.1
    (strsOf Fr b.2) w (hMg _ _ _ hf) (hOk a b ha hr hu hy hs hb) g F' hF hg
    (hBare a b ha hr hu hy g hg)

variable (hB : maskCallsB D (sigListCalls D rad x.link) x.link x.ns = true)
include hB

/-- **THE FIELD objects OF AttAtTableR.** -/
theorem calls_objects_att (A : Attention.Shape) (tl : HTailF2)
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ runs m 2 "objects")
    (hlink : Rd m = readersOfLink H l) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (St.at1 s Dt).mask j = Dt.mask j)
    (hMg : ∀ s y w, Mg.formsT m 2 "objects" (pi, s) y w →
      (meaningForms D.codes arr ms Rd runs St after N wt rw ah Mg₀).formsT m 2 "objects" (pi, s) y
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
      ∀ w, Mg.formsT m 2 "objects" (pi, b.1) (strsOf Fr b.2) w →
      attObjects x A tl D rad seatT arr (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard b.1 w :=
  calls_objects_nu x D rad set seatT arr claim N Mg Mg₀ links ps pi k m Yes Rc ms Rd runs St after
    wt rw ah pr H l pass (attNu x A tl D rad seatT arr)
    (fun a' w j M hj => att_maskRow x D rad seatT arr ms (N.sent m 0) A tl hB a' M w j hj)
    hA hrun hlink hpass hfind hSt hMg hOk hBare

/-- **THE FIELD objects OF LayAtTableR.** -/
theorem calls_objects_lay (q : LayPub) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (msgW : Wit Cells Tok MsgT → oW.Msg)
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ runs m 2 "objects")
    (hlink : Rd m = readersOfLink H l) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (St.at1 s Dt).mask j = Dt.mask j)
    (hMg : ∀ s y w, Mg.formsT m 2 "objects" (pi, s) y w →
      (meaningForms D.codes arr ms Rd runs St after N wt rw ah Mg₀).formsT m 2 "objects" (pi, s) y
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
      ∀ w, Mg.formsT m 2 "objects" (pi, b.1) (strsOf Fr b.2) w →
      layObjects x q tl D rad oW wOf nr nc seatT arr msgW (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard b.1 w :=
  calls_objects_nu x D rad set seatT arr claim N Mg Mg₀ links ps pi k m Yes Rc ms Rd runs St after
    wt rw ah pr H l pass (layNu x q tl D rad oW wOf nr nc seatT arr msgW)
    (fun a' w j M hj =>
      lay_maskRow x D rad seatT arr ms (N.sent m 0) q tl oW wOf nr nc msgW hB a' M w j hj)
    hA hrun hlink hpass hfind hSt hMg hOk hBare

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_objects_nu
#print axioms VerifiableInference.OnPublicFiles.calls_objects_att
#print axioms VerifiableInference.OnPublicFiles.calls_objects_lay
