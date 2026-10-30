-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FormsOfMeans.lean: THE LINE "forms" OF K4Lines (Johnson/Road/K4/CloseAtTable.lean),
IN ITS OWN WORDS, at a promise behind that remembers the accepting run (keptFrom,
Johnson/Road/K4/CloseRefFillK.lean), over a letter Mg with the structure of equations K4Means
(Johnson/Road/K4/K4Means.lean): at every statement b of the chain that meets that promise and bears
no mark, the table of joints' item formsT m 3 "own" gives the sentence FormsT of the statement of
K4's law at the law's own Sem, QK.semOf part par.hp.tl.

  `item_of_means`: what the item says at Mg, by K4Means' equation for the field formsT, where the
    data's runs and reader at segment m are K4's two runs and a segment's readers.
  `forms_of_means`: THE LINE.
No new argument: run_of_from (Johnson/Road/K4/CloseAtTableK.lean) hands the accepting run back;
kept_of_yes (Johnson/Road/K4/KeptOfYes.lean); forms_at_sem (Johnson/Road/K4/FormsAtSem.lean).
Limits. QK, part and M are letters. PREMISES of forms_of_means, none paid here; the last five are
asked AT AN ACCEPTING RUN INSIDE THE TABLE's PROMISE IN FRONT, at a statement that bears no mark,
and speak of the verifier's state that the run leaves:
  E: K4Means at Mg and the data D · hRd, hruns: the data's reader and runs at segment m · hk: the
    place's parameters let the lookup state its own claims.
  asks: KeptAsks, InTAsks and the seat's tie at both runs: the conclusion of asks_of_means
    (Johnson/Road/K4/Riders/AsksAtMeans.lean), to the letter.
  arrB: the one test on the reads' array (readsArrayB, Johnson/Road/K4/ReadsArrayAt.lean).
  X: StatedAt of the data's letter St at the public parameters' tl
    (statedAt_bySort, Johnson/Road/K4/ArmLay.lean, has it at the one stated function).
  hm: below the ledger's number of slots the value's mask row is the table's data's.
  hM: inside the ranges of tl the value's matrices are M at the table's data.
The promise behind at the table (onQ at k + 1) and "no mark" behind are in the line's words and are
not spent. Met through Lean at no member. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.FormsAtSem
import Johnson.Road.K4.CloseAtTableK
import Johnson.Road.K4.K4Means

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4

open Iop OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub Own)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Road.K4.InT (InTAsks StatesAt)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Claim Link K9.LinkHoles K9.statesOfLink K9.readersOfLink
  K9.segAt?)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (Frame Piece onQ meansQ MsgT GQ second dataQ formsTQ seatTab)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)

variable [scl : Inst.Model.Scl] {Xi P Tok Cl Mm : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

omit scl in
/-- What the item formsT m 3 "own" says at Mg, under E hRd hruns. -/
theorem item_of_means (E : K4Means Mg D) {Hh : K9.LinkHoles} {l : Link S Claim}
    (hRd : D.Rd m = K9.readersOfLink Hh l)
    (hruns : D.runs m 3 "own" = [(2, "front"), (2, "back")]) {b : S × Fr.E.Str}
    {w : Wit (CellsK rows cols) Tok MsgT}
    (h : meansQ (Fr := Fr) D.N Mg (fun s => (Z, s)) (.formsT m 3 "own") b w) :
    ∀ x ∈ [(2, "front"), (2, "back")],
      formsTQ (K9.readersOfLink Hh l) D.St (D.N.sent m 0) x.1 x.2 b.1
        (seatTab D.cs D.arr D.ms w) := by
  have h' : Mg.formsT m 3 "own" (Z, b.1) (VerifiableInference.Desc.Sound.strsOf Fr b.2) w := h
  rw [E.formsT] at h'
  have h1 := h'.1
  rw [hruns, hRd] at h1
  exact h1

/-- **THE LINE "forms"**, under E hRd hruns hk · asks arrB X hm hM. -/
theorem forms_of_means (QK : Plan4K Mm S) (part : Wit (CellsK rows cols) Tok MsgT → Mm)
    (M : S → Bound GQ → Mats GQ) (E : K4Means Mg D) {Hh : K9.LinkHoles} {l : Link S Claim}
    (hRd : D.Rd m = K9.readersOfLink Hh l)
    (hruns : D.runs m 3 "own" = [(2, "front"), (2, "back")]) (hk : par.k3Runs = true)
    (asks : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∃ (P₀ : Pub) (o₀ : Own),
        KeptAsks par a.1 (behindOf seatS q a τ o G').1 P₀ o₀ ∧
        InTAsks (D.N.sent m 0) par a.1 (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "front" (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "back" (behindOf seatS q a τ o G').1)
    (arrB : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → readsArrayB par.hp (behindOf seatS q a τ o G').1 = true)
    (X : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ (w : Wit (CellsK rows cols) Tok MsgT) A' o' c,
        K9.segAt? (behindOf seatS q a τ o G').1 = some A' →
        (behindOf seatS q a τ o G').1.own? = some o' → A'.L.arrayOf[o'.v.iU3]? = some c →
        second (behindOf seatS q a τ o G').1 c = true →
        StatedAt D.St M (behindOf seatS q a τ o G').1 par.hp.tl o' c (par.hp.nU.getD 2 0)
          (dataQ (D.N.sent m 0) A' (seatTab D.cs D.arr D.ms w)))
    (hm : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ (w : Wit (CellsK rows cols) Tok MsgT) A' G,
        K9.segAt? (behindOf seatS q a τ o G').1 = some A' →
        (behindOf seatS q a τ o G').1.fork? = some G → ∀ j, j < G.ns →
        QK.maskAt (part w) j = (dataQ (D.N.sent m 0) A' (seatTab D.cs D.arr D.ms w)).mask j)
    (hM : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ (w : Wit (CellsK rows cols) Tok MsgT) A',
        K9.segAt? (behindOf seatS q a τ o G').1 = some A' →
        InRange par.hp.tl (QK.mats (part w))
          (M (behindOf seatS q a τ o G').1
            (dataQ (D.N.sent m 0) A' (seatTab D.cs D.arr D.ms w)))) :
    ∀ b w, keptFrom (tableOn0 D.N Mg Z links ps k) par q b →
      onQ D.N Mg links ps (fun s => (Z, s)) (k + 1) b → b.1.failed = none →
      meansQ (Fr := Fr) D.N Mg (fun s => (Z, s)) (.formsT m 3 "own") b w →
      FormsT seatS (QK.semOf part par.hp.tl) (frontRun par) formsBack b.1 w := by
  intro b w hb _ _ hi
  obtain ⟨a, τ, fo, o, G', ha, hu, Y, rfl⟩ := run_of_from hb
  obtain ⟨P₀, o₀, A, I, s1, s2⟩ := asks a τ fo o G' ha hu Y
  exact forms_at_sem QK part M Hh l (D.N.sent m 0) (fun w => seatTab D.cs D.arr D.ms w) w
    (kept_of_yes Y) A I.names (arrB a τ fo o G' ha hu Y) s1 s2 hk (X a τ fo o G' ha hu Y w)
    (item_of_means E hRd hruns hi) (hm a τ fo o G' ha hu Y w) (hM a τ fo o G' ha hu Y w)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.item_of_means
#print axioms OnBytes.Road.K4.forms_of_means
