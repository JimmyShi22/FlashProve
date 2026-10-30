-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05WorthAtTable.lean: kind K5: WHAT THE KIND's LAW ASKS OF THE RELATION
BEHIND ITS BLOCK ON THE FORMS' WORTH (BillsWorthJ, Johnson/Desc/First/Att/K05BillsWorth.lean;
K5Behind.worth, Johnson/Desc/First/Att/K05LawOne.lean) FROM THE TABLE OF JOINTS' OWN SENTENCE ON THE
ITEMS THAT THE KIND's ROW OPENS (formsTQ, Johnson/Desc/Sound/FormsQ.lean):
"the forms of a run are worth 0", in front of the segment's second sending.

IS IT EMPTY HERE? NO MEMBER IS SHOWN. Three premises bear all the weight, and none is shown at any
filling: hR', hRd, hTie.

The matter. Both sentences say "a form is worth 0 in a world". The worlds are two:
  the law's: G.worldOf gl mask entry: under slot j: shown_j - factor_j * mask j off the ledger G
    behind the hearing; mask: the mask row's entries read off the law's part of the witness; entry:
    each entry read as its table's stated sum over the matrices of that part (entryOf).
  the table's: worldOwn a R.late (St.at1 s (dataQ own a rd)): under a slot that is not late the same
    off the open segment's ledger, at the mask row of the data; an entry is the cell of the array
    that the link's list names, in the data passed through the letter St.at1.
A form's worth reads a world at the slots and the entries that the form names, and nowhere else
(value_eq, FormsQ.lean). So the two sentences are one wherever the worlds agree THERE.

Main names:
  `WorldTie St own s a rd mask entry fs`: the two worlds agree at what the forms of fs name: (mask)
    at every slot; (entry) at every entry.
  `worth_of_formsTQ`: formsTQ at a run whose reader hands no late slot, and WorldTie at a list of
    the reader's forms, give AllZero of that list at the ledger's own world.
  `billsWorthJ_of_formsT`: **BillsWorthJ, at K5Behind.worth's letters** (statements: a record with
    anything Y beside it; there Y is the frame's oracles), under:
    hR': the relation behind holds formsTQ AT THE DRIVER's OWN PAIRS (2, "first"), (2, "second") and
      (2, "join"): the table's item at (3, "own") is, as reported,
      the conjunction of the sentences at the pairs that runsOf gives it ("keys" gathers no form);
      there is no sentence and no reader at the table's own names;
    hRd: at the record behind the lay, and every tuple with Returns: the reader's three lists have
      no late slot and hold what "first" gathers, what "second" gathers, and the join's form;
    hTie: AT THE SAME TUPLES WITH Returns, AND AT NO OTHER: WorldTie at the law's own mask and
      entry, at just these forms. (The law's entry reads the tuple's own list of tables: at a tuple
      that the run does not return the tie would ask another sum of the same cell.)
A CARRIAGE BETWEEN TWO WORLDS, NO PAYMENT: hR' is the same sentence in the table's world.
WHAT hTie's TWO CLAUSES ASK, IN WORDS. (mask): entry j of the segment's mask row, read off the
witness by seat through the layout and left alone by St.at1, is what the law's reader valAt gives at
(.mask j) of its part: two readers of one message. (entry): at the vector of reads (one row),
St.at1's stated function of the first sending's arrays at place i is entryOf's sum of the table at
place i over the law's matrices: a condition on whoever fills St.
Limits. A RULE OVER LETTERS. The lookup's run "planes" is not spent: the law's worth does not name
it.
No soundness of the protocol is claimed. Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.Att.K05BillsWorth
import Johnson.Desc.First.Att.K05BehindLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated formsTQ worldOwn dataQ value_eq slotW_ledger)
open VerifiableInference.Desc.K9 (Readers segAt? lateAt)
open K5Law (entryOf oldOf AllZero)

/-- **The table's world and a ledger's own world agree at what the forms name.** -/
structure WorldTie (St : Stated) (own : List (ℕ × ℕ)) (s : First.S) (a : VerifiableInference.Desc.K9.Part)
    (rd : ℕ × ℕ → MsgQ) (mask : ℕ → GQ) (entry : ℕ → ℕ → ℕ → GQ) (fs : List Aff) : Prop where
  mask : ∀ f ∈ fs, ∀ y ∈ f.slots.toList, (St.at1 s (dataQ own a rd)).mask y.1 = mask y.1
  entry : ∀ f ∈ fs, ∀ y ∈ f.ents.toList,
    (worldOwn a [] (St.at1 s (dataQ own a rd))).entry y.tree y.row y.idx = entry y.tree y.row y.idx

theorem WorldTie.mono {St : Stated} {own : List (ℕ × ℕ)} {s : First.S}
    {a : VerifiableInference.Desc.K9.Part} {rd : ℕ × ℕ → MsgQ} {mask : ℕ → GQ}
    {entry : ℕ → ℕ → ℕ → GQ} {fs fs' : List Aff} (T : WorldTie St own s a rd mask entry fs)
    (h : ∀ f ∈ fs', f ∈ fs) : WorldTie St own s a rd mask entry fs' :=
  ⟨fun f hf => T.mask f (h f hf), fun f hf => T.entry f (h f hf)⟩

/-- **The table's sentence gives the worth at the ledger's own world**, at every list of forms of
the reader's at which the worlds are tied. -/
theorem worth_of_formsTQ (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (s : First.S) (rd : ℕ × ℕ → MsgQ) (h : formsTQ Rd St own piece run s rd)
    {a : VerifiableInference.Desc.K9.Part} (ha : segAt? s = some a)
    {R : VerifiableInference.Desc.K9.Read} (hR : Rd.forms piece run s = some R) (hl : R.late = [])
    (mask : ℕ → GQ) (entry : ℕ → ℕ → ℕ → GQ) (fs : List Aff) (hsub : ∀ f ∈ fs, f ∈ R.forms)
    (T : WorldTie St own s a rd mask entry fs) :
    AllZero Reading.gl (a.F.worldOf Reading.gl mask entry) fs := by
  obtain ⟨a', R', ha', hR', _, hf⟩ := h
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  obtain rfl : R' = R := Option.some.inj (hR'.symm.trans hR)
  intro f hm
  have h0 := (hf f (hsub f hm)).2
  rw [hl] at h0
  rw [← h0]
  refine value_eq _ _ f (fun y hy => (T.entry f hm y hy).symm) (fun y hy => ?_)
  show Reading.gl.val (a'.F.vp.getD y.1 zeroE) - Reading.gl.val (a'.F.mf.getD y.1 zeroE) * mask y.1 = _
  rw [← T.mask f hm y hy]
  exact (slotW_ledger a'.F [] _ y.1 rfl).symm

section
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

/-- **THE FORMS' WORTH, AS THE KIND's LAW ASKS IT OF THE RELATION BEHIND, FROM THE TABLE's TWO
ITEMS.** -/
theorem billsWorthJ_of_formsT {W Y : Type} (S : Attention.Shape) (ns : ℕ) (N : Nums)
    (A0 : Attention.Plan) (Kc : ℕ) (k3 : Runs.PadIn) (nW : ℕ) (tj : OnBytes.K.Kc.Tape)
    (gOf : First.S × Y → Forest.Heard) (lk0 : First.S × Y → LookIn)
    (xr : Params.AttentionRounds) (on : First.S × Y → Prop)
    (part : W → (attSg x D rad).Msg) (R' : First.S × Y → W → Prop)
    (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ)) (rdOf : W → ℕ × ℕ → MsgQ)
    (hR' : ∀ b w, R' b w → formsTQ Rd St own 2 "first" b.1 (rdOf w) ∧
      formsTQ Rd St own 2 "second" b.1 (rdOf w) ∧ formsTQ Rd St own 2 "join" b.1 (rdOf w))
    (hRd : ∀ (a b : First.S × Y) (w : W), on a → R' b w → ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i Kc l₁ l₂ jn k3 kf G tj xj tl nW (lk0 a) →
        ∃ R₁ R₂ R₃ : VerifiableInference.Desc.K9.Read,
          Rd.forms 2 "first" b.1 = some R₁ ∧ R₁.late = [] ∧ (∀ f ∈ l₁, f ∈ R₁.forms) ∧
          Rd.forms 2 "second" b.1 = some R₂ ∧ R₂.late = [] ∧ (∀ f ∈ l₂, f ∈ R₂.forms) ∧
          Rd.forms 2 "join" b.1 = some R₃ ∧ R₃.late = [] ∧ xj.1 ∈ R₃.forms)
    (hTie : ∀ (a b : First.S × Y) (w : W), on a → R' b w → ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i Kc l₁ l₂ jn k3 kf G tj xj tl nW (lk0 a) →
        ∀ pt : VerifiableInference.Desc.K9.Part, segAt? b.1 = some pt →
          WorldTie St own b.1 pt (rdOf w) ((attLin x S tl D rad Ex Wp α ns N).maskOf (part w))
            (entryOf Reading.gl tl Kc (matsOfMsg x tl D rad (part w))
              (oldOf S (gOf a) i).t.funs.toList) (l₁ ++ l₂ ++ [xj.1])) :
    BillsWorthJ x tl D rad Ex Wp α S ns N A0 Kc k3 nW tj gOf lk0 seatSO xr
      (fun a : First.S × Y => a.1) (fun a : First.S × Y => a.1) on part R' := by
  intro a b w ha hR F G h L h1 h2 s1 s2 s3 l i l₁ l₂ jn kf xj Rt
  obtain ⟨R₁, R₂, R₃, e1, l1, m1, e2, l2, m2, e3, l3, m3⟩ :=
    hRd a b w ha hR F G h L h1 h2 s1 s2 s3 l i l₁ l₂ jn kf xj Rt
  obtain ⟨q1, q2, q3⟩ := hR' b w hR
  obtain ⟨att, e, _, eb⟩ := lay_is h1 h2
  have eb' : b.1 = behind a.1 att h G := eb
  have hp : segAt? b.1 = segAt? (behind a.1 att h G) := by rw [eb']
  obtain ⟨pt, _, hpt, _⟩ := id q1
  have hF : pt.F = G := by
    rw [hp] at hpt
    have : (segAt? (behind a.1 att h G)).map (·.F) = some G := rfl
    rw [hpt] at this
    exact Option.some.inj this
  have T := hTie a b w ha hR F G h L h1 h2 s1 s2 s3 l i l₁ l₂ jn kf xj Rt pt hpt
  have z1 := worth_of_formsTQ Rd St own 2 "first" b.1 (rdOf w) q1 hpt e1 l1 _ _ l₁ m1
    (T.mono fun f hf => List.mem_append_left _ (List.mem_append_left _ hf))
  have z2 := worth_of_formsTQ Rd St own 2 "second" b.1 (rdOf w) q2 hpt e2 l2 _ _ l₂ m2
    (T.mono fun f hf => List.mem_append_left _ (List.mem_append_right _ hf))
  have z3 := worth_of_formsTQ Rd St own 2 "join" b.1 (rdOf w) q3 hpt e3 l3 _ _ [xj.1]
    (fun f hf => by rw [List.mem_singleton.1 hf]; exact m3)
    (T.mono fun f hf => List.mem_append_right _ hf)
  rw [hF] at z1 z2 z3
  refine ⟨fun f hf => ?_, z3 _ (List.mem_singleton.2 rfl)⟩
  rcases List.mem_append.1 hf with hf | hf
  · exact z1 f hf
  · exact z2 f hf

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.worth_of_formsTQ
#print axioms VerifiableInference.Desc.First.Att.P.billsWorthJ_of_formsT
