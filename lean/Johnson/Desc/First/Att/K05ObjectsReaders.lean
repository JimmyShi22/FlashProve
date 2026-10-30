-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05ObjectsReaders.lean: kind K5: WHAT THE READERS OF A LINK ANSWER AT THE
LOOKUP's RUNS "objects" AND "guests" (hearing block 1): the rows of what the verifier has received
from the lookup argument, and nothing.

A LIGHT FILE, CUT OUT OF Johnson/Desc/First/Att/K05ObjectsBack.lean: the
four lemmas stand here TO THE LETTER, by program, but for TWO TOKENS, one in each reader's
proof: objects_reader calls the library's LinkJoin.lateOf_paid
(Johnson/Desc/First/Link/Law/HitemsMarks.lean) and guests_reader its LinkJoin.lateOf_self
(Johnson/Desc/First/Link/Law/HitemsStill.lean), and not the same two sentences in
Johnson/Desc/First/Att/K05JoinThere.lean and K05FormsMadeAt.lean. Why: the joins at the seated link
call them, without K05ObjectsBack.lean's five other K05 imports (the kind's whole tie).

Main names:
  objects_reader, guests_reader: the reader's answer at a list of runs in which find? finds the run,
    by what the run returns.
  objects_at_link, guests_at_link: the readers of a link give that answer, where the run stands
    behind the seat's guard.
THE LETTERS UNDER "FOR ALL": t free on purpose (a law of the readers' make); F, g pinned by two
equations at t; r, nm pinned by hf | hL.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05ReadersGuarded
import Johnson.Desc.First.StateLedger
import Johnson.Desc.First.Link.Law.HitemsMarks

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.K9 (RunOf readerOf statesOfLink readersOfLink LinkHoles lateOf ownRow)

/-- **The reader's answer at the run "objects"**, where a ledger is open, g was received and its rows are bare. r: the run, by what it returns. -/
theorem objects_reader {st : ℕ → List (RunOf First.S)} {b : ℕ} {nm : String}
    {r : ℕ → First.S → Except String (List Claim × First.S)} (claim : Aff → Claim)
    (hcl : ∀ f, (claim f).form = f ∧ (claim f).runs.isEmpty = true ∧ (claim f).eqFirst.isNone = true)
    (hf : ((st b).find? fun c => c.1 == "objects") = some (nm, r)) {t : First.S} {F : Fork} {g : Forest.Heard}
    (hF : t.fork? = some F) (hr : r 0 t = .ok (g.rows.toList.map claim, t.putFork (F.paid g.owedObjects)))
    (hb : ∀ f ∈ g.rows.toList, f.ents = #[]) :
    readerOf st b "objects" t = some { forms := g.rows.toList, late := [] } := by
  unfold readerOf
  rw [hf]
  show (match r 0 t, t.fork? with
    | .ok z, some F => _
    | _, _ => none) = _
  rw [hr, hF]
  have hG : (t.putFork (F.paid g.owedObjects)).fork? = some (F.paid g.owedObjects) := First.S.fork_putFork t F _ hF
  show ((t.putFork (F.paid g.owedObjects)).fork?.bind fun G => _) = _
  rw [hG]
  show (if ((g.rows.toList.map claim).all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) = true then
    some ({ forms := (g.rows.toList.map claim).map (·.form), late := lateOf F (F.paid g.owedObjects) } :
      VerifiableInference.Desc.K9.Read) else none) = _
  have hall : ((g.rows.toList.map claim).all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) = true := by
    refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨f, hfm, rfl⟩ := List.mem_map.1 hc
    obtain ⟨c1, c2, c3⟩ := hcl f
    rw [c1, c2, c3, hb f hfm]
    simp
  rw [if_pos hall, VerifiableInference.Desc.LinkJoin.lateOf_paid]
  have em : (g.rows.toList.map claim).map (·.form) = g.rows.toList := by
    rw [List.map_map]
    exact (List.map_congr_left fun f _ => (hcl f).1).trans (List.map_id _)
  rw [em]

/-- **The readers of a link give that answer.** r: the lot's run under "objects", by what it returns; in the chain it stands behind the seat's guard. -/
theorem objects_at_link (H : LinkHoles) (L : VerifiableInference.Desc.Link First.S Claim) (same : First.S → First.S → Bool)
    (claim : Aff → Claim)
    (hcl : ∀ f, (claim f).form = f ∧ (claim f).runs.isEmpty = true ∧ (claim f).eqFirst.isNone = true) {nm : String}
    {r : ℕ → First.S → Except String (List Claim × First.S)}
    (hL : ((statesOfLink L 1).find? fun c => c.1 == "objects") = some (guardC same (nm, r)))
    (hsame : ∀ s t : First.S, t.out = s.out → same s t = true)
    (hr : ∀ t F g, t.fork? = some F → t.lookHeard? = some g →
      r 0 t = .ok (g.rows.toList.map claim, t.putFork (F.paid g.owedObjects))) :
    ∀ (t : First.S) (F : Fork) (g : Forest.Heard), t.fork? = some F → t.lookHeard? = some g →
      (∀ f ∈ g.rows.toList, f.ents = #[]) →
      (readersOfLink H L).forms 1 "objects" t = some { forms := g.rows.toList, late := [] } :=
  fun t F g hF hg hb => hRds_of_link H L 1 "objects" t _ (by decide)
    (objects_reader (nm := nm) (r := (guardC same (nm, r)).2) claim hcl hL hF
      (guardC_yes same (nm, r) (hr t F g hF hg) (hsame _ _ (out_putFork t _))) hb)

/-- **The reader's answer at a run that states nothing and hands the state back** (the run "guests" of a block that is seated with no guest). -/
theorem guests_reader {st : ℕ → List (RunOf First.S)} {b : ℕ} {nm : String}
    {r : ℕ → First.S → Except String (List Claim × First.S)}
    (hf : ((st b).find? fun c => c.1 == "guests") = some (nm, r)) {t : First.S} {F : Fork} (hF : t.fork? = some F)
    (hr : r 0 t = .ok ([], t)) : readerOf st b "guests" t = some { forms := [], late := [] } := by
  unfold readerOf
  rw [hf]
  show (match r 0 t, t.fork? with
    | .ok z, some F => _
    | _, _ => none) = _
  rw [hr, hF]
  show (t.fork?.bind fun G => _) = _
  rw [hF]
  show (if (([] : List Claim).all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) = true then
    some ({ forms := ([] : List Claim).map (·.form), late := lateOf F F } : VerifiableInference.Desc.K9.Read) else none) = _
  rw [VerifiableInference.Desc.LinkJoin.lateOf_self]
  rfl

/-- The readers of a link give that answer. -/
theorem guests_at_link (H : LinkHoles) (L : VerifiableInference.Desc.Link First.S Claim) (same : First.S → First.S → Bool)
    {nm : String} {r : ℕ → First.S → Except String (List Claim × First.S)}
    (hL : ((statesOfLink L 1).find? fun c => c.1 == "guests") = some (guardC same (nm, r)))
    (hsame : ∀ s t : First.S, t.out = s.out → same s t = true) (hr : ∀ t, r 0 t = .ok ([], t)) :
    ∀ (t : First.S) (F : Fork), t.fork? = some F → (readersOfLink H L).forms 1 "guests" t = some { forms := [], late := [] } :=
  fun t F hF => hRds_of_link H L 1 "guests" t _ (by decide)
    (guests_reader (nm := nm) (r := (guardC same (nm, r)).2) hL hF (guardC_yes same (nm, r) (hr t) (hsame _ _ rfl)))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.objects_reader
#print axioms VerifiableInference.Desc.First.Att.P.objects_at_link
#print axioms VerifiableInference.Desc.First.Att.P.guests_reader
#print axioms VerifiableInference.Desc.First.Att.P.guests_at_link
