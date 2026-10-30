-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/GrownQuiet.lean: quietMaker AND quiet_lot HAVE NO DECLARATION HERE: THEY STAND IN `QuietLot`, WHICH THIS FILE IMPORTS: so that no name of ours is declared by two files. «mark» IS PAID: Quiet HAS A FOURTH CLAUSE («a mark that stands stays as it is»: Quiet.mark): hands_quiet_lot AND hear_quiet ASK NO PREMISE mark. OVER THE BASE (N) WITH L25's RIDER 5: e₁ AT THE PROOF FILE, THE HALF THAT READS THE VERIFIER's STATE ALONE: OUR OWN LINE OF THE LEDGER: THE 101 QUIET ROWS OF THE KINDS K3 · K4 · K5 · K6 · K8 · K11: FIVE OF Hands' SIX FIELDS PAID
(mark · shape · rows · members · book); more IS A PREMISE.
ON WORDS: «the state» is the value of type S that the description's fold carries from block to block (our earlier files call it «the record»).
OBJECT. The lot's own block b' at (1, some l, i + 1, k), k one of the six kinds: the field «hear» of `Shares` at these kinds. USER. The join.
CALLED, NOT TYPED: our own house's Whole Quiet at the seated constants (Johnson/Goal/Meaning/RecSeated.lean: theStated_quiet · blockAtC_quiet · k5AtN_quiet · seatedClaims_quiet · k8Whole_quiet · headMerge11_quiet) and StandKept (Johnson/IMR/StandKept.lean: stand_of_quiet) · shape_step
(Johnson/Desc/First/Link/Law/RbDef.lean) · `same_at` | `quiet_at` (the kernel's yes on the written list) · `hands_quiet`.

  keeps4_of_enters  Enters (the statement, the state's book and the count of roots are as they were) gives Keeps4.
  group_kept        a Quiet yes leaves the open link's whole state of the calls (L.check: its group, its frame, its rows): so the door's «K9.groupIs (m)» | «K10.groupIs (m)» are KEPT at these 101 rows (kept, not made).
  (in `QuietLot`:) quietMaker k      k is one of K3 · K4 · K5 · K6 · K8 · K11.
  (in `QuietLot`:) quiet_lot         (no scope; every o) a block of the seat's lots of one of the six kinds: EVERY YES OF ITS DECISION IS Quiet. Kind by kind, off the lot's own text.
  shape_kept        shapeAt passes from a place to the next where the table says the same stand, link and mayWait and the yes keeps StandKept.
  hands_quiet_lot   AT THE WRITTEN LIST: for a lot's block b' of one of the six kinds at placesW[k]: Hands N linksW placesW E ft k b', from: the plan's two counts are the same at the two places (hT | hM: counts_of_told | counts_step pay them under part 5's bookFit, past a block that tells
                    nothing) · more.

  hear_quiet        the same IN THE LETTERS OF THE FIELD «hear» of `Shares`: at l < 25, i < nAt l, k one of the six.

What is not claimed. more: E is a letter. hT | hM. No soundness.
-/
import Johnson.IMR.QuietLot
import Johnson.IMR.GrownJoin
import Johnson.IMR.K3Seat
import Johnson.IMR.K5Seat
import Johnson.IMR.K8Seat
import Johnson.IMR.StandKept
import Johnson.Desc.First.Link.Law.RbDef

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Place KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers shapeAt standAt mayWait)
open VerifiableInference.Desc.Keeps (Whole Decides)
open Meaning.K2 (Quiet Enters StandKept)
open ProofFile (Cl)

theorem keeps4_of_enters {s s' : S} (h : Enters s s') : Keeps4 s s' :=
  ⟨by rw [h.1], by rw [h.2.2.1], by rw [h.2.2.1], by rw [h.1]⟩

/-- **The group that the open link's context names is as it was** («K9.groupIs (m)» | «K10.groupIs (m)»: kept at a Quiet yes): Quiet keeps the open link's whole state of the calls. -/
theorem group_kept {s s' : S} (q : Quiet s s') :
    s'.link?.map (·.check) = s.link?.map (·.check) := by
  have h := q.open
  unfold Meaning.K2.openOf at h
  have h2 := congrArg (Option.map Prod.fst) h
  simpa [Option.map_map, Function.comp_def] using h2

/-- shapeAt passes from a place to the next where the table says the same and the yes keeps the stand. -/
theorem shape_kept {links : List ModelPart} {p p' : Place} {s s' : S}
    (h : shapeAt links (some p) s = true) (hS : StandKept s s')
    (hat : standAt links p' = standAt links p) (hpl : p'.link = p.link)
    (hmw : mayWait links p' = mayWait links p) : shapeAt links (some p') s' = true := by
  refine VerifiableInference.Desc.LinkJoin.shape_step links p p' s s' h hS.1 hat hpl ?_ hS.2.2
  have h1 : (s.noneWaits || mayWait links p) = true := by
    unfold shapeAt at h
    simp only [Bool.and_eq_true] at h
    exact h.1.2
  rcases Bool.or_eq_true_iff.1 h1 with a | a
  · exact Or.inl (hS.2.1 a)
  · exact Or.inr (hmw.trans a)

/-- **OUR LINE OF THE LEDGER: A LOT's BLOCK OF ONE OF THE SIX KINDS AT THE WRITTEN LIST's NUMBER k.** -/
theorem hands_quiet_lot {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b' : Block S Cl} (hb : b' ∈ L.blocks G) (hk : quietMaker b'.place.kind = true)
    {N : Numbers} {E : ℕ → S → Bool} {ft k : ℕ} {p' : Place} (hp : placesW[k]? = some b'.place)
    (hp' : placesW[k + 1]? = some p')
    (hT : N.treesAt placesW[k + 1]? = N.treesAt placesW[k]?)
    (hM : N.msgsAt placesW[k + 1]? = N.msgsAt placesW[k]?)
    (more : ∀ s s', Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E k s = true → E (k + 1) s' = true) :
    Hands N linksW placesW E ft k b' := by
  have hq : ∀ s s', Yes ft b' s s' → Quiet s s' := by
    rintro s s' ⟨rs, cols, n, e⟩
    exact quiet_lot hL hb hk s _ _ s'
      ((VerifiableInference.Desc.Sound.step_ok_iff ft b' s s' rs cols n).1 e).2.2.2
  have hkeep : keeper b'.place = true := by
    unfold quietMaker at hk
    unfold keeper
    simp only [Bool.or_eq_true] at hk ⊢
    exact Or.inl hk
  have hqk : quietKind b'.place.kind = true := by
    unfold quietMaker at hk
    unfold quietKind
    simp only [Bool.or_eq_true] at hk ⊢
    rcases hk with ((((a | a) | a) | a) | a) | a <;> simp [a]
  obtain ⟨e1, e2, e3⟩ := same_at hp hp' hkeep
  refine hands_quiet hp (quiet_at hp hqk) hT hM (fun s s' hy _ _ => keeps4_of_enters (hq s s' hy).1)
    (fun s s' hy h => (hq s s' hy).mark h) (fun s s' hy _ _ hx => ?_) more
  rw [hp']
  have h0 := (xk_parts hx).1
  rw [hp] at h0
  exact shape_kept h0 (Meaning.K2.stand_of_quiet (hq s s' hy)) e1 e2 e3

/-- **The field «hear» of the join's Shares, at the six kinds**, in the field's own letters. -/
theorem hear_quiet {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {N : Numbers} {E : ℕ → S → Bool} {ft : ℕ}
    {l i : ℕ} {k : KindName} {b' : Block S Cl} (hl : l < 25) (hi : i < nAt l)
    (hk : (VerifiableInference.Desc.First.kindsBeforeBatching (subAt l) (l == 0))[i]? = some k)
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hp : b'.place = { chain := 1, link := some l, piece := i + 1, kind := k })
    (hq : quietMaker k = true)
    (hT : N.treesAt placesW[14 * l + i + 2 + 1]? = N.treesAt placesW[14 * l + i + 2]?)
    (hM : N.msgsAt placesW[14 * l + i + 2 + 1]? = N.msgsAt placesW[14 * l + i + 2]?)
    (more : ∀ s s', Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + i + 2) s = true → E (14 * l + i + 2 + 1) s' = true) :
    Hands N linksW placesW E ft (14 * l + i + 2) b' := by
  obtain ⟨L, hL, hb⟩ := hlot
  obtain ⟨p', hp', -⟩ := number_at (l := l) (j := i + 2) hl (by omega)
  refine hands_quiet_lot hL hb (by rw [hp]; exact hq) (p' := p') ?_ ?_ hT hM more
  · rw [hp]
    exact hear_number_at hl hk hi
  · rw [show 14 * l + i + 2 + 1 = 14 * l + 1 + (i + 2) by omega]
    exact hp'

end IM

#print axioms IM.hear_quiet
#print axioms IM.group_kept
#print axioms IM.shape_kept
#print axioms IM.hands_quiet_lot
