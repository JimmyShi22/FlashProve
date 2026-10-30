-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/StopsReadCells.lean: the proofs of the thirteen statements of
Johnson/FrontRoad/StopsReadCellsSpec.lean: under the pin the private abort tests of the parts that a
chain's play takes read of the prover's input nothing but what the pins' reader yields of the trace;
in the shared chain none is asked.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  The steps   stopAt_of_agree, rowStop_of_agree: a part's, and a list of parts', function of stops
      (Part.stopAt, rowStopAt, Johnson/Desc/ProofFile/Honest/Side.lean) is the same at two inputs at
      which the private abort tests answer the same. find_one: a small fact on lists. or_ne_hid,
      unseen_part, unseen_row: given no input, a part and a list of parts never stop by the private
      class.
  The thirteen proofs   stops_read_cells, chainStop_of_agree, pinned_stops_read_cells,
      first_chain_stops_read_cells, unseen_never_stops_privately,
      unseen_chain_never_stops_privately, shared_sees_none, other_stop_not_halves,
      firing_not_halves, agree_all, first_chain_agree, differing_not_agree, index_reader_fails.

How it fits. stops_read_cells: in the arm with parameters the one part is quietStop (smallStop cells
P) (windowShare P.1), whose test is smallStop cells P, which reads its input through askOfInput
(Johnson/Desc/ProofFile/Honest/K8/Part.lean): the cells of the trace alone; in the other arm both
sides are none. first_chain_stops_read_cells: the last member is of the kind frame (k8_places_front,
Johnson/FrontRoad/ParOwnChecks.lean), so no half stands there. agree_all: that no two halves stand
at one place makes the places distinct (nodup_of_twice,
Johnson/Desc/ProofFile/Honest/Law/Rule/FileOkOf.lean). All limits: the head of
Johnson/FrontRoad/StopsReadCellsSpec.lean. Not one of the release's goal statements.
-/
import Johnson.FrontRoad.StopsReadCellsSpec
import Johnson.FrontRoad.PinPublic
import Johnson.Desc.ProofFile.Honest.Law.Rule.FileOkOf

set_option autoImplicit false

namespace OnBytes.FrontRoad
open VerifierAndGoals (PublicFiles InScope readFiles)
open P5J (TS LaidAt)
open OnBytes.Maker (WholeD)
open AtPublicFiles.AtFiles (descZ)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par round)
open OnBytes.HonestTrace (matsOf)
open ProofFile.Honest (Placed Local Common Cells Why Face chainStopAt rowStopAt)
open ProofFile.Honest.K8 (smallStop smallFits windowShare)
open ProofFile.Honest.K9 (quietStop)

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/-! ## The steps -/

section
variable {V W X : Type}

/-- A part's function of stops is the same at two inputs at which its private abort test answers the
same. -/
theorem stopAt_of_agree (p : ProofFile.Honest.Part V W X) (u v : V) (h : ∀ l o, p.hid u l o = p.hid v l o)
    (loc ds : List Fmt.Drawn) : p.stopAt (some u) loc ds = p.stopAt (some v) loc ds := by
  have e : ∀ j, ((some u : Option V).bind fun w => p.hid w loc (ds.take j)) =
      ((some v : Option V).bind fun w => p.hid w loc (ds.take j)) := fun j => h loc (ds.take j)
  unfold ProofFile.Honest.Part.stopAt
  simp only [e]

/-- The same of a list of parts. -/
theorem rowStop_of_agree (u v : V) : ∀ (ps : List (ProofFile.Honest.Part V W X)),
    (∀ p ∈ ps, ∀ l o, p.hid u l o = p.hid v l o) → ∀ loc ds,
    rowStopAt (some u) ps loc ds = rowStopAt (some v) ps loc ds
  | [], _, _, _ => rfl
  | p :: ps, h, loc, ds => by
    show (p.stopAt (some u) loc (ds.take p.moves.length)).or
        (rowStopAt (some u) ps (loc ++ ds.take p.moves.length) (ds.drop p.moves.length)) =
      (p.stopAt (some v) loc (ds.take p.moves.length)).or
        (rowStopAt (some v) ps (loc ++ ds.take p.moves.length) (ds.drop p.moves.length))
    rw [stopAt_of_agree p u v (h p List.mem_cons_self),
      rowStop_of_agree u v ps (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- Among the one half at a place, the first half at that place is that half. -/
theorem find_one (a : Place) (ps : List (ProofFile.Honest.Part V W X)) :
    ([⟨a, ps⟩] : List (Placed V W X)).find? (fun g => g.place == a) = some ⟨a, ps⟩ := by
  rw [List.find?_cons_of_pos]
  exact beq_self_eq_true _

/-- Of two answers neither of which is the private class, «or» gives none that is. -/
theorem or_ne_hid {a b : Option Why} (ha : a ≠ some Why.hid) (hb : b ≠ some Why.hid) :
    a.or b ≠ some Why.hid := by
  cases a with
  | none => exact hb
  | some w => exact ha

/-- A part that is given no input never stops by its private abort test. -/
theorem unseen_part (p : ProofFile.Honest.Part V W X) (loc ds : List Fmt.Drawn) :
    p.stopAt none loc ds ≠ some Why.hid := by
  intro h
  unfold ProofFile.Honest.Part.stopAt at h
  obtain ⟨j, -, hj⟩ := List.exists_of_findSome?_eq_some h
  split at hj
  · cases hj
  · simp at hj

/-- The same of a list of parts. -/
theorem unseen_row : ∀ (ps : List (ProofFile.Honest.Part V W X)) (loc ds : List Fmt.Drawn),
    rowStopAt (none : Option V) ps loc ds ≠ some Why.hid
  | [], _, _ => fun h => by cases h
  | p :: ps, loc, ds =>
    or_ne_hid (unseen_part p loc _) (unseen_row ps _ _)

end

/-! ## The thirteen -/

theorem stops_read_cells : Spec.stops_read_cells := by
  intro S Cl W₀ Rc Xi Tr X par cells hs bs u v hH hS b hb g hg p hp l o
  have h' := hH b hb
  cases hq : par b.place with
  | none =>
    rw [hq] at h'
    have h2 := (h' g hg p hp).1
    rw [h2 u l o, h2 v l o]
  | some P =>
    rw [hq] at h'
    obtain ⟨g', hg', hparts⟩ := h'
    rw [hg] at hg'
    obtain rfl := Option.some.inj hg'
    rw [hparts] at hp
    obtain rfl := List.mem_singleton.1 hp
    have e : cells u.trace = cells v.trace := hS
    show ProofFile.Honest.K8.smallHid P.1 ⟨ProofFile.Honest.K8.cellsAtOf (cells u.trace) P.2, P.2.length⟩ l o =
      ProofFile.Honest.K8.smallHid P.1 ⟨ProofFile.Honest.K8.cellsAtOf (cells v.trace) P.2, P.2.length⟩ l o
    rw [e]

theorem chainStop_of_agree : Spec.chainStop_of_agree := by
  intro S Cl W₀ Rc Xi Tr X hs bs u v
  induction bs with
  | nil =>
    intro _ loc ds
    rfl
  | cons b bs ih =>
    intro hA loc ds
    have hT : StopsAgreeAt u v hs bs := fun b' hb' => hA b' (List.mem_cons_of_mem _ hb')
    have hH : ((hs.find? fun h => h.place == b.place).bind fun h =>
          rowStopAt (some u) h.parts loc (ds.take b.rounds.length)) =
        ((hs.find? fun h => h.place == b.place).bind fun h =>
          rowStopAt (some v) h.parts loc (ds.take b.rounds.length)) := by
      cases hf : hs.find? fun h => h.place == b.place with
      | none => rfl
      | some g => exact rowStop_of_agree u v g.parts (hA b List.mem_cons_self g hf) loc _
    show ((hs.find? fun h => h.place == b.place).bind fun h =>
          rowStopAt (some u) h.parts loc (ds.take b.rounds.length)).or
        (chainStopAt (some u) bs hs (loc ++ ds.take b.rounds.length)
          (ds.drop b.rounds.length)) =
      ((hs.find? fun h => h.place == b.place).bind fun h =>
          rowStopAt (some v) h.parts loc (ds.take b.rounds.length)).or
        (chainStopAt (some v) bs hs (loc ++ ds.take b.rounds.length)
          (ds.drop b.rounds.length))
    rw [hH, ih hT]

theorem pinned_stops_read_cells : Spec.pinned_stops_read_cells := by
  intro S Cl W₀ Rc Xi Tr X par cells hs bs u v h hS
  exact chainStop_of_agree hs bs u v
    (stops_read_cells par cells hs bs u v ((pin_iff par cells hs bs).1 h).2 hS)

theorem agree_all : Spec.agree_all := by
  intro S Cl W₀ Rc Xi Tr X hs bs u v hS hT hA g hg p hp l o
  have hf : (hs.filter fun h => !(bs.any fun b => b.place == h.place)) = [] :=
    List.map_eq_nil_iff.1 hS
  have h1 := List.filter_eq_nil_iff.1 hf g hg
  have h2 : (bs.any fun b => b.place == g.place) = true := by
    cases hx : (bs.any fun b => b.place == g.place) with
    | true => rfl
    | false =>
      exact absurd (show (!(bs.any fun b => b.place == g.place)) = true by rw [hx]; rfl) h1
  obtain ⟨b, hb, e⟩ := List.any_eq_true.1 h2
  have eb : b.place = g.place := by simpa using e
  have hex : (hs.find? fun h => h.place == b.place).isSome = true :=
    List.find?_isSome.2 ⟨g, hg, by rw [eb]; exact beq_self_eq_true _⟩
  obtain ⟨g', hg'⟩ := Option.isSome_iff_exists.1 hex
  have ep : g'.place = b.place := by simpa using List.find?_some hg'
  have eg : g' = g := List.inj_on_of_nodup_map (ProofFile.Honest.nodup_of_twice hT)
    (List.mem_of_find?_eq_some hg') hg (ep.trans eb)
  subst eg
  exact hA b hb g' hg' p hp l o

theorem first_chain_agree : Spec.first_chain_agree := by
  intro Z Zp Np cF scope pp hr D r L W₀ Rc Xi Tr X mats cells hs u v h hn hS b hb g hg
  have hA := stops_read_cells (parOwn Zp mats) cells hs _ u v ((pin_iff _ cells hs _).1 h).2 hS
  have hl := (k8_places_front Z Zp Np cF scope hr L).2
  obtain ⟨bl, hbl, hk⟩ := Option.map_eq_some_iff.1 hl
  have hfl : (descZ Zp Np cF).first.blocksInOrder.dropLast ++ [bl] = (descZ Zp Np cF).first.blocksInOrder :=
    List.dropLast_append_getLast? bl hbl
  rw [← hfl] at hb
  rcases List.mem_append.1 hb with hb | hb
  · exact hA b hb g hg
  · obtain rfl := List.mem_singleton.1 hb
    have hp : g.place = b.place := by simpa using List.find?_some hg
    exact absurd (hp ▸ hk) (hn g (List.mem_of_find?_eq_some hg))

theorem first_chain_stops_read_cells : Spec.first_chain_stops_read_cells := by
  intro Z Zp Np cF scope pp hr D r L W₀ Rc Xi Tr X mats cells hs u v h hn hS
  exact chainStop_of_agree hs _ u v
    (first_chain_agree Z Zp Np cF scope hr L mats cells hs u v h hn hS)

theorem unseen_never_stops_privately : Spec.unseen_never_stops_privately := by
  intro V W X p loc ds
  exact unseen_part p loc ds

theorem unseen_chain_never_stops_privately : Spec.unseen_chain_never_stops_privately := by
  intro S Cl V W X bs hs
  induction bs with
  | nil =>
    intro loc ds h
    cases h
  | cons b bs ih =>
    intro loc ds
    show ((hs.find? fun h => h.place == b.place).bind fun h =>
          rowStopAt (none : Option V) h.parts loc (ds.take b.rounds.length)).or
        (chainStopAt (none : Option V) bs hs (loc ++ ds.take b.rounds.length)
          (ds.drop b.rounds.length)) ≠ some Why.hid
    refine or_ne_hid ?_ (ih _ _)
    cases hs.find? fun h => h.place == b.place with
    | none =>
      intro h
      cases h
    | some g => exact unseen_row g.parts loc _

theorem shared_sees_none : Spec.shared_sees_none := by
  intro W₀ Rc Ky w
  rfl

theorem other_stop_not_halves : Spec.other_stop_not_halves := by
  intro S Cl W₀ Rc Xi Tr X par cells b P p u l o hp hne hH
  have h' := hH b List.mem_cons_self
  rw [hp] at h'
  obtain ⟨g, hg, hparts⟩ := h'
  rw [find_one] at hg
  obtain rfl := Option.some.inj hg
  have e1 : p = quietStop (smallStop cells P) (windowShare P.1) := (List.cons.inj hparts).1
  exact hne (congrArg
    (fun q : ProofFile.Honest.Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X => q.hid u l o) e1)

theorem firing_not_halves : Spec.firing_not_halves := by
  intro S Cl W₀ Rc Xi Tr X par cells b p u l o e hp he hH
  have h' := hH b List.mem_cons_self
  rw [hp] at h'
  have h2 := (h' ⟨b.place, [p]⟩ (find_one _ _) p
    List.mem_cons_self).1 u l o
  rw [he] at h2
  cases h2

theorem differing_not_agree : Spec.differing_not_agree := by
  intro S Cl W₀ Rc Xi Tr X b p u v l o hne hA
  exact hne (hA b List.mem_cons_self ⟨b.place, [p]⟩
    (find_one _ _) p List.mem_cons_self l o)

theorem index_reader_fails : Spec.index_reader_fails := by
  intro S Cl Rc Xi Tr X par cells b sh rc x tr hs
  refine ⟨rfl, fun hA => ?_, fun hH => ?_⟩
  · have e : (some "" : Option String) = none :=
      hA b List.mem_cons_self _ (find_one _ _) _
        List.mem_cons_self [] []
    cases e
  · cases hq : par b.place with
    | none =>
      exact firing_not_halves par cells b _ ⟨true, rc, x, tr⟩ [] [] "" hq rfl hH
    | some P =>
      refine other_stop_not_halves par cells b P _ ⟨true, rc, x, tr⟩ [] [] hq (fun e => ?_) hH
      have e' : (some "" : Option String) = none := e
      cases e'

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.stopAt_of_agree
#print axioms OnBytes.FrontRoad.rowStop_of_agree
#print axioms OnBytes.FrontRoad.stops_read_cells
#print axioms OnBytes.FrontRoad.chainStop_of_agree
#print axioms OnBytes.FrontRoad.pinned_stops_read_cells
#print axioms OnBytes.FrontRoad.first_chain_stops_read_cells
#print axioms OnBytes.FrontRoad.unseen_never_stops_privately
#print axioms OnBytes.FrontRoad.shared_sees_none
#print axioms OnBytes.FrontRoad.other_stop_not_halves
#print axioms OnBytes.FrontRoad.firing_not_halves
#print axioms OnBytes.FrontRoad.or_ne_hid
#print axioms OnBytes.FrontRoad.unseen_part
#print axioms OnBytes.FrontRoad.unseen_row
#print axioms OnBytes.FrontRoad.agree_all
#print axioms OnBytes.FrontRoad.first_chain_agree
#print axioms OnBytes.FrontRoad.unseen_chain_never_stops_privately
#print axioms OnBytes.FrontRoad.differing_not_agree
#print axioms OnBytes.FrontRoad.index_reader_fails
#print axioms OnBytes.FrontRoad.find_one
