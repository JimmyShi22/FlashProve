-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/MemsSame.lean: THE TYPED ORACLE MESSAGES OF `msAt` (Johnson/P5T/MemberLists.lean) HAVE,
AS A SET, THE SHAPES AND (tree, tenant)s OF THE FIRST CHAIN's ENTRIES WITH AN OUT-OF-DOMAIN SAMPLE
(Johnson/P5T/PlanSeats.lean): A THEOREM BY `memberLists`' MAKE, UNDER TWO TESTS WITH CODE. One
definition, six theorems.

Why. `memberLists` takes each typed oracle message's (tree, tenant) from the entries of `planSeats`,
and its shape (with the radius) from the rows of the sendings (sendRowsOf). Laws in other files ask
that the two lists of pairs (shape, (tree, tenant)) have the same members.
  `sendsBelowB rows ps`: every entry with a sample has its sending's number below the number of the
    first chain's rows. `membersFault` DOES NOT SEE THIS: such an entry would be in no typed oracle
    message's list.
  `pairs_of_sending`, `plain_of_list`, `shapes_of_noFault`, `plain_members`: the steps.
  `mems_same`: at any rows and entries: where `membersFault` finds nothing and `sendsBelowB`
    accepts, the two lists of pairs have the same members.
  `memsSame_at`: so at `msAt Z lay` and `planSeats Z Z.D.1`, the two tests at the rows that `msAt`
    itself reads ((rowsAt? Z.pol lay Z.KL).getD []). WHERE THE ROWS' MAKER REFUSES THESE ROWS ARE
    EMPTY: `sendsBelowB` then rejects as soon as one entry has a sample: no third premise is wanted.

Limits. As sets: nothing on the order or on how often a pair stands. Both tests read the rows of the
sendings: this file stands over Johnson/G/LinkSig.lean. Nothing on the radii. Nothing on soundness.

-/
import Johnson.P5T.MemberLists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc.Sound (Mem Sending msOf sendsOf membersOf seatOf)

/-- Every entry with a sample has its sending's number below the number of the first chain's rows.
-/
def sendsBelowB (rows : List Johnson.G.SendRow) (ps : List PSeat) : Bool :=
  ps.all fun p => !p.smpd || decide (p.send < (firstRows rows).length)

/-- One sending: its typed oracle messages' pairs are its entries' pairs. -/
theorem pairs_of_sending (l : List (OnBytes.OracleShape × Nat)) (mine : List PSeat)
    (h : mine.map (·.shape) = l.map (·.1)) :
    (List.finRange l.length).map
        (fun i => ((l.get i).1, (mine.map (·.seat)).getD i.val (0, 0))) =
      mine.map fun p => (p.shape, p.seat) := by
  have hl : mine.length = l.length := by simpa using congrArg List.length h
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    have hi : i < mine.length := by simpa using h2
    have hi' : i < l.length := hl ▸ hi
    have e := congrArg (fun L => L[i]?) h
    simp [hi, hi'] at e
    simp [hi, e]

/-- A list of sendings. -/
theorem plain_of_list (T : List (Johnson.G.SendRow × Nat)) (ps : List PSeat)
    (h : ∀ r ∈ T, (ps.filter fun p => p.send == r.2 && p.smpd).map (·.shape) =
      r.1.sampled.map (·.1)) :
    (membersOf (T.map fun r => Sending.ofLists r.1.sampled
        ((ps.filter fun p => p.send == r.2 && p.smpd).map (·.seat)))).map
        (fun x => ((x.1.l.get x.2).1, seatOf x)) =
      T.flatMap fun r => (ps.filter fun p => p.send == r.2 && p.smpd).map
        fun p => (p.shape, p.seat) := by
  induction T with
  | nil => rfl
  | cons r T ih =>
    have h0 := h r (List.mem_cons_self ..)
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [membersOf, List.map_cons, List.flatMap_cons, List.map_append] at ih' ⊢
    rw [ih', List.map_map]
    congr 1
    exact pairs_of_sending r.1.sampled _ h0

theorem shapes_of_noFault (rows : List Johnson.G.SendRow) (ps : List PSeat)
    (h : membersFault rows ps = []) :
    ∀ r ∈ (firstRows rows).zipIdx, (ps.filter fun p => p.send == r.2 && p.smpd).map (·.shape) =
      r.1.sampled.map (·.1) := by
  intro r hr
  unfold membersFault at h
  have h1 := List.filterMap_eq_nil_iff.1 h r hr
  by_contra hne
  have h2 : ((ps.filter fun p => p.send == r.2 && p.smpd).map (·.shape) !=
      r.1.sampled.map (·.1)) = true := by simpa using hne
  simp [h2] at h1

theorem plain_members (rows : List Johnson.G.SendRow) (ps : List PSeat)
    (h : membersFault rows ps = []) :
    (msOf (memberLists rows ps)).map (fun x => ((x.1.l.get x.2).1, seatOf x)) =
      (firstRows rows).zipIdx.flatMap fun r =>
        (ps.filter fun p => p.send == r.2 && p.smpd).map fun p => (p.shape, p.seat) := by
  unfold msOf sendsOf memberLists
  rw [List.map_map]
  exact plain_of_list _ ps (shapes_of_noFault rows ps h)

/-- **The two lists of pairs have the same members.** -/
theorem mems_same (rows : List Johnson.G.SendRow) (ps : List PSeat)
    (ha : (membersFault rows ps).isEmpty = true) (hb : sendsBelowB rows ps = true)
    (y : OnBytes.OracleShape × (Nat × Nat)) :
    y ∈ (msOf (memberLists rows ps)).map (fun x => ((x.1.l.get x.2).1, seatOf x)) ↔
      y ∈ (ps.filter (·.smpd)).map fun p => (p.shape, p.seat) := by
  rw [plain_members rows ps (List.isEmpty_iff.1 ha)]
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨r, _, p, ⟨hp, hq⟩, rfl⟩
    exact ⟨p, ⟨hp, (Bool.and_eq_true_iff.1 hq).2⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hs⟩, rfl⟩
    have hlt : p.send < (firstRows rows).length := by
      have := List.all_eq_true.1 hb p hp
      simpa [hs] using this
    exact ⟨((firstRows rows)[p.send], p.send),
      List.mem_zipIdx_iff_getElem?.2 (by simp [hlt]), p, ⟨hp, by simp [hs]⟩, rfl⟩

/-- **At the composed filling's own terms.** -/
theorem memsSame_at (Z : ProofFile.Pub) (lay : ByteArray)
    (ha : (membersFault ((rowsAt? Z.pol lay Z.KL).getD []) (planSeats Z Z.D.1)).isEmpty = true)
    (hb : sendsBelowB ((rowsAt? Z.pol lay Z.KL).getD []) (planSeats Z Z.D.1) = true)
    (y : OnBytes.OracleShape × (Nat × Nat)) :
    y ∈ (msAt Z lay).map (fun x => ((x.1.l.get x.2).1, seatOf x)) ↔
      y ∈ ((planSeats Z Z.D.1).filter (·.smpd)).map fun p => (p.shape, p.seat) :=
  mems_same _ _ ha hb y

end P5T

#print axioms P5T.pairs_of_sending
#print axioms P5T.plain_of_list
#print axioms P5T.shapes_of_noFault
#print axioms P5T.plain_members
#print axioms P5T.mems_same
#print axioms P5T.memsSame_at
