-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HtinLeft.lean: THE FIELD htin OF THE LINK's TABLE AT THE PROOF FILE's
SEAT, SECOND FORM: `htin_at_seat` (HtinAtSeat.lean) WITH `good9` AND `SeatsThere` TAKEN OUT OF ITS
PREMISE ON on1. Theorems; one by the kernel, with a negative twin.

  `adds_part`, `batch_part`: a yes of the batching ends in a writing at a state at which the lens
    reads a part. `part_behind_batch`: **so at every state that is reached behind a link's
    batching's entry the lens reads a part** (by `atS_reads`).
  `rowsBehindB_W`: BY THE KERNEL: at each of the 25 borders behind a batching's entry a class of
    rows of that link is open in the written list. `rowsFarB_W`: A NEGATIVE TWIN: at border 0 none.
  `seats_behind`: `seats_at_fold` (Johnson/LPFK9R/SeatsAtBatch.lean), step for step, ONE
    BORDER ON: SeatsThere (N.group l) n s from: s is reached there · membersHeld N ‹what is open
    there› s · N.groupAt l = l · FrameFinds at the part. By `members_at` (n := 7,
    Johnson/IMR/FrameEntry.lean), `members_head` (n := 8, HeadMembers.lean) and `seatsThere_held`.
  `htin_left`: **htin, to the letter, at own := N.group x.1, from hOn : ∀ a, on1 a →
    ‹reached behind the batching's entry› ∧ ledgerB a.1 = true ∧ ‹the open ledger has a coefficient
    for each slot› ∧ membersHeld N ‹what is open there› a.1 = true ∧ ‹FrameFinds at every part
    read there›.**
Limits. FrameFinds (the frame finds the mask's message and each array's) HAS NO PAYER HERE. ledgerB
and membersHeld are tests of the table's own promise at that border; «a coefficient for each slot»
is slots_at_rch. sortsB at the 25 built links is an evaluation. In scope, at secondHashFunction
alone. No member. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.HtinAtSeat
import Johnson.Desc.First.Link.Law.PartRests
import Johnson.Desc.First.Link.Law.SeatsThereOf
import Johnson.Desc.First.Batch.Law.AtSLens
import Johnson.IMR.FrameEntry
import Johnson.IMR.HeadMembers
import Johnson.IMR.HandsDef
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S kindsBeforeBatching Numbers membersHeld rowSegs)
open VerifiableInference.Desc.JoinAtBlocks
open Johnson.Desc.First.Walk.Tied (Reach)
open IM (linksW placesW nAt openAt)
open ProofFile (Cl)

/-! ## 1 A part is read behind the batching -/

theorem part_some {T : Type} {X : K9.Lens T} {t : T} {s : K9.Part} (h : X.part t = .ok s) :
    (X.get? t).isSome = true := by
  unfold K9.Lens.part at h
  cases e : X.get? t with
  | none =>
    rw [e] at h
    exact nomatch h
  | some _ => rfl

theorem adds_part {T Cl' : Type} (X : K9.Lens T) (p : K9.Where) (piece : Nat) (what : String)
    (claims : T → Except String (List Claim × T)) {t t' : T} {rs gs}
    (h : (K9.adds (Cl := Cl') X p piece what claims).decide t rs gs = .ok t') :
    ∃ x a, (X.get? x).isSome = true ∧ t' = X.set x a := by
  simp only [K9.adds, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | exact ⟨_, _, part_some (by assumption), (Except.ok.inj h).symm⟩
    | cases h

theorem batch_part {T : Type} (X : K9.Lens T) (p : K9.Where)
    (claims : T → Except String (List Claim × T)) {t t' : T} {rs gs}
    (h : (K9.batch X p claims).decide t rs gs = .ok t') :
    ∃ x a, (X.get? x).isSome = true ∧ t' = X.set x a := by
  simp only [K9.batch, bind, Except.bind] at h
  split at h
  · cases h
  · exact adds_part X p p.piece _ claims h

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **AT EVERY STATE REACHED BEHIND A LINK's BATCHING's ENTRY THE LENS READS A PART.** -/
theorem part_behind_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) (a : ProofFile.InstPub × S)
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) a) :
    PartThere a.2 := by
  have hl : x.1 < 25 := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.1 hl
  obtain ⟨Lk, e, hf⟩ := P1K8S.batch_behind hS hR O x hx
  obtain ⟨L9, w, -, -, e9, -, -, -, -, -, hb9, -⟩ := (IM.k9_of hS hR O).2 x.1 hl
  obtain rfl : Lk = L9 := Option.some.inj (e.symm.trans e9)
  cases h with
  | @succ _ z s s' b hr hb hy =>
    obtain ⟨R, cc, _, e1⟩ := hy
    have hd := ((step_ok_iff 0 b s s' R cc cc.length).1 e1).2.2.2
    obtain rfl := Option.some.inj (hf.symm.trans hb)
    have y := ((IM.yes_alone (hb9 _) (a := IM.a9Of x.1 (IM.subAt x.1)) (fun h => nomatch h)
      s s' _ _).1 hd).1
    obtain ⟨u, q, hu, rfl⟩ := batch_part atS w _ y
    obtain ⟨a', ha', _⟩ := atS_reads u q hu
    exact ⟨a', ha'⟩

/-! ## 2 SeatsThere behind the batching -/

/-- At each of the 25 borders behind a batching's entry a class of rows of that link is open. -/
def rowsBehindB : Bool :=
  (List.range 25).all fun l => (rowSegs (openAt linksW placesW (14 * l + nAt l + 3))).contains l

set_option maxRecDepth 1000000 in
theorem rowsBehindB_W : rowsBehindB = true := by decide +kernel

/-- A negative twin: at the first border no class of rows is open. -/
def rowsFarB : Bool := (List.range 25).any fun l => (rowSegs (openAt linksW placesW 0)).contains l

set_option maxRecDepth 1000000 in
theorem rowsFarB_W : rowsFarB = false := by decide +kernel

theorem rowsOpen_behind {l : ℕ} (hl : l < 25) :
    l ∈ rowSegs (openAt linksW placesW (14 * l + nAt l + 3)) := by
  have h := List.all_eq_true.1 rowsBehindB_W l (List.mem_range.2 hl)
  simpa using h

theorem seats_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {y : ProofFile.InstPub × S} (hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + nAt l + 3) y)
    {N : Numbers} (hM : membersHeld N (openAt linksW placesW (14 * l + nAt l + 3)) y.2 = true)
    (hg : N.groupAt l = l) {a : K9.Part} (ha : atS.get? y.2 = some a) {n : ℕ}
    (hF : FrameFinds a n) : SeatsThere (N.group l) n y.2 := by
  obtain ⟨_, rs, cols, g⟩ := hr.fold
  have key : ∃ (L : LinkCtx) (G : Group) (pre : Array ℕ), y.2.link? = some L ∧
      y.2.st.groups[l]? = some G ∧
      G.members = pre ++ L.check.frame.keptBefore ++ L.check.frame.own := by
    by_cases h24 : l < 24
    · have e : 14 * l + nAt l + 3 = 14 * l + 3 + 7 := by
        unfold nAt
        rw [if_neg (by omega)]
      rw [e] at g
      obtain ⟨L, G, pre, h1, _, _, h4, _, h6, _⟩ :=
        Meaning.K2.members_at hS hR O h24 (n := 7) (by omega) g
      exact ⟨L, G, pre, h1, h4, h6⟩
    · obtain rfl : l = 24 := by omega
      have e : 14 * 24 + nAt 24 + 3 = 340 + 8 := by decide
      rw [e] at g
      obtain ⟨L, G, n₀, h1, _, _, h4, h5, _⟩ :=
        Meaning.K2.members_head hS hR O (n := 8) (by omega) g
      exact ⟨L, G, #[n₀], h1, h4, h5⟩
  obtain ⟨L, G, pre, h1, h4, h6⟩ := key
  have eL : a.L = L := Option.some.inj ((part_reads y.2 a ha).1.symm.trans h1)
  refine seatsThere_held (G := G) ha hF hM (rowsOpen_behind hl) (by rw [hg]; exact h4)
    fun o ho => ?_
  rw [h6, eL.symm]
  simp only [Array.toList_append, List.mem_append]
  rcases ho with ho | ho
  · exact Or.inr ho
  · exact Or.inl (Or.inr ho)

/-! ## 3 htin -/

theorem border_eq {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) :
    14 * x.1 + x.2.1 + 3 + x.2.2 + 1 = 14 * x.1 + nAt x.1 + 3 := by
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
  unfold nAt
  dsimp only
  split <;> omega

/-- **htin, TO THE LETTER, AT A LINK OF THE SEAT: SECOND FORM.** -/
theorem htin_left {α : Type} {Fr : Frame} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Lk : Link S Cl}
    (eL : c.links[x.1]? = some Lk) {Xl : LinkH} (e3 : Bs.G₀.built[x.1]? = some Xl)
    (hB : sortsB (Xl.Fp.trees.toList.map look) Xl.tl = true) (N : Numbers)
    (hg : N.groupAt x.1 = x.1) (z : ProofFile.InstPub) (on1 : S × Fr.E.Str → Prop)
    (hOn : ∀ a, on1 a →
      Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) (z, a.1) ∧
        First.ledgerB a.1 = true ∧ (∀ G, a.1.fork? = some G → G.LS.size = G.ns) ∧
        membersHeld N (openAt linksW placesW (14 * x.1 + nAt x.1 + 3)) a.1 = true ∧
        ∀ p, atS.get? a.1 = some p → FrameFinds p (Xl.Fp.trees.toList.map look).length) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) Lk).map (·.move)) a.1 t [] →
      K9.totalIn (N.group x.1) t = true := by
  have hl : x.1 < 25 := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.1 hl
  have h1 : ∀ a, on1 a → HasFork (SizedLooks (Xl.Fp.trees.toList.map look)) a.1 ∧
      SeatsThere (N.group x.1) (Xl.Fp.trees.toList.map look).length a.1 ∧
      SortsAt (Xl.Fp.trees.toList.map look) a.1 := fun a ha => by
    obtain ⟨r, lb, ls, mh, ff⟩ := hOn a ha
    obtain ⟨p, hp⟩ := part_behind_batch hS hR O hx (z, a.1) r
    have hF : a.1.fork? = some p.F := fork_part a.1 p hp
    have hs : SeatsThere (N.group x.1) (Xl.Fp.trees.toList.map look).length a.1 :=
      seats_behind hS hR O hl (y := (z, a.1)) (by rw [← border_eq hx]; exact r) mh hg hp
        (ff p hp)
    obtain ⟨L, l1, l2⟩ := link_behind_reach hS hR O hx (z, a.1) r
    have hk : 14 * x.1 + x.2.1 + 3 + x.2.2 + 1 ≤ 353 := by
      rw [border_eq hx]
      unfold nAt
      split <;> omega
    have hlk := looks_open_reach hS hR O hk (z, a.1) r p.F L hF l1
    rw [l2, shOf_at O.blank e3] at hlk
    have hsz : OnBytes.PscRun.Sized p.F := by
      unfold First.ledgerB at lb
      rw [hF] at lb
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at lb
      exact ⟨lb.1.1, lb.1.2, lb.2⟩
    exact ⟨⟨p.F, hF, ⟨hsz, ls p.F hF⟩, hlk⟩, hs,
      sortsAt_of_five
        (planned_behind_batch planned_five (fun _ _ => rfl) hS hR O hx e3 (z, a.1) r) hB⟩
  obtain ⟨Lk', _, _, e', _, hSeg, _⟩ := LPFK9.blocks_each hS hR O x.1 hl
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e')
  have hsub := IM.subs_scope hS hR O x.1 hl
  by_cases h24 : x.1 = 24
  · have es : IM.subAt x.1 = .head := by rw [h24]; rfl
    rw [es] at hSeg hsub
    obtain ⟨Lk', e', X, _, _, tLs, tTests⟩ := LPFK9.k8_ties O.made O.places O.chain x.1 .head hsub
      5 (by unfold kindsBeforeBatching; cases (x.1 == 0) <;> rfl) (by omega)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e')
    exact htin_head_part _ _ _ hSeg on1 h1 tLs tTests
  · by_cases he : x.1 % 2 = 0
    · have es : IM.subAt x.1 = .layers := by
        unfold IM.subAt
        rw [if_neg h24, if_pos he]
      rw [es] at hSeg hsub
      obtain ⟨Lk', e', X, _, _, tLs, tTests⟩ := LPFK9.k8_ties O.made O.places O.chain x.1 .layers
        hsub 4 (by unfold kindsBeforeBatching; cases (x.1 == 0) <;> rfl) (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e')
      obtain ⟨Lk', e', p, _, _, _, tFree⟩ := LPFK9.k4_ties O.made O.places O.chain x.1 .layers
        hsub (by unfold kindsBeforeBatching; cases (x.1 == 0) <;> rfl)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e')
      exact htin_layers_part _ _ _ hSeg on1 h1 tLs tFree tTests
    · have es : IM.subAt x.1 = .attention := by
        unfold IM.subAt
        rw [if_neg h24, if_neg he]
      rw [es] at hSeg hsub
      obtain ⟨Lk', e', X, _, _, tLs, tTests⟩ := LPFK9.k8_ties O.made O.places O.chain x.1
        .attention hsub 4 (by unfold kindsBeforeBatching; cases (x.1 == 0) <;> rfl) (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e')
      exact htin_attention_part _ _ _ hSeg on1 h1 tLs tTests

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.batch_part
#print axioms VerifiableInference.Desc.LinkJoin.part_behind_batch
#print axioms VerifiableInference.Desc.LinkJoin.rowsBehindB_W
#print axioms VerifiableInference.Desc.LinkJoin.rowsFarB_W
#print axioms VerifiableInference.Desc.LinkJoin.seats_behind
#print axioms VerifiableInference.Desc.LinkJoin.htin_left
