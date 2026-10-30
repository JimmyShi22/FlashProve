-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/Sits.lean: THE BLOCKS OF WHICH KIND K9's LAW
SPEAKS ARE THE BLOCKS THAT THE PROOF FILE's DESCRIPTION CALLS AT K9's PLACES, UP TO THE SEAT's
DRESS, AND WHAT THE LAW ASKS OF A BLOCK HOLDS OF THE SEATED BLOCK.
THE CONSTANT THAT THE SEAT CALLS: ProofFile.onlineDescription o pol lay KL (its first chain c, opened by IM.Open).
WHO SITS WHERE is other files' (Johnson/IMR/):
  IM.k9_of      at every link l < 25, in scope: for every gatherer g, Lk.batch g IS
                seatedAs sameReply (K9.batch atS p g) .. (the lot's block under guardMark, the
                spot's name, the driver's address, Block.guarded), ALONE; it stands at
                c.blocksInOrder[14 l + n + 2] at the frame's own gatherer.
  IM.close_of   Lk.close[j] IS seatedAs sameReply ((K9.closeOf p Q)[j]).retype .., ALONE, at
                j = 0, 1, 2.
  IM.step_alone a seated block's step says yes just where the lot's block's does, the record behind
                bears no mark and the guard's test passes: with the same return.
HERE, THE COROLLARY FOR K9's LAW (Johnson/Desc/First/Batch/Law/):
  drawMoves_of_yes   "a draw with moves behind it" passes to a block each of whose yeses is a yes of
                the other with the same return.
  behind_in_flat, close_in_flat   Block.lean's text of a link's flat list, read at two places.
  SitsAt c l Lk p Q   what K9's law asks of the blocks at a link, by name:
     hear, order, orderAfter   the number of hearing blocks and the two orders are the driver's at
                   the link's sort;
     link, flat    Lk is link l; the batching stands in the flat list at 14 l + n + 2; (flat2, and
                   inside equation and shut:) the frame's block behind it at + 3, the closing's
                   first at + 4, its third at + 6;
     rounds        the seated batching declares K9's one round [k9Decl p] (so hds: Law/CutAt.lean);
     draw          hb1 of the joining's hypothesis (LinkJoin.JoinAsks): THE SEATED BATCHING IS A
                   DRAW WITH ONE MOVE BEHIND IT: the adding of what the frame's gatherer gathers;
     behind        hb2: the frame's block behind the batching is one quiet move (general in the
                   link);
     equation      hb3: the closing's first block has no round, and a yes of its step is a yes of
                   the one equation's, at the same p, with the same return;
     shut          the closing's third block: the like for K9's "shut" at Q.piece + 1.
  k09_sits      **in scope, at every l < 25: there are Lk, p, Q with k9At Z l = some p,
                k10Par .. p = some Q and SitsAt c l Lk p Q.**
  k09_sits_desc the same from onlineDescription's yes (IM.seat_open): c is the description's first chain.
  chain_first, subs_are, k9Ix, table_k9, k9_only   in scope the first chain's places are the
                driver's table at the 25 sorts of link; there a place of kind K9 stands at one of
                three numbers of a link (table_k9: by the kernel).
  k09_each      **AT EACH PLACE OF THE KIND IN THE FIRST CHAIN**: an entry of c.blocksInOrder at a place of
                kind K9 IS the seated batching, the closing's first or its third of a link with
                SitsAt.
  k09_condition_seat   at the seat: 1 <= p.rows, p.rows - 1 <= 2^60, p.work = 0
                and the cap, at every link's p, where the description's declared rounds, written
                out, are a written list (all_at_desc, fed with "rounds" and "flat").
THE ROW's WORDS: "under the seat's wrappers alone .., OR ITS YES GIVES THAT LAW's PREMISE": this
file goes by the second arm (the wrappers are four: guardMark, the name and the address, the reply's
guard, and for the closing's blocks Block.retype).
ONE DIRECTION: from the seated block's yes to the law's block's. Not claimed: anything on the runs
that the gatherer calls (each stands behind the guard: IM.claim_yes, IM.after_yes: each kind's own
row); that onlineDescription returns in scope; fits p Q; the pieces' data (Law/CutAt.lean); THAT THE TWO
LATER CHAINS HOLD NO PLACE OF KIND K9; the key file's description (no file under Johnson/Desc/Key
names the kind: by a search, not by Lean). No soundness.

-/
import Johnson.IMR.CloseSeat
import Johnson.Desc.First.Link.Law.JoinAtBlocks
import Johnson.Desc.First.Batch.Law.ConditionWork
import Johnson.Desc.First.Batch.Law.ShutLaw

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName claimsInBy OpenedColumn)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching closeKinds firstChain flatPlacesOf)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L (DrawMoves IsMoves Move k9Decl)
open ProofFile (Cl)
open IM (Open LaidAlone k9At subAt a9Of cAt)

/-- "A draw with moves behind it" passes to a block each of whose yeses is a yes of the other. -/
theorem drawMoves_of_yes {T C : Type} (X : VerifiableInference.Desc.K9.Lens T) (p : Where)
    (ms : List (Move T)) (b b' : Block T C)
    (h : ∀ ft s rs cols x, b.step ft s rs cols = .ok x → b'.step ft s rs cols = .ok x)
    (H : DrawMoves X p ms b') : DrawMoves X p ms b :=
  fun ft s rs cols s' k hs => H ft s rs cols s' k (h ft s rs cols _ hs)

/-- A list of the flat list's form: what stands behind the first two groups. -/
theorem at_five {α : Type} (x a b z : α) (H C : List α) :
    (x :: H ++ [a, b] ++ C ++ [z])[H.length + 2]? = some b ∧
      ∀ j c, C[j]? = some c → (x :: H ++ [a, b] ++ C ++ [z])[H.length + 3 + j]? = some c := by
  constructor
  · refine IM.getElem?_append_some (IM.getElem?_append_some ?_ _) _
    have e : H.length + 2 = (x :: H).length + 1 := by rw [List.length_cons]
    rw [e, IM.getElem?_append_add]
    rfl
  · intro j c h
    refine IM.getElem?_append_some ?_ _
    have e : H.length + 3 + j = (x :: H ++ [a, b]).length + j := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    rw [e, IM.getElem?_append_add]
    exact h

/-- By Block.lean's text: behind the batching stands the frame's block; then the closing's blocks.
General in the link. -/
theorem behind_in_flat {σ C : Type} (Lk : Link σ C) :
    Lk.blocksInOrder[Lk.hear.length + 2]? = some Lk.behindB := (at_five _ _ _ _ _ _).1

theorem close_in_flat {σ C : Type} (Lk : Link σ C) (j : ℕ) (b : Block σ C)
    (h : Lk.close[j]? = some b) : Lk.blocksInOrder[Lk.hear.length + 3 + j]? = some b :=
  (at_five _ _ _ _ _ _).2 j b h

/-- **What K9's law asks of the blocks at a link.** -/
structure SitsAt (c : Chain S Cl) (l : ℕ) (Lk : Link S Cl) (p : Where)
    (Q : VerifiableInference.Desc.First.Close.Par) : Prop where
  link : c.links[l]? = some Lk
  hear : Lk.hear.length = (kindsBeforeBatching (subAt l) (l == 0)).length
  order : Lk.order = VerifiableInference.Desc.First.orderOf (subAt l)
  orderAfter : Lk.orderAfter = VerifiableInference.Desc.First.orderAfterOf (subAt l)
  flat : c.blocksInOrder[14 * l + Lk.hear.length + 2]? = some Lk.batchB
  rounds : Lk.batchB.rounds = [k9Decl p]
  draw : DrawMoves atS p [.add (claimsInBy Lk.each Lk.hear Lk.order)] Lk.batchB
  flat₂ : c.blocksInOrder[14 * l + Lk.hear.length + 3]? = some Lk.behindB
  behind : IsMoves atS [.quiet Lk.runBehind] Lk.behindB
  equation : ∃ b₃, Lk.close[0]? = some b₃ ∧ c.blocksInOrder[14 * l + Lk.hear.length + 4]? = some b₃ ∧
    b₃.rounds = [] ∧
    ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (VerifiableInference.Desc.K9.oneEquation (Cl := Cl) atS p).step ft s rs cols = .ok x
  shut : ∃ b₅, Lk.close[2]? = some b₅ ∧ c.blocksInOrder[14 * l + Lk.hear.length + 6]? = some b₅ ∧
    b₅.rounds = [] ∧
    ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (VerifiableInference.Desc.K9.shut (Cl := Cl) p (Q.piece + 1)).step ft s rs cols = .ok x

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **K09_sits.** -/
theorem k09_sits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (p : Where) (Q : VerifiableInference.Desc.First.Close.Par),
      k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧ SitsAt c l Lk p Q := by
  intro l hl
  obtain ⟨Lk, p, w, T, e1, e2, _, _, _, _, hb, hflat, _, _, _, hord, hordA, hlen, _⟩ :=
    (IM.k9_of hS hR O).2 l hl
  obtain ⟨Lk', p', Q, e1', e2', hQ, hc⟩ := IM.close_of hS hR O l hl
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : p = p' := Option.some.inj (e2.symm.trans e2')
  have hB := hb (claimsInBy Lk.each Lk.hear Lk.order)
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  have hix := IM.flatIx_scope hS hR O (l := l) (by omega) Lk.hear.length
  unfold IM.flatIx at hix
  have inFlat : ∀ j b, Lk.blocksInOrder[Lk.hear.length + 1 + j]? = some b →
      c.blocksInOrder[14 * l + Lk.hear.length + 2 + j]? = some b := fun j b h => by
    have h' := IM.link_at_flat e1 h
    rw [show (1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length +
        (Lk.hear.length + 1 + j)) = 14 * l + Lk.hear.length + 2 + j by omega] at h'
    exact h'
  refine ⟨Lk, p, Q, e2, hQ, e1, hlen, hord, hordA, hflat, ?_, ?_, inFlat 1 _ (behind_in_flat Lk),
    ?_, ?_, ?_⟩
  · exact (IM.alone_rounds hB).trans (VerifiableInference.Desc.K9L.batch_rounds atS p _)
  · exact drawMoves_of_yes atS p _ _ _
      (fun ft s rs cols x hs => ((IM.step_alone hB k9ne ft s x.1 x.2 rs cols).1 hs).1)
      (VerifiableInference.Desc.JoinAtBlocks.batch_drawMoves atS p _)
  · exact VerifiableInference.Desc.JoinAtBlocks.behind_isMoves atS Lk
  · obtain ⟨b, x, hb0, hx, hL⟩ := hc 0 KindName.K9 rfl
    obtain rfl := Option.some.inj (show some _ = some x from hx)
    exact ⟨b, hb0, inFlat 2 b (close_in_flat Lk 0 b hb0), IM.alone_rounds hL,
      fun ft s rs cols y hs =>
      ((IM.step_alone hL k9ne ft s y.1 y.2 rs cols).1 hs).1⟩
  · obtain ⟨b, x, hb2, hx, hL⟩ := hc 2 KindName.K9 rfl
    obtain rfl := Option.some.inj (show some _ = some x from hx)
    exact ⟨b, hb2, inFlat 4 b (close_in_flat Lk 2 b hb2), IM.alone_rounds hL,
      fun ft s rs cols y hs =>
      ((IM.step_alone hL k9ne ft s y.1 y.2 rs cols).1 hs).1⟩

/-! ## No other place of the kind in the first chain -/

/-- The chain is the driver's, at the plan's row of links. -/
theorem chain_first {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B₀ : ProofFile.PureBase}
    {base : List (Block S Cl)} {c : Chain S Cl}
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt T B₀).frames (ProofFile.partsAt T B₀).road = .ok c) :
    ∃ H several, firstChain H (ProofFile.subsOf Z) several = some c := by
  unfold ProofFile.chainBy at hc
  dsimp only at hc
  unfold ProofFile.chainC at hc
  split at hc
  · cases hc
  · dsimp only at hc
    split at hc
    · cases hc
    · rename_i c1 h1
      split at hc
      · cases hc
      · obtain rfl := Except.ok.inj hc
        exact ⟨_, _, h1⟩

/-- In scope the plan's row of links is the 25 sorts. -/
theorem subs_are (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ProofFile.subsOf Z = (List.range 25).map subAt := by
  have h25 := IM.links_25 hS hR O
  apply List.ext_getElem?
  intro l
  by_cases hl : l < 25
  · rw [IM.subs_scope hS hR O l hl]
    simp [hl]
  · have hn : ((List.range 25).map subAt)[l]? = none := by simp; omega
    rw [hn]
    cases hx : (ProofFile.subsOf Z)[l]? with
    | none => rfl
    | some sub =>
      obtain ⟨Lk, e, _⟩ := (IM.link_flat_places O.chain).2 l sub hx
      have := (List.getElem?_eq_some_iff.1 e).1
      omega

/-- The three numbers of kind K9 in link l's stretch of the flat list. -/
def k9Ix (l : ℕ) : List ℕ :=
  [14 * l + (kindsBeforeBatching (subAt l) (l == 0)).length + 2,
   14 * l + (kindsBeforeBatching (subAt l) (l == 0)).length + 4,
   14 * l + (kindsBeforeBatching (subAt l) (l == 0)).length + 6]

/-- The driver's table at the 25 sorts: a place of kind K9 stands at one of these numbers. By the
kernel. -/
theorem table_k9 (several : Bool) :
    ((flatPlacesOf ((List.range 25).map subAt) several).zipIdx.all fun x =>
      x.1.kind != KindName.K9 || (List.range 25).any fun l => (k9Ix l).contains x.2) = true := by
  cases several <;> decide +kernel

/-- **In the first chain's flat list a block at a place of kind K9 stands at one of the three
numbers of some link.** -/
theorem k9_only (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (i : ℕ) (b : Block S Cl)
    (hb : c.blocksInOrder[i]? = some b) (hk : b.place.kind = KindName.K9) : ∃ l < 25, i ∈ k9Ix l := by
  obtain ⟨H, several, hc⟩ := chain_first O.chain
  have hpl := VerifiableInference.Desc.First.flat_places H _ several c hc
  rw [subs_are hS hR O] at hpl
  have hi : (flatPlacesOf ((List.range 25).map subAt) several)[i]? = some b.place := by
    rw [← hpl, List.getElem?_map, hb]
    rfl
  have hm : (b.place, i) ∈ (flatPlacesOf ((List.range 25).map subAt) several).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.2 (by simpa using hi)
  have h := List.all_eq_true.1 (table_k9 several) _ hm
  simp only [hk, bne_self_eq_false, Bool.false_or, List.any_eq_true, List.mem_range,
    List.contains_iff_mem] at h
  exact h

/-- **K09_sits, AT EACH PLACE OF THE KIND IN THE FIRST CHAIN**: an entry of the flat list at a place
of kind K9 is the seated batching, the closing's first or the closing's third of a link at which
SitsAt holds. -/
theorem k09_each (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (i : ℕ) (b : Block S Cl)
    (hb : c.blocksInOrder[i]? = some b) (hk : b.place.kind = KindName.K9) :
    ∃ l < 25, ∃ (Lk : Link S Cl) (p : Where) (Q : VerifiableInference.Desc.First.Close.Par),
      k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧ SitsAt c l Lk p Q ∧
        (b = Lk.batchB ∨ Lk.close[0]? = some b ∨ Lk.close[2]? = some b) := by
  obtain ⟨l, hl, hi⟩ := k9_only hS hR O i b hb hk
  obtain ⟨Lk, p, Q, hp, hQ, H⟩ := k09_sits hS hR O l hl
  refine ⟨l, hl, Lk, p, Q, hp, hQ, H, ?_⟩
  obtain ⟨b₃, c3, f3, _⟩ := H.equation
  obtain ⟨b₅, c5, f5, _⟩ := H.shut
  have f1 := H.flat
  rw [H.hear] at f1 f3 f5
  simp only [k9Ix, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact Or.inl (Option.some.inj (hb.symm.trans f1))
  · obtain rfl : b = b₃ := Option.some.inj (hb.symm.trans f3)
    exact Or.inr (Or.inl c3)
  · obtain rfl : b = b₅ := Option.some.inj (hb.symm.trans f5)
    exact Or.inr (Or.inr c5)

/-- **K09_condition AT THE SEAT**: where the description's declared rounds, written out, are a
written list: at the seated batching of every link: the four numbers' facts. -/
theorem k09_condition_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {file : String}
    {R : OnBytes.Params.Rounds × OnBytes.Params.Rounds × OnBytes.Params.Rounds}
    (h : Johnson.G.OfPlan.writtenOf file F.roundsDeclaredByBlocks = .ok R)
    (hW : R.1 = Johnson.G.dryProofFull.1 ∨ R.1 = Johnson.G.dryProofSmall.1) :
    ∀ l < 25, ∃ p, k9At Z l = some p ∧ 1 ≤ p.rows ∧ p.rows - 1 ≤ 2 ^ 60 ∧ p.work = 0 ∧
      _root_.Iop.Err.le
        (OnBytes.Flat.allErr (fun _ _ => p.rows - 1) 0 [VerifiableInference.Desc.K9L.k9Round p])
        (_root_.Iop.Err.cap 128
          (OnBytes.Maker.uLT (_root_.Run.ckP .two) [VerifiableInference.Desc.K9L.k9Round p])) := by
  intro l hl
  obtain ⟨Lk, p, Q, hp, _, H⟩ := k09_sits hS hR O l hl
  have hd := O.desc
  subst hd
  exact ⟨p, hp, VerifiableInference.Desc.K9L.all_at_desc _ h hW Lk.batchB
    (List.mem_of_getElem? H.flat) p (by rw [H.rounds]; exact List.mem_singleton.2 rfl)⟩

/-- **The same from onlineDescription's yes.** c is the description's first chain: Open.desc says
F = fileDescBy .. c, whose field "first" is c. -/
theorem k09_sits_desc (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ Z Bs base c A B, Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B ∧
      ∀ l < 25, ∃ (Lk : Link S Cl) (p : Where) (Q : VerifiableInference.Desc.First.Close.Par),
        k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧ SitsAt c l Lk p Q := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  exact ⟨Z, Bs, base, c, A, B, O, k09_sits hS hR O⟩

end LPFK9

#print axioms LPFK9.k09_sits
#print axioms LPFK9.k09_sits_desc
#print axioms LPFK9.table_k9
#print axioms LPFK9.k09_each
#print axioms LPFK9.k09_condition_seat
