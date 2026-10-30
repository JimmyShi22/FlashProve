-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Pay/NoSpender.lean: WHERE A PLACE's ROUNDS ARE ALL NAMED "SEND seed"
OR "SEND answer", AND NO FOLD's FIRST SENDING BEHIND IT STANDS THERE, NO ENTRY OF THE BOOK HAS ITS
SPENDER AT THAT PLACE. General in the description: the book's maker names no kind.

  no_spender   under hB (bookWhole returns B): the whole law

Limits. An implication. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookPlain
import Johnson.Desc.ProofFile.Honest.K14.BookMakers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1.Pay
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow ProofFile.Honest.BookPlain

variable {Xi S Cl : Type}

/-- Every round at a place in a plan is a sending's. -/
def SendOnly (a : Place) (l : List PlanB) : Prop :=
  ∀ x ∈ l, x.place = a → ∀ d ∈ x.rounds, d.entry.name = "SEND seed" ∨ d.entry.name = "SEND answer"

/-- A fold's address is not at such a place, and its sending's is not, by hq. -/
theorem fold_off {a : Place} {l : List PlanB} (hn : SendOnly a l)
    (hq : ∀ i p q, behindFold l i = some (p, q) → q.place ≠ a) {i : Nat} {p q s : Addr}
    (hb : behindFold l i = some (p, q)) (hs : s = p ∨ s = q) : s.place ≠ a := by
  rcases hs with rfl | rfl
  · intro e
    obtain ⟨⟨x, hx, ex, d, hd, hnm⟩, -⟩ := behindFold_named hb
    rcases hn x hx (ex.trans e) d hd with h | h <;> · rw [hnm] at h; exact absurd h (by decide)
  · exact hq _ _ _ hb

/-- An entry of the chain of segments is carried to one of a fold's two addresses. -/
theorem segmentCarries_pq {here : List PlanB} {ms : List SentMsg} {l : List Ahead}
    (h : segmentCarries here ms = .ok l) :
    ∀ e ∈ l, ∃ i p q, behindFold here i = some (p, q) ∧ (e.spender = p ∨ e.spender = q) := by
  unfold segmentCarries at h
  obtain ⟨ll, hll, e⟩ := ex_map h
  intro a ha
  rw [← e] at ha
  obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
  refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, ∃ i p q, behindFold here i = some (p, q) ∧
    (a.spender = p ∨ a.spender = q)) ?_ hll inner hin a ha
  intro f _ r hr
  try dsimp only at hr
  split at hr
  · rename_i p q k hb hk
    have e2 := Except.ok.inj hr
    rw [← e2]
    intro a ha
    refine ⟨_, p, q, hb, ?_⟩
    rcases List.mem_append.1 ha with h1 | h1
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h1
      exact Or.inl rfl
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h1
      exact Or.inr rfl
  · cases hr

/-- The like for a group's carrying entries. -/
theorem groupCarries_pq {l : List PlanB} {i : Nat} {g : List SentMsg} {own : Option SentMsg}
    {r : List Ahead} (h : groupCarries l i g own = .ok r) :
    ∀ e ∈ r, ∃ i p q, behindFold l i = some (p, q) ∧ (e.spender = p ∨ e.spender = q) := by
  unfold groupCarries at h
  split at h
  · rename_i p q hb
    have e := Except.ok.inj h
    rw [← e]
    exact fun e he => ⟨_, p, q, hb, BookPlain.carryPair_spender e he⟩
  · cases h

/-- The part behind a fold that sends its own table is that fold's second address. -/
theorem ownFresh_pq {bs : List (Block S Cl)} {o : OwnFresh} (h : o ∈ ownFreshIn bs) :
    ∃ i, behindFold (planOf bs) i = some (o.fold, o.behind) := by
  have h' : o ∈ (((planOf bs).flatMap (·.rounds)).zipIdx.filter fun r =>
      r.1.entry.name == "FOLD epsilon" && r.1.entry.roots != 0).filterMap fun r =>
      if r.2 == 0 then none else
      (behindFold (planOf bs) (r.2 - 1)).bind fun pq =>
        (foldBehind (planOf bs) (r.2 - 1)).map fun f =>
          (⟨pq.1, pq.2, f.2.2, (maskWordsByRound bs).getD r.2 0 / 3⟩ : OwnFresh) := h
  obtain ⟨r, -, hr⟩ := List.mem_filterMap.1 h'
  by_cases h0 : (r.2 == 0) = true
  · rw [if_pos h0] at hr
    cases hr
  · rw [if_neg h0] at hr
    obtain ⟨pq, hpq, h1⟩ := opt_bind hr
    obtain ⟨f, -, rfl⟩ := opt_map h1
    obtain ⟨p, q⟩ := pq
    exact ⟨_, hpq⟩

/-! ## The parts that want scalars -/

theorem foldl_frame (rs : List (String × Nat)) (hr : ∀ y ∈ rs, frameNames.contains y.1 = true) :
    ∀ n, rs.foldl (fun n r => if frameNames.contains r.1 then n else n + r.2) n = n := by
  induction rs with
  | nil => intro n; rfl
  | cons y t ih =>
    intro n
    rw [List.foldl_cons, if_pos (hr y List.mem_cons_self)]
    exact ih (fun z hz => hr z (List.mem_cons_of_mem _ hz)) n

theorem mem_stretches {α : Type} : ∀ (ks : List Nat) (l : List α) (x : List α),
    x ∈ stretchesBy l ks → ∀ y ∈ x, y ∈ l
  | [], _, _, h, _, _ => by cases h
  | k :: ks, l, x, h, y, hy => by
    unfold stretchesBy at h
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_of_mem_take hy
    · exact List.mem_of_mem_drop (mem_stretches ks _ x h y hy)

/-- At a place of sendings alone no part has scalars of the segment's own. -/
theorem ownScalars_zero {b : Block S Cl}
    (hb : ∀ d ∈ b.rounds, d.entry.name = "SEND seed" ∨ d.entry.name = "SEND answer")
    {p : PartAt} (hp : p ∈ planParts b) : p.ownScalars = 0 := by
  unfold planParts at hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
  have hm := List.fst_mem_of_mem_zipIdx hx
  unfold PartAt.ownScalars
  refine foldl_frame _ (fun y hy => ?_) 0
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (mem_stretches _ _ _ hm y hy)
  show frameNames.contains d.entry.name = true
  rcases hb d hd with h | h <;> · rw [h]; decide

/-- A part's own wants are had only where it has scalars. -/
theorem partWants_scalars {row idx : MsgAt} {merge : Bool} {p : PartAt} {j t : Nat} {w : Want}
    (h : w ∈ (partWants row idx merge p j t).1) : p.ownScalars ≠ 0 := by
  intro e
  unfold partWants at h
  dsimp only at h
  rw [e] at h
  cases h

/-- What a stretch of parts wants names a part with scalars. -/
theorem partsWants_parts {row idx : MsgAt} {merges : List Addr} {w : Want} :
    ∀ (ps : List PartAt) (j t : Nat), w ∈ (partsWants row idx merges ps j t).1 →
      ∃ p ∈ ps, w.spender = p.addr ∧ p.ownScalars ≠ 0
  | [], _, _, h => by cases h
  | p :: ps, j, t, h => by
    unfold partsWants at h
    dsimp only at h
    rcases List.mem_append.mp h with h | h
    · exact ⟨p, List.mem_cons_self, partWants_spender h, partWants_scalars h⟩
    · obtain ⟨q, hq, e⟩ := partsWants_parts ps _ _ h
      exact ⟨q, List.mem_cons_of_mem _ hq, e⟩

/-- What a chain's links want names a part with scalars. -/
theorem linksWants_parts {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr} {w : Want} :
    ∀ (ls : List Nat) (t : Nat) (a : List Want × Nat),
      linksWants bs c later idx merges ls t = .ok a → w ∈ a.1 →
      ∃ b ∈ bs, ∃ p ∈ planParts b, w.spender = p.addr ∧ p.ownScalars ≠ 0
  | [], t, a, h, hw => by
    have e := Except.ok.inj h
    rw [← e] at hw
    cases hw
  | l :: ls, t, a, h, hw => by
    unfold linksWants at h
    split at h
    · cases h
    · rename_i row hrow
      obtain ⟨y, hy, e⟩ := ex_map h
      rw [← e] at hw
      rcases List.mem_append.1 hw with h1 | h1
      · unfold segmentWants at h1
        obtain ⟨p, hp, e1, e2⟩ := partsWants_parts _ _ _ h1
        obtain ⟨b, hb, hpb⟩ := List.mem_flatMap.1 hp
        exact ⟨b, List.mem_of_mem_filter hb, p, hpb, e1, e2⟩
      · exact linksWants_parts ls _ y hy h1

/-- What the sumchecks outside a segment want names a part with scalars. -/
theorem loneWants_parts {idx : MsgAt} {lone : List Addr} {w : Want} :
    ∀ (ps : List PartAt) (t : Nat), w ∈ (loneWants idx lone ps t).1 →
      ∃ p ∈ ps, w.spender = p.addr ∧ p.ownScalars ≠ 0
  | [], _, h => by cases h
  | p :: ps, t, h => by
    unfold loneWants at h
    dsimp only at h
    rcases List.mem_append.mp h with h | h
    · split at h
      · unfold loneSumWants at h
        split at h
        · rename_i hc
          rcases List.mem_singleton.1 h with rfl
          simp only [Bool.and_eq_true, bne_iff_ne] at hc
          exact ⟨p, List.mem_cons_self, rfl, by simpa using hc.2⟩
        · cases h
      · cases h
    · obtain ⟨q, hq, e⟩ := loneWants_parts ps _ h
      exact ⟨q, List.mem_cons_of_mem _ hq, e⟩

/-- **What spendingBook returns, at its field ahead**, with who wants: spendingBook_ahead, and of
the wants that each names a part with scalars. -/
theorem spendingBook_wants {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B₀ : ProverCoinCounts} (h : spendingBook F p0 p1 p2 M = .ok B₀) :
    ∃ (ws : List Want) (f0 f1 f2 : List Ahead),
      (∀ w ∈ ws, ∃ b ∈ F.first.blocksInOrder, ∃ p ∈ planParts b, w.spender = p.addr ∧ p.ownScalars ≠ 0) ∧
      foldEntries (planOf F.first.blocksInOrder) (planOf F.second.blocksInOrder) p0 = .ok f0 ∧
      foldEntries (planOf F.shared.blocksInOrder) [] p1 = .ok f1 ∧
      foldEntries (planOf F.second.blocksInOrder) [] p2 = .ok f2 ∧
      B₀.ahead = ws.map (·.entry) ++ f0 ++ f1 ++ f2 ++ (splitEntry F.shared.blocksInOrder p1).toList := by
  unfold spendingBook at h
  obtain ⟨r0, -, h⟩ := ex_bind h
  obtain ⟨r1, -, h⟩ := ex_bind h
  obtain ⟨r2, -, h⟩ := ex_bind h
  rcases hidx : ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
      "link 0, moment 0" isIndexMaskMsg with _ | idx
  · rw [hidx] at h
    obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  rw [hidx] at h
  obtain ⟨idx', hy, h⟩ := ex_bind h
  obtain rfl : idx = idx' := Except.ok.inj hy
  obtain ⟨a, ha, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨f0, hf0, h⟩ := ex_bind h
  obtain ⟨f1, hf1, h⟩ := ex_bind h
  obtain ⟨f2, hf2, h⟩ := ex_bind h
  have e := Except.ok.inj h
  refine ⟨a.1 ++ (loneWants idx M.lone
      ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1,
    f0, f1, f2, ?_, hf0, hf1, hf2, by subst e; rfl⟩
  intro w hw
  rcases List.mem_append.1 hw with h1 | h1
  · exact linksWants_parts _ _ a ha h1
  · obtain ⟨p, hp, e1, e2⟩ := loneWants_parts _ _ h1
    obtain ⟨b, hb, hpb⟩ := List.mem_flatMap.1 hp
    exact ⟨b, List.mem_of_mem_filter hb, p, hpb, e1, e2⟩

/-- The round that findIdx finds by the name "SPLIT" has that name. -/
theorem findIdx_split (L : List Fmt.DeclaredRound) {r : Fmt.DeclaredRound}
    (h : L[L.findIdx fun r : Fmt.DeclaredRound => r.entry.name == "SPLIT"]? = some r) :
    r.entry.name = "SPLIT" := by
  obtain ⟨hl, e⟩ := List.getElem?_eq_some_iff.1 h
  subst e
  exact beq_iff_eq.1 (List.findIdx_getElem (w := hl))

/-- A part of planParts stands at its block's place. -/
theorem planParts_place {b : Block S Cl} {p : PartAt} (hp : p ∈ planParts b) :
    p.addr.place = b.place := by
  unfold planParts at hp
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
  rfl

theorem mem_planOf {bs : List (Block S Cl)} {b : Block S Cl} (hb : b ∈ bs) :
    (⟨b.place, partsCut b, b.rounds⟩ : PlanB) ∈ planOf bs :=
  List.mem_map.2 ⟨b, hb, rfl⟩

/-- **THE LAW.** Where every round at the place a in the three plans is a sending's, and no fold's
first sending behind it stands at a, no entry of the whole book has its spender at a. -/
theorem no_spender {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) {a : Place}
    (n1 : SendOnly a (planOf F.first.blocksInOrder)) (n2 : SendOnly a (planOf F.shared.blocksInOrder))
    (n3 : SendOnly a (planOf F.second.blocksInOrder))
    (q1 : ∀ i p q, behindFold (planOf F.first.blocksInOrder) i = some (p, q) → q.place ≠ a)
    (q2 : ∀ i p q, behindFold (planOf F.shared.blocksInOrder) i = some (p, q) → q.place ≠ a)
    (q3 : ∀ i p q, behindFold (planOf F.second.blocksInOrder) i = some (p, q) → q.place ≠ a) :
    ∀ e ∈ B.ahead, e.spender.place ≠ a := by
  intro e he hpl
  unfold bookWhole at hB
  obtain ⟨W, hW, hc⟩ := ex_bindE hB
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB₀, -, -, hseg, -, hcF, -, hcO, hpq, -, eW⟩ :=
    bookRaw_ahead hW
  obtain ⟨ws, f0, f1, f2, hws, hf0, hf1, hf2, eB⟩ := spendingBook_wants hB₀
  have nofold : ∀ l : List PlanB, SendOnly a l → ∀ x ∈ l, x.place = a →
      ∀ d ∈ x.rounds, d.entry.name ≠ "FOLD epsilon" := by
    intro l hl x hx ex d hd hn
    rcases hl x hx ex d hd with h | h <;> · rw [hn] at h; exact absurd h (by decide)
  rw [eW, eB] at he
  simp only [List.mem_append] at he
  rcases he with ((((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h1
    obtain ⟨b, hb, p, hp, e1, e2⟩ := hws w hw
    have hbp : b.place = a := by
      rw [← planParts_place hp, ← e1]
      exact hpl
    exact e2 (ownScalars_zero (n1 _ (mem_planOf hb) hbp) hp)
  · obtain ⟨x, hx, ex, d, hd, hnm⟩ := foldEntries_spender hf0 e h1
    rcases List.mem_append.1 hx with hx | hx
    · exact nofold _ n1 x hx (ex.trans hpl) d hd hnm
    · exact nofold _ n3 x hx (ex.trans hpl) d hd hnm
  · obtain ⟨x, hx, ex, d, hd, hnm⟩ := foldEntries_spender hf1 e h1
    rw [List.append_nil] at hx
    exact nofold _ n2 x hx (ex.trans hpl) d hd hnm
  · obtain ⟨x, hx, ex, d, hd, hnm⟩ := foldEntries_spender hf2 e h1
    rw [List.append_nil] at hx
    exact nofold _ n3 x hx (ex.trans hpl) d hd hnm
  · have hs := K14.split_spender (Option.mem_toList.1 h1)
    obtain ⟨b, hb, ep, r, hr, er⟩ := addrOfRound_holds _ _ _ hs
    have hget := findIdx_split _ er
    rcases n2 _ (mem_planOf hb) (ep.trans hpl) r hr with h | h <;>
      · rw [hget] at h; exact absurd h (by decide)
  · obtain ⟨i, p, q, hb, hs⟩ := segmentCarries_pq hseg e h1
    exact fold_off n1 q1 hb hs hpl
  · obtain ⟨i, p, q, hb, hs⟩ := groupCarries_pq hcF e h1
    exact fold_off n2 q2 hb hs hpl
  · obtain ⟨i, p, q, hb, hs⟩ := groupCarries_pq hcO e h1
    exact fold_off n2 q2 hb hs hpl
  · have hb : behindFold (planOf F.second.blocksInOrder) 0 = some (pq.1, pq.2) := due_some hpq
    exact fold_off n3 q3 hb (BookPlain.carryPair_spender e h1) hpl
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 h1
    obtain ⟨i, hb⟩ := ownFresh_pq ho
    exact fold_off n2 q2 hb (Or.inr rfl) hpl

end ProofFile.Honest.K1.Pay

#print axioms ProofFile.Honest.K1.Pay.no_spender
