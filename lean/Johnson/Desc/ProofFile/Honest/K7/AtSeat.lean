-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/AtSeat.lean: the round that names the next token (kind K7) at a
thread of the first chain of the proof file's description, at border 338. In scope, at the chain c of
`IM.Open`, the seat and the record that Honest/K7/Plays.lean and Honest/K7/Lays.lean take as premises hold
at every thread whose list of sub-protocols is c.blocksInOrder and whose prover's sides find the kind's half at
the place. So at such a thread the member plays and lays the reply's clause.

  `k7_at_flat`   the member is number 338 of the chain's flat list
  `fresh_nil_of_oracles`   a member with no oracle message has no new tree
  `find_of_twice`, `reply_found`   where no two sides stand at one place, the look-up by the place
                   finds the side; so it finds the kind's half where a lot of the filling is `replyLot`
  `k7_stands_of_open`   the seat `K7Stands` and the record `K7Made`
  `k7_plays_at`, `k7_lays_at`   the member plays; the clause is laid

A thread is a letter here. Nothing is said of the member's own step: whether it accepts is a further
statement. This file proves nothing about soundness, completeness, hiding or any other property of
the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.Lays
import Johnson.Desc.ProofFile.Honest.K7.RowsAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The member is number 338 of the chain's flat list**, in scope. -/
theorem k7_at_flat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ blk : Block S Cl, c.blocksInOrder[338]? = some blk ∧ blk.place = IM.k7Place ∧
      blk.rounds = VerifiableInference.Desc.Kinds.Reply.rounds ∧ blk.oracles = [[]] ∧
      IM.Joined Z 24 blk (IM.k7Block Bs.G₀.W 24).retype IM.k7Place := by
  obtain ⟨Lk, b, e1, e2, hJ, -⟩ := IM.k7_sits hS hR O
  have hplaces := IM.places_scope hS hR O
  have hn : (c.blocksInOrder.map (·.place)).Nodup := by
    rw [hplaces]
    exact IM.places_nodup
  have hm : b ∈ c.blocksInOrder := List.mem_of_getElem? (IM.hear_at_flat e1 e2)
  have h338 : IM.placesW[338]? = some IM.k7Place := by decide +kernel
  rw [← hplaces, List.getElem?_map] at h338
  obtain ⟨b', hb', hp'⟩ := Option.map_eq_some_iff.1 h338
  obtain ⟨fr, f, h1, h2, e⟩ := id hJ
  have hp : b.place = IM.k7Place := by
    rw [e]
    rfl
  have hm' : b' ∈ c.blocksInOrder := List.mem_of_getElem? hb'
  obtain rfl : b' = b := List.inj_on_of_nodup_map hn hm' hm (hp'.trans hp.symm)
  refine ⟨b', hb', hp, ?_, ?_, hJ⟩
  · rw [e]
    rfl
  · rw [e]
    rfl

end

section
variable {Bk : ProverCoinCounts} {St Cl' V W X Pb : Type}

/-- A member with no oracle message has no new tree. -/
theorem fresh_nil_of_oracles (T : Thread Bk St Cl' V W X Pb) {b : Nat} {blk : Block St Cl'}
    (h : T.bs[b]? = some blk) (ho : blk.oracles.flatMap id = []) : T.fresh b = [] := by
  have e : treesTo T.bs (b + 1) = treesTo T.bs b := by
    unfold treesTo
    rw [List.take_add_one, h]
    simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, ho,
      List.append_nil]
  unfold Thread.fresh Thread.hand
  rw [e, List.filter_eq_nil_iff]
  intro σ hσ
  simp
  intro hn
  simp at hσ
  exact hσ.resolve_left hn

/-- Where no two sides stand at one place, the look-up by a side's place finds that side. -/
theorem find_of_twice {hs : List (Placed V W X)} {h : Placed V W X} (hm : h ∈ hs)
    (ht : twice hs = []) : hs.find? (fun x => x.place == h.place) = some h := by
  have hone : (hs.filter fun x => x.place == h.place).length ≤ 1 := by
    by_contra hc
    have hin : h.place ∈ ((hs.map (·.place)).filter fun a =>
        1 < (hs.filter fun x => x.place == a).length) := by
      refine List.mem_filter.2 ⟨List.mem_map.2 ⟨h, hm, rfl⟩, ?_⟩
      exact decide_eq_true (Nat.lt_of_not_le hc)
    unfold twice at ht
    have hnil : ∀ l : List Place, l.eraseDups = [] → l = [] := by
      intro l hl
      cases l with
      | nil => rfl
      | cons a t =>
        rw [List.eraseDups_cons] at hl
        cases hl
    rw [hnil _ ht] at hin
    cases hin
  have hself : h ∈ hs.filter fun x => x.place == h.place :=
    List.mem_filter.2 ⟨hm, beq_self_eq_true _⟩
  have hsome : (hs.find? fun x => x.place == h.place).isSome = true :=
    List.find?_isSome.2 ⟨h, hm, beq_self_eq_true _⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
  have e₀ := List.find?_some hy
  have hy' : y ∈ hs.filter fun x => x.place == h.place :=
    List.mem_filter.2 ⟨List.mem_of_find?_eq_some hy, e₀⟩
  have one : ∀ (l : List (Placed V W X)) (a b : Placed V W X), l.length ≤ 1 → a ∈ l → b ∈ l →
      a = b := by
    intro l a b hl ha hb
    match l, hl, ha, hb with
    | [x], _, ha, hb =>
      rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]
  rw [hy, one _ y h hone hy' hself]

end

/-- **The look-up finds the kind's half**, where a lot of the filling is `replyLot`, the ground has 25
links, and no two sides stand at one place. -/
theorem reply_found {W₀ Rc Tr X : Type} {Zp : ProofFile.Pub} {G : ProofFile.Ground}
    {ls : List (HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)} (hl : replyLot ∈ ls)
    (hsz : G.built.size = 25) (ht : twice (firstOf Zp G ls) = []) :
    (firstOf Zp G ls).find? (fun x => x.place == IM.k7Place) =
      some (replyHalf 24 1 G.W.hS.V) := by
  have hm : replyHalf (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X) 24 1 G.W.hS.V ∈ firstOf Zp G ls := by
    unfold firstOf
    refine List.mem_flatMap.2 ⟨replyLot, hl, ?_⟩
    show _ ∈ [replyHalf (G.built.size - 1) 1 G.W.hS.V]
    rw [hsz]
    exact List.mem_singleton.2 rfl
  exact find_of_twice hm ht

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb : Type}

/-- **The seat and the record**, at every thread whose list is c.blocksInOrder and whose sides find the kind's
half at the place. -/
theorem k7_stands_of_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb) (hbs : T.bs = c.blocksInOrder)
    {V : Nat} (hhalf : T.hs.find? (fun h => h.place == IM.k7Place) = some (replyHalf 24 1 V)) :
    ∃ (blk : Block S Cl) (x : Block S Unit) (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
      (f : Johnson.Desc.First.Walk.Seat.LinkFrame),
      K7Stands T 338 24 V blk ∧ K7Made Z Bs.G₀ 24 blk x IM.k7Place fs f := by
  obtain ⟨blk, hb, hp, hr, ho, hJ⟩ := k7_at_flat hS hR O
  obtain ⟨fs, f, h1, h2, e⟩ := id hJ
  have hmem : T.bs[338]? = some blk := by
    rw [hbs]
    exact hb
  have hsz := (IM.ground_gets hS hR O.pub O.blank).1
  have hx : ∃ x : Block S Unit, x ∈ ProofFile.h1Own Bs.G₀ ∧
      IM.Joined Z 24 blk x.retype IM.k7Place := by
    unfold ProofFile.h1Own
    rw [hsz]
    exact ⟨_, List.mem_singleton.2 rfl, hJ⟩
  obtain ⟨x, hxm, hxJ⟩ := hx
  refine ⟨blk, x, fs, f, ⟨hmem, hr, ho, ?_, ?_⟩, ⟨hxm, hxJ, h1, h2⟩⟩
  · rw [hp]
    exact hhalf
  · exact fresh_nil_of_oracles T hmem (by rw [ho]; rfl)

/-- **The member plays**, at every letter. -/
theorem k7_plays_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb) (hbs : T.bs = c.blocksInOrder)
    {V : Nat} (hhalf : T.hs.find? (fun h => h.place == IM.k7Place) = some (replyHalf 24 1 V))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop) : PlaysS T Said 338 := by
  obtain ⟨blk, x, fs, f, K, -⟩ := k7_stands_of_open hS hR O T hbs hhalf
  exact k7_playsS Said K

/-- **The reply's clause is laid**, at every letter. -/
theorem k7_lays_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb) (hbs : T.bs = c.blocksInOrder)
    {V : Nat} (hhalf : T.hs.find? (fun h => h.place == IM.k7Place) = some (replyHalf 24 1 V))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop) (lo hi : Nat) :
    LaysAtS T Said 338 ⟨lo, hi, fun _ v s => s.out.reply = some v.x.asked⟩ := by
  obtain ⟨blk, x, fs, f, K, D⟩ := k7_stands_of_open hS hR O T hbs hhalf
  exact k7_laysS Said K D lo hi

end

end ProofFile.Honest

#print axioms ProofFile.Honest.k7_at_flat
#print axioms ProofFile.Honest.fresh_nil_of_oracles
#print axioms ProofFile.Honest.find_of_twice
#print axioms ProofFile.Honest.reply_found
#print axioms ProofFile.Honest.k7_stands_of_open
#print axioms ProofFile.Honest.k7_plays_at
#print axioms ProofFile.Honest.k7_lays_at
