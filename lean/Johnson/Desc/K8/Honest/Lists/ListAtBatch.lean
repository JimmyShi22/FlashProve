-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/Lists/ListAtBatch.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: AT
EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING, AT ALL 25
SEGMENTS, THE OPEN LINK's LIST HAS AN ENTRY FOR EACH ARRAY OF THE OPEN LEDGER: IN THE GOALS' SCOPE,
THE FILES READ, UNDER AN OPENING OF THE DESCRIPTION. THAT ANY SUCH STATE IS REACHED IS NOT SHOWN.
Lemmas; none of the library's goals.

  `ntOfBuilt built l` the built links' lists' entries, by the link's number; `tpOk_at`, `ntOf_at`,
                   `letters_tp`: it is what `seatKeeps_list` asks, at the built links, at the blank
                   letters' links and at the head's link's letters
  `link_none_of_fork` where no ledger is open, no link is
  **`list_at_batch`** the scope · the files read · the opening · l < 25 · the built segment Xl · a
                   state reached at 14 l + (if l = 24 then 11 else 9) ⊢ there is L with s.link? =
                   some L, L.link = l and L.list.nt = Xl.Tp.nt
  `builtTrees_at_blank` the scope · the files read · the opening · l < 25 · the built segment Xl ⊢
                   Xl.Fp.trees.size = Xl.Tp.nt.size
  **`listSize_at_batch`** the premises of `list_at_batch` ⊢ for all G, a0 with s.fork? = some G and
                   K9.atS.get? s = some a0: a0.L.list.nt.size = G.trees.size
By: `seatKeeps_list` (Johnson/Desc/K8/Honest/Lists/ListSeat.lean) · the library's
Meaning.K2.open_fold (Johnson/IMR/OpenWalk.lean), Meaning.K2.group_all (GroupHead.lean),
Meaning.Carry.front_len, LinkJoin.start_none (Johnson/LPFK9R/LooksSeat.lean), Meaning.K2.blank_built
(Johnson/IMR/OwnSeat.lean), LinkJoin.zip_lists, LinkJoin.built_trees (Johnson/P5T/NamesAtMg.lean),
ProofFile.Law.pub_builtOf, LinkJoin.part_reads · `arrayNames_at_batch` (NamesAtBatch.lean), by the lists'
lengths.
WRITTEN A FURTHER TIME: `list_at_batch` is `arrayNames_at_batch`'s proof at another seat ·
`tpOk_at`, `letters_tp` after the library's arrOk_at, letters_arr (OwnSeat.lean) ·
`builtTrees_at_blank`'s second half is the proof of the library's names_of_pub (NamesAtMg.lean),
which ends in another size. KIN: the library's link_between (Johnson/IMR/ListsAtDraw.lean: between
the segments no link is open) beside `link_none_of_fork`.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `simp [a
list]` on seven lines · `simp only [a list]` on one · `omega` on two, behind `split_ifs`, on numbers
of segments and borders alone.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED IN FRONT OF A BATCHING: where none is, all is idle.
IN SCOPE ALONE: the full size; the first chain; at OnBytes.secondHashFunction. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.Lists.ListSeat
import Johnson.Desc.K8.Honest.NamesAtBatch
import Johnson.Desc.First.Link.Law.AtBatchOpen
import Johnson.P5T.NamesAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.K2 (blank_built)

/-- The built links' lists' entries, by the link's number. -/
def ntOfBuilt (built : Array LinkH) (l : ℕ) : Array N2 := (built.map (·.Tp.nt)).getD l #[]

theorem tpOk_at (built : Array LinkH) : TpOk (ntOfBuilt built) built := fun l X h => by
  unfold ntOfBuilt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, h]
  rfl

/-- Of the blank letters' link number l. -/
theorem ntOf_at {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G) {l : ℕ} {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    Xl.Tp.nt = ntOfBuilt Z.p.built.links l := by
  obtain ⟨links, e⟩ := blank_built h
  rw [e] at e3
  obtain ⟨b, hb, -, u2⟩ := LinkJoin.zip_lists e3
  rw [u2]
  exact tpOk_at _ l b hb

/-- The head's link's letters, off the blank letters, bear the built link's list. -/
theorem letters_tp {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G) {l : ℕ} {P : First.K2.HeadPar}
    (hP : P1K2.pureLetters G l = some P) : P.X.Tp.nt = ntOfBuilt Z.p.built.links P.l := by
  unfold P1K2.pureLetters at hP
  obtain ⟨X', hX', rfl⟩ := Option.map_eq_some_iff.1 hP
  exact ntOf_at h hX'

/-- Where no ledger is open, no link is. -/
theorem link_none_of_fork {s : S} (h : s.fork? = none) : s.link? = none := by
  cases hh : s.here with
  | lay a => simp [S.fork?, hh] at h
  | att a => simp [S.fork?, hh] at h
  | head a =>
    by_cases ho : a.opened = true
    · simp [S.fork?, hh, ho] at h
    · simp [S.link?, hh, ho]
  | between => simp [S.link?, hh]
  | fin a => simp [S.link?, hh]
  | mem a => simp [S.link?, hh]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING: a link is open, with the segment's
number, and its list has the built segment's entries.** -/
theorem list_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ L, s.link? = some L ∧ L.link = l ∧ L.list.nt = Xl.Tp.nt := by
  obtain ⟨-, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.reach_fold.1 h
  have hk' : 14 * l + (if l = 24 then 11 else 9) ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.Carry.front_len hS hR O]
    split_ifs <;> omega
  obtain ⟨L, h1, h2, -⟩ := Meaning.K2.group_all hS hR O hl
    (k := 14 * l + (if l = 24 then 11 else 9)) (by split_ifs <;> omega) (by split_ifs <;> omega) f
  have hlk : L.list.nt = ntOfBuilt Z.p.built.links L.link :=
    Meaning.K2.open_fold (seatKeeps_list (tOf := ntOfBuilt Z.p.built.links)) O (tpOk_at _)
      (fun l Q hQ => letters_tp O.blank hQ) hk' f
      (fun L hL => by
        rw [link_none_of_fork (LinkJoin.start_none O.pub z)] at hL
        cases hL) L h1
  rw [h2] at hlk
  exact ⟨L, h1, h2, hlk.trans (ntOf_at O.blank e3).symm⟩

/-- In scope the built segment's ledger has as many arrays as its list has entries, at the blank
letters' own link. -/
theorem builtTrees_at_blank (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : Xl.Fp.trees.size = Xl.Tp.nt.size := by
  obtain ⟨links, e⟩ := blank_built O.blank
  rw [e] at e3
  obtain ⟨b, hb, u1, u2⟩ := LinkJoin.zip_lists e3
  have hW : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    rw [← O.W]
    exact O.public
  obtain ⟨bt, hbt, e'⟩ := ProofFile.Law.pub_builtOf O.pub
  rw [← e'] at hb
  have hX' : (bt.links.map ProofFile.Law.blank)[l]? = some b := hb
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  have k : Y.Fp.trees.size = Y.Tp.nt.size := LinkJoin.built_trees hS hR hW hbt hl hY
  rw [u1, u2]
  exact k

/-- **THE CLAUSE: the link's list has an entry for each array of the open ledger.** -/
theorem listSize_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∀ G a0, s.fork? = some G → K9.atS.get? s = some a0 → a0.L.list.nt.size = G.trees.size := by
  intro G a0 hG h0
  obtain ⟨L, h1, -, h3⟩ := list_at_batch hS hR O hl e3 h
  obtain rfl : a0.L = L := Option.some.inj ((LinkJoin.part_reads s a0 h0).1.symm.trans h1)
  have hn := congrArg List.length (arrayNames_at_batch hS hR O l hl Xl e3 z s h G hG)
  simp only [arrayNames, List.length_map, Array.length_toList] at hn
  rw [h3, ← builtTrees_at_blank hS hR O hl e3, hn]

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.tpOk_at
#print axioms VerifiableInference.Desc.First.K8.Honest.ntOf_at
#print axioms VerifiableInference.Desc.First.K8.Honest.letters_tp
#print axioms VerifiableInference.Desc.First.K8.Honest.link_none_of_fork
#print axioms VerifiableInference.Desc.First.K8.Honest.list_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.builtTrees_at_blank
#print axioms VerifiableInference.Desc.First.K8.Honest.listSize_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.ntOfBuilt
