-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/TupleOfMembers.lean:
The proximity test (the kind K12), first arm, at the numbering of trees by labels: ONE
TUPLE OF TYPED MESSAGES BEHIND OUR GAME's RELATION QW (GameOut.lean), WITH WHAT IS OWED OF EACH
MEMBER OF THE GROUP UNDER TEST WRITTEN AS ONE LEAN STRUCTURE. General in the IOP as written in Lean,
the frame, the place, the doors, the first tree's number, AND IN THE NUMBER OF MEMBERS. A
definition, statements and proofs; each proof is calls and a count.
  `MemberAt`: at the verifier's state t behind the door in, strings y, a message's number o and a
    member x of a sending: `MemberPub` (WordAtMember.lean: no state is read) · the sendings'
    invariant K1.SeedIs at o, at x's listed shape · the reading of out-of-domain (OOD) samples is
    K1.smpAt at o · mem lays x at o · the book places o at x's seat, and the tree there has the told
    shape · every leaf of x's word is shown.
  `memberFacts_at`:
    `MemberAt` and the two «accept»s (the decision's own; the plain data's tests') ⊢ `MemberFacts`
    (Johnson/Desc/Sound/SeamMembers.lean) at whatever the state fixes: `memberFacts_of`
    (SeamMemberOf.lean) with the site's «accept» by `site_of_mem` | `site_mask` (ShapesAtSeat.lean), the
    sample's by `hQ_of_yes` (CoreAtYes.lean), the word by `word_at`, the depth by `log_at`. WHY NOT
    `MemberLeft`: its first arm for the site asks of a shape without mask rows that its mask
    code's number lie beyond the list of codes: true of the key file's U; FALSE, by an evaluation at
    the stored full-size files, of the one member of the proof file's first chain's last test.
  `tuple_of_members`: QW · johOk · planOk · at the state behind the door in: the codes · "in
    order" · the book in order · the mask has come · each member o of the group under test stands in
    a relation Rel to some x with `MemberAt`, and Rel gives one x to at most one o ⊢ one tuple of
    typed messages of which all rows taken in hold, a candidate at whatever mem lays at a member of
    the group: `core_behind_QWn` ∘ `coreLeft_of_members` (CoreBehindQ.lean), as `core_behind_QWm₂`'s
    own proof goes, with `memberFacts_at` at each member.
KIN: our K12Members29.lean (`left_29`): the like at the key file's row 2.9, at two named members.
What it is not. `MemberAt` is a premise: no field of it is shown here. A SHAPE WITH ROWS OF BOTH
KINDS IS NOT SERVED (`MemberPub.one`). The second arm's like is not typed. No example. It pays no
field of a table. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.WordAtMember
import Johnson.Desc.K12.Coin.MemberOfSeed
import Johnson.Desc.K12.Coin.MembersLaid
import Johnson.Desc.Sound.SeamGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open OnBytes.Maker
open _root_.Run
open H2K.First (Seat1 Plain gpL)
open H2K.Pub (sgOf johOk)
open _root_.Desc.K14.Law.Fence (codes_fixed MemberFacts memberFacts_of seed_at_member)

/-- **What is owed of one member of the group under test.** -/
structure MemberAt (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12) (lo : ℕ)
    (r : Fmt.M1.Stage → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (t : T12) (y : Fr.E.Str) (a0 : A) (o : ℕ) (x : Mem) : Prop where
  pub : MemberPub cs G Fr π r x
  /-- the sendings' invariant at the message's number, at the member's listed shape -/
  seed : ∃ ρ yv, K1.SeedIs cs (x.1.l.get x.2).1 t.st o ρ yv
  /-- the reading of OOD samples is the kind's own at that number -/
  reads : smp a0 x.1 x.2 = K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 t.st o
  laid : mem o = some x
  /-- the book places the message at the member's seat, and the tree there has the told shape -/
  place : ∃ q, t.book.place[o]? = some q ∧ x.1.seat x.2 = (lo + q.1, q.2) ∧
    ∀ u, G.oracleAt (x.1.seat x.2).1 = some u →
      ∀ T, t.book.trees[q.1]? = some T → ShapeIs T.shape u
  shown : ShownAt G cs x.1.l x.1.seat (strsOf Fr y) x.2

/-- **A member's seven clauses at whatever the state fixes, from `MemberAt` and the two «accept»s.** -/
theorem memberFacts_at (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (lo ft : ℕ) (r : Fmt.M1.Stage → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (t : T12) (y : Fr.E.Str) (a0 : A) (o : ℕ) (x : Mem)
    (h : MemberAt cs G Fr π lo r smp mem t y a0 o x) (hmk : t.mask.isSome = true)
    (hft : π.nums.firstTree = ft) (hB : BookOrd ft t.book) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hy : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (s : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t s rest G0 Ly D) (row : GroupRow)
    (hok : H2K.First.ok (gpL π s row D) = true) (hcs : D.st.codes = cs)
    (j : Fin D.mems.length) (hj : (D.mems.get j).id = o) :
    MemberFacts cs G Fr (nuOf π (nlAt π lo) t) (fun q => r q.st) smp mem y a0 (strsOf Fr y) s D j x
      (x.1.l.get x.2).2 := by
  subst hj
  subst hcs
  obtain ⟨ρ, yv, hs⟩ := h.seed
  obtain ⟨q, hq, hseat, htold⟩ := h.place
  obtain ⟨hsh, hsd⟩ := seed_at_member hf row j h.pub.tie hs
  have hlog := log_at π ft t D.st.codes G hf hmk hft hB j q hq x h.pub.fits htold
  refine memberFacts_of D.st.codes G Fr _ _ smp mem y a0 _ π t s rest G0 Ly D hf j x
    (x.1.l.get x.2).1 (x.1.l.get x.2).2 rfl h.pub.tie ρ yv hs h.reads ?_ ?_
    (h.pub.fit s rest hf.1) h.laid
    (heq_of_eq (word_at π lo ft t D.st.codes G Fr hf hmk hft hB j q hq x hseat y h.pub.fits h.shown
      htold h.pub.depth).symm)
  · rcases h.pub.site with s1 | ⟨s1, s2, s3⟩
    · have s1' : 0 < (D.mems.get j).sh.mainRows := by rw [hsh]; exact s1
      refine site_of_mem D.st.codes s D.L j.val (D.mems.get j) (mem_of_ok π s row D hok j)
        (fun c => absurd c (Nat.pos_iff_ne_zero.1 s1')) (fun _ => ?_)
        (fun c => absurd c (Nat.pos_iff_ne_zero.1 s1'))
      rw [hlog, hsh]
      exact Nat.le_max_right _ _
    · exact site_mask π s row D hok j (by rw [hsh]; exact s1) (by rw [hsh]; exact s2)
        (by rw [hlog]; exact s3 s rest hf.1)
  · exact hQ_of_yes π he hp t tE rs gs hy s rest G0 Ly D hf row hok j hsd
      (by rw [hsh]; exact h.pub.tie.one) (by rw [hsh]; exact h.pub.one)
      (by rw [hsh]; exact h.pub.site.imp id fun c => c.1) (by rw [hsh]; exact h.pub.case)

/-- **One tuple of typed messages behind QW, general in the members.** -/
theorem tuple_of_members {P S Xi A : Type} (cs : Codes) (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (lo ft : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × Fr.E.Str) (a0 : A) (h : QW Fr π (nlAt π lo) r rdN enter leave a b)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hft : π.nums.firstTree = ft) (Rel : ℕ → Mem → Prop)
    (hinj : ∀ o o' x, Rel o x → Rel o' x → o = o')
    (hcod : ∀ t, enter a.1.2 = .ok t → t.st.codes = cs)
    (hI : ∀ t, enter a.1.2 = .ok t → InOrder t.st)
    (hB : ∀ t, enter a.1.2 = .ok t → BookOrd ft t.book)
    (hmk : ∀ t, enter a.1.2 = .ok t → t.mask.isSome = true)
    (hex : ∀ t G0, enter a.1.2 = .ok t → t.st.groups[t.g]? = some G0 →
      ∀ o ∈ G0.members.toList, ∃ x, Rel o x ∧ MemberAt cs G Fr π lo r smp mem t a.2 a0 o x) :
    ∃ t G0, enter a.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
      ∃ m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
        AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT cs mem rd m) ∧
        ∀ o ∈ G0.members.toList, ∀ x, mem o = some x →
          CandAt cs G smp x a0 (strsOf Fr a.2) (m x) := by
  have he := H2K.JointK.early_of_planOk π hp
  obtain ⟨t0, tE, h1, _, hq, rs, gs, hy⟩ := id h
  obtain ⟨s0, rest0, G00, Ly0, D0, hf0, row₀, hok, _⟩ := id hq
  obtain ⟨t, G0, ht, hG, m, hall, hc⟩ := core_behind_QWn cs G Fr π (nlAt π lo) r rdN smp mem
    (fun z => ∃ t G0 o, enter a.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
      o ∈ G0.members.toList ∧ mem o = some z)
    rd hrd enter leave a b a0 (strsOf Fr a.2) h hj he hp
    (fun t ht => by
      obtain rfl : t0 = t := Except.ok.inj (h1.symm.trans ht)
      refine coreLeft_of_members cs G Fr π _ _ smp mem _ t0 a.2 a0 _ fun s rest G0 Ly D hf => ?_
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fixes_one π t0 hf0 hf
      have hG : t0.st.groups[t0.g]? = some G00 := hf.2.1
      obtain ⟨hlen, hid⟩ := mems_ids π t0 s0 rest0 G00 Ly0 D0 hf
      have hid' : ∀ j : Fin D0.mems.length,
          G00.members.toList[j.val]? = some (D0.mems.get j).id := fun j => by
        rw [Array.getElem?_toList]
        exact hid j
      have hmemb : ∀ j : Fin D0.mems.length, (D0.mems.get j).id ∈ G00.members.toList :=
        fun j => List.mem_of_getElem? (hid' j)
      choose xs hxs using fun j : Fin D0.mems.length => hex t0 G00 ht hG _ (hmemb j)
      have hnd : G00.members.toList.Nodup := ((hI t0 ht).groups t0.g G00 hG).nodup
      have hcs : D0.st.codes = cs := (codes_fixed π t0 s0 rest0 G00 Ly0 D0 hf).trans (hcod t0 ht)
      refine ⟨hcs, xs, fun j => ((xs j).1.l.get (xs j).2).2, ?_, ?_, ?_⟩
      · intro j j' e
        have e1 : (D0.mems.get j).id = (D0.mems.get j').id :=
          hinj _ _ _ (hxs j).1 (by rw [e]; exact (hxs j').1)
        have hlt : j.val < G00.members.toList.length := by
          rw [Array.length_toList, ← hlen]
          exact j.isLt
        exact Fin.ext (List.getElem?_inj hlt hnd (by rw [hid' j, hid' j', e1]))
      · rintro z ⟨t', G0', o, ht', hG', ho, hz⟩
        obtain rfl : t0 = t' := Except.ok.inj (ht.symm.trans ht')
        obtain rfl : G00 = G0' := Option.some.inj (hG.symm.trans hG')
        obtain ⟨i, hi, hio⟩ := List.mem_iff_getElem.1 ho
        have hi' : i < D0.mems.length := by
          rw [hlen, ← Array.length_toList]
          exact hi
        have e2 : (D0.mems.get ⟨i, hi'⟩).id = o := by
          have := hid' ⟨i, hi'⟩
          rw [List.getElem?_eq_getElem hi, hio] at this
          exact (Option.some.inj this).symm
        refine ⟨⟨i, hi'⟩, ?_⟩
        have e3 := (hxs ⟨i, hi'⟩).2.laid
        rw [e2, hz] at e3
        exact (Option.some.inj e3).symm
      · exact fun j => memberFacts_at cs G Fr π lo ft r smp mem t0 a.2 a0 _ (xs j) (hxs j).2
          (hmk t0 ht) hft (hB t0 ht) he hp tE rs gs hy s0 rest0 G00 Ly0 D0 hf row₀ hok hcs j rfl)
    hI
  exact ⟨t, G0, ht, hG, m, hall, fun o ho x hx => hc x ⟨t, G0, o, ht, hG, ho, hx⟩⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.memberFacts_at
#print axioms VerifiableInference.Desc.K12.Coin.tuple_of_members
