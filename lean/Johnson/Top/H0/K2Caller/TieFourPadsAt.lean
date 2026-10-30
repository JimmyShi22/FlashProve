-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TieFourPadsAt.lean: code switching: TWO PREMISES OF THE FOURTH TIE AT A
PLACE (k02_t4R, K2Caller/TieFourR.lean), hE AND hNd, at seatN := seatNew N m r (SeatsOfN.lean) and
minePad := minePadAt ms N links p (Johnson/Desc/Sound/BordersFill.lean): hNd from a test on public
lists alone; hE from such tests and the tie's own binder hext. Theorems with their proofs. NO
SUB-PROTOCOL IMPORTS THIS FILE. In this head l is the place's segment number,
p.link.getD links.length (the number of segments where the place has none: the last code switch),
and m the segment in front, l - 1.
  laysPads_cases    the tenants whose pads alone the extractor at a place lays are none, or those
                    of segment l - 1's group that the next segment keeps
  new_not_kept      where numbersFit os N n passes and m < n: no tenant of N.sent (m + 1) 0 is one
                    of N.keptOf m
  seatNew_off_pads  so no seat of the new sending's members is the seat of a member whose pad the
                    extractor at the place lays: the premise hs of msgsOf_ext (ExtMade.lean)
  msgs_stay_at      an extractor that is extAt at mine := [] and minePad := minePadAt ms N links p
                    leaves the new sending's typed messages. General in the extractor's arguments
  k02_t4R_hE        hE, from the binder hext (at any OOD samples smp in the place of
                    smpNamed r.cs seats)
  msgs_stay_table   the same of the table of joints' own extractor extQAt at sub-protocol number k,
                    where the place there is of the kind K2
  pads_nodup_once   hNd at ms := msOf L, from onceB L (N.keptOf (l - 1)) (MembersAtB.lean)
  k02_t4R_hNd       hNd from the whole test membersK2B (MembersAtK2.lean)
  new_long_enough   from membersK2B's last clause: no fewer new tenants than typed new members
  numbers_of_side   numbersFit is a clause of planSideOk (Johnson/Desc/First/BordersPlan.lean)
THE PREMISES. On public data: numbersFit os N n = true · m < n · l - 1 = m, A SUBTRACTION OF NATURAL
NUMBERS (0 - 1 = 0: a place of segment 0 passes it at m = 0; TieFourPadsAtPlan.lean asks l = m + 1)
· r.l.length ≤ (N.sent (m + 1) 0).length · onceB | membersK2B = true. NOT on public data alone:
hext (msgs_stay_at, k02_t4R_hE). At msgs_stay_table: ps[k]? = some p and p.kind = .K2.
THAT THE CONCLUSIONS ARE THE TIE's BINDERS is Lean's own comparison (up to unfolding, not letter by
letter): Johnson/Loose/PVK2/TieFourFits.lean applies k02_t4R to them. THE TESTS' VALUES at the
stored full-size example: Johnson/Loose/PVK2/PadsAtFull.lean evaluates them. NEITHER FILE IS IN
THIS LIBRARY. WHAT hNd ADDS to kept_at_table | kept_at_plan
(MembersAtK2.lean · MembersAtPlan.lean), which conclude it too: it asks no r.OK, no kind, no «the
row lays» and no seats of the old members.
LIMITS. The tests' values are premises; no theorem here shows one. WHERE THE EXTRACTOR AT p LAYS NO
PAD (p is not of the kind K2, or its row does not lay; and at the last code switch of the full size,
where nothing is kept) minePadAt ms N links p IS EMPTY AND BOTH CONCLUSIONS SAY LITTLE: hNd is of
the empty list, hE of an extractor that lays nothing. At such a p, with N.keptOf m not empty, the
tie's binder hAl (x ∈ minePad) cannot be met: THIS CHOICE OF minePad SERVES THE TIE ONLY AT A PLACE
OF THE KIND WHOSE ROW LAYS. WHERE THE NEW SENDING's LIST IS TOO SHORT seatNew FALLS TO (0, 0): the
premise on the lengths shuts that out. That a sub-protocol's extractor IS extAt at these lists is
the binder hext, shown by nobody here. That N, L and r are those of the program that makes the list
of rounds is said by nothing here; nor that N.sent (m + 1) 0 sits in the trees that the code switch
sends. No soundness is claimed. On hiding nothing.
-/
import Johnson.Top.H0.K2Caller.ExtMade
import Johnson.Top.H0.K2Caller.SeatsOfN
import Johnson.Top.H0.K2Caller.ExtAtK2
import Johnson.Top.H0.K2Caller.MembersAtK2
import Johnson.Desc.First.BordersPlan
import Johnson.Desc.First.Link.Law.EqNumbersOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Iop Cb Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc (FileDescription Strs Wit Place Oracle MemberLists oraclesOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Numbers numbersFit laysPads planSideOk)
open VerifiableInference.Desc.LinkJoin (eachOnce_nodup)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)

/-! ## 1 The numbers -/

/-- The tenants whose pads alone the extractor at a place lays: none, or those of the group of the
segment in front that the next segment keeps. -/
theorem laysPads_cases (N : Numbers) (links : List ModelPart) (p : Place) :
    laysPads N links p = [] ∨ laysPads N links p = N.keptOf (p.link.getD links.length - 1) := by
  unfold laysPads
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- **No tenant of the first sending of segment m + 1 is one of those of segment m's group that the
next segment keeps.** n: the number of segments. -/
theorem new_not_kept {os : List Oracle} {N : Numbers} {n m : ℕ} (h : numbersFit os N n = true)
    (hm : m < n) (q : ℕ × ℕ) (hq : q ∈ N.sent (m + 1) 0) : q ∉ N.keptOf m := by
  intro hk
  simp only [numbersFit, Bool.and_eq_true] at h
  obtain ⟨⟨-, h4⟩, h5⟩ := h
  have k1 := List.all_eq_true.1 h5 m (List.mem_range.2 hm)
  have k3 : q ∈ N.group m := List.contains_iff_mem.1 (List.all_eq_true.1 k1 q hk)
  have nd := (eachOnce_nodup _ h4).of_append_left.of_append_left
  have pw := (List.nodup_flatMap.1 nd).2
  have d := List.pairwise_iff_getElem.1 pw m (m + 1) (by rw [List.length_range]; omega)
    (by rw [List.length_range]; omega) (Nat.lt_succ_self m)
  rw [List.getElem_range, List.getElem_range] at d
  exact d k3 (List.mem_append_left _ (List.mem_append_left _ hq))

/-- **No seat of the new sending's members is the seat of a member whose pad the extractor at the
place lays.** -/
theorem seatNew_off_pads {os : List Oracle} {N : Numbers} {n m : ℕ} (ms : List Mem)
    (links : List ModelPart) (p : Place) (r : SwRow) (h : numbersFit os N n = true) (hm : m < n)
    (hp : p.link.getD links.length - 1 = m) (hl : r.l.length ≤ (N.sent (m + 1) 0).length)
    (i : Fin r.l.length) : seatNew N m r i ∉ (minePadAt ms N links p).map seatOf := by
  intro hi
  obtain ⟨x, hx, e⟩ := List.mem_map.1 hi
  unfold minePadAt at hx
  have h1 : seatOf x ∈ laysPads N links p := List.contains_iff_mem.1 (List.mem_filter.1 hx).2
  rw [e] at h1
  have h2 : seatNew N m r i ∈ N.keptOf m := by
    rcases laysPads_cases N links p with e0 | e0
    · rw [e0] at h1
      exact absurd h1 (by simp)
    · rw [e0, hp] at h1
      exact h1
  exact new_not_kept h hm _
    (List.mem_of_getElem? (seatNew_at N m r i (Nat.lt_of_lt_of_le i.2 hl))) h2

/-! ## 2 hE -/

/-- **An extractor that lays no message, and pads at the place's own members alone, leaves the new
sending's typed messages.** X, T: what the extractor reads beside the witness; at, st: the
statement and the oracle messages that it hands to extAt. -/
theorem msgs_stay_at {os : List Oracle} {N : Numbers} {n m : ℕ} {Xi A Cells Tok X T : Type}
    {r : SwRow} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf r.cs s.l).om i).Smp)
    (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells) (c₀ : Cells) (ms : List Mem)
    (links : List ModelPart) (p : Place) (tokNew : Option Tok)
    (ext' : X → T → Wit Cells Tok MsgT → Wit Cells Tok MsgT) (at' : X → A) (st : X → Strs)
    (hext : ∀ a τ w, ext' a τ w = extAt r.cs G arr smp decT c₀ [] (minePadAt ms N links p) false
      tokNew (at' a) (st a) w)
    (h : numbersFit os N n = true) (hm : m < n) (hp : p.link.getD links.length - 1 = m)
    (hl : r.l.length ≤ (N.sent (m + 1) 0).length) :
    ∀ a τ w, msgsOf r.cs r.l (seatNew N m r) arr (ext' a τ w) =
      msgsOf r.cs r.l (seatNew N m r) arr w := by
  intro a τ w
  rw [hext a τ w]
  exact msgsOf_ext r.cs G arr smp decT c₀ r.l (seatNew N m r) (minePadAt ms N links p) tokNew
    (at' a) (st a) w (seatNew_off_pads ms links p r h hm hp hl)

/-- **hE OF THE FOURTH TIE AT A PLACE**, from the tie's own binder hext, at seatN := seatNew N m r
and minePad := minePadAt ms N links p. smp stands where the tie has smpNamed r.cs seats. -/
theorem k02_t4R_hE {F : Frame} {os : List Oracle} {N : Numbers} {n m : ℕ}
    {P Cells Tok Xi : Type} {r : SwRow} (G : FileDescription Xi) (d₁ d₂ : RDT) (arr : ℕ → ℕ → ℕ)
    (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf r.cs s.l).om i).Smp)
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
    (c₀ : Cells)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (links : List ModelPart) (p : Place) (z : P) (ms : List Mem)
    (hext : ∀ a τ w, ext' a τ w = extAt r.cs G arr smp decT c₀ [] (minePadAt ms N links p) false
      none (z, a.1) (strsOf F a.2) w)
    (h : numbersFit os N n = true) (hm : m < n) (hp : p.link.getD links.length - 1 = m)
    (hl : r.l.length ≤ (N.sent (m + 1) 0).length) :
    ∀ a τ w, msgsOf r.cs r.l (seatNew N m r) arr (ext' a τ w) =
      msgsOf r.cs r.l (seatNew N m r) arr w :=
  msgs_stay_at G arr smp decT c₀ ms links p none ext' (fun a => (z, a.1))
    (fun a => strsOf F a.2) hext h hm hp hl

/-- **The same of the table of joints' own extractor at sub-protocol number k**, where the place
there is of the kind K2. -/
theorem msgs_stay_table {Fr : Frame} {os : List Oracle} {N : Numbers} {n m : ℕ}
    {P Cells Tok Xi A : Type} {r : SwRow} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf r.cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
    (c₀ : Cells) (tokOf : P × First.S → Tok) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) (p : Place) (hk : ps[k]? = some p) (hK : p.kind = .K2)
    (h : numbersFit os N n = true) (hm : m < n) (hp : p.link.getD links.length - 1 = m)
    (hl : r.l.length ≤ (N.sent (m + 1) 0).length) (a b : A × Fr.E.Str)
    (w : Wit Cells Tok MsgT) :
    msgsOf r.cs r.l (seatNew N m r) arr
        (extQAt r.cs G arr smp ms decT c₀ tokOf N links ps get k a b w) =
      msgsOf r.cs r.l (seatNew N m r) arr w := by
  rw [extQAt_k2 r.cs G arr smp ms decT c₀ tokOf N links ps get k p hk hK a b w]
  exact msgsOf_ext r.cs G arr smp decT c₀ r.l (seatNew N m r) (minePadAt ms N links p) none
    (get a.1) (strsOf Fr a.2) w (seatNew_off_pads ms links p r h hm hp hl)

/-! ## 3 hNd -/

/-- **The members whose pads the extractor at a place lays have different seats**, where no two
members of the plain lists sit at one tenant of the segment in front that the next segment keeps. At
every place: where the row lays no pad there is no such member. -/
theorem pads_nodup_once {L : MemberLists} (N : Numbers) (links : List ModelPart) (p : Place)
    (h : onceB L (N.keptOf (p.link.getD links.length - 1)) = true) :
    ((minePadAt (msOf L) N links p).map seatOf).Nodup := by
  unfold minePadAt
  rcases laysPads_cases N links p with e0 | e0
  · rw [e0]
    have e : ((msOf L).filter fun x => ([] : List (ℕ × ℕ)).contains (x.1.seat x.2)) = [] :=
      List.filter_eq_nil_iff.2 fun _ _ => by simp
    rw [e]
    exact List.nodup_nil
  · rw [e0]
    exact nodup_of_B h

/-- **hNd OF THE FOURTH TIE AT A PLACE**, at minePad := minePadAt (msOf L) N links p, from the test
on the members at a code switch. -/
theorem k02_t4R_hNd {L : MemberLists} {nq : List (ℕ × ℕ)} {r : SwRow} (N : Numbers)
    (links : List ModelPart) (p : Place)
    (h : membersK2B L (N.keptOf (p.link.getD links.length - 1)) nq r = true) :
    ((minePadAt (msOf L) N links p).map seatOf).Nodup := by
  unfold membersK2B at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact pads_nodup_once N links p h.1.1.2

/-! ## 4 Two clauses of tests from other files -/

/-- Where the test on the members at a code switch passes there are no fewer new tenants than typed
new members (the test asks as many). -/
theorem new_long_enough {L : MemberLists} {kq nq : List (ℕ × ℕ)} {r : SwRow}
    (h : membersK2B L kq nq r = true) : r.l.length ≤ nq.length := by
  unfold membersK2B at h
  rw [Bool.and_eq_true] at h
  exact Nat.le_of_eq (beq_iff_eq.1 h.2).symm

/-- The test on the numbers is a clause of `planSideOk`, the one test on those letters of the table
of joints that come of the list of rounds. -/
theorem numbers_of_side {Xi : Type} {Fd : FileDescription Xi} {codes : OnBytes.Codes} {L : MemberLists}
    {arr : ℕ → ℕ → ℕ} {N : Numbers} {links : List ModelPart} {ps : List Place}
    (h : planSideOk Fd codes L arr N links ps = true) :
    numbersFit (oraclesOf Fd.first.blocksInOrder) N links.length = true := by
  simp only [planSideOk, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.2

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.laysPads_cases
#print axioms VerifiableInference.Desc.First.K2Caller.new_not_kept
#print axioms VerifiableInference.Desc.First.K2Caller.seatNew_off_pads
#print axioms VerifiableInference.Desc.First.K2Caller.msgs_stay_at
#print axioms VerifiableInference.Desc.First.K2Caller.k02_t4R_hE
#print axioms VerifiableInference.Desc.First.K2Caller.msgs_stay_table
#print axioms VerifiableInference.Desc.First.K2Caller.pads_nodup_once
#print axioms VerifiableInference.Desc.First.K2Caller.k02_t4R_hNd
#print axioms VerifiableInference.Desc.First.K2Caller.new_long_enough
#print axioms VerifiableInference.Desc.First.K2Caller.numbers_of_side
