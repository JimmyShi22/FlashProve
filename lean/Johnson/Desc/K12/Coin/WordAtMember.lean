-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/WordAtMember.lean:
The proximity test (the kind K12), first arm (the first fold's mask has come ahead), at the
numbering of trees by labels: ONE MEMBER OF THE GROUP UNDER TEST: its word off the frame's strings
is the committed word at its seat. General in the IOP as written in Lean, the frame, the place, the
first tree's number ft, the offset lo and the member. Statements and proofs: calls.
  `MemberPub`: a Lean structure: what the law asks of a member on the list of rounds and the list
    of members alone.
  `nu_at`: where the mask has come, the place's first tree is ft and the book is in order from ft
    on, the numbering by labels is z ↦ lo + z at the book's own trees.
  `seatIs_at`: `SeatIs` (FramesTie.lean) at a member whose place in the book is q, at the seat
    (lo + q.1, q.2), where the book's tree at q.1, if there is one, has the shape that the IOP as
    written tells (that there is one is read off what the test's own plain data hold).
  `word_at`: the last clause of `MemberFacts` (Johnson/Desc/Sound/SeamMembers.lean) as an
    equation, at the member's own list of shapes: `wordsOf_is_strOf` (FramesMeet.lean) called there.
  `log_at`: the member's tree's depth is the log-length of its listed shape's code.
  `dep_at`: the member's tree's depth is at most the first stage's mask code's, from one comparison
    of closed numbers.
KIN: K12Left2910.lean (`nu_29` · `seatIs_29` · `word_29`) and K12Members29.lean (`dep_at_29`)
say the same at the key file's six messages, at ft = 0, through a lemma on a list of one member.
What it is not. Every premise is a premise; none is shown here. No example. It pays no field of a
table. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.FirstBook
import Johnson.Desc.K12.Coin.GameLabelsO
import Johnson.Desc.Sound.FramesMeet
import Johnson.Desc.K1.Law.Port2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.First (made_of)
open H2K.Pin (strOf layOf)

/-- **What the law asks of a member on the list of rounds and the list of members alone**: no state
is read. With s the member's listed shape and e0 its listed radius. -/
structure MemberPub (cs : Codes) {Xi : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (r : Fmt.M1.Stage → ℕ) (x : Mem) : Prop where
  tie : K1.Tie cs (x.1.l.get x.2).1
  /-- rows of one kind -/
  one : ¬ (0 < (x.1.l.get x.2).1.mainRows ∧ 0 < (x.1.l.get x.2).1.maskRows)
  case : (0 < (x.1.l.get x.2).1.maskRows ∨ (x.1.l.get x.2).1.mainDeg = 3) ∨
    ((x.1.l.get x.2).1.maskRows = 0 ∧ (x.1.l.get x.2).1.mainDeg = 1)
  /-- main rows; or mask rows alone, with the depth's comparison at the first stage. (The
  first arm asks nothing of the mask code's number: what the site's test asks of the code of a part
  without rows follows from the told depth: `log_at`.) -/
  site : 0 < (x.1.l.get x.2).1.mainRows ∨
    (0 < (x.1.l.get x.2).1.maskRows ∧ cs.base.size ≤ (x.1.l.get x.2).1.code ∧
      ∀ st rest, π.nums.stages = st :: rest → aOf cs (x.1.l.get x.2).1 ≤ st.Z.a)
  /-- the test's radius at the first stage against the member's listed radius -/
  fit : ∀ st rest, π.nums.stages = st :: rest →
    r (H2K.Pub.sgOf st).st <
      ((x.1.l.get x.2).2 + 1) * 2 ^ ((H2K.Pub.sgOf st).C.a - aOf cs (x.1.l.get x.2).1)
  fits : SeatFits G cs x.1.l x.1.seat
  /-- the frame lists the member's tree no deeper than the IOP as written tells -/
  depth : ∀ u, G.oracleAt (x.1.seat x.2).1 = some u →
    ∀ e ∈ Fr.all, e.no = (x.1.seat x.2).1 → e.a ≤ u.logLength

section
variable (π : P12) (lo ft : ℕ) (t : T12) {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
  {G0 : OnBytes.Group} {Ly : GroupLayout} {D : H2K.First.Plain}

/-- **The numbering by labels is z ↦ lo + z** at the book's own trees. -/
theorem nu_at (hf : Fixes π t a rest G0 Ly D) (hmk : t.mask.isSome = true)
    (hft : π.nums.firstTree = ft) (hB : BookOrd ft t.book) (z : ℕ)
    (hz : z < t.book.trees.size) : nuOf π (nlAt π lo) t z = lo + z := by
  rw [nuOf_of_fixes hf, book_of_fixes π t hmk a rest G0 Ly D hf]
  unfold nlAt H2K.First.numAt
  have hT : t.book.trees[z]? = some t.book.trees[z] := Array.getElem?_eq_getElem hz
  rw [hft, hT, Option.map_some, Option.getD_some, hB z _ hT]
  omega

/-- **`SeatIs` at a member**, at the seat that its place in the book names. -/
theorem seatIs_at (hf : Fixes π t a rest G0 Ly D) (hmk : t.mask.isSome = true)
    (hft : π.nums.firstTree = ft) (hB : BookOrd ft t.book) (j : Fin D.mems.length) (q : ℕ × ℕ)
    (hq : t.book.place[(D.mems.get j).id]? = some q) (u : VerifiableInference.Desc.Oracle)
    (hshape : ∀ T, t.book.trees[q.1]? = some T → ShapeIs T.shape u) :
    SeatIs (nuOf π (nlAt π lo) t) D.book (D.mems.get j) (lo + q.1) q.2 u := by
  have hbk := book_of_fixes π t hmk a rest G0 Ly D hf
  have hM := made_of π _ a Ly D (hf.2.2.2 default)
  obtain ⟨_, _, hpl, T0, hT0, _, _⟩ := hM.mem j
  rw [hbk, hq] at hpl
  rw [hbk] at hT0
  have e2 := Option.some.inj hpl
  refine seatIs_of_made hM _ j _ _ u (fun z v e => ?_) (fun z v T e eT => ?_)
  · rw [hbk, hq] at e
    obtain rfl := Option.some.inj e
    have hz : z < t.book.trees.size := by
      have e3 : z = (D.mems.get j).t := congrArg Prod.fst e2
      rw [e3]
      exact (Array.getElem?_eq_some_iff.1 hT0).1
    exact ⟨nu_at π lo ft t hf hmk hft hB z hz, rfl⟩
  · rw [hbk, hq] at e
    obtain rfl := Option.some.inj e
    rw [hbk] at eT
    exact hshape T eT

variable (cs : Codes) {Xi : Type} (G : FileDescription Xi) (Fr : Frame)

/-- **A member's word off the frame's strings is the committed word at its seat.** -/
theorem word_at (hf : Fixes π t a rest G0 Ly D) (hmk : t.mask.isSome = true)
    (hft : π.nums.firstTree = ft) (hB : BookOrd ft t.book) (j : Fin D.mems.length) (q : ℕ × ℕ)
    (hq : t.book.place[(D.mems.get j).id]? = some q) (x : Mem)
    (hseat : x.1.seat x.2 = (lo + q.1, q.2)) (y : Fr.E.Str)
    (hF : SeatFits G cs x.1.l x.1.seat) (hS : ShownAt G cs x.1.l x.1.seat (strsOf Fr y) x.2)
    (htold : ∀ u, G.oracleAt (x.1.seat x.2).1 = some u →
      ∀ T, t.book.trees[q.1]? = some T → ShapeIs T.shape u)
    (hd : ∀ u, G.oracleAt (x.1.seat x.2).1 = some u →
      ∀ e ∈ Fr.all, e.no = (x.1.seat x.2).1 → e.a ≤ u.logLength) :
    Sound.wordsOf G cs x.1.l x.1.seat (strsOf Fr y) x.2 =
      strOf cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 (layOf (D.mems.get j))
        (W0 Fr (nuOf π (nlAt π lo) t) D.book y (D.mems.get j).t).1
        (W0 Fr (nuOf π (nlAt π lo) t) D.book y (D.mems.get j).t).2 :=
  wordsOf_is_strOf cs G x.1.l x.1.seat Fr _ D.book y x.2 (D.mems.get j) hF hS
    (fun u hu => by
      have S := seatIs_at π lo ft t hf hmk hft hB j q hq u (htold u hu)
      rw [hseat]
      exact S) hd

/-- **The member's tree's depth is the log-length of its listed shape's code.** -/
theorem log_at (hf : Fixes π t a rest G0 Ly D) (hmk : t.mask.isSome = true)
    (hft : π.nums.firstTree = ft) (hB : BookOrd ft t.book) (j : Fin D.mems.length) (q : ℕ × ℕ)
    (hq : t.book.place[(D.mems.get j).id]? = some q) (x : Mem)
    (hF : SeatFits G cs x.1.l x.1.seat)
    (htold : ∀ u, G.oracleAt (x.1.seat x.2).1 = some u →
      ∀ T, t.book.trees[q.1]? = some T → ShapeIs T.shape u) :
    (D.mems.get j).tsh.logN = aOf cs (x.1.l.get x.2).1 := by
  obtain ⟨u, _, hu, _, hlog, _⟩ := hF x.2
  have S := seatIs_at π 0 ft t hf hmk hft hB j q hq u (htold u hu)
  rw [S.log, hlog]

/-- **The member's tree is no deeper than the first stage's mask code.** -/
theorem dep_at (hf : Fixes π t a rest G0 Ly D) (hmk : t.mask.isSome = true)
    (hft : π.nums.firstTree = ft) (hB : BookOrd ft t.book) (j : Fin D.mems.length) (q : ℕ × ℕ)
    (hq : t.book.place[(D.mems.get j).id]? = some q) (x : Mem)
    (hF : SeatFits G cs x.1.l x.1.seat)
    (htold : ∀ u, G.oracleAt (x.1.seat x.2).1 = some u →
      ∀ T, t.book.trees[q.1]? = some T → ShapeIs T.shape u)
    (hZ : aOf cs (x.1.l.get x.2).1 ≤ a.Z.a) : (D.mems.get j).tsh.logN ≤ a.Z.a := by
  rw [log_at π ft t cs G hf hmk hft hB j q hq x hF htold]
  exact hZ

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.nu_at
#print axioms VerifiableInference.Desc.K12.Coin.seatIs_at
#print axioms VerifiableInference.Desc.K12.Coin.word_at
#print axioms VerifiableInference.Desc.K12.Coin.log_at
#print axioms VerifiableInference.Desc.K12.Coin.dep_at
