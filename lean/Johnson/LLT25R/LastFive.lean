-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastFive.lean:
FOUR OF THE SEVEN CONJUNCTS OF `FiveAt`
(LastMembers.lean: what the seam still asks of one member at the last chain's own proximity
test) FROM TESTS ON THE PLAN AND TWO FACTS ON THE VERIFIER's STATE.
  `BookAt G no D j x`: the two facts, at a member j of the data and a member x of the lists: by the
    data's book the member's place is (a place whose tree has x's seat's number through the file,
    x's seat's tenant); the tree there has the shape that the description G tells of that tree.
    WHICH SHAPE IT ASKS: THE ONE THAT THE DESCRIPTION TELLS OF THE TREE WITH THAT NUMBER (`ShapeIs
    T.shape o` at o := what G tells); at Omega's copy it does NOT ask that the new tree has the
    shape of the shared chain's tree which it takes the number and the source of: K14's second part
    lays the new tree's shape by the verifier's own layout of the plan's notice for Omega, and
    compares it with the shared book's nowhere (Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean, its Limits (2)).
  `site_word`: **the yes of `siteL` and "the word as sent is the table's"**: from `Fixes`, the
    game's own conclusion `NTuple`, the state's message at the member's number has x's shape,
    `BookAt`, and on the plan: the seat fits (`SeatFits`); the description tells a tree at x's seat;
    `ShapeFits` at x's shape and that tree's depth; no column of the frame at that tree is deeper
    than it; and from the promise: every leaf is shown. By `site_of_tuple`,
    `wordsOf_is_strOf` and `seatIs_of_made`.
  `codes_at_W`: inside the book-keeping's yes at border 2 the data's codes are the plan's.
  `PlanAt`: the tests on the plan at one of mine, with the shape's tie and "the radius fits".
    `five_of`: **`FiveAt` from `PlanAt`, `BookAt`, the message's shape, "shown", and the three
    conjuncts on the OOD sample (the invariant, the reader, the yes of `sampleL`).**
Limits. `BookAt` and the three on the OOD sample are shown at no state; `PlanAt` is evaluated
nowhere. Nothing on soundness.
-/
import Johnson.LLT25R.LastMembers
import Johnson.Desc.K12.Coin.SiteAtSeats
import Johnson.Desc.K12.Coin.FramesTie
import Johnson.Desc.Sound.FramesMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open Cb Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Johnson.Pack
open OnBytes.Means H2K.ClaimSays H2K.Pin
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Third
open H2K.First (Plain made_of)
open H2K.Pub (sgOf)
open _root_.Run

/-- **Two facts on the verifier's state**: where the member lies by the data's book, and what
shape its tree has there. -/
def BookAt {Xi : Type} (G : FileDescription Xi) (no : ℕ → ℕ) (D : Plain) (j : Fin D.mems.length)
    (x : Mem) : Prop :=
  (∀ z u, D.book.place[(D.mems.get j).id]? = some (z, u) →
    no z = (seatOf x).1 ∧ u = (seatOf x).2) ∧
  ∀ z u T, D.book.place[(D.mems.get j).id]? = some (z, u) → D.book.trees[z]? = some T →
    ∀ o, G.oracleAt (seatOf x).1 = some o → ShapeIs T.shape o

/-- **The yes of `siteL`, and the word.** -/
theorem site_word (cs : Codes) {Xi : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (t : T12) (y : Fr.E.Str) (st : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t st rest G0 Ly D) (hN : NTuple Fr π no rad rd (t, y) st rest G0 Ly D)
    (hcs : D.st.codes = cs) (j : Fin D.mems.length) (x : Mem)
    (hsh : (t.st.oracles[(D.mems.get j).id]?).map (·.shape) = some (x.1.l.get x.2).1)
    (hB : BookAt G no D j x) (hF : SeatFits G cs x.1.l x.1.seat)
    (hS : ShownAt G cs x.1.l x.1.seat (strsOf Fr y) x.2)
    (told : ∃ o, G.oracleAt (seatOf x).1 = some o)
    (fits : ∀ o, G.oracleAt (seatOf x).1 = some o →
      ShapeFits cs st (x.1.l.get x.2).1 o.logLength)
    (hd : ∀ o, G.oracleAt (seatOf x).1 = some o →
      ∀ e ∈ Fr.all, e.no = (seatOf x).1 → e.a ≤ o.logLength) :
    ok (siteL cs st (D.mems.get j)) = true ∧
      HEq (strOf cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 (layOf (D.mems.get j))
          (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
        (VerifiableInference.Desc.Sound.wordsOf G cs x.1.l x.1.seat (strsOf Fr y) x.2) := by
  have hm := made_of π _ st Ly D (hf.2.2.2 default)
  have hI : ∀ o, G.oracleAt (seatOf x).1 = some o →
      SeatIs no D.book (D.mems.get j) (seatOf x).1 (seatOf x).2 o := fun o ho =>
    seatIs_of_made hm no j _ _ o hB.1 fun z u T hp hT => hB.2 z u T hp hT o ho
  obtain ⟨xo, hxo, exo⟩ := Option.map_eq_some_iff.1 hsh
  obtain ⟨o, ho⟩ := told
  refine ⟨site_of_tuple no rad rd y hf hN cs hcs j xo hxo ?_, ?_⟩
  · rw [exo, (hI o ho).log]
    exact fits o ho
  · exact heq_of_eq
      (wordsOf_is_strOf cs G x.1.l x.1.seat Fr no D.book y x.2 (D.mems.get j) hF hS hI hd).symm

/-- Inside the book-keeping's yes at border 2 the data's codes are the plan's. -/
theorem codes_at_W (p : P₁₄) (R : List Fmt.DeclaredRound) (f : VerifiableInference.Desc.Last.Handed)
    (e : SharedOut) (s : S₃) (t : T12) (π : P12)
    (hk : VerifiableInference.Desc.Last.shapeAt p R 2 f e s = true)
    (ht : VerifiableInference.Desc.K12.Seat.enterOwn s = .ok t) (st : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t st rest G0 Ly D) : D.st.codes = p.codes := by
  obtain ⟨⟨s₀, B⟩, -⟩ := VerifiableInference.Desc.Last.behindOk_of_two hk
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨-, hc⟩ := start_codes B.start
  have e0 : t.st = s.st := by
    obtain rfl : _ = t := Except.ok.inj ht
    rfl
  rw [_root_.Desc.K14.Law.Fence.codes_fixed π t st rest G0 Ly D hf, e0, L.codes, hc]

/-- **The tests on the plan, at one of mine and the test's first stage.** -/
def PlanAt (cs : Codes) {Xi : Type} (G : FileDescription Xi) (Fr : Frame) (r : Fmt.M1.Stage → ℕ)
    (st : Fmt.M1.Stage) (x : Mem) : Prop :=
  K1.Tie cs (x.1.l.get x.2).1 ∧
  r (sgOf st).st < ((x.1.l.get x.2).2 + 1) * 2 ^ ((sgOf st).C.a - aOf cs (x.1.l.get x.2).1) ∧
  SeatFits G cs x.1.l x.1.seat ∧
  (∃ o, G.oracleAt (seatOf x).1 = some o) ∧
  (∀ o, G.oracleAt (seatOf x).1 = some o → ShapeFits cs st (x.1.l.get x.2).1 o.logLength) ∧
  ∀ o, G.oracleAt (seatOf x).1 = some o → ∀ e ∈ Fr.all, e.no = (seatOf x).1 → e.a ≤ o.logLength

/-- **`FiveAt`.** -/
theorem five_of {P S₁ S₂ : Type} {Fr : Frame} (p : P₁₄) {Xi : Type} (G : FileDescription Xi)
    (smp : ((P × S₁ × S₂) × S₃) → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf p.codes s.l).om i).Smp)
    (π : P12) (no : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ)
    (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) (t : T12) (st : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t st rest G0 Ly D)
    (hN : NTuple Fr π no (fun s => r s.st) rd (t, a.2) st rest G0 Ly D)
    (hcs : D.st.codes = p.codes) (j : Fin D.mems.length) (x : Mem)
    (hsh : (t.st.oracles[(D.mems.get j).id]?).map (·.shape) = some (x.1.l.get x.2).1)
    (hPl : PlanAt p.codes G Fr r st x) (hB : BookAt G no D j x)
    (hS : ShownAt G p.codes x.1.l x.1.seat (strsOf Fr a.2) x.2)
    (hseed : ∃ ρ yv, K1.SeedIs p.codes (x.1.l.get x.2).1 t.st (D.mems.get j).id ρ yv)
    (hsmp : smp a.1 x.1 x.2 =
      K1.smpAt p.codes (x.1.l.get x.2).1 (x.1.l.get x.2).2 t.st (D.mems.get j).id)
    (h2 : ∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
      ok (sampleL p.codes (D.mems.get j) o) = true) :
    FiveAt p G smp no r a t st D j x := by
  obtain ⟨hT, h3, hF, told, fits, hd⟩ := hPl
  obtain ⟨h1, h7⟩ := site_word p.codes G Fr π no (fun s => r s.st) rd t a.2 st rest G0 Ly D hf hN
      hcs
    j x hsh hB hF hS told fits hd
  exact ⟨hT, hseed, hsmp, h1, h2, h3, h7⟩

end LLT25

#print axioms LLT25.codes_at_W
#print axioms LLT25.site_word
#print axioms LLT25.five_of
