-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieMatFront.lean: tieMatS_of_owners (TieMatOwners.lean) WITH THE PUBLIC HALF AT THE PART IN
FRONT OF THE MEMBER. What the library has at a reached state, behind the promise, is the seats in front of a segment's reads
(firstSeated_at_reads, Johnson/Desc/AtSeats/FirstSeatedAtReads.lean; the fold facts). The reads' member then rides: Rides, and
cell_back (Johnson/Desc/K1/Law/ArmAttMats.lean) carries a seated cell from the part behind to the part in front.

  MatSeatF            the public half, at the part A in front and the part B behind
  tieMatS_of_front    TieMatS from MatSeatF, OwnerHolds, hLay, hSame


NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieMatOwners
import Johnson.Desc.K1.Law.ArmAttMats

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt cellsAt_name dataQ seatTab seatOf seatBy noFirst Rides)
open OnBytes.HonestTrace (Sz packedCells)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **Public, at a stand: where matrix ν of segment l is read, at the part in front.** g: the seats of
the segment's first commitment. own: the owner's number, segment, matrix and array, off the plan.
A definition: a premise's form. -/
def MatSeatF (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (cs : OnBytes.Codes)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Sz₀ : Sz) (b l NM : ℕ) (g : List (ℕ × ℕ))
    (own : ℕ → ℕ × ℕ × ℕ × ReqArray) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ tl : HTailF2, s'.tl? = some tl → tl.NM = NM ∧ ∃ A B : K9.Part, K9.segAt? s = some A ∧
    K9.segAt? s' = some B ∧ Rides g A B ∧ A.d.st.codes = cs ∧
    ∀ ν, ν < NM → ∃ (q : ℕ × ℕ) (yM : Mem) (o : ℕ) (x : _) (sh : OracleShape) (c₁ : ℕ × String)
        (a₁ : ReqArray) (l₀ ν₀ : ℕ),
      g.contains q = true ∧ A.d.st.oracles[o]? = some x ∧ x.shape = sh ∧
      A.d.book.place[o]? = some q ∧ seatBy noFirst A.d.book o = some q ∧
      (ms.find? fun z => decide (seatOf z = q)) = some yM ∧ (yM.1.l.get yM.2).1 = sh ∧
      A.L.arrayOf[tl.gtTree.getD ν 0]? = some c₁ ∧
      reqArray A.L.check.rows.layout c₁.1 c₁.2 = some a₁ ∧
      A.L.check.frame.whereIs c₁.1 a₁.message = some o ∧
      laidMatrixOk a₁ (A.d.st.rowBits o .main) (A.d.st.placeBits o .main) = true ∧
      own ν = (arr q.1 q.2, l₀, ν₀, a₁) ∧
      Sz₀.packedShape l ν = Sz₀.packedShape l₀ ν₀ ∧
      ∀ i c rp, i < (Sz₀.packedShape l ν).1 → c < (Sz₀.packedShape l ν).2 →
        laidAt a₁ i c = some rp → rp.1 < sh.mainRows ∧ padB cs sh false rp.1 rp.2 = false

/-- **The first family at every segment, from the part in front.** -/
theorem tieMatS_of_front {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {cs : OnBytes.Codes}
    {arr : ℕ → ℕ → ℕ} {ms : List Mem} {Sz₀ : Sz} {wit : Local W₀ Rc Xi Tr' → PlaceIn Xi}
    {b l NM N : ℕ} {g : List (ℕ × ℕ)} {own : ℕ → ℕ × ℕ × ℕ × ReqArray}
    (hSeat : MatSeatF L Said cs arr ms Sz₀ b l NM g own)
    (hsub : ∀ x ∈ g, x ∈ L.N.group l)
    (hN : N ≤ L.thread.front + roundsTo L.bs b)
    (hHold : ∀ ν, ν < NM → ∀ n l₀ ν₀ a, own ν = (n, l₀, ν₀, a) → OwnerHolds L wit Sz₀ n N l₀ ν₀ a)
    (hLay : ∀ ν, ν < NM → ∀ n l₀ ν₀ a, own ν = (n, l₀, ν₀, a) → ∀ i c,
      i < (Sz₀.packedShape l ν).1 → c < (Sz₀.packedShape l ν).2 → ∃ rp, laidAt a i c = some rp)
    (hSame : ∀ w, L.valid w → ∀ ν, ν < NM → ∀ n l₀ ν₀ a, own ν = (n, l₀, ν₀, a) → ∀ i c,
      i < (Sz₀.packedShape l ν).1 → c < (Sz₀.packedShape l ν).2 →
      packedCells Sz₀ (wit w).R.cells.cell l₀ ν₀ i c = packedCells Sz₀ (wit w).R.cells.cell l ν i c) :
    TieMatS L Said cs arr ms Sz₀ wit b l := by
  intro blk hb k s μ E ds y cols s' hA hd hS tl htl ds' A' hAe ν hν c hc i' hi'
  obtain ⟨hNM, A, B, hfront, hbehind, hR, hcs, hall⟩ := hSeat blk hb k s μ E ds y cols s' hA hd hS tl htl
  have hν' : ν < NM := hNM ▸ hν
  obtain ⟨q, yM, o, x, sh, c₁, a₁, l₀, ν₀, hown, hx, hxs, hq, hseat, hy, hsh, hc₁, ha, ho, hok, hO,
    hShape, hoff⟩ := hall ν hν'
  obtain ⟨rp, hrp⟩ := hLay ν hν' _ _ _ _ hO i' c hi' hc
  obtain ⟨hr, hpad⟩ := hoff i' c rp hi' hc hrp
  have hval : L.valid μ.st.input := hA.1.2.2.2.2.2.2
  have hlenH : μ.st.heard.length = L.thread.front + roundsTo L.bs b := by
    have q' := drawsFit_length _ _ hA.1.2.1
    rw [q', List.length_append]
    rfl
  have hlen : N ≤ (μ.st.heard ++ (ds ++ ds')).length := by
    rw [List.length_append, hlenH]
    omega
  have hin : (K9.arrayIn g A (tl.gtTree.getD ν 0)).isSome = true := by
    unfold K9.arrayIn
    rw [hc₁]
    show ((reqArray A.L.check.rows.layout c₁.1 c₁.2).bind _).isSome = true
    rw [ha]
    show ((A.L.check.frame.whereIs c₁.1 a₁.message).bind _).isSome = true
    rw [ho]
    show ((K9.seatAt g A.d.book o).map _).isSome = true
    unfold K9.seatAt
    rw [hq]
    show ((if g.contains q then some q else none).map _).isSome = true
    rw [if_pos hown]
    rfl
  obtain ⟨cn, hcn, hback⟩ := VerifiableInference.Desc.K1.cell_back g (L.N.group l) hsub A B
    (seatTab cs arr ms (L.Q.wit k μ.st.input (μ.st.heard ++ (ds ++ ds')))) hR _ hin
  obtain rfl : cn = c₁ := Option.some.inj (hcn.symm.trans hc₁)
  have hc₁B : B.L.arrayOf[tl.gtTree.getD ν 0]? = some cn := by
    rw [hR.arrays]
    exact hc₁
  subst hAe
  rw [cellsAt_name _ arr ms L.N l _ s' _ B hbehind (tl.gtTree.getD ν 0) cn hc₁B i' c, hback i' c,
    cell_at_seat cs arr ms g A _ cn a₁ o i' c rp sh q yM x ha ho hok hrp hx hxs hq hseat hown hy hsh
      hcs hr hpad,
    hHold ν hν' _ _ _ _ hO k μ.st.input _ hval hlen i' c rp hrp (hShape ▸ hc) (hShape ▸ hi'),
    hSame μ.st.input hval ν hν' _ _ _ _ hO i' c hi' hc]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tieMatS_of_front
